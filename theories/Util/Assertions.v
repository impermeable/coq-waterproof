(******************************************************************************)
(*                  This file is part of Waterproof-lib.                      *)
(*                                                                            *)
(*   Waterproof-lib is free software: you can redistribute it and/or modify   *)
(*    it under the terms of the GNU General Public License as published by    *)
(*     the Free Software Foundation, either version 3 of the License, or      *)
(*                    (at your option) any later version.                     *)
(*                                                                            *)
(*     Waterproof-lib is distributed in the hope that it will be useful,      *)
(*      but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*       MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the         *)
(*               GNU General Public License for more details.                 *)
(*                                                                            *)
(*     You should have received a copy of the GNU General Public License      *)
(*   along with Waterproof-lib. If not, see <https://www.gnu.org/licenses/>.  *)
(*                                                                            *)
(******************************************************************************)

Require Import Ltac2.Ltac2.
Require Import Ltac2.Int.
Require Import Ltac2.Message.
Require Import Waterproof.Waterproof.
Require Import Waterproof.Util.MessagesToUser.

Require Import Util.Init.

Local Ltac2 concat_list (ls : message list) : message :=
  List.fold_right concat (of_string "") ls.

(**   Introduce global test verbosity. *)
Ltac2 mutable test_verbosity () := 0.

Ltac2 Type exn ::= [ TestFailedError(message) ].

Ltac2 fail_test (msg:message) := 
  Control.zero (TestFailedError msg).

Definition type_of_test_aux {T : Type} (x : T) := T.

(**
  A function that prints a message in case a test is passed. The function only prints if the global test_verbosity is larger than or equal than 1.

  Arguments:
    - [msg : message] The message to print on success.
*)
Ltac2 print_success (msg : message) := 
  match (ge (test_verbosity ()) 1) with 
    |  false => ()
    |  _ => print msg
  end.

(**
  Checks if the function "f" raises an error when evaluated.

  Arguments:
    - f, function without arguments.
    
  Raises Exceptions:
    - TestFailedError, if the execution of "f" does **not** raise a catchable exception.
*)
Ltac2 assert_raises_error f :=
  match Control.case f with
    | Val _ => fail_test (of_string "Should raise an error")
    | Err exn => print_success (concat 
      (of_string "Test passed, got error:") 
      (of_exn exn))
  end.

(**
  Checks if a tactic fails with error message corresponding to a specific string

  Arguments:
    - tac, the tactic to execute
    - expected_string, the expected error message

  Raises Exceptions:
    - TestFailedError, if the tactic does not fail or if it fails with the wrong error message
*)
Ltac2 assert_fails_with_string (tac : unit -> 'a) (expected_string : string) :=
  match Control.case tac with
  | Val _ => fail_test (of_string ("The tactic was expected to fail but it didn't"))
  | Err exn =>
    let inner_msg_equal := fun msg =>
      String.equal (Message.to_string msg) expected_string in
    let inner_msg_test := fun msg =>
      if inner_msg_equal msg then
        print_success (of_string ("The tactic failed with the expected error message"))
      else
        fail_test (concat_list [of_string "The tactic failed, but with an unexpected error message. Expected:"; fnl ();
        of_string expected_string; fnl (); of_string "Got:"; fnl (); msg]) in
    match exn with
    | RedirectedToUserError msg => inner_msg_test msg
    | TestFailedError msg => inner_msg_test msg
    (** TODO: add more possible errors here *)
    | e => 
      let msg := Message.of_exn e in
      inner_msg_test msg
    end
  end.

Ltac2 @ external get_last_warning : unit -> message option :=
  "coq-waterproof" "get_last_warning_external".
Ltac2 @ external get_feedback_log : unit -> message list :=
  "coq-waterproof" "get_feedback_log_external".

(**
  Checks if a tactic warns with warning corresponding to a specific string

  Arguments:
    - tac, the tactic to execute
    - expected_string, the expected warning message

  Raises exceptions:
    - TestFailedError, if the tactic does not warn or if it warns with the wrong warning message
*)
Ltac2 assert_warns_with_string (tac : unit -> 'a) (expected_string : string) :=
  let length_before := List.length (get_feedback_log ()) in
  tac ();
  let length_after := List.length (get_feedback_log ()) in
  if Int.equal length_after length_before then
    fail_test (of_string ("The tactic was expected to warn but it didn't"))
  else
  match get_last_warning () with
  | Some msg =>
    if String.equal (Message.to_string msg) expected_string then
      print_success (of_string ("The tactic warned with the expected message"))
    else
      fail_test (concat_list [of_string "The tactic warned, but with an unexpected error message. Expected:"; fnl (); of_string expected_string; fnl ();
      of_string "Got:"; fnl (); of_string (to_string msg)])
  | None => fail_test (of_string ("No warning was registered"))
  end.

(**
  Checks if a tactic warns

  Arguments:
    - tac, the tactic to execute

  Raises exceptions:
    - TestFailedError, if the tactic does not warn or if it warns with the wrong warning message
*)
Ltac2 assert_warns (tac : unit -> 'a) :=
  let length_before := List.length (get_feedback_log ()) in
  tac ();
  let length_after := List.length (get_feedback_log ()) in
  if Int.equal length_after length_before then
    fail_test (of_string ("The tactic was expected to warn but it didn't"))
  else
    print_success (of_string ("The tactic warned")).

(**
  Checks if two lists (of arbitrary type) are equal. 
  
  Raises an error if they have different lengths, or that there exists an index such that their value at that index differs.

  Arguments:
    - x, y: ('a list), lists of arbitrary type to be compared.

  Raises Exceptions:
    - TestFailedError, if x and y have a different length.
    - TestFailedError, if there exists an i such that x[i] ≠ y[i].
*)
Ltac2 rec assert_list_equal (f : 'a -> 'a -> bool) (of_a : 'a -> message) (x:'a list) (y: 'a list) :=    
  match x with
    | x_head::x_tail =>
      match y with
        | y_head::y_tail =>
          match (f x_head y_head) with
            | true => assert_list_equal f of_a x_tail y_tail
            | false =>
              fail_test 
                (concat 
                  (of_string "Unequal elements:") 
                  (concat (of_a x_head) (of_a y_head))
                )
          end
        | [] => fail_test (of_string "First list has more elements")
      end
    | [] => 
      match y with
        | [] => print_success (of_string "Test passed: lists indeed equal")
        | y_head::y_tai => fail_test (of_string "Second list has more elements")
      end
  end.

(**
  Asserts that the hypothesis of the given ident exists in the current environment.

  Arguments:
    - [h : ident], identifier of target hypothesis

  Raises Exceptions:
    - [TestFailedError], if there is no hypothesis with the identifier stored in [h] in the current context.
*)
Ltac2 assert_hyp_exists (h: ident) :=
  match Control.case (fun () => Control.hyp h) with
    | Val _ => print_success(concat (of_string "Indeed hyp exists:") (of_ident h))
    | Err exn => fail_test (concat (of_exn exn) (of_string "Hyp not found"))
  end.

(**
  Asserts that the hypothesis of the given ident exists in the current environment, AND has the indicated type.

  Arguments:
    - [h : ident], identifier of target hypothesis.
    - [t : constr], expected type of the hypothesis identified by the value of [h].

  Raises Exceptions:
    - [TestFailedError], if there is no hypothesis with the identifier stored in [h] in the current context.
    - [TestFailedError], if the hypothesis identified by [h] has a different type than [t]. Types are normalized before comparison.
*)
Ltac2 assert_hyp_has_type (h: ident) (t: constr) :=
  assert_hyp_exists h;
  let h_val := Control.hyp h in
  let h_normalized :=  (eval cbv in (type_of_test_aux $h_val)) in
  let t_normalized :=  (eval cbv in $t) in
  match Constr.equal h_normalized t_normalized with
    | true => print_success
      (concat
        (concat (of_string "Hypothesis '") (of_ident h))
        (concat (of_string "' indeed has type: ") (of_constr t))
      )
  
    | false =>
      fail_test (concat
        (concat
          (of_string "Hypothesis has wrong type. Expected type: ") 
          (of_constr t)
        )
        (concat
          (of_string ", actual type: ") 
          (of_constr (eval cbv in (type_of_test_aux $h_val)))
        )
      )
  end.

(**
  Asserts that the constr-variable describes a Gallina [bool] with value [true].

  Arguments:
    - [b: constr], should equal [true].

  Raises Exceptions:
    - [TestFailedError], if [b] is not a [bool].
    - [TestFailedError], if [b] is [false].
*)
Ltac2 assert_constr_is_true (b:constr) :=
  match Constr.equal b constr:(true) with
    | true => print_success (of_string "Test passed: received constr:(true)")
    | false => fail_test (of_string "Did not get a constr equal to a bool with value true")
  end.

(**
  Asserts that the Ltac2-variable is a bool with value [true].

    Arguments:
        - [b: bool], should equal [true].

    Raises Exceptions:
        - [TestFailedError], if [b] is not a [bool].
        - [TestFailedError], if [b] is [false].
*)
Ltac2 assert_is_true (b:bool) :=
  match b with
    | true => print_success (of_string "Test passed: received true")
    | false => fail_test (of_string "Expected Ltac2 true, got Ltac2 bool 'false'")
  end.

(**
  Asserts that the Ltac2-variable is a bool with value [false].

  Arguments:
    - [b: bool], should equal [false].

  Raises Exceptions:
    - [TestFailedError], if b is not a [bool].
    - [TestFailedError], if b is [true].
*)
Ltac2 assert_is_false (b:bool) :=
  match b with
    | false => print_success (of_string "Test passed: received false")
    |  true => fail_test (of_string "Expected Ltac2 FALSE, got Ltac2 bool 'true'")
  end.

Local Ltac2 rec string_equal_rec (idx) (s1:string) (s2:string) :=
  (* If the strings are of unequal length, 
      then they are never equal*)
  let len1 := (String.length s1) in
  let len2 := (String.length s2) in
  match Int.equal len1 len2 with
    | false => false
    | true => 
      (* If we are past the last index of the strings,
      then stop and return "true".
      Otherwise, compare the integer representation
      of the characters of the current index and recurse.*)
      match (Int.equal idx len1) with
        | true => true
        | false =>
          let ascii_int_1 := Char.to_int (String.get s1 idx) in
          let ascii_int_2 := Char.to_int (String.get s2 idx) in
          match Int.equal ascii_int_1 ascii_int_2 with
            | true => string_equal_rec (Int.add idx 1) s1 s2
            | false => false
          end
      end
  end.

(**
  Compares two Ltac2 strings for equality.

  Arguments:
    - [s1, s2: string], strings to compare.

  Returns:
    - [bool]: indicates if [s1] and [s2] have the same length and the same characters
*)
Ltac2 string_equal (s1:string) (s2:string) := string_equal_rec 0 s1 s2.

(**
  Asserts two Ltac2 strings are equal.

  Arguments:
    - [s1, s2: string], strings to compare.

  Raises Exceptions:
    - [TestFailedError], if [s1] has different characters or a different length as [s2].
*)
Ltac2 assert_string_equal (s1:string) (s2:string) :=
  match string_equal s1 s2 with
    | true => print_success (of_string "Test passed: strings are equal")
    | false => fail_test (of_string "Strings not equal")
  end.


(**
  Checks if the current goal under focus is judgementally equal to the provided [constr].

  Arguments:
    - [target: constr], expression that should be judgementally equal to the goal.

  Raises exceptions:
    - [TestFailedError], if [target] is not judgementally equal to the goal.
*)
Ltac2 assert_goal_is (target:constr) :=
  let g := Control.goal () in
  let g' :=  (eval cbv in $g) in
  let t' :=  (eval cbv in $target) in
  match Constr.equal g' t' with
    | true => print_success (of_string "Target is indeed equal to the goal.")
    | false => fail_test (of_string "Target not equal to the goal.")
  end.

(**
  Checks if the type of a term corresponds to an expected type.
    
  Arguments:
    - [term : constr] the term to determine the type of
    - [expected_type : constr] the expected type

  Raises exceptions:
    - [TestFailedError] if the type of term doesn't correspond to expected_type.
*)
Ltac2 assert_type_equal (term:constr) (expected_type:constr) :=
  match (Constr.equal (eval cbv in (type_of $term)) (eval cbv in $expected_type)) with
    | true => print_success (of_string "Type is as expected")
    | false =>
      fail_test (concat 
        (concat
          (of_string "Type not as expected, got: ")
          (of_constr (eval cbv in (type_of $term)))
        ) (concat
          (of_string "but expected: ")
          (of_constr (eval cbv in ($expected_type)))
        )
      )
  end.

(**
  Checks if two [constr] are equal without normalization.

  Arguments:
    - [c1, c2: constr], any constr.

  Raises exceptions:
    - [TestFailedError], if [c1] is not equal to [c2].
*)
Ltac2 assert_constr_equal (c1: constr) (c2: constr) :=
  match Constr.equal c1 c2 with
    | true => print_success (of_string "Constr indeed equal.")
    | false => fail_test (concat
        (concat
            (of_string "Constr not equal, got: ")
            (of_constr c1)
        ) (concat
            (of_string " and: ")
            (of_constr c2)
        )
    )
  end.
