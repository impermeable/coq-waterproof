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
Require Import Ltac2.Std.
Require Import Ltac2.Message.
Local Ltac2 concat_list (ls : message list) : message :=
  List.fold_right concat (of_string "") ls.

Require Import Util.Goals.
Require Import Util.MessagesToUser.

Ltac2 Type exn ::=  [ Inner ].

(**
  Attemtps to unfold definition(s) in a statement according to specified method. 
  If succesful it also throws a fatal error suggesting the user to replace this 
  command by an alternative, suitable tactic with the unfolded statement. 
    E.g. if the statement corresponds with the proof goal, 
  the user is suggested to use
    'We need to show that ([statement with unfolded definiton])'.

  Arguments:
    - [unfold method: constr -> constr], method to be used for unfolding
        unfolding is deemed to be succesful if [unfold_method statement] =\= [statement]
    - [def_name: string], optional string used for error message when unfolding
        is unsuccesful
    - [statement : constr], term in which definitions are to be unfolded.

  Raises fatal exceptions:
    - always
 
*)
Ltac2 unfold_in_statement (unfold_method: constr -> constr) 
  (def_name : string option) (statement : constr) := 
  let unfolded_statement := unfold_method statement in
  match Constr.equal statement unfolded_statement with
  | false =>
    match! goal with
    | [ |- ?g] => 
      match Constr.equal g statement with
      | false => Control.zero Inner
      | true => 
        let msg (unfolded : constr) := concat_list
          [of_string "replace line with:
  We need to show that "; of_constr unfolded; of_string "."] in
        throw (msg unfolded_statement)
      end
    | [_ : ?hyp |- _ ] =>
      match Constr.equal hyp statement with
      | false => Control.zero Inner
      | true => 
        let msg (unfolded : constr) := concat_list
          [of_string "replace line with:
  It holds that "; of_constr unfolded; of_string "."] in
        throw (msg unfolded_statement)
      end
    | [ |- _ ] =>
      let msg (unfolded : constr) := concat_list
      [of_string "result:
  "; of_constr unfolded; of_string "
Remove this line to continue."] in
      throw (msg unfolded_statement)
    end    
  | true => 
    match def_name with
    | None => throw (concat_list 
      [of_string "definition does not appear in "; of_constr statement; of_string "."])
    | Some def_name => throw (concat_list 
      [of_string "'"; of_string def_name; of_string "'";
        of_string " does not appear in "; of_constr statement; of_string "."])
    end
  end.

(**
  Attemtps to unfold definition(s) in a statement according to specified method. 
  If succesful it prints a message suggesting the user to
  use a suitable tactic with the unfolded statement. 
    E.g. if the statement corresponds with the proof goal, 
  the user is suggested to use
    'We need to show that ([statement with unfolded definiton])'.

  Arguments:
    - [unfold method: constr -> constr], method to be used for unfolding
        unfolding is deemed to be succesful if [unfold_method statement] =\= [statement]
    - [def_name: string], optional string used for error message when unfolding
        is unsuccesful
    - [statement : constr], term in which definitions are to be unfolded.

  Raises fatal exceptions:
    - none
 
*)
Ltac2 unfold_in_statement_no_error (unfold_method: constr -> constr) 
  (def_name : string option) (statement : constr) := 
  let unfolded_statement := unfold_method statement in
  match Constr.equal statement unfolded_statement with
  | false =>
    match! goal with
    | [ |- ?g] => 
      match Constr.equal g statement with
      | false => Control.zero Inner
      | true => 
        let msg (unfolded : constr) := concat_list
          [of_string "use:
  We need to show that "; of_constr unfolded; of_string "."] in
        print (msg unfolded_statement)
      end
    | [_ : ?hyp |- _ ] =>
      match Constr.equal hyp statement with
      | false => Control.zero Inner
      | true => 
        let msg (unfolded : constr) := concat_list
          [of_string "use:
  It holds that "; of_constr unfolded; of_string "."] in
        print (msg unfolded_statement)
      end
    | [ |- _ ] =>
      let msg (unfolded : constr) := concat_list
      [of_string "result:
  "; of_constr unfolded] in
      print (msg unfolded_statement)
    end    
  | true => 
    match def_name with
    | None => print (concat_list 
      [of_string "definition does not appear in "; of_constr statement; of_string "."])
    | Some def_name => print (concat_list 
      [of_string "'"; of_string def_name; of_string "'";
        of_string " does not appear in "; of_constr statement; of_string "."])
    end
  end.


(* Tactic notation for unfolding generic Gallinea terms, not notations.
  For an example of how to used [unfold_in_statement] to unfold notations,
  see [tests/tactics/Unfold.v] *)

Ltac2 Notation "Expand" "the" "definition" "of" targets(list1(seq(reference, occurrences), ",")) "in" statement(constr) :=
  panic_if_goal_wrapped ();
  unfold_in_statement (eval_unfold targets) None statement.

Ltac2 Notation "_internal_" "Expand" "the" "definition" "of" targets(list1(seq(reference, occurrences), ",")) "in" statement(constr) :=
  panic_if_goal_wrapped ();
  unfold_in_statement_no_error (eval_unfold targets) None statement.
