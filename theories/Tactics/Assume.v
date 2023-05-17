Require Import Ltac2.Ltac2.
Require Import Ltac2.Message.

Require Import Util.Constr.
Require Import Util.Goals.
Require Import Util.Hypothesis.
Require Import Util.Init.

Ltac2 Type exn ::= [ AssumeError(message) ].

Local Ltac2 expected_of_type_instead_of_message (e : constr) (t : constr) := 
  concat (concat
    (concat (of_string "Expected assumption of ") (of_constr e))
    (concat (of_string " instead of ") (of_constr t))) (of_string ".").

(**
  Attempts to assume a negated expression.

  Arguments:
      - [x : (constr * (ident option)) list]: list of (expression optional name for expression)).
  Does:
      - For the first pair of (expession (and name)) in [x], assume the expression.

  Raises Exceptions:
    - [AssumeError], if the current goal does not require the assumption of an expression [t] where [t] is the expression from the first pair in [x].
    - [AssumeError], if [x] contains more than one element.
*)
Local Ltac2 assume_negation (x : (constr * (ident option)) list) :=
  match x with 
    | [] => () (* Done. *)
    | head::tail => match head with
      | (t, n) => (* Check whether the right negated expression is assumed. *)
        lazy_match! goal with
          | [ |- not ?u ] => 
            match check_constr_equal u t with
              | false => Control.zero (AssumeError (expected_of_type_instead_of_message u t))
              | true  => (* Check whether this was the only assumption made.*)
                match tail with
                  | h::t => Control.zero (AssumeError (of_string "Nothing left to assume after the negated expression."))
                  | [] => (* Assume negation : check whether a name has been given *)
                    match n with
                      | None   => let h := Fresh.in_goal @__wp__h in intro $h
                      | Some n => intro $n
                    end
                end
            end
          | [ |- _ ] => Control.zero (Unreachable "")
      end
  end
end.

(**  
  Attempts to recursively assume a list of hypotheses.

  Arguments:
    - [x : (constr * (ident option)) list)]: list of (hypothesis and optional hypothesis name).
  
  Does:
    - For the first pair of (hypothesis (and name)) in [x], assume the hypothesis (with specified name).
      If the assumed hypothesis did not come from a negated expression, proceeds to call itself with the remaining pairs in [x] as a new list [x'].

  Raises Exceptions:
    - [AssumeError], if the current goal does not require the assumption of any more hypotheses in general or one of type [t], where [t] is the type from the first pair in [x].
*)
Local Ltac2 rec process_ident_type_pairs (x : (constr * (ident option)) list) :=
  match x with
    | head::tail =>
      match head with
        | (t, n) => (* Check whether next assumption (i.e. [t]) is that of a negated expression. *)
          lazy_match! goal with
            | [ |- not _ ]   => assume_negation x (* If so, switch to different subroutine. *)
            | [ |- ?u -> _ ] => (* Check whether the domain is a proposition. *)
              let sort_u := get_value_of_hyp u in
              match check_constr_equal sort_u constr:(Prop) with
                | true => (* Check whether we need variabled of type t. *)
                  match check_constr_equal u t with
                    | true => (* Check whether a name has been given *)
                      match n with
                        | None   => let h := Fresh.in_goal @__wp__h in intro $h
                        | Some n => intro $n
                          end
                    | false => Control.zero (AssumeError (expected_of_type_instead_of_message u t))
                  end
                | false => Control.zero (AssumeError (of_string "[Assume] cannot be used to construct a map (→). Use [Take] instead."))
              end
            | [ |- _ ] => Control.zero (AssumeError (of_string "Tried to assume too many properties."))
          end
      end;

      (* Attempt to introduce remaining variables of (different) types. *)
      process_ident_type_pairs tail
    
    | [] => () (* Done. *)
  end.

Local Ltac2 remove_contra_wrapper (wrapped_assumption : constr) (assumption : constr) :=
  match (check_constr_equal wrapped_assumption assumption) with
    | true  => apply (ByContradiction.wrap $wrapped_assumption)
    | false => Control.zero (AssumeError (of_string "Wrong assumption specified."))
  end.


(**
  Checks whether the 'Assume' tactic can be applied to the current goal, attempts to introduce a list of hypotheses.
*)
Local Ltac2 assume (x : (constr * (ident option)) list) := 
  (* Handle goal wrappers *)
  lazy_match! goal with
    | [ |- ByContradiction.Wrapper ?a _ ] => 
      match x with 
      | head::_ => 
        match head with
        | (t,_) => remove_contra_wrapper a t
        end
      | [] => panic_if_goal_wrapped ()
      end
    | [ |- _ ] => panic_if_goal_wrapped ()
    end;
  (* Make assumption and perform checks on input *)
  lazy_match! goal with
    | [ |- not _ ]  => assume_negation x
    | [ |- _ -> _ ] => process_ident_type_pairs x
    | [ |- _ ] => Control.zero (AssumeError (of_string "[Assume] can only be used to prove an implication (⇨) or a negation (¬)."))
  end.


(**
  Version with type checking.
*)
Ltac2 Notation "Assume" "that" x(list1(seq(constr, opt(seq("(", ident, ")"))), "and")) := assume x.

(**
  Simply alternative notation for [Assume].
*)
Ltac2 Notation "such" "that" x(list1(seq(constr, opt(seq("(", ident, ")"))), "and")) := assume x.
