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
Require Import Ltac2.Message.
Local Ltac2 concat_list (ls : message list) : message :=
  List.fold_right concat (of_string "") ls.

Require Import Util.Constr.
Require Import Util.Goals.
Require Import Util.Hypothesis.
Require Import Util.Init.
Require Import Util.MessagesToUser.
Require Import Util.TypeCorrector.

Require Import Waterproof.Tactics.Help.

Local Ltac2 expected_of_type_instead_of_message (e : constr) (t : constr) := 
  concat_list [of_string "Expected assumption of "; of_constr e;
    of_string " instead of "; of_constr t; of_string "."].
(**
  Attempts to assume a negated expression.

  Arguments:
      - [x : (constr * (ident option)) list]: list of (expression optional name for expression)).
  Does:
      - For the first pair of (expession (and name)) in [x], assume the expression.

  Raises fatal exceptions:
    - If the current goal does not require the assumption of an expression [t] where [t] is the expression from the first pair in [x].
    - If [x] contains more than one element.
*)
Local Ltac2 assume_negation (x : (constr * (ident option)) list) :=
  match x with 
  | [] => () (* Done. *)
  | head::tail => 
      match head with
      | (t, n) => (* Check whether the right negated expression is assumed. *)
          lazy_match! goal with
          | [ |- not ?u ] => 
              let t := correct_type_by_wrapping t in
              match check_constr_equal u t with
              | false => throw (expected_of_type_instead_of_message u t)
              | true  => (* Check whether this was the only assumption made.*)
                  match tail with
                  | h::t => throw (of_string "Nothing left to assume after the negated expression.")
                  | [] => (* Assume negation : check whether a name has been given *)
                      match n with
                      | None   => let h := Fresh.in_goal @_H in intro $h; change $t in $h
                      | Some n => intro $n; change $t in $n
                      end;
                      (* Print suggestion on how to use new statement. *)
                      HelpNewHyp.suggest_how_to_use t n
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

  Raises fatale xceptions:
    - If the current goal does not require the assumption of any more hypotheses in general or one of type [t], where [t] is the type from the first pair in [x].
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
                  let t := correct_type_by_wrapping t in
                  match check_constr_equal u t with
                  | true => (* Check whether a name has been given *)
                      match n with
                      | None   => let h := Fresh.in_goal @_H in intro $h; change $t in $h
                      | Some n => intro $n; change $t in $n
                      end;
                      (* Print suggestion on how to use new statement. *)
                      HelpNewHyp.suggest_how_to_use t n
                  | false => throw (expected_of_type_instead_of_message u t)
                  end
              | false => throw (of_string "`Assume ...` cannot be used to construct a map (→). Use [Take] instead.")
              end
          | [ |- _ ] => throw (of_string "Tried to assume too many properties.")
          end
      end;

      (* Attempt to introduce remaining variables of (different) types. *)
      process_ident_type_pairs tail
    
    | [] => () (* Done. *)
  end.

Local Ltac2 remove_contra_wrapper (wrapped_assumption : constr) (assumption : constr) :=
  match (check_constr_equal wrapped_assumption assumption) with
  | true  => apply (ByContradiction.wrap $wrapped_assumption)
  | false => throw (of_string "Wrong assumption specified.")
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
  | [ |- _ ] => throw (of_string "`Assume ...` can only be used to prove an implication (⇨) or a negation (¬).")
  end.

(* TODO: Remove hack after update to 8.18 and replace with Pcoq.set_keyword_state call *)
Notation "[ ( % @ < x 'and'" := x (at level 0, only parsing).
Notation "[ ( % @ < x 'as'" := x (at level 0, only parsing).


(**
  Parses input from Ltac2 notation of the form 'A (i), B, C, D (ii), E and F', 
  see tactic notation specifications below.
  Returns a single list with the user's input (e.g. the above becomes [A (i); B; C; D (ii); E; F]).
*)
Local Ltac2 parse_natural_language_listing (x1 : constr * (ident option)) 
  (x2 : ((((constr * (ident option)) list) option) * (constr * (ident option))) option) 
  : (constr * (ident option)) list :=
  match x2 with 
  | Some (Some x2, x3)  => List.append (x1 :: x2) [x3]
  | Some (None   , x3)  => [x1; x3]
  | None                => [x1]
  end.


(**
  Version with type checking.
*)
Ltac2 Notation "Assume" "that" x1(seq(lconstr, opt(seq("as", "(", ident, ")")))) 
  x2(opt(seq(opt(seq(",", seq(list0(seq(lconstr, opt(seq("as", "(", ident, ")"))), ",")))),
  "and", seq(lconstr, opt(seq("as", "(", ident, ")"))))) )
:= assume (parse_natural_language_listing x1 x2).



(**
  Simply alternative notation for [Assume].
*)
Ltac2 Notation "such" "that" x1(seq(lconstr, opt(seq("as", "(", ident, ")")))) 
  x2(opt(seq(opt(seq(",", seq(list0(seq(lconstr, opt(seq("as", "(", ident, ")"))), ",")))),
  "and", seq(lconstr, opt(seq("as", "(", ident, ")"))))) )
:= assume (parse_natural_language_listing x1 x2).
