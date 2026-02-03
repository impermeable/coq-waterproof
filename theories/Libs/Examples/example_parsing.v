From Stdlib Require Import Reals.Reals.

Require Import Notations.Common.
Require Import Notations.Reals.
Require Import Notations.Sets.
Require Import Tactics.
Require Import Waterproof.Automation.

Open Scope R_scope.

Waterproof Disable Filter Errors.

Goal True -> (∃ x ∈ ℝ, x = x) -> False.
Proof.
Assume.
(*
current:
Unbound constructor Assume
wanted, standard Rocq:
- Syntax error: "that" expected after "Assume"
wanted, waterproof:
- Syntax error: Did you mean: "Assume that ..."?
*)
assume.
(*
current:
Unbound value assume.
Similar to above.
*)
intr i.
(*
current:
Unbould value intr.
wanted, standard Rocq.
- Syntax error: Unbound value intr. Did you mean intro?
*)
intros x, y.
(*
current:
Unbound value y
wanted, standard Rocq
- Syntax error: No ',' expected after x. Did you mean intros x y?
*)
intro x y.
(*
current:
This expression has type unit.
It is not a function and cannot be applied.
wanted, standard Rocq:
- Syntax error: '.' expected after x
- Alternative
  Did you mean "intros x y."?
*)
intro _G.
Assume that (∃ x ∈ ℝ, x = x) as (i).
It holds that 2 * = 3.
(*
Maybe strictly speaking not a syntax error.
current:
Unknown interpretation for notation "= _".
wanted:
- term of type `R` expected after "2 * " in main argument "2 * = 3"
*)
Obtain x according to i.
(*
current:
Syntax error: '(' expected after 'to' (in [ltac2_expr]).
wanted, standard Rocq: 
- Syntax error: label starting with '(' expected after "Obtain x according to".
  error squiggly line underneath _H
- Syntax error: valid `label` expected after "Obtain x according to".
  A label is of the form "( ident )". Did you mean "(i)"?
  error squiggly line unerneath i
wanted, Waterproof:
- label expected after "Obtain x according to". A label is of the form
(i), so an opening parenthesis is missing here.
with error squiggly line underneath `i`. (as is currently the case)
*)
Obtain x according to (i.
(*
current:
Syntax error: '(' expected after 'to' (in [ltac2_expr]).
- Syntax error: ')' expected after "Obtain x according to (i".
  Squiggly line after i. (currently the case)
- Syntax error: valid `label` expected after "Obtain x according to".
  A label is of the form "( ident )". Did you mean "(i)"?
  error squiggly line underneath "(i".
wanted, Waterproof:
- label expected after "Obtain x according to". A label is of the form
(i), so an opening parenthesis is missing here.
with error squiggly line underneath `i`. (as is currently the case)
*)
Obtain x.
(*
current:
Syntax error: ',' or 'according' 'to' expected (in [ltac2_expr]).
wanted:
- Syntax error: ',' or 'according to' expected after "Obtain x".
- Expected one fo the following:
  * "Obtain such an x"
  * "Obtain x according to (ident)".
  * "Obtain x, ... according to (ident)".
    (For Waterproof, we're also okay with assuming that the user did
     not want to type another variable with the comma)
*)
Obtain sch an x. (* sch is interpreted as a variable... *)
(*
current:
Syntax error: ',' or 'according' 'to' expected (in [ltac2_expr]).
This is a tricky one. sch is interpreted as an identifier, and in principle
"Obtain sch according to (i)" is valid input. Nonetheless,
we would love to see here:
- Syntax error: 'such' expected after 'Obtain'.
- Expected one of the following:
  - "Obtain such an x"
  - "Obtain sch according to ( ident )" if sch was meant as a variable name.
*)
By (i) we conclude tht 3 = 3.
(*
current:
Syntax error: 'that' expected after [ltac2_expr level 5] (in [ltac2_expr]).
wanted, standard Rocq:
- Syntax error: "that" expected after "By (i) we conclude".
  with error squiggly line underneath tht.
- Alternative suggestion:
  Syntax error: in main clause. Expected one of:
  * it holds that
  * we conclude that
  * it suffices to show that
  did you mean "we conclude that"?
  error squiggly line underneath "we conclude tht".
wanted, Waterproof:
- syntax error after "By (i) we conclude", did you mean "that"?
with error scribble underneath `tht`
- Alternative:
  Expected one of the possible main clauses
  * it holds that
  * we conclude that
  * it suffices to show that
  after "By (i)". Did you mean "we conclude that"?
*)
By (i) we cnclude that 3 = 3.
(* wanted:
Syntax error: ',' or 'and' or [ltac2_expr level 5] expected after [lconstr] (in [ltac2_expr]).
wanted, standard Rocq:
- Syntax error: 'conclude' expected after "By (i)) we".
  with error squiggly line underneath cnclude
- Alternativer suggestion:
  Syntax error: in main clause. Expected one of:
  * it holds that
  * we conclude that
  * it suffices to show that
  did you mean "we conclude that"?
wanted, Waterproof:
- syntax error after "By (i) we", did you mean "conclude"?
  with error squiggly line underneath `cnclude`
- Alternative:
  Expected one of the possible main clauses
  * it holds that
  * we conclude that
  * it suffices to show that
  after "By (i)". Did you mean "we conclude that"?
*)
Fail It holds tht 0 = 0.
(* Syntax error: [ltac2_use_default] expected after [ltac2_expr] (in [ltac2_command]).
solutions similar to above. *)
Abort.
