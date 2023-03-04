(** * [write_as.v]
Authors: 
    - Lulof Pirée (1363638)
    - Jelle Wemmenhove
Creation date: 16 June 2021
Latest edit:   12 Oct  2021

Tactic used to rewrite part of an expression.

--------------------------------------------------------------------------------

This file is part of Waterproof-lib.

Waterproof-lib is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

Waterproof-lib is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with Waterproof-lib.  If not, see <https://www.gnu.org/licenses/>.
*)

From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Option.


Require Import Waterproof.message.

Require Import Waterproof.tactics.forward_reasoning.rewrite_using.
Require Import Waterproof.auxiliary.
Require Import Waterproof.tactics.goal_wrappers.
Require Import Waterproof.tactics.unfold.

(** * print_rewrite_success
    Print that the hypothesis identified by [id]
    has successfully been rewritten.
*)
Local Ltac2 print_rewrite_success (id:ident) :=
print (concat
(concat
    (of_string "Successfully rewrote '")
    (of_ident id)
)
(concat
    (concat 
        (of_string "' to ")
        (let hyp := Control.hyp id in
        of_constr constr:(Aux.type_of $hyp))
        
    )
    (of_string ".")
    )
).

(** * write_as
    Try to rewrite the definition the hypothesis identified by [id]
    to [replacement].

    Arguments:
        - [id: ident], identifier of hypothesis to rewrite.
        - [replacement: constr], term/type to use for the rewrite.

    Raises exceptions:
        - [RewriteError], in case the rewrite fails.
*)
Local Ltac2 write_as (id: ident) (replacement: constr) :=
    let result () := change $replacement in $id in
    match Control.case result with
    | Val _ => print_rewrite_success id
    | Err exn => Control.zero (
        RewriteError 
        "Cannot rewrite the hypothesis with this term.")
    end.

(** * unwrap_or_write_as
    1) If the goal is wrapped in ExpandDef.Hyp.Wrapper, attempt to remove the wrapper.
    2) Else, try to rewrite the hypothesis identified by [id]
        to [replacement].

    Arguments:
        - [id: ident], 1) identifier in which a definition was unfolded, part of the wrapping;
                       2) identifier of hypothesis to rewrite.
        - [replacement: constr], 1) type of [id] after unfolding, part of wrapping;
                                 2) term/type to use for the rewrite.

    Raises exceptions:
        - 1) [ExpandDefError], if the arguments [id] and [replacement] 
                                do not match the wrapper.
        - 2) [RewriteError], in case the rewrite fails.
*)
Local Ltac2 unwrap_or_write_as (id : ident) (replacement : constr) :=
    lazy_match! goal with
    | [|- ExpandDef.Hyp.Wrapper _ _ _] => hyp_as id replacement (*[hyp_as] is from unfold.v*)
    | [|- _] => write_as id replacement
    end.


Ltac2 Notation "Write" id(ident) "as" replacement(constr) :=
    unwrap_or_write_as id replacement.