(** * [write_as.v]
Authors: 
    - Lulof Pirée (1363638)
Creation date: 16 June 2021

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
From Ltac2 Require Import Message.

Require Import Waterproof.auxiliary.
Require Import Waterproof.tactics.forward_reasoning.rewrite_using.

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

(** * print_rewrite_success
    Try to rewrite the definition the hypothesis identified by [id]
    to [replacement_term].

    Arguments:
        - [id: ident], identifier of hypothesis to rewrite.
        - [replacement_term: constr], term to use for the rewrite.

    Raises exceptions:
        - [RewriteError], in case the rewrite fails.
*)
Local Ltac2 write_as (id: ident) (replacement_term: constr) :=
    let result () := change $replacement_term in $id in
    match Control.case result with
    | Val _ => print_rewrite_success id
    | Err exn => Control.zero (
        RewriteError 
        "Cannot rewrite the hypothesis with this term.")
    end.

(** * Write ... as ...
    Try to rewrite the definition the hypothesis identified by [id]
    to [replacement_term].

    Arguments:
        - [id: ident], identifier of hypothesis to rewrite.
        - [replacement_term: constr], term to use for the rewrite.

    Raises exceptions:
        - [RewriteError], in case the rewrite fails.
*)
Ltac2 Notation "Write" id(ident) "as" replacement_term(constr) :=
    write_as id replacement_term.