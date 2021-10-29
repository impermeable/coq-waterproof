(** * decidability_db.v
Authors: 
    - Jim Portegies
Creation date: 15 June 2021

Hint database for being able to prove via case distinction.
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


(** **Decidability**
    There are a number of tactics that deal with decidability. 
    They are of the form ``{r1 s1 r2} + {r1 s2 r2}``, and can be useful in case evaluation.
    To implement this, we create a new database ``decidiability``, and a tactic that uses 
    this database (only).
    We first add existing lemmas to the new database.
*)


From Ltac2 Require Import Ltac2.

Require Import Rbase.
Require Import Qreals.
Require Import Rfunctions.
Require Import SeqSeries.
Require Import Rtrigo.
Require Import Ranalysis.
Require Import Integration.
Require Import micromega.Lra.
Require Import Max.

Local Open Scope R_scope.



Create HintDb decidability.

(** Automatically unfold > to <so (_ > _) no longer has to occur in the options below.
    We cannot do the same for >= as it is not defined as <= .*)
Global Hint Extern 1 => unfold Rgt : decidability.

Global Hint Resolve Req_EM_T : decidability.

(** Lemmas to write e.g. `{r1 ≤ r2} + {r2 < r1}`.*)
Global Hint Resolve Rlt_le_dec : decidability.
Lemma Rlt_ge_dec : forall r1 r2, {r1 < r2} + {r1 >= r2}.
Proof.
    intros.
    destruct (total_order_T r1 r2). 
    destruct s.
    exact (left r).
    exact (right (Req_ge r1 r2 e)). 
    exact (right (Rle_ge r2 r1 (Rlt_le r2 r1 r))).
Qed.
Global Hint Resolve Rlt_ge_dec : decidability.

(** Lemmas to write e.g. `{r1 ≤ r2} + {~r2 ≥ r1}`.*)
Global Hint Resolve Rlt_dec Rle_dec Rge_dec : decidability.
Lemma Rle_ge_dec : forall r1 r2, {r1 <= r2} + {~ r2 >= r1}.
Proof.
    intros.
    destruct (total_order_T r1 r2).
    destruct s.
    ltac1:(apply (left (Rlt_le r1 r2 r))).
    ltac1:(apply (left (Req_le r1 r2 e))).
    ltac1:(apply (right (Rlt_not_ge r2 r1 r))).
Qed.
Lemma Rge_le_dec : forall r1 r2, {r1 >= r2} + {~ r2 <= r1}.
Proof.
    intros.
    destruct (total_order_T r1 r2). 
    destruct s.
    ltac1:(apply (right (Rlt_not_le r2 r1 r))).
    ltac1:(apply (left (Req_ge r1 r2 e))).
    ltac1:(apply (left (Rgt_ge r1 r2 r))).
Qed.
Global Hint Resolve Rle_ge_dec Rge_le_dec : decidability.

(** Lemmas to split e.g. `{r1 <= r2} into {r1 < r2} + {r1 = r2}`.*)
Lemma Rge_lt_or_eq_dec : forall r1 r2, (r1 >= r2) -> {r2 < r1} + {r1 = r2}.
Proof.
    intros.
    destruct (total_order_T r2 r1).
    - destruct s.
      + left. exact r.
      + right. symmetry. exact e.
    - ltac1:(exfalso).
      exact (Rlt_not_ge _ _ r H).
Qed.
Global Hint Resolve Rle_lt_or_eq_dec Rge_lt_or_eq_dec : decidability.

Global Hint Resolve total_order_T : decidability. (* x < y, x = y or y < x*)