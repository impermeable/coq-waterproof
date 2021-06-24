# Waterproof Tactics Library

The Waterproof tactics-library provides custom tactics to Coq.
These tactics allow to write **pen-and-paper like sentences in valid Coq proofs**. 
This makes proofscripts more similar to non-mechanized mathematical proofs. As a result, the proofscript becomes reasonably readable to mathematicians not familiar with the Coq syntax. 

## Example
The following gives a flavour of the tactics.
Note that also optional alternative notations for build-in terms 
such as `R` (`ℝ`) and `forall` (`∀`) are provided:
```coq
Lemma R_complete : ∀ (A : subsets_R) (x : A),
    is_bounded_above A ⇒ mk_subset_R (fun M : ℝ => is_supp A M).
Proof.
    Take A : subsets_R.
    Take a : (subsets_R_to_elements A).
    Assume A_bdd_above : (is_bounded_above A).
    We claim that H : (sig (is_lub (is_in A))).
    Apply completeness.
    Expand the definition of is_bounded_above in A_bdd_above.
    Expand the definition of is_upper_bound in A_bdd_above.
    Expand the definition of bound.
    Choose M such that A_bdd_by_M according to A_bdd_above.
    Choose m := M.
    We need to show that (∀ a : ℝ, is_in A a ⇒ a ≤ M).
    Expand the definition of Raxioms.is_upper_bound.
    Take a : ℝ.
    Assume w : (is_in A a).
    Define b := (mk_element_R (is_in A) a w).
    ltac1:(pose proof (A_bdd_by_M b)).
    This follows by assumption.
    Choose y := x.
    induction y.
    This follows by assumption.
    Choose M such that M_upp_bd according to H.

    destruct (equivalence_sup_lub A M) as [M_is_sup_A H2]. 
    specialize (M_is_sup_A M_upp_bd).
    exists M. 
    exact M_is_sup_A.
Qed.
```

## Features
* Less cryptic, **sentence-like statements for build-in Coq tactics**.
* Automation to **hide details not used in written proofs**.
* **Enforce explicit steps**: for example, to a variable or a hypothesis one *must* supply the type along with the name (and this will be checked).
* **Help messages** and more **elaborate error messages**.
* **Runtime-configurable presets of databases** used by the automation.
* All tactics are implemented in Ltac2.
* **Unit-tests for all tactics**. These are run at compile-time, to ensure a working version is compiled. Unit-tests raise an error if they fail. They are located in the directory `waterproof/test`.

## Usage
To use the tactics in a `.v` file, use the following import:
```coq
Require Import Waterproof.AllTactics.
```
For the custom notations, also add the following imports:
```coq
Require Import Waterproof.notations.notations.
Require Import Waterproof.definitions.set_definitions.
```

## Automation
The more advanced tactics rely on automation.
This automation employs `auto` and `eauto` (and optionally also `intuition`), together with a customizable set of hint-databases.
### Configuration
The baviour of the automated tactics can be configured by imporing specific files.

* **Adding a Database**: import the specific file in `waterproof/load_database`. Example:
    ```coq
    Require Import Waterproof.load_database.Sets.
    ```
* **Search depth**: import any of the files in `waterproof/set_seach_depth`. Example:
    ```coq
    Require Import Waterproof.set_search_depth.To_5.
    ```

* **Enabling intuition**: Add the import
    ```coq
    Require Import Waterproof.set_intuition.Enabled.
    ```
    To disable it again, add:
    ```coq
    Require Import Waterproof.set_intuition.Disabled.
    ```
### Examples of automation features
A few highlights of the automation features are shown below.

#### Rewriting equalities
One can use literal equalities to rewrite goals and hypotheses. This alleviates the need to know the names of build-in Coq lemmas and theorems. The automation features will verify the literal, use it as a temporal lemma to rewrite the target, and remove it again from the proof state.
Example:
```coq
Lemma example: forall x y: nat, x + y + (x + y) = x + y + x + y.
Proof.
    intros x y.
    Rewrite using (forall n m p : nat, n + (m + p) = n + m + p).
    reflexivity.
Qed.
```
Used by tactics:
* `Rewrite using (constr).` (to rewrite to goal)
* `Rewrite using (constr) in (ident).` (to rewrite a hypothesis)
* `Write goal using (constr) as (constr).` (to rewrite a the goal and verify the result is expected)
* `Write goal using (constr) as (constr).` (to rewrite a the goal and verify the result is expected)
* `Write (ident) using (constr) as (constr).` (to rewrite a hypothesis and verify the result is expected)

#### Rewriting inequalities
In written proofs, a chain of statements of the form $$s_1 < s_2 < s_3 < ... < s_n$$ are often used, where each $s_i$ is a mathematical expression.
Waterproof allows a similar notation in Coq:
```coq
Lemma example: forall a b c: R, (a > b /\ b > c) -> (a > c).
    intros a b c h.
    destruct h as [h1 h2].
    Rewrite inequality a ">" b ">" c.
Qed.
```
(Note that the quotes between connectives are necessary,
since Ltac2 does not yet support customized syntactic classes)

## Background
The Waterproof tactics-library is developed as part of the educational [Waterproof](https://github.com/impermeable/waterproof) GUI. 
The tactics are designed to be used by mathematics students who are unfamiliar with Coq. This is also the reason the tactics require the user to be explicit: students are must learn to write readable proofs.

The library was originally written by Jim Portegies in Ltac1. It was extended and ported to Ltac2 by Cosmin Manea, Lulof Pirée, Adrian Vrămuleţ and Tudor Voicu as part of the 'Waterfowl' bachelor Software Engineering Project at the [Eindhoven University of Technology](https://www.tue.nl/en/) (in May-June 2021).
