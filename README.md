# coq-waterproof

The coq-waterproof library allows you to write Coq proofs in **a style that resembles non-mechanized mathematical proofs**.
Mathematicians unfamiliar with the Coq syntax are able to read the resulting proof scripts.


## Example
The following snippet from `sample_proof.v` gives a taste of a proof written using coq-waterproof.
```coq
Goal (¬ [0,1) is closed).
Proof.
  Expand the definition of closed.
  That is, write the goal as (¬ ℝ\[0,1) is open).
  Expand the definition of open.
  That is, write the goal as 
    (¬ ∀ a : ℝ, a : ℝ\[0,1) ⇒ a is an interior point of ℝ\[0,1)).
  It suffices to show that
    (∃ a : ℝ, a : ℝ\[0,1) ∧ ¬ a is an interior point of ℝ\[0,1)).
  Choose a := 1.
  We show both statements.
  - We conclude that (1 : ℝ\[0,1)).
  - We need to show that (¬ 1 is an interior point of ℝ\[0,1)).
    Expand the definition of interior point.
    That is, write the goal as
      (¬ ∃ r : ℝ, r > 0 ∧ (∀ x : ℝ, x : B(1,r) ⇒ x : ℝ\[0,1))).
    It suffices to show that
      (∀ r : ℝ, r > 0 ⇒ (∃ x : ℝ, x : B(1,r) ∧ x : [0,1))).
    Take r : ℝ. Assume that (r > 0).
    Choose x := (Rmax(1/2, 1 - r/2)).
    We show both (x : B(1,r)) and (x : [0,1)).
    + We need to show that (| x - 1 | < r).
      It suffices to show that (-r < x - 1 < r).
      We show both (-r < x - 1) and (x - 1 < r).
      * It holds that (1 - r/2 ≤ Rmax(1/2, 1 - r/2)).
        We conclude that (& -r < -r/2 = 1 - r/2 - 1 ≤ Rmax(1/2, 1 - r/2) - 1 = x - 1).
      * We conclude that (& x - 1 = Rmax(1/2, 1 - r/2) - 1 < 0 < r).
    + We need to show that (x : [0,1)).
      We need to show that (0 ≤ x ∧ x < 1).
      We show both (0 ≤ x) and (x < 1).
      * We conclude that (& 0 ≤ 1/2 ≤ Rmax(1/2, 1 - r/2) = x).
      * We conclude that (& x = Rmax(1/2, 1 - r/2) < 1).
Qed.
```

## Features
* Less cryptic, **controlled natural language formulations for build-in Coq tactics**.
* Commonplace **mathematical notation** such as `ℝ` or `A is closed`.
* **Enforced signposting:** after a case distinction, for example, one **has** to state which case is to be shown.
* Allows for reasoning with **chains of (in)equalities**.
* Automation to **hide details not used in written proofs**.
* **Help messages** and more **elaborate error messages**.
* **Runtime-configurable presets of hint databases** used by the automation.
* All tactics implemented in Ltac2.
<!--* **Unit-tests for all tactics**. These are run at compile-time, to ensure a working version is compiled. Unit-tests raise an error if they fail. They are located in the directory `waterproof/test`.-->


## Usage
To use the tactics in a `.v` file, use the import:
```coq
Require Import Waterproof.AllTactics.
```
For the custom notations, also add:
```coq
Require Import Waterproof.notations.notations.
```

## Automation
The more advanced tactics rely on automation.
The automation function is called `waterprove`, 
which employs `auto` and `eauto` (and optionally also `intuition`), 
together with a customizable set of hint-databases.

### Configuration
The behavior of the automatation tactics can be configured by importing specific files (and modules).

* **Adding a Database**: Example:
    ```coq
    Require Import Waterproof.load.
    Module Import db_RealsAndIntegers := databases(RealsAndIntegers).
    ```
* **Search depth**: import any of the files in `waterproof/set_seach_depth`. Example:
    ```coq
    Require Import Waterproof.set_search_depth.To_5.
    ```
One can also write custom database config files. For example,
```coq
Require Import Waterproof.populate_database.
Require Import Waterproof.load.
    
Module ExampleDBConfig <: db_config.
  Module preload_module := wp_all.
  Ltac2 append_databases := true.
  Ltac2 global_databases () := [ @real; @wp_reals].
  Ltac2 decidability_databases () := [ @nocore; @wp_decidability_classical].
  Ltac2 negation_databases () := [ @nocore; @wp_negation_reals].
  Ltac2 first_attempt_databases () := [].
End ExampleDBConfig.
    
Module Import my_db := databases(ExampleDBConfig).
```
<!--(deprecated)## Rewriting equalities
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
* `Write (ident) using (constr) as (constr).` (to rewrite a hypothesis and verify the result is expected)-->

## Chains of (in)equalities
In written proofs, one often uses a chain of (in)equalities to explain why more complicated (in)equalities hold.
Waterproof allows you to use a similar notation in Coq.
For example, `sample_proof.v` contains the statement

```coq
We conclude that (& -r < -r/2 = 1 - r/2 - 1 ≤ Rmax(1/2, 1 - r/2) - 1 = x - 1).
```
The chain of inequalities is used to show that `-r < x - 1`.

## Background
The coq-waterproof library is developed as part of the educational [Waterproof](https://github.com/impermeable/waterproof) editor for Coq.
The tactics are designed to be used by first-year mathematics students who are unfamiliar with Coq. This is also why the tactics require the user to be explicit: the students have to learn to write readable proofs.

The library was originally written by Jim Portegies in Ltac1. It was extended and ported to Ltac2 by Cosmin Manea, Lulof Pirée, Adrian Vrămuleţ and Tudor Voicu as part of the 'Waterfowl' bachelor Software Engineering Project at the [Eindhoven University of Technology](https://www.tue.nl/en/) (in May-June 2021). Since then it has been under further development by Jelle Wemmenhove and Jim Portegies.

