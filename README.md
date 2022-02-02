# Waterproof Tactics Library

The Waterproof tactics-library provides custom tactics to Coq.
These tactics allow to write **pen-and-paper like sentences in valid Coq proofs**. 
This makes proofscripts more similar to non-mechanized mathematical proofs. As a result, the proofscript becomes reasonably readable to mathematicians not familiar with the Coq syntax. 

## Example
The following snippet of file `sample_proof.v` gives a flavour of the tactics.
Note that also optional alternative notations for build-in terms 
such as `R` (`ℝ`) and `forall` (`∀`) are provided:
```coq
Goal (¬ is_open [0,1)).
Proof.
  Assume that (is_open [0,1)).
  It holds that ([0,1) 0).
  It holds that (is_interior_point 0 [0,1)) (i).
  Obtain r according to (i), so for r : ℝ it holds that
    (r > 0 ∧ (for all x : ℝ, (open_ball 0 r) x ⇒ [0,1) x)) (ii).
  Because (ii) both (r > 0) and 
    (for all x : ℝ, (open_ball 0 r) x ⇒ [0,1) x) (iii) hold.
  It holds that ( | -r/2 - 0 | < r).
  It holds that ((open_ball 0 r) (-r/2)).
  By (iii) it holds that ([0,1) (-r/2)) (iv).
  Because (iv) both (0 ≤ -r/2) and (-r/2 < 1) hold.
  It holds that (¬ r > 0).
  Contradiction.
Qed.

Goal (¬ is_closed [0,1)).
Proof.
  We need to show that 
    (¬ (for all a : ℝ, ([0,1)^c a) ⇒ is_interior_point a [0,1)^c)).
  It suffices to show that
    (there exists a : ℝ, ([0,1)^c a) ∧ ¬(is_interior_point a [0,1)^c)).
  Choose a := 1.
  We show both statements.
  - We need to show that ([0,1)^c 1).
    We conclude that ([0,1)^c 1).
  - We need to show that (¬(is_interior_point 1 [0,1)^c)).
    We need to show that 
      (¬ there exists r : ℝ, r > 0 ∧ (for all x : ℝ, open_ball 1 r x ⇒ [0,1)^c x)).
    It suffices to show that
      (for all r : ℝ, r > 0 ⇒ (there exists x : ℝ, (open_ball 1 r x) ∧ (¬ [0,1)^c x))).
    Take r : R. Assume that (r > 0).
    Choose x := ((Rmax (1/2) (1 - r/2))).
    We show both (open_ball 1 r x) and (¬[0,1)^c x).
    + We need to show that (| x - 1 | < r).
      It suffices to show that (-r < x - 1 < r).
      We show both (-r < x - 1) and (x - 1 < r).
      * It holds that (1 - r/2 ≤ (Rmax (1/2) (1 - r/2))).
        We conclude that (& -r &< -r/2 &= 1 - r/2 - 1 &≤ (Rmax (1/2) (1-r/2)) - 1 &= x - 1).
      * We conclude that (& x - 1 &= Rmax (1/2) (1 - r/2) - 1 &< 0 &< r).
    + We need to show that (¬ [0,1)^c x).
      It suffices to show that ([0,1) x).
      We need to show that (0 ≤ x ∧ x < 1).
      We show both (0 ≤ x) and (x < 1).
      * We conclude that (& 0 &≤ 1/2 &≤ Rmax (1/2) (1 - r/2) &= x).
      * We conclude that (& x &= Rmax (1/2) (1 - r/2) &< 1).
Qed.
```

## Features
* Less cryptic, **sentence-like statements for build-in Coq tactics**.
* Automation to **hide details not used in written proofs**.
* **Enforce explicit steps**: for example, after splitting the proof of a conjunstion, one has to write what is to be shown (and this will be checked).
* **Help messages** and more **elaborate error messages**.
* **Runtime-configurable presets of hint databases** used by the automation.
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
The automation function is called `waterprove`, 
which employs `auto` and `eauto` (and optionally also `intuition`), 
together with a customizable set of hint-databases.

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

<!--(deprecated)#### Rewriting equalities
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

#### Chains of (in)equalities
In written proofs, a chain of statements of the form *s<sub>1</sub> < s<sub>2</sub> = s<sub>3</sub> ≤ ... < s<sub>n</sub>$$ are often used, where each *s<sub>i</sub>* is a mathematical expression.
Waterproof allows a similar notation in Coq:
```coq
Lemma example: forall a b c: R, (a < b ∧ b < c) -> (a < c).
    Take a, b, c, : R.
    Assume that (a < b ∧ b < c) (i).
    Because (i) both (a < b) and (b < c) hold.
    We conclude that (& a &< b &< c).
Qed.
```

(Note that as of now only chains for `=`, `<` and `≤` are implemented.)
<!--(Note that the quotes between connectives are necessary,
since Ltac2 does not yet support customized syntactic classes)-->

## Background
The Waterproof tactics-library is developed as part of the educational [Waterproof](https://github.com/impermeable/waterproof) GUI. 
The tactics are designed to be used by mathematics students who are unfamiliar with Coq. This is also the reason the tactics require the user to be explicit: students are must learn to write readable proofs.

The library was originally written by Jim Portegies in Ltac1. It was extended and ported to Ltac2 by Cosmin Manea, Lulof Pirée, Adrian Vrămuleţ and Tudor Voicu as part of the 'Waterfowl' bachelor Software Engineering Project at the [Eindhoven University of Technology](https://www.tue.nl/en/) (in May-June 2021). Since then it has been under further development by Jelle Wemmenhove and Jim Portegies.
