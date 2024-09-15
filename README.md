[![Build][build-badge]][build-link]
[![Documentation][documentation-badge]][documentation-link]

[build-badge]: https://github.com/impermeable/coq-waterproof/workflows/Build/badge.svg
[documentation-badge]: https://github.com/impermeable/coq-waterproof/workflows/Documentation/badge.svg

[build-link]: https://github.com/impermeable/coq-waterproof/actions?query=workflow:"Build"
[documentation-link]: https://github.com/impermeable/coq-waterproof/actions?query=workflow:"Documentation"

# coq-waterproof

The coq-waterproof plugin allows you to write Coq proofs in **a style that resembles non-mechanized mathematical proofs**.
Mathematicians unfamiliar with the Coq syntax are able to read the resulting proof scripts.

## Installation

### Linux

#### With Opam

Firstly you should install [`opam`](https://opam.ocaml.org/).

Then, you can create a new switch and install the requirements by running :

```bash

$ opam switch create waterproof --packages coq.8.19.0
$ eval $(opam env --switch=waterproof)
```

Then, you can clone this repository and install the library by running :

```bash
$ git clone https://github.com/impermeable/coq-waterproof.git && cd coq-waterproof
$ opam install .
```

Once this is done, you can use coq-waterproof in any file of your system by switching to the `waterproof` switch on opam.

#### Manually

You can also install coq-waterproof without using opam (though it is greatly recommended for Coq) by compiling it by hand with :

```bash
$ git clone https://github.com/impermeable/coq-waterproof.git && cd coq-waterproof
$ dune build -p coq-waterproof
$ dune install -p coq-waterproof
```

## Usage
To use the tactics in a `.v` file, use the import:
```coq
Require Import Waterproof.Waterproof.
```

To use the automation system, add:
```coq
Require Import Waterproof.Automation.
```

To use the tactics system, add:
```coq
Require Import Waterproof.Tactics.
```

To use the notations defined, add:
```coq
Require Import Waterproof.Notations.
```

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

## Automation

The more advanced tactics rely on automation. The automation function is called `waterprove`, which employs `wp_auto` and `wp_eauto`, together with a customizable set of hint-databases.

`wp_auto` and `wp_eauto` are rewrite of `auto` and `eauto` with better backtracking support, which can be use to retrieve the full backtrace during the execution of those functions, which allows to have a better control on the execution flow of the hints. For example, it can be used to reject a complete proof if certain lemmas are not used and continue to search for a new one.  

### Configuration

The behavior of the automation tactics can be configured by importing specific files.

* **Adding a Database**: Example:
    ```coq
    Require Import Waterproof.Automation.

    Waterproof Enable Automation RealsAndIntegers.
    ```

* **Removing a Database**: Example:
    ```coq
    Require Import Waterproof.Automation.

    Waterproof Enable Automation RealsAndIntegers.
    Waterproof Disable Automation RealsAndIntegers.
    ```

* **Clearing every Databases**: Example:
    ```coq
    Require Import Waterproof.Automation.

    Waterproof Enable Automation RealsAndIntegers.
    Waterproof Enable Automation Intuition.
    Waterproof Clear Automation.
    ```

* **Declaring a new automation dataset**: Example:
  ```coq
  Require Import Waterproof.Automation.
  
  Waterproof Declare Automation Foo.
  Waterproof Set Main Databases Foo core, wp_core.
  Waterproof Set Decidability Databases Foo wp_decidability_classical.
  Waterproof Set Shorten Databases Foo core.
  ```

* **Turn debugging of automation on**: Example:
  ```coq
  Waterproof Enable Debug Automation.
  ```

* **Turn debugging of automation off**: Example:
  ```coq
  Waterproof Disable Debug Automation.
  ```

## Chains of (in)equalities
In written proofs, one often uses a chain of (in)equalities to explain why more complicated (in)equalities hold.
Waterproof allows you to use a similar notation in Coq.
For example, `sample_proof.v` contains the statement

```coq
We conclude that (& -r < -r/2 = 1 - r/2 - 1 ≤ Rmax(1/2, 1 - r/2) - 1 = x - 1).
```
The chain of inequalities is used to show that `-r < x - 1`.

## TODO

- [ ] Split total statements in Ltac2 before calling `waterprove` to have more precise error locations
- [ ] Add a restricted version of `wp_autorewrite` then change the `restricted_automation_routine` in [`src/waterprove.ml`](src/waterprove.ml)
- [ ] Flatten the search tree during `wp_auto` and `wp_eauto` not to make restricted versions skip branches

## Background

The coq-waterproof library is developed as part of the educational [Waterproof](https://github.com/impermeable/waterproof) editor for Coq.
The tactics are designed to be used by first-year mathematics students who are unfamiliar with Coq. This is also why the tactics require the user to be explicit: the students have to learn to write readable proofs.

The library was originally written by Jim Portegies in Ltac1. It was extended and ported to Ltac2 by Cosmin Manea, Lulof Pirée, Adrian Vrămuleţ and Tudor Voicu as part of the 'Waterfowl' bachelor Software Engineering Project at the [Eindhoven University of Technology](https://www.tue.nl/en/) (in May-June 2021). Since then it has been under further development by Jelle Wemmenhove and Jim Portegies. In April-June 2023, Balthazar Patiachvili improved the automation, and converted parts of the library to an OCaml plugin.
