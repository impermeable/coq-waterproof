Require Import Waterproof.Waterproof.
Require Import Waterproof.Automation.

Goal forall P : Prop, {P} + {~P}.
Proof.
  auto with wp_decidability_classical.
Qed.