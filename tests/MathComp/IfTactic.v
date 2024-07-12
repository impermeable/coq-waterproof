From Waterproof Require Import Waterproof.
From Waterproof Require Import Automation.
From Waterproof Require Import Tactics.
From Waterproof Require Import MathComp.

Waterproof Enable Automation Algebra.

From mathcomp Require Import eqtype ssrbool.

Parameter T : eqType.
Parameter x y a b : T.

Goal if (x == x) then True else False.
Proof.
    It suffices to show that (True).
    We conclude that (True).
Qed.

Goal (a == b) -> (x == y) -> (if x == y then True else False).
Proof.
    Assume that (a == b).
    Assume that (x == y).
    It suffices to show that (True).
    We conclude that (True).
Qed.

Goal (x != y) -> (if x == y then False else True).
Proof.
    Assume that (x != y).
    It suffices to show that (True).
    We conclude that (True).
Qed.

Goal (x == y) -> (if x == y then True else (if x == y then True else False)).
Proof.
    Assume that (x == y).
    It suffices to show that (True).
    We conclude that (True).
Qed.

Goal (x != y) -> (if x == y then False else (if x == y then False else True)).
Proof.
    Assume that (x != y).
    It suffices to show that (True).
    We conclude that (True).
Qed.

Goal (x != y) -> (if x == y then False else (if x != y then True else False)).
Proof.
    Assume that (x != y).
    It suffices to show that (True).
    We conclude that (True).
Qed.

Goal (x != y) -> (if x == y then False else (if x != y then True else False)).
Proof.
    Assume that (x != y).
    It suffices to show that (if x != y then True else False).
    It suffices to show that (True).
    We conclude that (True).
Qed.

Goal (if x == x then if x == x then if x == x then if x == x then True 
    else False else False else False else False).
Proof.
    It suffices to show that (True).
    We conclude that (True).
Qed.
