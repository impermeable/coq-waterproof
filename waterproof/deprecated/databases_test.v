(** # **Databases**

Authors: 
    - Adrian Vramulet
    - Tudor Voicu
    - Lulof Pirée (1363638)
Creation date: 14 June 2021

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

Require Import Waterproof.test_auxiliary.
Load deprecated_collect_db.


(*Test 1 : this should work fine*)
Goal forall x y z, x*(y+z) = x*y + x*z.
Proof.
  Ltac2 Eval(collect_all_db ()).
  myauto(2).
Defined.

(*Test 2 : this test should fail since it requires the database eq_sqr*)
Goal forall x, x^2 = x².
Proof.
  Ltac2 Eval(collect_all_db ()).
  assert_raises_error(fun() => solve[auto with nocore eq_mult]).
  solve[auto with nocore eq_sqr].
Defined.

(*Test 3 : Alternatively, it can be solved by calling the myauto function*)
Goal forall x, x^2 = x².
Proof.
  myauto(2).
Defined.

(*Test 4 : Some goal mroe complex.*)
Goal forall x y z, x*(y+z)^2 = x*y^2 + 2*x*y*z + x*z^2.
Proof.
  Ltac2 Eval(collect_all_db ()).
  myauto(2).
Defined.

(*Test 5 : Simply calling auto will not solve this goal.*)
Goal forall x y, exp(x+y) = exp(x) * exp(y).
Proof.
  auto.
  myauto(2).
Defined.

(*Test 6: Calling the wrong database will not solve this goal.*)
Goal forall x y, exp(x+y) = exp(x) * exp(y).
Proof.
  assert_raises_error(fun() =>solve[auto with nocore eq_one]).
  myauto(2).
Defined.

(*Test 7 : Calling the right database will solve the goal.*)
Goal forall x y, exp(x+y) = exp(x) * exp(y).
Proof.
  solve[auto with nocore eq_exp].
Defined.

(*Test 8: This goal should be solved.*)
Goal forall x y, (x+y)/x = x/x + y/x.
Proof.
  Ltac2 Eval(collect_all_db ()).
  myauto(2).
Defined.

Axiom div: forall x, x/x = 1.
Hint Extern 1 => (rewrite div) : eq_general.

(*Test 9: This goal should not be solved, since there's no hint 
in the database that states the axiom div.*)
Goal forall x y, (x+y)/x = 1 + y/x.
Proof.
  assert_raises_error(fun() =>myauto(2)).
  solve[auto with nocore eq_general].
Defined.