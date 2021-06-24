(** * either.v
Authors: 
    - Cosmin Manea (1298542)

Creation date: 02 June 2021

Tactic for proving by case distinction.
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
From Ltac2 Require Import Message.



Require Import Waterproof.tactics.automation_databases.decidability_db.


(** * either_case_1_or_case_2
    Split the proof by case distinction.

    Arguments:
        - [t1 : constr], the first case.
        - [t2 : constr], the second case.

    Does:
        - splits the proof by case distinction; also prints a recommendation for the user 
          to specifically write in which case he is working on.
*)
Ltac2 either_case_1_or_case_2 (t1:constr) (t2:constr) :=
    print (of_string "Recommendation: Please use comments to indicate the case 
    you are in after writing this line. This helps to keep the proof readable.");
    ltac1:(t1 t2 |- first [ assert ({t1} + {t2}) as u by auto with decidability nocore; destruct u |
                            assert ({t2} + {t1}) as u by auto with decidability nocore; destruct u 
                          ]) (Ltac1.of_constr t1) (Ltac1.of_constr t2).

Ltac2 Notation "Either" t1(constr) "or" t2(constr) :=
    either_case_1_or_case_2 t1 t2.
