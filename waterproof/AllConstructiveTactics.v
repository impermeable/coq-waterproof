(** * [AllConstructiveTactics.v]
Authors: 
    - Lulof Pirée (1363638)
    - Jelle Wemmenhove
Creation date: 9 June 2021

File that imports all subfiles under the [tactics] folder of the Waterproof library.

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
From Ltac2 Require Export Ltac2.
Require Export Waterproof.tactics.assume.
Require Export Waterproof.tactics.automation_databases.decidability_db.
Require Export Waterproof.tactics.because.
Require Export Waterproof.tactics.goal_to_hint.
Require Export Waterproof.tactics.rewrite_inequalities.
Require Export Waterproof.tactics.sets_tactics.sets_automation_tactics.
Require Export Waterproof.tactics.take.
Require Export Waterproof.tactics.unfold.
Require Export Waterproof.tactics.we_know.
Require Export Waterproof.tactics.choose.
Require Export Waterproof.tactics.choose_such_that.
Require Export Waterproof.tactics.either.
Require Export Waterproof.tactics.we_need_to_show.
Require Export Waterproof.tactics.we_show_both_directions.
Require Export Waterproof.tactics.we_show_both_statements.
Require Export Waterproof.tactics.forward_reasoning.apply.
Require Export Waterproof.tactics.forward_reasoning.claims.
Require Export Waterproof.tactics.forward_reasoning.it_suffices_to_show.
Require Export Waterproof.tactics.forward_reasoning.proof_finishing_tactics.
Require Export Waterproof.tactics.forward_reasoning.rewrite_using.
Require Export Waterproof.tactics.forward_reasoning.define.
Require Export Waterproof.tactics.forward_reasoning.forward_reasoning_aux.
Require Export Waterproof.tactics.forward_reasoning.induction.
Require Export Waterproof.tactics.forward_reasoning.it_holds_that.
Require Export Waterproof.tactics.forward_reasoning.we_conclude_that.
Require Export Waterproof.tactics.forward_reasoning.write_as.
Require Export Waterproof.tactics.forward_reasoning.write_using.
Require Export Waterproof.tactics.forward_reasoning.simplify.