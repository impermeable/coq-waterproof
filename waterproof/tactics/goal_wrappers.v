(** * [goal_wrappers.v]
Authors: 
    - Jelle Wemmenhove

Creation date: 08 Oct 2021

Contains the wrappers that a goal can be wrapped in to force the user to
apply a specific tactic.
The aim of these wrappers is to keep the proof script readable without relying
on the proofview window.
Also contains a tactic that throws an exception if the goal is wrapped.
This is to be used to prevent other tactics from advancing the proof state whilst
the goal is wrapped.

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

