(** * Testcases for [string_auxiliary.v]
Authors: 
    - Lulof Pirée (1363638)
Creation date: 23 May 2021

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
From Ltac2 Require Option.
From Ltac2 Require Import Message.

Load string_auxiliary.
Require Import Waterproof.test_auxiliary.

(*
--------------------------------------------------------------------------------
*) (** *  Testcase for [replace_at_pos]
*)

Ltac2 Eval 
    let result := (replace_at_pos "hollo" 1 (Char.of_int 101)) in
    assert_string_equal result "hello".


(*
--------------------------------------------------------------------------------
*) (** *     Testcases for [concat_strings]
*)

Ltac2 Eval 
    let result := (concat_strings "hello " "world") in
    assert_string_equal result "hello world".

Ltac2 Eval 
    let result := (concat_strings "1" "2") in
    assert_string_equal result "12".

(*
--------------------------------------------------------------------------------
*) (** *     Testcase for [copy_suffix_to_target]
*)

Ltac2 Eval
    let result := (copy_suffix_to_target 12 1 
                   "Hello world Unicorns!" "~_________~") in
    assert_string_equal result "~Unicorns!~".

(*
--------------------------------------------------------------------------------
*) (**    Testcase for [add_to_ident_name]
*)
Ltac2 Eval Ident.equal @unicorn (add_to_ident_name @uni "corn").

(*
--------------------------------------------------------------------------------
*) (** * Testcases for [string_equal]
*)
Ltac2 Eval assert_is_true (string_equal "hello" "hello").
Ltac2 Eval assert_is_false (string_equal "hello" "Hello").
Ltac2 Eval assert_is_false (string_equal "hello" "hell").
