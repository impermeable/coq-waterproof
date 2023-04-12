(** * [debug.v]
Authors:
    - Balthazar Patiachvili
Creation date: 12 April 2023

A library to print debug messages. 

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

Require Import Ltac2.Ltac2.
Require Import Ltac2.Printf.

Require Import Waterproof.init_automation_global_variables.

Local Ltac2 debug_level (lvl : Std.debug): int :=
  match lvl with
    | Std.Off => 0
    | Std.Info => 1
    | Std.Debug => 2
  end.

(** * debug
  Print the debug message `Debug(<fun_name>): <arg>` if the global_debug_level is Std.Info or Std.Debug.

  Arguments:
    
    - [fun_name : string], name of the function in which the call is made (it can be anything actually, it is to create standard debug messages)

    - [arg : string], content of the message
*)
Ltac2 debug (fun_name: string) (arg: string) :=
  if (Bool.neg (Int.equal (debug_level global_debug_level) (debug_level Std.Off))) 
    then printf "Debug(%s): %s" fun_name arg
    else ().

(** * debug_int
  Print the debug message `Debug(<fun_name>): <arg_name> -> <arg>` if the global_debug_level is Std.Info or Std.Debug.

  Arguments:
    
    - [fun_name : string], name of the function in which the call is made (it can be anything actually, it is to create standard debug messages)

    - [arg_name : string], name of the printed argument

    - [arg : int], printed argument
*)
Ltac2 debug_int (fun_name: string) (arg_name: string) (arg: int) :=
  if (Bool.neg (Int.equal (debug_level global_debug_level) (debug_level Std.Off))) 
    then printf "Debug(%s): %s -> %i" fun_name arg_name arg 
    else ().

(** * debug_int_option
  Print the debug message `Debug(<fun_name>): <arg_name> -> <arg>` if the global_debug_level is Std.Info or Std.Debug.

  Arguments:
    
    - [fun_name : string], name of the function in which the call is made (it can be anything actually, it is to create standard debug messages)

    - [arg_name : string], name of the printed argument

    - [arg : int opiton], printed argument
*)
Ltac2 debug_int_option (fun_name: string) (arg_name: string) (arg: int option) :=
  if (Bool.neg (Int.equal (debug_level global_debug_level) (debug_level Std.Off))) 
    then match arg with
      | None => printf "Debug(%s): %s -> None" fun_name arg_name
      | Some i => printf "Debug(%s): %s -> Some %i" fun_name arg_name i 
    end 
    else ().

(** * debug_string
  Print the debug message `Debug(<fun_name>): <arg_name> -> <arg>` if the global_debug_level is Std.Info or Std.Debug.

  Arguments:
    
    - [fun_name : string], name of the function in which the call is made (it can be anything actually, it is to create standard debug messages)

    - [arg_name : string], name of the printed argument

    - [arg : string], printed argument
*)
Ltac2 debug_string (fun_name: string) (arg_name: string) (arg: string) :=
  if (Bool.neg (Int.equal (debug_level global_debug_level) (debug_level Std.Off))) 
    then printf "Debug(%s): %s -> %s" fun_name arg_name arg 
    else ().

(** * debug_ident
  Print the debug message `Debug(<fun_name>): <arg_name> -> <arg>` if the global_debug_level is Std.Info or Std.Debug.

  Arguments:
    
    - [fun_name : string], name of the function in which the call is made (it can be anything actually, it is to create standard debug messages)

    - [arg_name : string], name of the printed argument

    - [arg : ident], printed argument
*)
Ltac2 debug_ident (fun_name: string) (arg_name: string) (arg: ident) :=
  if (Bool.neg (Int.equal (debug_level global_debug_level) (debug_level Std.Off))) 
    then printf "Debug(%s): %s -> %I" fun_name arg_name arg 
    else ().

(** * debug_constr
  Print the debug message `Debug(<fun_name>): <arg_name> -> <arg>` if the global_debug_level is Std.Info or Std.Debug.

  Arguments:
    
    - [fun_name : string], name of the function in which the call is made (it can be anything actually, it is to create standard debug messages)

    - [arg_name : string], name of the printed argument

    - [arg : constr], printed argument
*)
Ltac2 debug_constr (fun_name: string) (arg_name: string) (arg: constr) :=
  if (Bool.neg (Int.equal (debug_level global_debug_level) (debug_level Std.Off))) 
    then printf "Debug(%s): %s -> %t" fun_name arg_name arg 
    else ().