(** * [string_auxiliary.v]
Authors: 
    - Lulof Pirée (1363638)
Creation date: 23 May 2021

Auxiliary functions defining some basic operations on Ltac2 strings.
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

(** * replace_at_pos
    Replace a single character at a string and return the result.

    Arguments:
        - [s : string], the string to modify.
        - [pos : int], the index of the character to replace.
            Counting starts at 0.
        - [c : char], the replacement character.

    Returns:
        - [string]: same as [s], 
            but with the character at [pos]
            replaced with [c].

    Raises exceptions:
        - [Out_of_bounds], if [pos] is greater or equal to the
            length of  [s].
*)
Ltac2 replace_at_pos (s:string) (pos: int) (c:char) :=
    (String.set s pos c; s).


(** * copy_to_target
    Copy substring of [source] into [target].
    Replaces previously present part of [target].
    In Python notation: copy source[source_idx:source_end] to 
    target[target_idx: target_idx + (source_end - source_idx)]

    Arguments:
        - [source_idx : int], starting index of substring to copy from [source]
        - [target_idx: int], position of [target] where substring 
            should be pasted.
        - [source_end : int], fist index of [source] 
            that should not be part of substring.
            Note that [source_end - 1] is the last index that is included
            in the substring.
        - [source: string], string to copy substring from.
        - [target: string], string to copy substring into.

    Returns:
        - [string: same] as [target] but with with the characters at indices
            [target_idx] up to [target_idx + (source_end - source_idx)] replaced
            with the the characters of [source] between 
            [source_idx] and (not including) [source_end].

    Raises exceptions:
        - [Out_of_bounds], if one of the following indices does not exist:
            - [source_idx] or [source_end-1]  in [source].
            - [target_idx] in [target].
            - [target_idx + (source_end - source_idx)] in target.
*)
Local Ltac2 rec copy_to_target (source_idx: int) (target_idx:int) 
                               (source_end:int) (source: string) 
                               (target: string) :=
    match Int.equal source_idx source_end with
    | true => target
    | false => 
        let t' := replace_at_pos target target_idx 
                                 (String.get source source_idx) 
        in
        copy_to_target (Int.add source_idx 1) (Int.add target_idx 1) 
                       source_end source t'
    end.

(** * copy_suffix_to_target
    Copy the suffix (starting at index [source_idx]) of [source]
    intro [target] at position [target_idx].
    In Python notation:
        "return target[:target_idx] + source[source_idx:] 
                + target[len(source) + target_idx:]"


    Arguments:
        - [source_idx : int], starting index of substring (suffix) 
            to copy from [source]
        - [target_idx: int], position of [target] where the substring 
            should be pasted.
        - [source: string], string to copy substring from.
        - [target: string], string to copy substring into.

    Returns:
        - [string], same as [target] but with with the characters at indices
        [target_idx] up to [target_idx + String.length(source)] replaced
        with the the characters of [source] starting at index [source_idx].

    Raises exceptions:
        - [Out_of_bounds], if one of the following indices does not exist:
            - [source_idx] in [source].
            - [target_idx] in [target].
            - [target_idx + String.length(source)] in target.
*)
Ltac2 copy_suffix_to_target (source_idx: int) (target_idx:int) 
                         (source: string) (target: string):=
    let i := String.length(source) in
    copy_to_target source_idx target_idx i source target.

(** * concat_strings
    Concatenate two strings and return a longer string.

    Arguments:
        - [s1 : string], string to form the prefix of the output.
        - [s2 : string], string to form the suffix of the output.

    Returns:
        - [string], concatenation of [s1] and [s2].
*)
Ltac2 concat_strings (s1:string) (s2: string) :=
    let underscore := Char.of_int 95 in
    let tot_len := Int.add (String.length s1) (String.length s2) in
    let empty_result := String.make tot_len underscore in
    let half_result := copy_suffix_to_target 0 0 s1 empty_result in
        copy_suffix_to_target 0 (String.length s1) s2 half_result.

Ltac2 Type exn ::= [ AddToIdentNameError(string) ].
(** * add_to_ident_name
    Add a string to an ident and return it as a new ident.

    Arguments:
        - [h: ident], the ident to extend.
        - [s: string], the string to add.
    Returns:
        - [ident], concatenation of string representation of [h] and [s],
            and converted back to [ident].
*)
Ltac2 add_to_ident_name (h: ident) (s: string) :=
    let result := Ident.of_string(concat_strings (Ident.to_string h) s) in
    (* [result] is of type [ident option] instead of [ident] *)
    match result with
    | Some r => r
    | None => Control.zero (AddToIdentNameError "Cannot add string to ident")
    end.

(** ** string_cmp_rec
    Helper function for string_cmp.
*)
Local Ltac2 rec string_cmp_rec (idx) (s1:string) (s2:string) :=
    let len1 := (String.length s1) in
    let len2 := (String.length s2) in
        if Bool.or (Int.equal idx len1) (Int.equal idx len2)
        then
            if (Int.equal len1 len2) then 0 else
                if (Int.lt len1 len2) then -1 else 1
        else
            let ascii_int_1 := Char.to_int (String.get s1 idx) in
            let ascii_int_2 := Char.to_int (String.get s2 idx) in
            if Int.equal ascii_int_1 ascii_int_2 then
                string_cmp_rec (Int.add idx 1) s1 s2
            else 
                if Int.lt ascii_int_1 ascii_int_2 then
                    -1 else 1.

(** * string_cmp
    Compare two Ltac2 strings lexicographically.

    Arguments:
        - [s1, s2: string], strings to compare.

    Returns:
        - int
            - 0 if [s1] and [s2] have 
                the same length and the same characters.
            - (-1) if [s2] would come later in the dictionary than [s1]
            - (1) if [s1] would come later in the dictionary than [s2]
*)
Ltac2 string_cmp (s1 : string) (s2 : string) :=
    string_cmp_rec 0 s1 s2.
