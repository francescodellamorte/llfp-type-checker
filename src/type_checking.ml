(*
	Copyright 07/2016 Michielini Vincent and Scagnetto Ivan
    All rights reserved.

    Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

    * Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
    * Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.

    THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

open Alpha
open Definitions
open Domains
open Intermediate
open Proof
open Substitutions
open Unlock
open Variables

let rec is_signature (sign : signature) : bool =
(* returns true if sign is a signature *)
let aux () =
	(*Printf.printf "CHECKING signature : %s\n\n"(Intermediate.signature_to_string_terminal sign);*)
	match sign with
		| [] ->
			true
		| (Const_family (a, k)) :: sign' ->
			if (is_kind sign' [] k)
			then
				try (
					let _ = (return_associated_kind_in_signature sign' a) in
						false
					)
				with 
					Failure "not in the signature" ->
						true
			else
				false
		| Const (c, sigma) :: sign' ->
			if has_canonical_family_kind_type sign' [] sigma
			then
				try (
					let _ = return_associated_family_in_signature sign' c in
						false
					)
				with
					Failure "not in the signature" ->
						true
			else
				false
in let b = aux () in (*Printf.printf "returned if it's signature: %b\n" b;*) b

and is_context (sign : signature) (gamma : context) : bool =
(* returns true if gamma is a context considering sign *)
let aux () =
	(*Printf.printf "CHECKING context : %s\n\n"(Intermediate.context_to_string_terminal gamma);*)
	match gamma with
		| [] ->
			is_signature sign
		| (x, sigma) :: gamma' ->
			if has_canonical_family_kind_type sign gamma' sigma
			then
				try (
					let _ = return_associated_family_in_context gamma' x in
						false
					)
				with
					Failure "not in the context" ->
						true
			else
				false
in let b = aux () in (*Printf.printf "returned if it's context: %b\n" b;*) b

and is_kind (sign : signature) (gamma : context) (k : kind) : bool =
(* returns true if k is a kind considering sign and gamma *)
let aux () =
	(*Printf.printf "CHECKING kind : %s\n\n"(Intermediate.kind_to_string_terminal k);*)
	match k with
		| Type ->
			is_context sign gamma
		| Pi (x, sigma, k1) ->
			is_kind sign ((x, sigma) :: gamma) k1
in let b = aux () in (*Printf.printf "returned if it's kind: %b\n" b;*) b

and has_canonical_family_kind_type (sign : signature) (gamma : context) (sigma : canonical_family) : bool =
(* returns true if sigma has kind type considering sign and gamma *)
let aux () =
	(*Printf.printf "CHECKING canonical_family : %s\n\n"(Intermediate.canonical_family_to_string_terminal sigma);*)
	match sigma with
		| Atomic tho ->
			(
				try(
					return_kind_to_atomic_family sign gamma tho = Type 
				)
				with
					Failure s when s <> "quit" ->
						false
			)
		| Pi (x, sigma1, sigma2) ->
			has_canonical_family_kind_type sign ((x, sigma1) :: gamma) sigma2
		| Lock (prop1, m1, sigma1, sigma2) ->
			let x = fresh_variable (variables_list_of_canonical_family sigma2 []) in
				let rec fun_aux q_list =
					(
					match q_list with
						| [] ->
							has_canonical_family_kind_type sign gamma sigma2 && has_canonical_object_canonical_family sign gamma m1 sigma1
						| ((prop0, m0, sigma0, n0) as q) :: q_list' when prop1 = prop0 = alpha_conversion_on_canonical_objects m0 m1 [] && alpha_conversion_on_canonical_families sigma0 sigma1 []->
							let sigma2' = substitute_unlock_on_canonical_family sigma2 x q in
								(
								match return_canonical_family_to_atomic_object sign gamma n0 with
									| Lock (prop3, m3, sigma3, sigma4) when prop3 = prop1 && alpha_conversion_on_canonical_objects m3 m1 [] && alpha_conversion_on_canonical_families sigma3 sigma1 [] ->
										if has_canonical_family_kind_type sign ((x, sigma4) :: gamma) (Lock (prop1, m1, sigma1, sigma2'))
										then
											true
										else
											fun_aux q_list'
									| _ -> fun_aux q_list'
								)
						| _ :: q_list' -> fun_aux q_list'
					)
				in
					fun_aux (list_of_all_unlock_in_canonical_family sigma2 [])
		| Prod (sigma1, sigma2) ->
			has_canonical_family_kind_type sign gamma sigma1 && has_canonical_family_kind_type sign gamma sigma2
in let b = aux () in (*Printf.printf "returned if it's of kind type to canonical_family: %b\n" b;*) b

and return_kind_to_atomic_family (sign : signature) (gamma : context) (tho : atomic_family) : kind =
(* returns the type of tho considering sign and gamma *)
let aux () =
	(*Printf.printf "CHECKING atomic_family : %s\n\n" (Intermediate.atomic_family_to_string_terminal tho);*)
	match tho with
		| Const_family a ->
			return_associated_kind_in_signature sign a
		| App (tho1, m) ->
			(
			match return_kind_to_atomic_family sign gamma tho1 with
				| Pi (x, sigma, k) ->
					if has_canonical_object_canonical_family sign gamma m sigma
					then
						substitute_on_kind k m x
					else
						failwith "wrong type in application for family"
				| _ ->
					failwith "matching application for family"
			)
in let k = aux () in (*Printf.printf "returned kind to atomic_family: %s\n" (Intermediate.kind_to_string_terminal k);*) k

and has_canonical_object_canonical_family (sign : signature) (gamma : context) (m : canonical_object) (sigma : canonical_family) : bool =
(* returns true if m has type sigma considering sign and gamma *)
let aux () =
	(*Printf.printf "CHECKING canonical_object: %s\n\tcanonical_family: %s\n\n" (Intermediate.canonical_object_to_string_terminal m) (Intermediate.canonical_family_to_string_terminal sigma);*)
	match (m, sigma) with
		| (Atomic n, _) ->
			(
				try(
					let sigma' = return_canonical_family_to_atomic_object sign gamma n in
						alpha_conversion_on_canonical_families sigma sigma' []
					)
				with
					Failure s when s <> "quit" ->
						false
			)
		| (Lam (x, sigma1, m2), Pi (y, sigma3, sigma2)) when substitute_on_canonical_family sigma3 (Atomic (Var x)) y = sigma1 ->
			has_canonical_object_canonical_family sign ((x, sigma1) :: gamma) m2 (substitute_on_canonical_family sigma2 (Atomic (Var x)) y)
		| (Lock (prop1, m1, sigma1, m2), Lock (prop3, m3, sigma3, sigma2)) when prop3 = prop1 && alpha_conversion_on_canonical_families sigma3 sigma1 [] && alpha_conversion_on_canonical_objects m3 m1 [] ->
			let x = fresh_variable (variables_list_of_canonical_family sigma2 (variables_list_of_canonical_object m2 []))
			and unlock_list = list_of_all_unlock_in_canonical_object m2 (list_of_all_unlock_in_canonical_family sigma2 []) in
				let rec fun_aux q_list =
					(
					match q_list with
						| [] -> has_canonical_object_canonical_family sign gamma m1 sigma1 && has_canonical_object_canonical_family sign gamma m2 sigma2
						| ((prop0, m0, sigma0, n0) as q) :: q_list' when prop0 = prop1 && alpha_conversion_on_canonical_objects m0 m1 [] && alpha_conversion_on_canonical_families sigma0 sigma1 [] ->
							let sigma2' = substitute_unlock_on_canonical_family sigma2 x q
							and m2' = substitute_unlock_on_canonical_object m2 x q in
								(
								match return_canonical_family_to_atomic_object sign gamma n0 with
									| Lock (prop4, m4, sigma4, sigma3) when prop4 = prop1 && alpha_conversion_on_canonical_objects m4 m1 [] && alpha_conversion_on_canonical_families sigma4 sigma1 [] ->
										if has_canonical_object_canonical_family sign ((x, sigma3) :: gamma) (Lock (prop1, m1, sigma1, m2')) (Lock (prop1, m1, sigma1, sigma2'))
										then
											true
										else
											fun_aux q_list'
									| _ -> fun_aux q_list'
								)
						| _ :: q_list' -> fun_aux q_list'
					) in
					fun_aux unlock_list
		| (Pair (m1, m2), Prod (sigma1, sigma2)) ->
			has_canonical_object_canonical_family sign gamma m1 sigma1 && has_canonical_object_canonical_family sign gamma m2 sigma2
		| _ ->
			false
in let b = aux () in (*Printf.printf "returned if canonical_object has canonical_family: %b\n" b;*) b

and return_canonical_family_to_atomic_object (sign : signature) (gamma : context) (n : atomic_object) : canonical_family =
(* returns the family of n considering sign and gamma *)
let aux () =
	(*Printf.printf "CHECKING atomic_object : %s\n\n" (Intermediate.atomic_object_to_string_terminal n);*)
	match n with
		| Const c ->
			if is_context sign gamma
			then
				try(
					return_associated_family_in_signature sign c
					)
				with
					Failure "not in the signature" ->
						failwith "error in return_canonical_family_to_atomic_object: constant not in the signature"
			else
				failwith "error in return_canonical_family_to_atomic_object, case constant: not a context"
		| Var x ->
			if is_context sign gamma
			then
				try(
					return_associated_family_in_context gamma x
					)
				with
					Failure ("not in the context") ->
						failwith "error in return_canonical_family_to_atomic_object: variable not in the context"
			else
				failwith "error in return_canonical_family_to_atomic_object, case variable: not a context"
		| App (n1, m) ->
			(
			match return_canonical_family_to_atomic_object sign gamma n1 with
				| Pi (x, sigma2, sigma1) ->
					if has_canonical_object_canonical_family sign gamma m sigma2
					then
						substitute_on_canonical_family sigma1 m x
					else
						failwith "wrong type in application for object"
				| _ ->
					failwith "matching application for object"
			)
		| Unlock (prop1, m1, sigma1, n1) ->
			(
			match return_canonical_family_to_atomic_object sign gamma n1 with
				| Lock (prop2, m2, sigma3, sigma2) when prop2 = prop1 && alpha_conversion_on_canonical_families sigma3 sigma1 [] && alpha_conversion_on_canonical_objects m2 m1 [] ->
					if has_canonical_object_canonical_family sign gamma m1 sigma1
					then
						if proves prop1 sign gamma m1 sigma1
						then
							sigma2
						else
							failwith "wrong prof"
					else
						failwith "wrong type in unlock for object"
				| _ ->
					failwith "matching unlock for object"
			)
in let sigma = aux () in (*Printf.printf "returned canonical_family to atomic_object: %s\n" (Intermediate.canonical_family_to_string_terminal sigma);*) sigma
