(*
	Copyright 07/2016 Michielini Vincent and Scagnetto Ivan
    All rights reserved.

    Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

    * Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
    * Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.

    THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

open Definitions

let rec substitute_on_kind (k0 : kind) (m : canonical_object) (x : string) : kind =
(* returns a kind: k in which x is substituted by m *) 
	match k0 with
		| Type ->
			Type
		| Pi (y, sigma, k1) when x <> y ->
			Pi (y, substitute_on_canonical_family sigma m x, substitute_on_kind k1 m x)
		| _ ->
			failwith "unable to substitute on the data"

and substitute_on_canonical_family (sigma : canonical_family) (m : canonical_object) (x : string) : canonical_family =
(* returns a canonical_family: sigma in which x is subsituted by m *)
let rec aux () : canonical_family =
	(*Printf.printf "SUBSTITUTION canonical_family: %s\n\tobject: %s\n\tstring: %s\n" (Intermediate.canonical_family_to_string sigma) (Intermediate.canonical_object_to_string m) x;*)
	match sigma with
		| Atomic tho ->
			Atomic (substitute_on_atomic_family tho m x)
		| Pi (y, sigma1, sigma2) when x <> y->
			Pi (y, substitute_on_canonical_family sigma1 m x, substitute_on_canonical_family sigma2 m x)
		| Lock (prop1, m0, sigma1, sigma2) ->
			Lock (prop1, substitute_on_canonical_object m0 m x, substitute_on_canonical_family sigma1 m x, substitute_on_canonical_family sigma2 m x)
		| Prod (sigma1, sigma2) ->
			Prod (substitute_on_canonical_family sigma1 m x, substitute_on_canonical_family sigma2 m x)
		| _ ->
			failwith "unable to substitute on the data"
in let s = aux () in (*Printf.printf "substitution over for canonical_family: %s\n" (Intermediate.canonical_family_to_string s); *)s

and substitute_on_atomic_family (tho0 : atomic_family) (m : canonical_object) (x : string) : atomic_family =
(* returns an atomic family: tho in which x is replaced by sigma *)
let rec aux () =
	(*Printf.printf "SUBSTITUTION atomic_family: %s\n\tobject: %s\n\tstring: %s\n" (Intermediate.atomic_family_to_string tho0) (Intermediate.canonical_object_to_string m) x;*)
	match tho0 with
		| Const_family _ ->
			tho0
		| App (tho1, m0) ->
			App (substitute_on_atomic_family tho1 m x, substitute_on_canonical_object m0 m x)
in let t = aux () in (*Printf.printf "substitution over for atomic_family: %s\n" (Intermediate.atomic_family_to_string t);*) t

and substitute_on_canonical_object (m0 : canonical_object) (m : canonical_object) (x : string) : canonical_object =
(* returns a canonical_object: m0 in which x is replaced by m *)
let rec aux () : canonical_object =
	(*Printf.printf "SUBSTITUTION canonical_family: %s\n\tobject: %s\n\tstring: %s\n" (Intermediate.canonical_object_to_string m0) (Intermediate.canonical_object_to_string m) x;*)
	match m0 with
		| Atomic n ->
			(
			match substitute_on_atomic_object n m x with
				| Atomic n' ->
					Atomic n'
				| Canonical m1 ->
					m1
			)
		| Lam (y, sigma, m1) when x <> y->
			Lam (y, substitute_on_canonical_family sigma m x, substitute_on_canonical_object m1 m x)
		| Lock (prop1, m1, sigma1, m2) ->
			Lock (prop1, substitute_on_canonical_object m1 m x, substitute_on_canonical_family sigma1 m x, substitute_on_canonical_object m2 m x)
		| Pair (m1, m2) ->
			Pair (substitute_on_canonical_object m1 m x, substitute_on_canonical_object m2 m x)
		| _ ->
			failwith "unable to substitute on the data"
in let m7 = aux () in(* Printf.printf "substitution over for canonical_object: %s\n" (Intermediate.canonical_object_to_string m7);*) m7

and substitute_on_atomic_object (n0 : atomic_object) (m : canonical_object) (x : string) : all_object =
(* returns a all_object: n in which x is replaced by m *)
let rec aux () =
	(*Printf.printf "SUBSTITUTION atomic_object: %s\n\tobject: %s\n\tstring: %s\n" (Intermediate.atomic_object_to_string n0) (Intermediate.canonical_object_to_string m) x;*)
	match n0 with
		| Const _ ->
			Atomic n0
		| Var y ->
			if x = y
			then
				(
				match m with
					| Atomic n0 ->
						Atomic n0
					| _ ->
						Canonical m
				)
			else
				Atomic n0
		| App (n1, m1) ->
			(
			match substitute_on_atomic_object n1 m x with
				| Atomic n2 ->
					let m2 = substitute_on_canonical_object m1 m x in
						Atomic (App (n2, m2))
				| Canonical (Lam (y, sigma, m2)) ->
					let m3 = substitute_on_canonical_object m1 m x in
						let m4 = substitute_on_canonical_object m2 m3 y in
							Canonical (m4)
				| _ ->
					failwith "matching application"
			)
		| Unlock (prop1, m0, sigma0, n1) ->
			(
			match substitute_on_atomic_object n1 m x with
				| Atomic n2 ->
					let sigma1 = substitute_on_canonical_family sigma0 m x and m1 = substitute_on_canonical_object m0 m x in
						Atomic (Unlock (prop1, m1, sigma1, n2))
				| Canonical (Lock (prop0, m1, sigma1, m2)) when prop0 = prop1 ->
					let sigma2 = substitute_on_canonical_family sigma0 m x and m3 = substitute_on_canonical_object m0 m x in
						if sigma2 = sigma1 && m3 = m1
						then
							Canonical (m2)
						else
							failwith "condition unlock"
				| _ -> failwith "matching unlock"
			)
in let a = aux () in(* Printf.printf "substitution over for atomic_object: %s\n" (match a with Atomic n11 -> Intermediate.atomic_object_to_string n11 | Canonical m47 -> Intermediate.canonical_object_to_string m47);*) a
