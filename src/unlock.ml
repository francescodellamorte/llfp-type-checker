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
open Variables

(* the first four functions return, for any object or family, the list of its unlock sub-objects *)

let rec list_of_all_unlock_in_canonical_family (sigma : canonical_family) (q_list : (string * canonical_object * canonical_family * atomic_object) list) =
	match sigma with
		| Atomic tho ->
			list_of_all_unlock_in_atomic_family tho q_list
		| Pi (x, sigma1, sigma2) ->
			list_of_all_unlock_in_canonical_family sigma1 (list_of_all_unlock_in_canonical_family sigma2 q_list)
		| Lock (prop, m, sigma1, sigma2) ->
			list_of_all_unlock_in_canonical_object m (list_of_all_unlock_in_canonical_family sigma1 (list_of_all_unlock_in_canonical_family sigma2 q_list))
		| Prod (sigma1, sigma2) ->
			list_of_all_unlock_in_canonical_family sigma1 (list_of_all_unlock_in_canonical_family sigma2 q_list)

and list_of_all_unlock_in_atomic_family (tho : atomic_family) (q_list : (string * canonical_object * canonical_family * atomic_object) list) =
	match tho with
		| Const_family _ ->
			q_list
		| App (tho', m) ->
			list_of_all_unlock_in_atomic_family tho' (list_of_all_unlock_in_canonical_object m q_list)

and list_of_all_unlock_in_canonical_object (m : canonical_object) (q_list : (string * canonical_object * canonical_family * atomic_object) list) =
	match m with
		| Atomic n ->
			list_of_all_unlock_in_atomic_object n q_list
		| Lam (x, sigma, m') ->
			list_of_all_unlock_in_canonical_family sigma (list_of_all_unlock_in_canonical_object m' q_list)
		| Lock (prop, m1, sigma, m2) ->
			list_of_all_unlock_in_canonical_object m1 (list_of_all_unlock_in_canonical_family sigma (list_of_all_unlock_in_canonical_object m2 q_list))
		| Pair (m1, m2) ->
			list_of_all_unlock_in_canonical_object m1 (list_of_all_unlock_in_canonical_object m2 q_list)

and list_of_all_unlock_in_atomic_object (n : atomic_object) (q_list : (string * canonical_object * canonical_family * atomic_object) list) =
	match n with
		| Const _ ->
			q_list
		| Var _ ->
			q_list
		| App (n', m) ->
			list_of_all_unlock_in_atomic_object n' (list_of_all_unlock_in_canonical_object m q_list)
		| Unlock (prop, m, sigma, n') ->
			let q = (prop, m, sigma, n')
			and q_list' = list_of_all_unlock_in_canonical_object m (list_of_all_unlock_in_canonical_family sigma (list_of_all_unlock_in_atomic_object n' q_list)) in
				if List.mem q q_list'
				then
					q_list'
				else
					q :: q_list'

let rec substitute_unlock_on_canonical_family (sigma : canonical_family) (x : string) (q : (string * canonical_object * canonical_family * atomic_object)) : canonical_family =
(* returns a canonical_family: sigma in which Unlock(m0, sigma0, n0) is subsituted by x *)
	match sigma with
		| Atomic tho ->
			Atomic (substitute_unlock_on_atomic_family tho x q)
		| Pi (y, sigma1, sigma2) ->
			Pi (y, substitute_unlock_on_canonical_family sigma1 x q, substitute_unlock_on_canonical_family sigma2 x q)
		| Lock (prop, m0, sigma1, sigma2) ->
			Lock (prop, substitute_unlock_on_canonical_object m0 x q, substitute_unlock_on_canonical_family sigma1 x q, substitute_unlock_on_canonical_family sigma2 x q)
		| Prod (sigma1, sigma2) ->
			Prod (substitute_unlock_on_canonical_family sigma1 x q, substitute_unlock_on_canonical_family sigma2 x q)

and substitute_unlock_on_atomic_family (tho : atomic_family) (x : string) (q : (string * canonical_object * canonical_family * atomic_object)) =
(* returns an atomic family: tho in which Unlock(m0, sigma0, n0) is subsituted by x *)
	match tho with
		| Const_family _ ->
			tho
		| App (tho', m) ->
			App (substitute_unlock_on_atomic_family tho' x q, substitute_unlock_on_canonical_object m x q)

and substitute_unlock_on_canonical_object (m : canonical_object) (x : string) (q : (string * canonical_object * canonical_family * atomic_object)) =
(* returns a canonical_object: m in which Unlock(m0, sigma0, n0) is subsituted by x *)
	match m with
		| Atomic n ->
			Atomic (substitute_unlock_on_atomic_object n x q)
		| Lam (y, sigma, m') ->
			Lam (y, substitute_unlock_on_canonical_family sigma x q, substitute_unlock_on_canonical_object m' x q)
		| Lock (prop1, m1, sigma1, m2) ->
			Lock (prop1, substitute_unlock_on_canonical_object m1 x q, substitute_unlock_on_canonical_family sigma1 x q, substitute_unlock_on_canonical_object m2 x q)
		| Pair (m1, m2) ->
			Pair (substitute_unlock_on_canonical_object m1 x q, substitute_unlock_on_canonical_object m2 x q)

and substitute_unlock_on_atomic_object (n : atomic_object) (x : string) ((prop0, m0, sigma0, n0) as q : (string * canonical_object * canonical_family * atomic_object)) =
(* returns an atomic object: n in which Unlock(m0, sigma0, n0) is subsituted by x *)
	match n with
		| (Const _ | Var _) ->
			n
		| App (n', m) ->
			App (substitute_unlock_on_atomic_object n' x q, substitute_unlock_on_canonical_object m x q)
		| Unlock (prop1, m1, sigma1, n1) ->
			if prop0 = prop1 && alpha_conversion_on_canonical_objects m0 m1 [] && alpha_conversion_on_canonical_families sigma0 sigma1 [] && alpha_conversion_on_atomic_objects n0 n1 []
			then
				Var x
			else
				Unlock (prop1, substitute_unlock_on_canonical_object m1 x q, substitute_unlock_on_canonical_family sigma1 x q, substitute_unlock_on_atomic_object n1 x q)

let rec intersection l1 l2 =
	match l1 with
		| [] ->
			[]
		| t1 :: l1' ->
			if List.mem t1 l2
			then
				t1 :: (intersection l1' l2)
			else
				intersection l1' l2
