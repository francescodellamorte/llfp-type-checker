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

(* this first four functions return, for any object or family, the list of variables in it *)

let rec variables_list_of_canonical_family (sigma : canonical_family) (s_list : string list) =
	match sigma with
		| Atomic tho ->
			variables_list_of_atomic_family tho s_list
		| Pi (x, sigma1, sigma2) ->
			let s_list' = variables_list_of_canonical_family sigma1 (variables_list_of_canonical_family sigma2 s_list) in
				if List.mem x s_list'
				then
					s_list'
				else
					x::s_list'
		| Lock (_, m, sigma1, sigma2) ->
			variables_list_of_canonical_object m  (variables_list_of_canonical_family sigma1  (variables_list_of_canonical_family sigma2 s_list))
		| Prod (sigma1, sigma2) ->
			variables_list_of_canonical_family sigma1  (variables_list_of_canonical_family sigma2 s_list)

and variables_list_of_atomic_family (tho : atomic_family) (s_list : string list) =
	match tho with
		| Const_family a ->
			if List.mem a s_list
			then
				a :: s_list
			else
				s_list
		| App (tho', m) ->
			variables_list_of_atomic_family tho' (variables_list_of_canonical_object m s_list)

and variables_list_of_canonical_object (m : canonical_object) (s_list : string list) =
	match m with
		| Atomic n ->
			variables_list_of_atomic_object n s_list
		| Lam (x, sigma, m') ->
			let s_list' = variables_list_of_canonical_family sigma (variables_list_of_canonical_object m' s_list) in
				if List.mem x s_list'
				then
					s_list'
				else
					x::s_list'
		| Lock (_, m1, sigma, m2) ->
			 variables_list_of_canonical_object m1 (variables_list_of_canonical_family sigma (variables_list_of_canonical_object m2 s_list))
		| Pair (m1, m2) ->
			variables_list_of_canonical_object m1  (variables_list_of_canonical_object m2 s_list)

and variables_list_of_atomic_object (n : atomic_object) (s_list : string list) =
	match n with
		| Const c ->
			s_list
		| Var x ->
			if List.mem x s_list
			then
				s_list
			else
				x :: s_list
		| App (n', m) ->
			variables_list_of_atomic_object n' (variables_list_of_canonical_object m s_list)
		| Unlock (_, m, sigma, n') ->
			variables_list_of_canonical_object m (variables_list_of_canonical_family sigma (variables_list_of_atomic_object n' s_list))

let fresh_variable v_list =
(* creates a new variable for m, which doesn't already appear in it *)
		let rec fresh_i i =
			let x_i = "x" ^ (string_of_int i) in
				if List.mem x_i v_list
				then
					fresh_i (i+1)
				else
					x_i
			in
				fresh_i 0
