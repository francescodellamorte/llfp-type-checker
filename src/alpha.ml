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

let rec alpha_conversion_on_kinds (k1 : kind) (k2 : kind) (l : (string * string) list) =
(* tells if k1 and k2 are alpha-equivalent considering l *)
	match (k1, k2) with
		| Type, Type ->
			true
		| Pi (x1, sigma1, k1'), Pi (x2, sigma2, k2') ->
			let l' = (x1, x2) :: l in
				alpha_conversion_on_canonical_families sigma1 sigma2 l' && alpha_conversion_on_kinds k1' k2' l'
		| _ ->
			false

and alpha_conversion_on_canonical_families (sigma1 : canonical_family) (sigma2 : canonical_family) (l : (string * string) list) =
(* tells if sigma1 and sigma2 are alpha-equivalent considering l *)
	match (sigma1, sigma2) with
		| Atomic n1, Atomic n2 ->
			alpha_conversion_on_atomic_families n1 n2 l
		| Pi (x1, sigma1', sigma1''), Pi (x2, sigma2', sigma2'') ->
			let l' = (x1, x2) :: l in
				alpha_conversion_on_canonical_families sigma1' sigma2' l' && alpha_conversion_on_canonical_families sigma1'' sigma2'' l'
		| Lock (prop1, m1, sigma1', sigma1''), Lock (prop2, m2, sigma2', sigma2'') ->
			prop1 = prop2 && alpha_conversion_on_canonical_objects m1 m2 l && alpha_conversion_on_canonical_families sigma1' sigma2' l && alpha_conversion_on_canonical_families sigma1'' sigma2'' l
		| Prod (sigma1', sigma1''), Prod (sigma2', sigma2'') ->
			alpha_conversion_on_canonical_families sigma1' sigma2' l && alpha_conversion_on_canonical_families sigma1'' sigma2'' l
		| _ ->
			false

and alpha_conversion_on_atomic_families (tho1 : atomic_family) (tho2 : atomic_family) (l : (string * string) list) =
(* tells if tho1 and tho2 are alpha-equivalent considering l *)
	match (tho1, tho2) with
		| Const_family a1, Const_family a2 ->
			a1 = a2
		| App (tho1', m1), App (tho2', m2) ->
			alpha_conversion_on_atomic_families tho1' tho2' l && alpha_conversion_on_canonical_objects m1 m2 l
		| _ ->
			false

and alpha_conversion_on_canonical_objects (m1 : canonical_object) (m2 : canonical_object) (l : (string * string) list) =
(* tells if m1 and m2 are alpha-equivalent considering l *)
	match (m1, m2) with
		| Atomic n1, Atomic n2 ->
			alpha_conversion_on_atomic_objects n1 n2 l
		| Lam (x1, sigma1, m1'), Lam (x2, sigma2, m2') ->
			let l' = (x1, x2) :: l in
				alpha_conversion_on_canonical_families sigma1 sigma2 l' && alpha_conversion_on_canonical_objects m1' m2' l'
		| Lock (prop1, m1', sigma1, m1''), Lock (prop2, m2', sigma2, m2'') ->
			prop1 = prop2 && alpha_conversion_on_canonical_objects m1' m2' l && alpha_conversion_on_canonical_families sigma1 sigma2 l && alpha_conversion_on_canonical_objects m1'' m2'' l
		| Pair (m1', m1''), Pair (m2', m2'') ->
			alpha_conversion_on_canonical_objects m1' m2' l && alpha_conversion_on_canonical_objects m1'' m2'' l
		| _ ->
			false

and alpha_conversion_on_atomic_objects (n1 : atomic_object) (n2 : atomic_object) (l : (string * string) list) =
(* tells if n1 and n2 are alpha-equivalent considering l *)
	match (n1, n2) with
		| Const c1, Const c2 ->
			c1 = c2
		| Var x1, Var x2 ->
			x2 = (try List.assoc x1 l with Not_found -> x1)					
		| App (n1', m1), App (n2', m2) ->
			alpha_conversion_on_atomic_objects n1' n2' l && alpha_conversion_on_canonical_objects m1 m2 l
		| Unlock (prop1, m1, sigma1, n1'), Unlock (prop2, m2, sigma2, n2') ->
			alpha_conversion_on_canonical_objects m1 m2 l && alpha_conversion_on_canonical_families sigma1 sigma2 l && alpha_conversion_on_atomic_objects n1' n2' l
		| _ ->
			false
