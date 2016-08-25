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

let rec doesnt_contain_canonical_family_constant (sigma : canonical_family) (c : string) =
	match sigma with
		| Atomic tho ->
			doesnt_contain_atomic_family_constant tho c
		| Pi (_, sigma1, sigma2) ->
			doesnt_contain_canonical_family_constant sigma1 c && doesnt_contain_canonical_family_constant sigma2 c
		| Lock (_, m, sigma1, sigma2) ->
			doesnt_contain_canonical_object_constant m c && doesnt_contain_canonical_family_constant sigma1 c && doesnt_contain_canonical_family_constant sigma2 c
		| Prod (sigma1, sigma2) ->
			doesnt_contain_canonical_family_constant sigma1 c && doesnt_contain_canonical_family_constant sigma2 c

and doesnt_contain_atomic_family_constant (tho : atomic_family) (c : string) =
	match tho with
		| Const_family _ ->
			true
		| App (tho1, m) ->
			doesnt_contain_atomic_family_constant tho1 c && doesnt_contain_canonical_object_constant m c

and doesnt_contain_canonical_object_constant (m : canonical_object) (c : string) =
	match m with
		| Atomic n ->
			doesnt_contain_atomic_object_constant n c
		| Lam (_, sigma, m1) ->
			doesnt_contain_canonical_family_constant sigma c && doesnt_contain_canonical_object_constant m1 c
		| Lock (_, m1, sigma, m2) ->
			doesnt_contain_canonical_object_constant m1 c && doesnt_contain_canonical_family_constant sigma c && doesnt_contain_canonical_object_constant m2 c
		| Pair (m1, m2) ->
			doesnt_contain_canonical_object_constant m1 c && doesnt_contain_canonical_object_constant m2 c

and doesnt_contain_atomic_object_constant (n : atomic_object) (c : string) =
	match n with
		| Const c1 ->
			c <> c1
		| Var _ ->
			true
		| App (n1, m) ->
			doesnt_contain_atomic_object_constant n1 c && doesnt_contain_canonical_object_constant m c
		| Unlock (_, m, sigma, n1) ->
			doesnt_contain_canonical_object_constant m c && doesnt_contain_canonical_family_constant sigma c && doesnt_contain_atomic_object_constant n1 c
