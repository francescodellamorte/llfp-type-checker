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

let rec check_delta_canonical_family (sigma : canonical_family) y m0 =
	match sigma with
		| Atomic tho ->
			check_delta_atomic_family tho y m0
		| Pi (x, sigma1, sigma2) ->
			check_delta_canonical_family sigma1 y m0 && check_delta_canonical_family sigma2 y m0
		| Lock (prop, m, sigma1, sigma2) ->
			check_delta_canonical_object m y m0 && check_delta_canonical_family sigma1 y m0 && check_delta_canonical_family sigma2 y m0
		| Prod (sigma1, sigma2) ->
			check_delta_canonical_family sigma1 y m0 && check_delta_canonical_family sigma2 y m0

and check_delta_atomic_family tho y m0 =
	match tho with
		| Const_family _ ->
			true
		| App (tho1, m) ->
			check_delta_atomic_family tho1 y m0 && check_delta_canonical_object m y m0

and check_delta_canonical_object m y m0 =
	match m with
		| Atomic n ->
			check_delta_atomic_object n y m0
		| Lam (x, sigma, m1) ->
			check_delta_canonical_family sigma y m0 && check_delta_canonical_object m1 y m0
		| Lock (x, m1, sigma, m2) ->
			check_delta_canonical_object m1 y m0 && check_delta_canonical_family sigma y m0 && check_delta_canonical_object m2 y m0
		| Pair (m1, m2) ->
			check_delta_canonical_object m1 y m0 && check_delta_canonical_object m2 y m0

and check_delta_atomic_object n y m0 =
	match n with
		| App (App (Const "c_d", m1), Atomic (Var y1)) when alpha_conversion_on_canonical_objects m1 m0 [] && y1 = y ->
			true
		| Const x ->
			true
		| Var x ->
			x <> y
		| App (n1, m) ->
			check_delta_atomic_object n1 y m0 && check_delta_canonical_object m y m0
		| Unlock (x, m, sigma, n) ->
			check_delta_canonical_object m y m0 && check_delta_canonical_family sigma y m0 && check_delta_atomic_object n y m0
