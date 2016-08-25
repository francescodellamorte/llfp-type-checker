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
open Closed
open Contain

let l_true _ _ _ _ =
	true

let l_val _ _ (m : canonical_object) _ =
	match m with
		| Atomic (App (Const s, _)) ->
			s = "c_free" || s = "c_lam"
		| _ ->
			false

let l_qf _ _ (m : canonical_object) (sigma : canonical_family) =
	sigma = Atomic (Const_family "bool") && closed_canonical_object_under_list [] m [] 0 m && doesnt_contain_canonical_object_constant m "c_forall"

let l_set _ _ (m : canonical_object) (sigma : canonical_family) =
	sigma = Atomic (Const_family "args") &&
	match m with
		| Atomic (App (App (Const "c_assoc", (Atomic (Const c))), e)) ->
			closed_canonical_object_under_list [] e [] 0 e && doesnt_contain_canonical_object_constant e c
		| _ ->
			false

let l_closed _ (gamma : context) (m : canonical_object) (sigma : canonical_family) =
	closed_canonical_object_under_list gamma m [] 0 m

let l_fitch _ (gamma : context) (m : canonical_object) (sigma : canonical_family) =
	match (m, sigma) with
		| (Pair (m1, m2), Prod (Atomic (App (Const_family "T", a1)), Atomic (App (Const_family "T" , Atomic (App (App (Const "c_r", a2), b)))))) when alpha_conversion_on_canonical_objects a1 a2 [] ->
			closed_canonical_object_under_list gamma m1 [] 2 m1 && closed_canonical_object_under_list gamma m2 [] 2 m2
		| _ ->
			false
