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
open Delta
open Domains

let rec closed_canonical_family_under_list (gamma : context) (sigma : canonical_family) (s_list : string list) (num : int) (m_ret : canonical_object) =
	match sigma with
		| Atomic tho ->
			closed_atomic_family_under_list gamma tho s_list num m_ret
		| Pi (x, sigma1, sigma2) ->
			closed_canonical_family_under_list gamma sigma1 (x :: s_list) num m_ret && closed_canonical_family_under_list gamma sigma2 (x :: s_list) num m_ret
		| Lock (_, m, sigma1, sigma2) ->
			closed_canonical_family_under_list gamma sigma1 s_list num m_ret && closed_canonical_family_under_list gamma sigma2 s_list num m_ret && closed_canonical_object_under_list gamma m s_list num m_ret
		| Prod (sigma1, sigma2) ->
			closed_canonical_family_under_list gamma sigma1 s_list num m_ret && closed_canonical_family_under_list gamma sigma2 s_list num m_ret

and closed_atomic_family_under_list (gamma : context) (tho : atomic_family) (s_list : string list) (num : int) (m_ret : canonical_object) =
	match tho with
		| Const_family _ ->
			true
		| App (tho1, m) ->
			closed_atomic_family_under_list gamma tho1 s_list num m_ret && closed_canonical_object_under_list gamma m s_list num m_ret

and closed_canonical_object_under_list (gamma : context) (m : canonical_object) (s_list : string list) (num : int) (m_ret : canonical_object) =
	match m with
		| Atomic n ->
			closed_atomic_object_under_list gamma n s_list num m_ret
		| Lam (x, sigma, m1) ->
			closed_canonical_family_under_list gamma sigma (x :: s_list) num m_ret && closed_canonical_object_under_list gamma m1 (x :: s_list) num m_ret
		| Lock (_, m1, sigma, m2) ->
			closed_canonical_object_under_list gamma m1 s_list num m_ret && closed_canonical_family_under_list gamma sigma s_list num m_ret && closed_canonical_object_under_list gamma m2 s_list num m_ret
		| Pair (m1, m2) ->
			closed_canonical_object_under_list gamma m1 s_list num m_ret && closed_canonical_object_under_list gamma m2 s_list num m_ret

and closed_atomic_object_under_list (gamma : context) (n : atomic_object) (s_list : string list) (num : int) (m_ret : canonical_object) =
	match n with
		| Const _ ->
			true
		| Var x ->
			(
			match num with
				| 0 ->
					List.mem x s_list
				| 1 ->
					List.mem x s_list ||
					return_associated_family_in_context gamma x = Atomic (Const_family "o")
				| _ ->
					List.mem x s_list ||
					let sigma = return_associated_family_in_context gamma x in
						sigma = Atomic (Const_family "o") ||
						match sigma with
							| Atomic (App (Const_family "V", m0)) ->
								check_delta_canonical_object m_ret x m0
							| _ -> false
			)
		| App (n1, m) ->
			closed_atomic_object_under_list gamma n1 s_list num m_ret && closed_canonical_object_under_list gamma m s_list num m_ret
		| Unlock (_, m, sigma, n1) ->
			closed_canonical_object_under_list gamma m s_list num m_ret && closed_canonical_family_under_list gamma sigma s_list num m_ret && closed_atomic_object_under_list gamma n1 s_list num m_ret
