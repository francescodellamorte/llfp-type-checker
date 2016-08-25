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
open Proof
open Substitutions
open Type_checking

let rec canonize_signature_element (sign : signature) (s_e' : signature_element') : signature_element =
	match s_e' with
		| Const_family (a, k') ->
			Const_family (a, canonize_kind sign [] k')
		| Const (c, sigma') ->
			Const (c, canonize_family sign [] sigma')

and canonize_signature (sign' : signature') : signature =
	match sign' with
		| [] ->
			[]
		| s_e' :: sign'' ->
			let sign = canonize_signature sign'' in
				(canonize_signature_element sign s_e') :: sign

and canonize_context (sign : signature) (gamma' : context') : context =
	match gamma' with
		| [] ->
			[]
		| (x, sigma') :: gamma'' ->
			let gamma = canonize_context sign gamma'' in
				(x, canonize_family sign gamma sigma') :: gamma

and canonize_kind (sign : signature) (gamma : context) (k' : kind') : kind =
	match k' with
		| Type ->
			Type
		| Pi (x, sigma', k1') ->
			let sigma = canonize_family sign gamma sigma' in
				let k1 = canonize_kind sign ((x, sigma) :: gamma) k1' in
					Pi (x, sigma, k1)

and canonize_family (sign : signature) (gamma : context) (sigma' : family') : canonical_family =
	match (canonize_aux_family sign gamma sigma') with
		| Canonical sigma ->
			sigma
		| Atomic tho ->
			Atomic tho 

and canonize_aux_family (sign : signature) (gamma : context) (sigma' : family') : all_family =
	match sigma' with
		| Const_family a ->
			Atomic (Const_family a)
		| Pi (x, sigma1', sigma2') ->
			Canonical (Pi (x, canonize_family sign gamma sigma1', canonize_family sign gamma sigma2'))
		| Lock (prop, m', sigma1', sigma2') ->
			Canonical (Lock (prop, canonize_object sign gamma m', canonize_family sign gamma sigma1', canonize_family sign gamma sigma2'))
		| App (sigma1', m') ->
			(
			match canonize_aux_family sign gamma sigma1' with
				| Atomic tho ->
					Atomic (App (tho, canonize_object sign gamma m'))
				| _ ->
					failwith "unable to canonize the data"
			)
		| Prod (sigma1', sigma2') ->
			Canonical (Prod (canonize_family sign gamma sigma1', canonize_family sign gamma sigma2'))

and canonize_object (sign : signature) (gamma : context) (m' : object') : canonical_object =
	match (canonize_aux_object sign gamma m') with 
		| Canonical m ->
			m
		| Atomic n ->
			Atomic n

and canonize_aux_object (sign : signature) (gamma : context) (m' : object') : all_object =
	match m' with
		| Const c ->
			Atomic (Const c)
		| Var x ->
			Atomic (Var x)
		| Lam (x, sigma', m1') ->
			Canonical (Lam (x, canonize_family sign gamma sigma', canonize_object sign gamma m1'))
		| Lock (prop, m1', sigma', m2') ->
			Canonical (Lock (prop, canonize_object sign gamma m1', canonize_family sign gamma sigma', canonize_object sign gamma m2'))
		| App (m1', m2') ->
			(
			match canonize_aux_object sign gamma m1' with
				| Atomic n ->
					Atomic (App (n, canonize_object sign gamma m2'))
				| Canonical (Lam (x, sigma, m)) ->
					let m2 = canonize_object sign gamma m2' in
						if has_canonical_object_canonical_family sign gamma m2 sigma
						then
							Canonical (substitute_on_canonical_object m m2 x)
						else
							failwith "unable to canonize the data"
				| _ ->
					failwith "unable to canonize the data"
			)
		| Unlock (prop1, m1', sigma', m2') ->
			(
			match canonize_aux_object sign gamma m2' with
				| Atomic n ->
					Atomic (Unlock (prop1, canonize_object sign gamma m1', canonize_family sign gamma sigma', n))
				| Canonical (Lock (prop2, m1, sigma, m2)) when prop2 = prop1 && m1 = canonize_object sign gamma m1' && sigma = canonize_family sign gamma sigma' ->
					if has_canonical_object_canonical_family sign gamma m1 sigma && proves prop1 sign gamma m1 sigma
					then
						Canonical (m2)
					else
						failwith "no proof achieved for unlock rule"
				| _ ->
					failwith "unable to canonize the data"
			)
		| Pair (m1', m2') ->
			Canonical (Pair (canonize_object sign gamma m1', canonize_object sign gamma m2'))
