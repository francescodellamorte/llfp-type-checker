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

(* the following functions associate to each element of the theory a string to be understood by Coq *)

let rec signature_element_to_string_coqide (s_e : signature_element) =
	match s_e with
		| Const_family (a, k) ->
			"Const_family_s_e \"" ^ a ^ "\" (" ^ (kind_to_string_coqide k) ^ ")"
		| Const (c, sigma) ->   
			"Const_s_e \"" ^ c ^ "\" (" ^ (canonical_family_to_string_coqide sigma) ^ ")"

and signature_to_string_coqide (sign : signature) =
	match sign with
		| [] ->
			"nil"
		| s_e :: sign' ->
			"cons (" ^ (signature_element_to_string_coqide s_e) ^ ") (" ^ (signature_to_string_coqide sign') ^ ")"

and context_to_string_coqide (gamma : context) =
	match gamma with
		| [] ->
			"nil"
		| (x, sigma) :: gamma' ->
			"cons (Var_c_e \"" ^ x ^ "\" (" ^ (canonical_family_to_string_coqide sigma) ^ ")) (" ^ (context_to_string_coqide gamma') ^ ")"

and kind_to_string_coqide (k : kind) =
	match k with
		| Type ->
			"Type_k"
		| Pi (x, sigma, k') ->
			"Pi_k \"" ^ x ^ "\" (" ^ (canonical_family_to_string_coqide sigma) ^ ") (" ^ (kind_to_string_coqide k') ^ ")"

and canonical_family_to_string_coqide (sigma : canonical_family) =
	match sigma with
		| Atomic tho ->
			"Atomic_c_f (" ^ (atomic_family_to_string_coqide tho) ^ ")"
		| Pi (x, sigma1, sigma2) ->
			"Pi_c_f (\"" ^ x ^ "\") (" ^ (canonical_family_to_string_coqide sigma1) ^ ") (" ^ (canonical_family_to_string_coqide sigma2) ^ ")"
		| Lock (prop, m, sigma1, sigma2) ->
			"Lock_c_f \""^ prop ^ "\" (" ^ (canonical_object_to_string_coqide m) ^ ") (" ^ (canonical_family_to_string_coqide sigma1) ^ ") (" ^ (canonical_family_to_string_coqide sigma2) ^ ")"
		| Prod (sigma1, sigma2) ->
			"Prod_c_f (" ^ (canonical_family_to_string_coqide sigma1) ^ ") (" ^ (canonical_family_to_string_coqide sigma2) ^ ")"

and atomic_family_to_string_coqide (tho : atomic_family) =
	match tho with
		| Const_family a ->
			"Const_family_a_f (\"" ^ a ^ "\")"
		| App (tho', m) ->
			"App_a_f (" ^ (atomic_family_to_string_coqide tho') ^ ") (" ^ (canonical_object_to_string_coqide m) ^ ")"

and canonical_object_to_string_coqide (m : canonical_object) =
	match m with
		| Atomic n ->
			"Atomic_c_o (" ^ (atomic_object_to_string_coqide n) ^ ")"
		| Lam (x, sigma, m) ->
			"Lam_c_o (\"" ^ x ^ "\") (" ^ (canonical_family_to_string_coqide sigma) ^ ") (" ^ (canonical_object_to_string_coqide m) ^ ")"
		| Lock (prop, m1, sigma, m2) ->
			"Lock_c_o \""^ prop ^ "\" (" ^ (canonical_object_to_string_coqide m1) ^ ") (" ^ (canonical_family_to_string_coqide sigma) ^ ") (" ^ (canonical_object_to_string_coqide m2) ^ ")"
		| Pair (m1, m2) ->
			"Paid_c_o (" ^ (canonical_object_to_string_coqide m1) ^ ") (" ^ (canonical_object_to_string_coqide m2) ^ ")"

and atomic_object_to_string_coqide (n : atomic_object) =
	match n with
		| Const c ->
			"Const_a_o (\"" ^ c ^ "\")"
		| Var x ->
			"Var_a_o (\"" ^ x ^ "\")"
		| App (n', m) ->
			"App_a_o (" ^ (atomic_object_to_string_coqide n') ^ ") (" ^ (canonical_object_to_string_coqide m) ^ ")"
		| Unlock (prop, m, sigma, n') ->
			"Unlock_a_o \""^ prop ^ "\" (" ^ (canonical_object_to_string_coqide m) ^ ") (" ^ (canonical_family_to_string_coqide sigma) ^ ") (" ^ (atomic_object_to_string_coqide n') ^ ")"

let theorem_to_string_coqide (prop : string) (sign : signature) (gamma : context) (m : canonical_object) (sigma : canonical_family) =
	"Theorem intermediar_theorem :\n" ^ prop ^ " ( " ^ (signature_to_string_coqide sign) ^ " ) ( " ^ (context_to_string_coqide gamma) ^ " ) ( " ^ (canonical_object_to_string_coqide m) ^ " ) ( " ^ (canonical_family_to_string_coqide sigma) ^ " )."

(* the following functions associate to each element of the theory a string to be printed in the terminal *)

let rec signature_element_to_string_terminal (s_e : signature_element) =
	match s_e with
		| Const_family (a, k) ->
			a ^ " : " ^ (kind_to_string_terminal k)
		| Const (c, sigma) ->   
			c ^ " : " ^ (canonical_family_to_string_terminal sigma)

and signature_to_string_terminal (sign : signature) =
	match sign with
		| [] ->
			""
		| s_e :: sign' ->
			(signature_element_to_string_terminal s_e) ^ "\n" ^ (signature_to_string_terminal sign')

and context_to_string_terminal (gamma : context) =
	match gamma with
		| [] ->
			""
		| (x, sigma) :: gamma' ->
			x ^ " : " ^ (canonical_family_to_string_terminal sigma) ^ "\n" ^ (context_to_string_terminal gamma')

and kind_to_string_terminal (k : kind) =
	match k with
		| Type ->
			"*"
		| Pi (x, sigma, k') ->
			"Pi " ^ x ^ ": " ^ (canonical_family_to_string_terminal sigma) ^ ". " ^ (kind_to_string_terminal k')

and canonical_family_to_string_terminal (sigma : canonical_family) =
	match sigma with
		| Atomic tho ->
			atomic_family_to_string_terminal tho
		| Pi (x, sigma1, sigma2) ->
			"Pi " ^ x ^ ": " ^ (canonical_family_to_string_terminal sigma1) ^ ". " ^ (canonical_family_to_string_terminal sigma2)
		| Lock (prop, m, sigma1, sigma2) ->
			"Lock "^ prop ^ " (" ^ (canonical_object_to_string_terminal m) ^ ", " ^ (canonical_family_to_string_terminal sigma1) ^ ") [" ^ (canonical_family_to_string_terminal sigma2) ^ "]"
		| Prod (sigma1, sigma2) ->
			"(" ^ (canonical_family_to_string_terminal sigma1) ^ ") X (" ^ (canonical_family_to_string_terminal sigma2) ^ ")"

and atomic_family_to_string_terminal (tho : atomic_family) =
	match tho with
		| Const_family a ->
			a
		| App (tho', m) ->
			"(" ^ (atomic_family_to_string_terminal tho') ^ ") (" ^ (canonical_object_to_string_terminal m) ^ ")"

and canonical_object_to_string_terminal (m : canonical_object) =
	match m with
		| Atomic n ->
			atomic_object_to_string_terminal n
		| Lam (x, sigma, m) ->
			"Lam " ^ x ^ ": " ^ (canonical_family_to_string_terminal sigma) ^ ". " ^ (canonical_object_to_string_terminal m)
		| Lock (prop, m1, sigma, m2) ->
			"Lock "^ prop ^ " (" ^ (canonical_object_to_string_terminal m1) ^ ", " ^ (canonical_family_to_string_terminal sigma) ^ ") [" ^ (canonical_object_to_string_terminal m2) ^ "]"
		| Pair (m1, m2) ->
			"<" ^ (canonical_object_to_string_terminal m1) ^ ", " ^ (canonical_object_to_string_terminal m2) ^ ">"

and atomic_object_to_string_terminal (n : atomic_object) =
	match n with
		| Const c ->
			c
		| Var x ->
			x
		| App (n', m) ->
			"(" ^ (atomic_object_to_string_terminal n') ^ ") (" ^ (canonical_object_to_string_terminal m) ^ ")"
		| Unlock (prop, m, sigma, n') ->
			"Unlock "^ prop ^ " (" ^ (canonical_object_to_string_terminal m) ^ ", " ^ (canonical_family_to_string_terminal sigma) ^ ") [" ^ (atomic_object_to_string_terminal n') ^ "]"

let theorem_to_string_coqide (prop : string) (sign : signature) (gamma : context) (m : canonical_object) (sigma : canonical_family) =
	"Theorem intermediar_theorem :\n" ^ prop ^ " ( " ^ (signature_to_string_coqide sign) ^ " ) ( " ^ (context_to_string_coqide gamma) ^ " ) ( " ^ (canonical_object_to_string_coqide m) ^ " ) ( " ^ (canonical_family_to_string_coqide sigma) ^ " )."

let theorem_to_string_terminal (prop : string) (sign : signature) (gamma : context) (m : canonical_object) (sigma : canonical_family) =
	"SIGNATURE:\n"  ^ (signature_to_string_terminal sign) ^ "\n\nCONTEXT:\n" ^ (context_to_string_terminal gamma) ^ "\n\nOBJECT:\n" ^ (canonical_object_to_string_terminal m) ^ "\n\nFAMILY:\n" ^ (canonical_family_to_string_terminal sigma) ^ "\n\nPREDICATE:\n" ^ prop
