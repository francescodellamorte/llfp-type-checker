(*
	Copyright 07/2016 Michielini Vincent and Scagnetto Ivan
    All rights reserved.

    Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

    * Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
    * Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.

    THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

(* definition of all the different structures *)

type signature_element = 
	| Const_family of string * kind
	| Const of string * canonical_family

and signature = signature_element list

and context = (string * canonical_family) list

and kind =
	| Type
	| Pi of string * canonical_family * kind

and canonical_family =
	| Atomic of atomic_family
	| Pi of string * canonical_family * canonical_family
	| Lock of string * canonical_object * canonical_family * canonical_family
	| Prod of canonical_family * canonical_family

and atomic_family =
	| Const_family of string
	| App of atomic_family * canonical_object

and canonical_object =
	| Atomic of atomic_object
	| Lam of string * canonical_family * canonical_object
	| Lock of string * canonical_object * canonical_family * canonical_object
	| Pair of canonical_object * canonical_object

and atomic_object =
	| Const of string
	| Var of string
	| App of atomic_object * canonical_object
	| Unlock of string * 
canonical_object * canonical_family * atomic_object

type signature_element' = 
	| Const_family of string * kind'
	| Const of string * family'

and signature' = signature_element' list

and context' = (string * family') list

and kind' =
	| Type
	| Pi of string * family' * kind'

and family' =	
	| Const_family of string
	| Pi of string * family' * family'
	| Lock of string * object' * family' * family'
	| App of family' * object'
	| Prod of family' * family'

and object' =
	| Const of string
	| Var of string
	| Lam of string * family' * object'
	| Lock of string * object' * family' * object'
	| App of object' * object'
	| Unlock of string * object' * family' * object'
	| Pair of object' * object'

type all_family =
	| Atomic of atomic_family
	| Canonical of canonical_family

type all_object =
(* this type is crucial for the substitution of objects : the substitution of an atomic object can be either atomic either canonical *)
	| Atomic of atomic_object
	| Canonical of canonical_object

type all_tc =
(* this type is useful to use the parser *)
	{
		sign : signature';
		gamma : context';
		m : object';
		sigma : family';
	}

type all_kc =
	{
		sign : signature';
		gamma : context';
		sigma : family';
	}

type all_ik =
	{
		sign : signature';
		gamma : context';
		k : kind';
	}

type all =
	| TC of all_tc
	| KC of all_kc
	| IK of all_ik
