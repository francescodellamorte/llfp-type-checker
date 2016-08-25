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

let rec return_associated_family_in_context (gamma : context) (x : string) =
(* returns the family associated to x in he context gamma, returns an error if x is not in its domain *)
	match gamma with
		| [] -> failwith "not in the context"
		| (y, _) :: gamma' when x <> y -> return_associated_family_in_context gamma' x
		| (y, sigma) :: _ -> sigma

let rec return_associated_kind_in_signature (sign : signature) (a : string) =
(* returns the kind associated to a in the signature sign, returns an error if a is not in its domain *)
	match sign with
		| [] -> failwith "not in the signature"
		| (Const _) :: sign' -> return_associated_kind_in_signature sign' a
		| (Const_family (b, _)) :: sign' when a <> b -> return_associated_kind_in_signature sign' a
		| (Const_family (b, k)) :: _ -> k

let rec return_associated_family_in_signature (sign : signature) (c : string) =
(* returns the family associated to a in the signature sign, returns an error if c is not in its domain *)
	match sign with
		| [] -> failwith "not in the signature"
		| (Const_family _) :: sign' -> return_associated_family_in_signature sign' c
		| (Const (d, _)) :: sign' when c <> d -> return_associated_family_in_signature sign' c
		| (Const (d, sigma)) :: _ -> sigma
