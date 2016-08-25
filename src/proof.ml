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
open Intermediate
open Library

let compute_from_string (prop : string) (sign : signature) (gamma : context) (m : canonical_object) (sigma : canonical_family) =
	match prop with
		| "true" ->
			l_true sign gamma m sigma
		| "val" ->
			l_val sign gamma m sigma
		| "qf" ->
			l_qf sign gamma m sigma
		| "set" ->
			l_set sign gamma m sigma
		| "closed" ->
			l_closed sign gamma m sigma
		| "fitch" ->
			l_fitch sign gamma m sigma
		| _ ->
			failwith "undefined"

let open_coqide coq_file prop sign gamma m sigma =
	let rec fresh i =
		let string_i = "proof/interm" ^ (string_of_int i) in
			try (
				let file = open_in (string_i ^ ".v") in
					close_in file;
					fresh (i+1)
				)
			with _ ->
				string_i
	in
	let interm = fresh 0 in
	let new_file = open_out (interm ^ ".v") in
	begin
		Printf.fprintf new_file "%s" ("Require Import " ^ (String.sub coq_file 0 (String.length coq_file - 1)) ^ "\nRequire Import definitions.\n\n");
		Printf.fprintf new_file "%s" (theorem_to_string_coqide prop sign gamma m sigma ^ "\n\n");
		Printf.fprintf new_file "%s" "Proof.\n\n(* Prove the propriety to continue. *)\n(* When you achieved it, close coqide\n   (don't forget to enter 'Qed' and compile)\n   and type anything in the command line. *)\n\n";
		close_out new_file;
		begin
			Sys.command ("coqide " ^ (interm ^ ".v"));
			let _ = read_line () in
			try (open_in (interm ^ ".vo")) with _ -> failwith "no proof";
		end
	end

let proves prop sign gamma m sigma =
	Printf.printf "%s" ("here is the theorem one has to prove:\n\n" ^ (theorem_to_string_terminal prop sign gamma m sigma) ^ "\n\n\nwhat kind of program do you want to prove the theorem with?\n\n(ocaml or coqide)\n\n");
	let rec f_aux1 () =
		let s = read_line () in
			if s = "ocaml" || s = "coqide" || s = "coq" || s = "quit" || s = "q" 
			then
				s
			else
				begin
					Printf.printf "%s" "what you wrote wasn't understandable, please write ocaml or coqide, or q if you want to quit\n\n";
					f_aux1 ()
				end
	in
		let rec f_aux2 prog =
			if prog = "ocaml"
			then
				try
					compute_from_string prop sign gamma m sigma
				with
					Failure "undefined" ->
						begin
							Printf.printf "%s" (prog ^ " is not defined in library.ml\n\n");
							f_aux2 (f_aux1 ())
						end
			else
				if prog = "coq" || prog = "coqide"
				then
					(
					Printf.printf "%s" ("\nplease enter the file in which " ^ prop ^ " is defined\n\n");
					let coq_file = read_line () in
						try
							open_coqide coq_file prop sign gamma m sigma;
							true
						with
							Failure "no proof" ->
								false
					)
				else
					failwith "quit"
		in
			f_aux2 (f_aux1 ())
