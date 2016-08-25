(*
	Copyright 07/2016 Michielini Vincent and Scagnetto Ivan
    All rights reserved.

    Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

    * Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
    * Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.

    THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

open Canonical
open Definitions
open Lexer
open Parser
open Type_checking

let main file =
	let file1 = open_in file in
		let all = Parser.all_tc Lexer.read (Lexing.from_channel file1) in
			match all with
				| TC all_tc ->
					let sign =
						try (canonize_signature all_tc.sign)
						with _ ->
							failwith "error: unable to canonize the signature"
					in
						let gamma =
							try (canonize_context sign all_tc.gamma)
							with _ ->
								failwith "error: unable to canonize the context"
						in
							let m =
								try (canonize_object sign gamma all_tc.m)
								with _ ->
									failwith "error: unable to canonize the object"
							in
								let sigma =
									try (canonize_family sign gamma all_tc.sigma)
									with _ ->
										failwith "error: unable to canonize the family"
								in
									let b =
										try (
											has_canonical_object_canonical_family sign gamma m (canonize_family sign gamma all_tc.sigma)
										)
										with _ -> false in
											begin
												close_in file1;
												Printf.printf "your judgement is %s\n" (if b then "correct" else "uncorrect")
											end
				| IK _ ->
					failwith "error: this file is a is_kind file"
				| KC _ ->
					failwith "error: this file is a kind_checking file";;

try (main Sys.argv.(1))
with Failure s ->
	Printf.printf "%s\n" s
