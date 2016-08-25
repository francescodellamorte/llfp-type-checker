/*
	Copyright 07/2016 Michielini Vincent and Scagnetto Ivan
    All rights reserved.

    Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

    * Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
    * Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.

    THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*/

%{open Definitions%}

%token SIGN
%token ENDS
%token CONT
%token ENDC
%token OBJ
%token FAM
%token KIND
%token LPAR
%token RPAR
%token SEP
%token TYPE
%token LAM
%token DPOINT
%token POINT
%token LCK
%token COMMA
%token LBRK
%token RBRK
%token UNLCK
%token PI
%token INF
%token SUP
%token PROD
%token <string> CONST
%token <string> VAR
%token EOF

%start all_tc
%start all_kc
%start all_ik
%type <Definitions.all> all_tc
%type <Definitions.all> all_kc
%type <Definitions.all> all_ik

%%

all_tc :
	| SIGN sign CONT gamma OBJ m FAM sigma {TC {sign = List.rev $2; gamma = List.rev $4; m = $6; sigma = $8}}
	| SIGN sign CONT gamma FAM sigma OBJ m {TC {sign = List.rev $2; gamma = List.rev $4; m = $8; sigma = $6}}
	| SIGN sign OBJ m CONT gamma FAM sigma {TC {sign = List.rev $2; gamma = List.rev $6; m = $4; sigma = $8}}
	| SIGN sign OBJ m FAM sigma CONT gamma {TC {sign = List.rev $2; gamma = List.rev $8; m = $4; sigma = $6}}
	| SIGN sign FAM sigma CONT gamma OBJ m {TC {sign = List.rev $2; gamma = List.rev $6; m = $8; sigma = $4}}
	| SIGN sign FAM sigma OBJ m CONT gamma {TC {sign = List.rev $2; gamma = List.rev $8; m = $6; sigma = $4}}
	| CONT gamma SIGN sign OBJ m FAM sigma {TC {sign = List.rev $4; gamma = List.rev $2; m = $6; sigma = $8}}
	| CONT gamma SIGN sign FAM sigma OBJ m {TC {sign = List.rev $4; gamma = List.rev $2; m = $8; sigma = $6}}
	| OBJ m SIGN sign CONT gamma FAM sigma {TC {sign = List.rev $4; gamma = List.rev $6; m = $2; sigma = $8}}
	| OBJ m SIGN sign FAM sigma CONT gamma {TC {sign = List.rev $4; gamma = List.rev $8; m = $2; sigma = $6}}
	| FAM sigma SIGN sign CONT gamma OBJ m {TC {sign = List.rev $4; gamma = List.rev $6; m = $8; sigma = $2}}
	| FAM sigma SIGN sign OBJ m CONT gamma {TC {sign = List.rev $4; gamma = List.rev $8; m = $6; sigma = $2}}
	| CONT gamma OBJ m SIGN sign FAM sigma {TC {sign = List.rev $6; gamma = List.rev $2; m = $4; sigma = $8}}
	| CONT gamma FAM sigma SIGN sign OBJ m {TC {sign = List.rev $6; gamma = List.rev $2; m = $8; sigma = $4}}
	| OBJ m CONT gamma SIGN sign FAM sigma {TC {sign = List.rev $6; gamma = List.rev $4; m = $2; sigma = $8}}
	| OBJ m FAM sigma SIGN sign CONT gamma {TC {sign = List.rev $6; gamma = List.rev $8; m = $2; sigma = $4}}
	| FAM sigma CONT gamma SIGN sign OBJ m {TC {sign = List.rev $6; gamma = List.rev $4; m = $8; sigma = $2}}
	| FAM sigma OBJ m SIGN sign CONT gamma {TC {sign = List.rev $6; gamma = List.rev $8; m = $4; sigma = $2}}
	| CONT gamma OBJ m FAM sigma SIGN sign {TC {sign = List.rev $8; gamma = List.rev $2; m = $4; sigma = $6}}
	| CONT gamma FAM sigma OBJ m SIGN sign {TC {sign = List.rev $8; gamma = List.rev $2; m = $6; sigma = $4}}
	| OBJ m CONT gamma FAM sigma SIGN sign {TC {sign = List.rev $8; gamma = List.rev $4; m = $2; sigma = $6}}
	| OBJ m FAM sigma CONT gamma SIGN sign {TC {sign = List.rev $8; gamma = List.rev $6; m = $2; sigma = $4}}
	| FAM sigma CONT gamma OBJ m SIGN sign {TC {sign = List.rev $8; gamma = List.rev $4; m = $6; sigma = $2}}
	| FAM sigma OBJ m CONT gamma SIGN sign {TC {sign = List.rev $8; gamma = List.rev $6; m = $4; sigma = $2}}

all_kc :
	| SIGN sign CONT gamma FAM sigma {KC {sign = List.rev $2; gamma = List.rev $4; sigma = $6}}
	| SIGN sign CONT gamma FAM sigma {KC {sign = List.rev $2; gamma = List.rev $4; sigma = $6}}
	| SIGN sign CONT gamma FAM sigma {KC {sign = List.rev $2; gamma = List.rev $4; sigma = $6}}
	| SIGN sign FAM sigma CONT gamma {KC {sign = List.rev $2; gamma = List.rev $6; sigma = $4}}
	| SIGN sign FAM sigma CONT gamma {KC {sign = List.rev $2; gamma = List.rev $6; sigma = $4}}
	| SIGN sign FAM sigma CONT gamma {KC {sign = List.rev $2; gamma = List.rev $6; sigma = $4}}
	| CONT gamma SIGN sign FAM sigma {KC {sign = List.rev $4; gamma = List.rev $2; sigma = $6}}
	| CONT gamma SIGN sign FAM sigma {KC {sign = List.rev $4; gamma = List.rev $2; sigma = $6}}
	| SIGN sign CONT gamma FAM sigma {KC {sign = List.rev $2; gamma = List.rev $4; sigma = $6}}
	| SIGN sign FAM sigma CONT gamma {KC {sign = List.rev $2; gamma = List.rev $6; sigma = $4}}
	| FAM sigma SIGN sign CONT gamma {KC {sign = List.rev $4; gamma = List.rev $6; sigma = $2}}
	| FAM sigma SIGN sign CONT gamma {KC {sign = List.rev $4; gamma = List.rev $6; sigma = $2}}
	| CONT gamma SIGN sign FAM sigma {KC {sign = List.rev $4; gamma = List.rev $2; sigma = $6}}
	| CONT gamma FAM sigma SIGN sign {KC {sign = List.rev $6; gamma = List.rev $2; sigma = $4}}
	| CONT gamma SIGN sign FAM sigma {KC {sign = List.rev $4; gamma = List.rev $2; sigma = $6}}
	| FAM sigma SIGN sign CONT gamma {KC {sign = List.rev $4; gamma = List.rev $6; sigma = $2}}
	| FAM sigma CONT gamma SIGN sign {KC {sign = List.rev $6; gamma = List.rev $4; sigma = $2}}
	| FAM sigma SIGN sign CONT gamma {KC {sign = List.rev $4; gamma = List.rev $6; sigma = $2}}
	| CONT gamma FAM sigma SIGN sign {KC {sign = List.rev $6; gamma = List.rev $2; sigma = $4}}
	| CONT gamma FAM sigma SIGN sign {KC {sign = List.rev $6; gamma = List.rev $2; sigma = $4}}
	| CONT gamma FAM sigma SIGN sign {KC {sign = List.rev $6; gamma = List.rev $2; sigma = $4}}
	| FAM sigma CONT gamma SIGN sign {KC {sign = List.rev $6; gamma = List.rev $4; sigma = $2}}
	| FAM sigma CONT gamma SIGN sign {KC {sign = List.rev $6; gamma = List.rev $4; sigma = $2}}
	| FAM sigma CONT gamma SIGN sign {KC {sign = List.rev $6; gamma = List.rev $4; sigma = $2}}

all_ik :
	| SIGN sign CONT gamma KIND k {IK {sign = List.rev $2; gamma = List.rev $4; k = $6}}
	| SIGN sign CONT gamma KIND k {IK {sign = List.rev $2; gamma = List.rev $4; k = $6}}
	| SIGN sign CONT gamma KIND k {IK {sign = List.rev $2; gamma = List.rev $4; k = $6}}
	| SIGN sign KIND k CONT gamma {IK {sign = List.rev $2; gamma = List.rev $6; k = $4}}
	| SIGN sign KIND k CONT gamma {IK {sign = List.rev $2; gamma = List.rev $6; k = $4}}
	| SIGN sign KIND k CONT gamma {IK {sign = List.rev $2; gamma = List.rev $6; k = $4}}
	| CONT gamma SIGN sign KIND k {IK {sign = List.rev $4; gamma = List.rev $2; k = $6}}
	| CONT gamma SIGN sign KIND k {IK {sign = List.rev $4; gamma = List.rev $2; k = $6}}
	| SIGN sign CONT gamma KIND k {IK {sign = List.rev $2; gamma = List.rev $4; k = $6}}
	| SIGN sign KIND k CONT gamma {IK {sign = List.rev $2; gamma = List.rev $6; k = $4}}
	| KIND k SIGN sign CONT gamma {IK {sign = List.rev $4; gamma = List.rev $6; k = $2}}
	| KIND k SIGN sign CONT gamma {IK {sign = List.rev $4; gamma = List.rev $6; k = $2}}
	| CONT gamma SIGN sign KIND k {IK {sign = List.rev $4; gamma = List.rev $2; k = $6}}
	| CONT gamma KIND k SIGN sign {IK {sign = List.rev $6; gamma = List.rev $2; k = $4}}
	| CONT gamma SIGN sign KIND k {IK {sign = List.rev $4; gamma = List.rev $2; k = $6}}
	| KIND k SIGN sign CONT gamma {IK {sign = List.rev $4; gamma = List.rev $6; k = $2}}
	| KIND k CONT gamma SIGN sign {IK {sign = List.rev $6; gamma = List.rev $4; k = $2}}
	| KIND k SIGN sign CONT gamma {IK {sign = List.rev $4; gamma = List.rev $6; k = $2}}
	| CONT gamma KIND k SIGN sign {IK {sign = List.rev $6; gamma = List.rev $2; k = $4}}
	| CONT gamma KIND k SIGN sign {IK {sign = List.rev $6; gamma = List.rev $2; k = $4}}
	| CONT gamma KIND k SIGN sign {IK {sign = List.rev $6; gamma = List.rev $2; k = $4}}
	| KIND k CONT gamma SIGN sign {IK {sign = List.rev $6; gamma = List.rev $4; k = $2}}
	| KIND k CONT gamma SIGN sign {IK {sign = List.rev $6; gamma = List.rev $4; k = $2}}
	| KIND k CONT gamma SIGN sign {IK {sign = List.rev $6; gamma = List.rev $4; k = $2}}

sign :
	| ENDS {[]}
	| CONST DPOINT sigma SEP sign {(Const ($1, $3)) :: $5}
	| VAR DPOINT k SEP sign {(Const_family ($1, $3)) :: $5}

gamma :
	| ENDC {[]}
	| VAR DPOINT sigma SEP gamma {($1, $3) :: $5}

k :
	| LPAR k RPAR {$2}
	| TYPE {Type}
	| PI VAR DPOINT sigma POINT k {Pi ($2, $4, $6)}

sigma :
	| LPAR sigma RPAR {$2} 
	| VAR {Const_family ($1)}
	| PI VAR DPOINT sigma POINT sigma {Pi ($2, $4, $6)}
	| LCK VAR LPAR m COMMA sigma RPAR LBRK sigma RBRK {Lock ($2, $4, $6, $9)}
	| sigma PROD sigma {Prod ($1, $3)}
	| sigma m {App ($1, $2)}

m :
	| LPAR m RPAR {$2}
	| CONST {Const ($1)}
	| VAR {Var ($1)}
	| LAM VAR DPOINT sigma POINT m {Lam ($2, $4, $6)}
	| LCK VAR LPAR m COMMA sigma RPAR LBRK m RBRK {Lock ($2, $4, $6, $9)}
	| m m {App ($1, $2)}
	| UNLCK VAR LPAR m COMMA sigma RPAR LBRK m RBRK {Unlock ($2, $4, $6, $9)}
	| INF m COMMA m SUP {Pair ($2, $4)}
