{
module Parser.Lexer where -- TODO: export list


import Control.Monad.Except ( Except, runExcept, throwError )
import Control.Monad.State ( MonadState(get, put), gets, StateT( runStateT ) )

import Data.Word ( Word8 )
import Data.Char ( ord )
import Data.List ( uncons )

import Parser.Token ( Token )


}

%encoding "iso-8859-1"


$upper                = [A-Z]

$lower                = [a-z]

$digit                = [0-9]

@lowerident           = [$lower $digit] [$lower \- \_ $digit \']*

@upperident           = $upper [$lower $upper \- \_ $digit \']*

@number               = [$digit]+

$space                = [\ \t\f\v\n]


detour :-

$space+                 ;

"%".*\n                 ;

"ᶜ"                     { \_ -> token Token.Constant'Before }

"("                     { \_ -> token Token.Paren'Open }
")"                     { \_ -> token Token.Paren'Close }
"["                     { \_ -> token Token.Box'Open }
"]"                     { \_ -> token Token.Box'Close }
"{"                     { \_ -> token Token.Bracket'Open }
"}"                     { \_ -> token Token.Bracket'Close }

-- keywords
","                     { \_ -> token Token.Comma }
"."                     { \_ -> token Token.Period }
"theorem"               { \_ -> token Token.Theorem }
"constants"             { \_ -> token Token.Constants }
"axioms"                { \_ -> token Token.Axioms }
"aliases"               { \_ -> token Token.Aliases }
":"                     { \_ -> token Token.Colon }
"⊢"                     { \_ -> token Token.Turnstile }
"by"                    { \_ -> token Token.By }
"rule"                  { \_ -> token Token.Rule }
"induction"             { \_ -> token Token.Induction }
"unproved"              { \_ -> token Token.Unproved }
"on"                    { \_ -> token Token.On }
"all"                   { \_ -> token Token.All }

"="                     { \_ -> token Token.Equal }

-- logical connectives
"⊤"                     { \_ -> token Token.Tautology }
"TRUE"                  { \_ -> token Token.Tautology }
"True"                  { \_ -> token Token.Tautology }
"Tautology"             { \_ -> token Token.Tautology }
"TAUTOLOGY"             { \_ -> token Token.Tautology }


"⊥"                     { \_ -> token Token.Contradiction }
"FALSE"                 { \_ -> token Token.Contradiction }
"FALSE"                 { \_ -> token Token.Contradiction }
"CONTRADICTION"         { \_ -> token Token.Contradiction }
"Contradiction"         { \_ -> token Token.Contradiction }

"∀"                     { \_ -> token Token.Forall }
"forall"                { \_ -> token Token.Forall }

"∃"                     { \_ -> token Token.Exists }
"exists"                { \_ -> token Token.Exists }

"¬"                     { \_ -> token Token.Negate }
"NOT"                   { \_ -> token Token.Negate }

"∧"                     { \_ -> token Token.And }
"&&"                    { \_ -> token Token.And }
"&"                     { \_ -> token Token.And }
"AND"                   { \_ -> token Token.And }

"∨"                     { \_ -> token Token.Or }
"||"                    { \_ -> token Token.Or }
"|"                     { \_ -> token Token.Or }
"OR"                    { \_ -> token Token.Or }

"=>"                    { \_ -> token Token.Implication }
"==>"                   { \_ -> token Token.Implication }
"⟹"                     { \_ -> token Token.Implication }

"<=>"                   { \_ -> token Token.Equivalence }
"<==>"                  { \_ -> token Token.Equivalence }
"⟺"                     { \_ -> token Token.Equivalence }



@lowerident             { emit Token.Lower'Var }

@upperident             { emit Token.Upper'Var }

@number                 { emit Token.Number }
