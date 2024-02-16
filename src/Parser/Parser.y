{
module Parser.Parser where -- TODO: export list

import Control.Monad.Except ( throwError )
import Control.Monad.State ( MonadState(get, put), gets )
import Data.Either.Extra ( mapRight )
import Data.List qualified as List
import Data.Maybe ( fromMaybe )

import Lexer  -- TODO: import list
import Token ( Token )
import Token qualified as Token

import Syntax.Assumption ( Assumption(..) )
import Syntax.Definition ( Definition(..) )
import Syntax.Derivation ( Derivation(..) )
import Syntax.Formula ( Formula(..) )
import Syntax.Justification ( Justification(..) )
import Syntax.Module ( Module(..) )
import Syntax.Relation ( Relation(..) )
import Syntax.Term ( Term(..) )
import Syntax.Theorem ( Theorem(..) )

import Syntax.Assumption qualified as S
import Syntax.Relation qualified as S
import Syntax.Term qualified as S
import Syntax.Formula qualified as S
import Syntax.Theorem qualified as S
import Syntax.Definition qualified as S
import Syntax.Derivation qualified as S
import Syntax.Justification qualified as S
import Syntax.Module qualified as S

}

%name parseModule Module
%name parseTheorems Theorems
%name parseFormula Formula

%tokentype { Token }
%monad { Lexer }
%lexer { lexer } { Token.EOF }

%errorhandlertype explist
%error { parseError }

%token
  UPPER       { Token.Upper'Var $$ }

  LOWER       { Token.Lower'Var $$ }

  NUMBER      { Token.Number $$ }

  'ᶜ'         { Token.Constant'Before }

  ','         { Token.Comma }
  '.'         { Token.Period }
  'theorem'   { Token.Theorem }
  'constants' { Token.Constants }
  'axioms'    { Token.Axioms }
  'aliases'   { Token.Aliases }
  'by'        { Token.By }
  'rule'      { Token.Rule }
  'induction' { Token.Induction }
  'on'        { Token.On }
  'all'       { Token.All }
  'unproved'  { Token.Unproved }
  ':'         { Token.Colon }
  '⊢'         { Token.Turnstile }
  '⊤'         { Token.Tautology }
  '⊥'         { Token.Contradiction }
  '∀'         { Token.Forall }
  '∃'         { Token.Exists }
  '¬'         { Token.Negate }
  '∧'         { Token.And }
  '∨'         { Token.Or }
  '==>'       { Token.Implication }
  '<=>'       { Token.Equivalence }
  '('         { Token.Paren'Open }
  ')'         { Token.Paren'Close }
  '['         { Token.Box'Open }
  ']'         { Token.Box'Close }
  '{'         { Token.Bracket'Open }
  '}'         { Token.Bracket'Close }

  '_'         { Token.Underscore }
  '='         { Token.Equal }

  '|'         { Token.Pipe }
  '---'       { Token.Dash }

  BEGIN_LAYOUT  { Token.Begin'Layout }
  END_LAYOUT    { Token.End'Layout }



%right '<=>'
%right '==>'
%left '∨'
%left '∧'
%right '¬'

%%

Module      ::  { ([String], [(String, Term)], [Formula], [Theorem]) }
            :   Constants Aliases Axioms Theorems
                                            { ($1, $2, $3, $4) }


Constants   ::  { [String] }
            :   'constants' ':' Consts      {%  do
                                                { s <- get
                                                ; put s{ constants = $3 }
                                                ; return $3 } }
            |   {-  empty   -}              { [] }


Aliases     ::  { [(String, Term)] }
            :   'aliases' ':' Alis          { $3 }
            |   {- empty -}                 { [] }


Alis        ::  { [(String, Term)] }
            :   Alias                       { [$1] }
            |   Alias ',' Alis              { $1 : $3 }


Alias       ::  { (String, Term) }
            :   Ali '=' Term                {%  do
                                                { s <- get
                                                ; let aliases' = aliases s
                                                ; put s{ aliases = ($1, $3) : aliases' }
                                                ; return ($1, $3) } }


Ali         ::  { String }
            :   Constant                    {%  do
                                                { s <- get
                                                ; let consts = constants s
                                                ; let alis = aliases s
                                                ; col'now <- gets (ai'col'no . lexer'input)
                                                ; l'no <- gets (ai'line'no . lexer'input)
                                                ; let col'no = col'now - (List.length $1)
                                                ; if $1 `elem` consts
                                                  then do { throwError ("Parsing Error: Illegal alias `" ++ $1 ++ "' on line " ++ show l'no ++ " column " ++ show col'no ++ ".\nAliases can not redefine existing constants.", col'no) }
                                                  else  case List.lookup $1 alis of
                                                        { Just _ -> do { throwError ("Parsing Error: Illegal alias `" ++ $1 ++ "' on line " ++ show l'no ++ " column " ++ show col'no ++ ".\nAliases can not redefine existing aliases.", col'no) }
                                                        ; Nothing -> do { return $1 } } } }


Consts      ::  { [String] }
            :   Constant                    { [ $1 ] }
            |   Constant ',' Consts         { $1 : $3 }


Constant    ::  { String }
            :   LOWER                       { $1 }
            |   UPPER                       { $1 }
            |   NUMBER                      { $1 }


Axioms      ::  { [Formula] }
            :   'axioms' ':' Axs            { $3 }
            |   {-  empty   -}              { [] }


Axs         ::  { [Formula] }
            :   Formula                     { [ $1 ] }
            |   Formula ',' Axs             { $1 : $3 }


Theorems    ::  { [Theorem] }
            :   Theorem Theorems            { $1 : $2 }
            |   {-  empty   -}              { [] }


Theorem     ::  { Theorem }
            :   'theorem' LOWER ':' Assumptions '⊢' Conclusion Proof
                                            { Theorem { name = $2
                                                      , assumptions = $4
                                                      , conclusion = $6
                                                      , proof = $7 } }
            |   'theorem' LOWER ':' Formula Proof
                                            { Theorem { name = $2
                                                      , assumptions = []
                                                      , conclusion = $4
                                                      , proof = $5 } }


Assumptions ::  { [Formula] }
            :   Formula AssumpsRest         { $1 : $2 }
            |   {-  empty   -}              { [] }

AssumpsRest ::  { [Formula] }
            :   ',' Formula AssumpsRest     { $2 : $3 }
            |   {-  empty   -}              { [] }


Conclusion  ::  { Formula }
            :   Formula                     { $1 }


Formula     ::  { Formula }
            :   '⊤'                         { S.True }
            |   '⊥'                         { S.False }
            |   Relation                    { Atom $1 }
            |   '¬' Formula                 { Not $2 }
            |   Formula '∧' Formula         { $1 `And` $3 }
            |   Formula '∨' Formula         { $1 `Or` $3 }
            |   Formula '==>' Formula       { $1 `Impl` $3 }
            |   Formula '<=>' Formula       { $1 `Eq` $3 }
            |   '∀' Binders QFormula        { List.foldl' (flip Forall) $3 (List.reverse $2) }  --  NOTE: The Binders will never return an empty list, so don't worry.
            |   '∃' Binders QFormula        { List.foldl' (flip Exists) $3 (List.reverse $2) }  --  NOTE: The Binders will never return an empty list, so don't worry.
            |   '(' Formula ')'             { $2 }
            |   '{' Formula '}'             { $2 }
            |   '[' Formula ']'             { $2 }


Binders     ::  { [String] }
            :   LOWER                       {% do
                                                { s <- get
                                                ; let binders = scope s
                                                ; put s{ scope = $1 : binders }
                                                ; return [ $1 ] } }
            |   LOWER Binders               {% do
                                                { s <- get
                                                ; let binders = scope s
                                                ; put s{ scope = $1 : binders }
                                                ; return ($1 : $2) } }


QFormula    ::  { Formula }
            :   Formula                     {% do
                                                { s <- get
                                                ; let (binder : binders) = scope s
                                                ; put s{ scope = binders }
                                                ; return $1 } }


Relation    ::  { Rel }
            :   UPPER TermArgsM             { case $2 of
                                              { Just terms -> Rel $1 terms
                                              ; Nothing -> Rel $1 [] } }


TermArgsM   ::  { Maybe [Term] }
            :   '(' TArgsSep ')'            { Just $2 }
            |   '[' TArgsSep ']'            { Just $2 }
            |   '{' TArgsSep '}'            { Just $2 }
            |   {- empty  -}                { Nothing }


TArgsSep    ::  { [Term] }
            :   Term                        { [ $1 ] }
            |   Term ',' TArgsSep           { $1 : $3 }
            |   {-  empty   -}              { [] }


Term        ::  { Term }
            :   NUMBER                      {%  do
                                                { consts <- gets constants
                                                ; alis <- gets aliases
                                                ; col'now <- gets (ai'col'no . lexer'input)
                                                ; l'no <- gets (ai'line'no . lexer'input)
                                                ; let col'no = col'now - List.length $1
                                                ; if $1 `elem` consts
                                                  then return (Fn $1 [])
                                                  else  case List.lookup $1 alis of
                                                        { Just tm -> do { return tm }
                                                        ; Nothing -> do { throwError ("Parsing Error: Unknown numeric constant `" ++ $1 ++ "' on line " ++ show l'no ++ " column " ++ show col'no ++ ".", col'no) } } } }
            |   NUMBER 'ᶜ'                  { Fn $1 [] }
            |   LOWER TermArgsM             {%  case $2 of
                                                { Just terms -> return $! Fn $1 terms
                                                ; Nothing -> do
                                                  { consts <- gets constants
                                                  ; alis <- gets aliases
                                                  ; binders <- gets scope
                                                  ; col'now <- gets (ai'col'no . lexer'input)
                                                  ; l'no <- gets (ai'line'no . lexer'input)
                                                  ; let col'no = col'now - List.length $1
                                                  ; let is'constant = $1 `elem` consts
                                                  ; let is'bound = $1 `elem` binders
                                                  ; if is'bound
                                                    then return (Var $1)
                                                    else  if is'constant
                                                          then return (Fn $1 [])
                                                          else  case List.lookup $1 alis of
                                                                { Just tm -> do { return tm }
                                                                ; Nothing -> do { throwError ("Parsing Error: Unbound variable `" ++ $1 ++ "' on line " ++ show l'no ++ " column " ++ show col'no ++ ".", col'no) } } } } }

            |   LOWER 'ᶜ' TermArgsM         { Fn $1 (fromMaybe [] $3) }
            |   UPPER TermArgsM             {%  case $2 of
                                                { Just terms -> return $! Fn $1 terms
                                                ; Nothing -> do
                                                  { consts <- gets constants
                                                  ; alis <- gets aliases
                                                  ; col'now <- gets (ai'col'no . lexer'input)
                                                  ; l'no <- gets (ai'line'no . lexer'input)
                                                  ; let col'no = col'now - List.length $1
                                                  ; if $1 `elem` consts
                                                    then do { return (Fn $1 []) }
                                                    else  case List.lookup $1 alis of
                                                          { Just tm -> do { return tm }
                                                          ; Nothing -> do { throwError ("Parsing Error: Unknown constant or alias `" ++ $1 ++ "' on line " ++ show l'no ++ " column " ++ show col'no ++ ".", col'no) } } } } }
                                                    
            |   UPPER 'ᶜ' TermArgsM         { Fn $1 (fromMaybe [] $3) }
            |   '(' Term ')'                { $2 }


Proof       ::  { [Derivation] }
            :   Subproof Proof              { $1 : $2 }
            |   Claim Proof                 { $1 : $2 }
            |   {- empty -}                 { [] }


Subproof    ::  { Proof }
            :   SubProofAux                 { Proof { name = Nothing
                                                    , assumptions = fst $1
                                                    , derivations = snd $1 } }
            |   '_' ':' SubProofAux         { Proof { name = Nothing
                                                    , assumptions = fst $3
                                                    , derivations = snd $3 } }
            |   LOWER ':' SubProofAux       { Proof { name = Just $1
                                                    , assumptions = fst $3
                                                    , derivations = snd $3 } }

SubProofAux ::  { (Assumption, [Derivation]) }
            :   BEGIN_LAYOUT Assumption '---' Proof END_LAYOUT
                                            { ($2, $4) }


Assumption  ::  { Assumption }
            :   'all' Universals            { Universal $2 }
            |   AssumedFormulae             { Formula $1 }


AssumedFormulae
            ::  { [(Maybe String, Formula)] }
            :   '_' ':' Formula             { (Nothing, $3) }
            |   Formula                     { (Nothing, $1) }
            |   LOWER ':' Formula           { (Just $1, $3) }


Universals  ::  { [String] }
            :   LOWER                       { [ $1 ] }
            |   LOWER ',' Universals        { $1 : $3 }


-- Claims      ::  { [ Claim ] }
--             :   Claim Claims                { $1 : $2 }
--             |   {- empty -}                 { [] }


Claim       ::  { Claim }
            :   Name ':' Formula Just       { Claim { name = Just $1
                                                    , formula = $3
                                                    , justification = $4 } }
            |   Formula Just                { Claim { name = Nothing
                                                    , formula = $1
                                                    , justification = $2 } }


name        ::  { Maybe String }
            :   LOWER                             { Just $1 }
            |   '_'                               { Nothing }


Just        ::  { Justification }
            :   'by' 'rule' LOWER 'on' Terms      { Rule{ name = $3, on = $5 } } 
            -- |   'by' LOWER 'on' Terms             {  }  -- which one would it be? rule or theorem? or should I look it up and figure it out?
            |   'by' 'induction' 'on' Terms       { Induction { on = $4 } }
            |   'by' 'unproved'                   { Unproved }
            |   'by' 'theorem' LOWER 'on' Terms   { Theorem { name = $3, on = $5 } }


Terms       ::  { [Term] }
            :   Term                        { [ $1 ] }
            |   Term ',' TermsAux           { $1 : $3 }

TermsAux    ::  { [Term] }
            :   Term ',' TermsAux           { $1 : $3 }
            |   Term                        { [ $1 ] }





{

parse'module :: String -> Either (String, Int) ([String], [(String, Term)], [Formula], [Theorem])
parse'module source = mapRight fst $! eval'parser parseModule source

parse'theorems :: String -> Either (String, Int)  [Theorem]
parse'theorems source = mapRight fst $! eval'parser parseTheorems source


parse'formula :: String -> Either (String, Int) Formula
parse'formula source = mapRight fst $! eval'parser parseFormula source


parseError _ = do
  col'no <- gets (ai'col'no . lexer'input)
  l'no <- gets (ai'line'no . lexer'input)
  last'char <- gets (ai'last'char . lexer'input)
  state <- get
  throwError ("Parse error near character `" ++ [last'char] ++ "' on line " ++ show l'no ++ ", column " ++ show col'no ++ ".", col'no)
}
