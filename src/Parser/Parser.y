{
module Parser.Parser where -- TODO: export list

-- import Control.Monad.Except ( throwError )
-- import Control.Monad.State ( MonadState(get, put), gets )
import Control.Monad ( unless )
import Data.Either.Extra ( mapRight )
import Data.List qualified as List
import Data.Maybe ( fromMaybe )
import Data.Char ( isUpper )
import Data.Map.Strict qualified as Map

import Parser.Lexer  -- TODO: import list
import Parser.Lexer qualified as A
import Parser.Token ( Token )
import Parser.Token qualified as Token

import Syntax.Assumption ( Assumption(..) )
import Syntax.Claim ( Claim(..) )
import Syntax.Definition ( Definition(..) )
import Syntax.Judgment ( Judgment(..) )
import Syntax.Formula ( Formula(..) )
import Syntax.Justification ( Justification(..), Rule(..) )
import Syntax.Module ( Module )
import Syntax.Proof ( Proof(..) )
import Syntax.Relation ( Relation(..), Prop'Var(..) )
import Syntax.Term -- ( Term(..), Level(..), pattern Const, pattern Bound'Var )
import Syntax.Theorem ( Theorem(..) )
import Syntax.Type ( Type(..), Type'Scheme(..) )
import Syntax.Syntax ( Syntax(..), Constructor(..) )
import Syntax.Jud ( Jud(..) )
import Syntax.Case ( Case(..) )

import Syntax.Assumption qualified as S
import Syntax.Claim qualified as S
import Syntax.Claim qualified as C
import Syntax.Relation qualified as S
import Syntax.Term qualified as S
import Syntax.Formula qualified as S
import Syntax.Theorem qualified as S
import Syntax.Theorem qualified as T
import Syntax.Definition qualified as S
import Syntax.Judgment qualified as S
import Syntax.Judgment qualified as JD
import Syntax.Justification qualified as S
import Syntax.Justification qualified as J
import Syntax.Module qualified as M
import Syntax.Proof qualified as S
import Syntax.Proof qualified as P
import Syntax.Jud qualified as Jud

import Check.Substitution
import Check.Substitute

}

%name parseModule Module
%name parseTheorems Theorems
%name parseFormula Formula

%tokentype { Token }
%monad { Alex }
%lexer { lexer } { Token.EOF }

%errorhandlertype explist
%error { parseError }

%token
  IDENT           { Token.Ident $$ }

  'ᶜ'             { Token.Constant'Before }
  'module'        { Token.Module }

  ','             { Token.Comma }
  '.'             { Token.Period }
  'schema'        { Token.Schema }
  'theorem'       { Token.Theorem }
  'judgment'      { Token.Judgment }
  'syntax'        { Token.Syntax }
  'constants'     { Token.Constants }
  -- 'axioms'    { Token.Axioms }
  'axiom'         { Token.Axiom }
  'aliases'       { Token.Aliases }
  'by'            { Token.By }
  'rule'          { Token.Rule }
  'induction'     { Token.Induction }
  'on'            { Token.On }
  'for'           { Token.For }
  'all'           { Token.All }
  'some'          { Token.Some }
  'unproved'      { Token.Unproved }
  'case'          { Token.Case }
  'analysis'      { Token.Analysis }
  'object'        { Token.Object }
  'objects'       { Token.Object }
  'proposition'   { Token.Proposition }
  'propositions'  { Token.Proposition }
  ':='            { Token.Defines }
  ':'             { Token.Colon }
  '⊢'             { Token.Turnstile }
  '⊤'             { Token.Tautology }
  '⊥'             { Token.Contradiction }
  '∀'             { Token.Forall }
  '∃'             { Token.Exists }
  '¬'             { Token.Negate }
  '∧'             { Token.And }
  '∨'             { Token.Or }
  '==>'           { Token.Implication }
  '<=>'           { Token.Equivalence }
  '('             { Token.Paren'Open }
  ')'             { Token.Paren'Close }
  '['             { Token.Box'Open }
  ']'             { Token.Box'Close }
  '{'             { Token.Bracket'Open }
  '}'             { Token.Bracket'Close }

  '->'            { Token.Type'Arrow }

  '_'             { Token.Underscore }
  '='             { Token.Equal }

  '|'             { Token.Pipe }
  '---'           { Token.Dash }

  BEGIN_LAYOUT    { Token.Begin'Layout }
  END_LAYOUT      { Token.End'Layout }


-- %attributetype        { Attributes a }
-- %attribute inScope    { [(String, Level)] }
-- %attribute outScopt   { [(String, Level)] }
-- %attribute value      { a }


%right '<=>'
%right '==>'
%left '∨'
%left '∧'
%right '¬'

%name parse Module

%%

-- TODO: return Module
Module      ::  { Module }
            :   'module' ModuleName ConstantsD Aliases Axioms Syntax Judgments Theorems
                                            { M.Module{ M.name = $2
                                                      , M.constants = $3
                                                      , M.aliases = $4
                                                      , M.axioms = $5
                                                      , M.syntax = $6
                                                      , M.judgments = $7
                                                      , M.theorems = $8 } }
                                            -- { ($1, $2, $3, $4) }


ModuleName  ::  { String }
            :   IDENT                       { $1 }


ConstantsD  ::  { [(String, Type'Scheme)] }
            :   'constants' ':' Consts      {%  do
                                                { s <- alexGetUserState
                                                ; let constants = map (\ (s, _) -> s) $3
                                                ; alexSetUserState s{ A.constants = constants
                                                                    , A.typing'ctx = Map.fromList $3 }
                                                --  TODO: store the constants with their type schemata too
                                                --        so that they can be put as a starting typing context
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
                                                { s <- alexGetUserState
                                                ; let aliases' = aliases s
                                                ; alexSetUserState s{ aliases = ($1, $3) : aliases' }
                                                ; return ($1, $3) } }


Ali         ::  { String }
            :   IDENT                       {%  do
                                                { s <- alexGetUserState
                                                ; let consts = A.constants s
                                                ; let alis = aliases s
                                                ; if $1 `elem` consts
                                                  then do { report'error ("Parsing Error: Illegal alias `" ++ $1 ++ "'.\nAliases can not redefine existing constants.") }
                                                  else  case List.lookup $1 alis of
                                                        { Just _ -> do { report'error ("Parsing Error: Illegal alias `" ++ $1 ++ "'.\nAliases can not redefine existing aliases.") }
                                                        ; Nothing -> do { return $1 } } } }


Consts      ::  { [(String, Type'Scheme)] }
            :   TypeAnn                       { [ $1 ] }
            |   TypeAnn ',' Consts            { $1 : $3 }


Axioms      ::  { [(String, Formula)] }
            :   {-  empty   -}              { [] }
            |   Axs Axioms                  { $1 : $2 }


Axs         ::  { (String, Formula) }
            :   'axiom' IDENT ':' Formula   { ($2, $4) }


Syntax      ::  { [(String, Syntax)] }
            :   Syn Syntax                  { $1 : $2 }
            |   {- empty  -}                { [] }


Syn         ::  { (String, Syntax) }
            :   'syntax' PropVar Constructors
                                            { ($2, Syntax $3)  }


Constructors
            ::  { [Constructor] }
            :   '=' Constructor ConstrsAux  { $2 : $3 }
            |   {-  empty -}                { [] }


Constructor ::  { Constructor }
            :   IDENT                       {% do
                                                { s <- alexGetUserState
                                                ; alexSetUserState s{ A.constants = $1 : A.constants s }
                                                ; return $! Constructor $1 [] } }
            |   IDENT '(' Type Types ')'    {% do
                                                { s <- alexGetUserState
                                                ; alexSetUserState s{ A.constants = $1 : A.constants s }
                                                ; return $! Constructor $1 ($3 : $4) } }


--  TODO: because of the | meaning two different things, this is a bit broken
ConstrsAux  ::  { [Constructor] }
            :   BEGIN_LAYOUT Constructor ConstrsAux END_LAYOUT  { $2 : $3 }
            |   {-  empty -}                { [] }


Types       ::  { [Type] }
            :   ',' Type Types              { $2 : $3 }
            |   {-  empty -}                { [] }


Judgments   ::  { [Jud] }
            :   Jud Judgments               { $1 : $2 }
            |   {-  empty -}                { [] }


Jud         ::  { Jud }
            :   'judgment' IDENT '=' Constructor Rules
                                            { let { Constructor name types = $4 }
                                              in  Jud $2 (name, types) $5 }


Rules       ::  { [Jud.Rule] }
            :   Rule Rules                  { $1 : $2}
            |   {-  empty -}                { [] }


Rule        ::  { Jud.Rule }
            :   'rule' IDENT ':' BEGIN_LAYOUT Formulas '---' IDENT Formula END_LAYOUT
                                            {% do
                                                { unless  ($2 == $7)
                                                          (report'error ("A rule should have the same name as in declaration.\nThe rule `" ++ $2 ++ "' has also been given a name `" ++ $7 ++ "'.\nPick just one!"))
                                                ; return $! Jud.Rule $2 [] $5 $8 } }
            |   'rule' 'schema' IDENT 'for' 'all' 'object' Objects ':'
                BEGIN_LAYOUT Formulas '---' IDENT Formula END_LAYOUT
                                            {% do
                                                { unless  ($3 == $12)
                                                          (report'error ("A rule should have the same name as in declaration.\nThe rule `" ++ $3 ++ "' has also been given a name `" ++ $12 ++ "'.\nPick just one!"))
                                                ; return $! Jud.Rule $3 $7 $10 $13 } }


Objects     ::  { [(String, Type)] }
            :   TypeAnn2                    { [$1] }
            |   TypeAnn2 ',' Objects        { $1 : $3 }


TypeAnn2  ::  { (String, Type) }
          :   '(' IDENT ':' PropVar ')'     { ($2, Type'Const $4) }


Formulas    ::  { [Formula] }
            :   Formula Formulas            { $1 : $2 }
            |   {-  empty -}                { [] }


Theorems    ::  { [Theorem] }
            :   Theorem Theorems            { $1 : $2 }
            |   {-  empty   -}              { [] }


Theorem     ::  { Theorem }
            :   'theorem' IDENT ':' Assumptions '⊢' Conclusion Proof
                                            { T.Theorem { T.name = $2
                                                      , assumptions = $4
                                                      , conclusion = $6
                                                      , proof = $7 } }
            |   'theorem' IDENT ':' Formula Proof
                                            { T.Theorem { T.name = $2
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
            |   '∀' B Binders ':' QFormula      { List.foldr Forall $5 $3 }
            |   '∃' B Binders ':' QFormula      { List.foldr Exists $5 $3 }
            |   '(' Formula ')'             { $2 }
            |   '{' Formula '}'             { $2 }
            |   '[' Formula ']'             { $2 }


B           ::  { () }
            :   {-  -}                      {% do
                                                { s <- alexGetUserState
                                                ; let binders = bound s
                                                ; alexSetUserState s{ bound = [] :  binders } } }


Binders     ::  { [(String, Type'Scheme)] }
            :   {-  empty -}                { [] }
            |   TypeAnn Binders             {% do
                                                { s <- alexGetUserState
                                                ; let (b : bs) = bound s
                                                ; let (n, t) = $1
                                                ; alexSetUserState s{ bound = (n : b) : bs }
                                                ; return ($1 : $2) } }


TypeAnn   ::  { (String, Type'Scheme) }
          :   '(' IDENT ':' Type ')'      { ($2, Forall'T [] $4) }
          |   IDENT                       {% do
                                              { n <- fresh'name
                                              ; return ($1, Forall'T [n] (Type'Var n)) } }


Type      ::  { Type }
          :   PropVar                     { Type'Const $1 }
          |   Type '->' Type              { Type'Fn $1 $3 }


QFormula    ::  { Formula }
            :   Formula                     {% do
                                                { s <- alexGetUserState
                                                ; let (b : bs) = bound s
                                                ; alexSetUserState s{ bound = bs }
                                                ; return $1 } }


Relation    ::  { Relation }
            :   PropVar TermArgsM           { case $2 of
                                                    { Just terms -> Rel $1 terms
                                                    ; Nothing -> Rel $1 [] } }
            |   '_'                         {% do
                                                { name <- fresh'name
                                                ; return (Meta'Rel (Prop'Var name))  } }

            |   '_' PropVar                 { Meta'Rel (Prop'Var ('_' : $2)) }


PropVar     ::  { String }
            :   IDENT                      {% do
                                                { unless  (isUpper (head $1))
                                                          (report'error ("Parsing Error: Illegal proposition `" ++ $1 ++ "'\n" ++ "Propositions should begin with an upper case character."))
                                                ; return $1 } }


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
            --  Any ident with a ᶜ after it is a constant.
            :   IDENT 'ᶜ' TermArgsM         { App (S.C $1) (fromMaybe [] $3) }

            |   IDENT TermArgsM             {%  case $2 of
                                                { Just terms -> return $! App (S.C $1) terms
                                                ; Nothing -> do
                                                  { s <- alexGetUserState
                                                  ; let cons = A.constants s
                                                  ; let rs = A.rigids s
                                                  ; let alis = aliases s
                                                  ; let bs = bound s
                                                  ; let is'constant = $1 `elem` cons
                                                  ; let is'upper = isUpper (head $1)
                                                  ; let is'bound = List.any ($1 `elem`) bs
                                                  ; let is'rigid = List.any ($1 `elem`) rs
                                                  ; if is'bound
                                                    then return (Bound'Var $1)
                                                    else  if is'rigid
                                                          then return (Var (Rigid (R $1)))
                                                          else  if is'upper || is'constant
                                                                then return (Const $1)
                                                                else  case List.lookup $1 alis of
                                                                      { Just tm -> do { return tm }
                                                                      ; Nothing -> return $! Free'Var $1 } } } }
                                                                      -- ; Nothing -> do { report'error ("Parsing Error: Unbound variable `" ++ $1 ++ "'\n" ++ "Perhaps you forgot to define a constant or an alias?") } } } } }
                                        
            |   '(' Term ')'                { $2 }


Proof       ::  { [Judgment] }
            :   Subproof Proof              { JD.Sub'Proof $1 : $2 }
                                            -- ; $1.inScope = $$.inScope `union` $$.outScope
                                            -- ; $2.inScope = $$.inScope
                                            -- ; $$.outScope = $2.outScope }
            |   Claim Proof                 { JD.Claim $1 : $2 }
                                            -- ; $1.inScope = $$.inScope
                                            -- ; $2.inScope = $$.inScope `union` $1.outScope
                                            -- ; $$.outScope = $1.outScope `union` $2.outScope }
            |   '_' PropVar ':=' Formula Proof
                                            { (JD.Alias ('_' : $2) $4) : $5 }
            |   {- empty -}                 { [] }
                                            -- ; $$.outScope = empty }


Subproof    ::  { Proof }
            :   SubProofAux                 { Proof { P.name = Nothing
                                                    , assumption = fst $1
                                                    , derivations = snd $1 } }
            |   Name ':' SubProofAux        { Proof { P.name = $1
                                                    , assumption = fst $3
                                                    , derivations = snd $3 } }


SubProofAux ::  { (Assumption, [Judgment]) }
            :   BEGIN_LAYOUT Assumption '---' Proof END_LAYOUT
                                            {% do
                                                { s <- alexGetUserState
                                                ; let _ : rs = rigids s
                                                ; alexSetUserState s{ rigids = rs }
                                                ; return ($2, $4) }  }


Assumption  ::  { Assumption }
            :   ForAll Rigids               {% do
                                                { s <- alexGetUserState
                                                ; let rs = rigids s
                                                ; let strs = map (\ ((R n), _) -> n) $2
                                                ; alexSetUserState s{ rigids = strs : rs }
                                                ; return $! Universal $2 } }  --  TODO: all these identifiers must be recorded in the environment to be parsed as constants
            |   AssumedFormulae             {% do
                                                { s <- alexGetUserState
                                                ; let rs = rigids s
                                                ; alexSetUserState s{ rigids = [] : rs }
                                                ; return $! Formula $1 } }
            |   AssumedFormula 'for' 'some' Rigids
                                            {% do
                                                { s <- alexGetUserState
                                                ; let rs = rigids s
                                                ; let strs = map (\ ((R n), _) -> n) $4
                                                ; let subst = concatMap (\ s -> F s ==> Var (Rigid (R s))) strs
                                                ; let fm = apply subst $1
                                                ; alexSetUserState s{ rigids = strs : rs }
                                                ; return $! Existential fm $4 } }   --  TODO: all these identifiers must be recorded in the env to be parsed as constants


ForAll      ::  { () }
            : 'all'                         { () }
            | 'for' 'all'                   { () }


AssumedFormula
            ::  { (Maybe String, Formula) }
            :   Name ':' Formula            { ($1, $3) }
            |   Formula                     { (Nothing, $1) }


AssumedFormulae
            ::  { [(Maybe String, Formula)] }
            :   AssumedFormula AssumedFormulae
                                            { $1 : $2 }
            |   {- empty -}                 { [ ] }


-- Universals  ::  { [(Constant, Type)] }
--             :   IDENT                       { [ C $1 ] }
--             |   IDENT ',' Universals        { C $1 : $3 }


Rigids      ::  { [(Rigid, Type'Scheme)] }
            :   TypeAnn1                    { let { (n, t) = $1 } in [ (R n, t) ] }
            |   TypeAnn1 ',' Rigids         { let { (n, t) = $1 } in (R n, t) : $3 }


TypeAnn1  ::  { (String, Type'Scheme) }
          :   '(' IDENT ':' PropVar ')'   { ($2, Forall'T [] (Type'Const $4)) }
          |   IDENT                       {% do
                                              { n <- fresh'name
                                              ; return ($1, Forall'T [] (Type'Var n)) } }


Claim       ::  { Claim }
            :   Name ':' Formula Just       { C.Claim { C.name = $1
                                                      , formula = $3
                                                      , justification = $4 } }
            |   Formula Just                { C.Claim { C.name = Nothing
                                                      , formula = $1
                                                      , justification = $2 } }

            -- |   Formula                     {% report'error ("Formula `" ++ show $1 ++ "' is missing a justification." ) }


Name        ::  { Maybe String }
            :   IDENT                             { Just $1 }
            |   '_'                               { Nothing }


Just        ::  { Justification }
            :   'by' 'rule' RuleKind OnIdents     { Rule{ J.kind = $3, on = $4 } }
            |   'by' 'induction' 'on' Term        { Induction { on'1 = $4 } }
            |   'by' 'unproved'                   { Unproved }
            |   'by' 'axiom' IDENT                { Rule{ J.kind = Repetition, on = [$3] } }
            |   'by' 'theorem' IDENT OnIdents     { J.Theorem { J.name = $3, on = $4 } }
            |   'by' 'case' 'analysis' 'on' Term ':' Cases
                                                  { Case'Analysis { on'1 = $5, proofs = $7 } }


Cases       ::  { [Case] }
            :   Case Cases                        { $1 : $2 }
            |   {-  empty -}                      { [] }


Case        ::  { Case }
            :   'case' Pattern '->' SubProofAux   {% do
                                                    { s <- alexGetUserState
                                                    ; let (_ : rs) = rigids s
                                                    ; alexSetUserState s{ rigids = rs }
                                                    ; return $! Case $2 (Proof{ P.name = Nothing
                                                                              , assumption = fst $4
                                                                              , derivations = snd $4 }) } }


Pattern     ::  { (Constant, [Rigid]) }
            :   IDENT 'ᶜ' PatVars                 {% do
                                                      { s <- alexGetUserState
                                                      ; let rs = rigids s
                                                      ; let strs = map (\ (R s) -> s) $3
                                                      ; alexSetUserState s{ rigids = strs : rs }
                                                      ; return (C $1, $3) } }

            |   IDENT PatVars                     {%  do
                                                      { s <- alexGetUserState
                                                      ; let rs = rigids s
                                                      ; let strs = map (\ (R s) -> s) $2
                                                      ; alexSetUserState s{ rigids = strs : rs}
                                                      ; return (C $1, $2) } }
                                        
            |   '(' Pattern ')'                   { $2 }


PatVars     ::  { [Rigid] }
            :   '(' PatVs ')'                     { $2 }
            |   {-  empty -}                      { [] }


PatVs       ::  { [Rigid] }
            :   PatVss                            { $1 }
            |   {-  empty -}                      { [] }


PatVss      ::  { [Rigid] }
            :   PatV ',' PatVss                   { $1 : $3 }
            |   PatV                              { [$1] }


PatV        ::  { Rigid }
            :   IDENT                             { R $1 }


RuleKind    ::  { Rule }
            :   IDENT                             { str'to'rule'kind $1 }


OnIdents    ::  { [String] }
            :   'on' Idents                       { $2 }
            |   {- empty -}                       { [] }


Idents      ::  { [String] }
            :   IDENT                             { [ $1 ] }
            |   IDENT ',' IdentsAux               { $1 : $3 }

IdentsAux   ::  { [String] }
            :   IDENT ',' IdentsAux               { $1 : $3 }
            |   IDENT                             { [ $1 ] }




{

-- run'parser :: Alex a -> String -> Either (String, Int) (a, AlexState)
-- run'parser parser source = runExcept $! runStateT parser (initial'state source)


lex :: String -> Either (String, [Token]) [Token]
lex source = run [] (run'alex alexMonadScan st)
-- (runExcept $! runStateT read'token (initial'state source))

  where run :: [Token] -> Either String (AlexState, Token) -> Either (String, [Token]) [Token]
        run tokens (Left msg) = Left (msg, tokens)
        run tokens (Right (s, Token.EOF)) = Right (tokens ++ [Token.EOF])
        run tokens (Right (s, t)) = run (tokens ++ [t]) (run'alex alexMonadScan s) -- (runExcept $! runStateT read'token s)

        st = AlexState{ alex_pos   = AlexPn 0 0 0
                      , alex_inp   = source
                      , alex_chr   = '\n'
                      , alex_bytes = []
                      , alex_ust   = alexInitUserState
                      , alex_scd   = 0 }

        run'alex :: Alex a -> AlexState -> Either String (AlexState, a)
        run'alex (Alex f) st = case f st of
            Left msg     -> Left msg
            Right (s, a) -> Right (s, a)


parse'module :: String -> Either String Module
parse'module source = {- mapRight fst $! -} runAlex source parseModule -- run'parser parseModule source


-- parse'theorems :: String -> Either (String, Int) [Theorem]
-- parse'theorems source = mapRight fst $! run'parser parseTheorems source


-- parse'formula :: String -> Either (String, Int) Formula
-- parse'formula source = mapRight fst $! run'parser parseFormula source


lexer cont = alexMonadScan >>= cont


parseError _ = do
  (_, last'char, _, _) <- alexGetInput
  report'error ("Parse error near character `" ++ [last'char] ++ "'.")


report'error :: String -> Alex a
report'error msg = do
  col'no <- alexGetCol
  l'no <- alexGetLine

  alexError (show l'no ++ ":" ++ show col'no ++ "\n" ++ msg)
  


str'to'rule'kind :: String -> Rule
str'to'rule'kind "==>-intro" = Impl'Intro
str'to'rule'kind "==>-elim" = Impl'Elim
str'to'rule'kind "∧-intro" = Conj'Intro
str'to'rule'kind "∧-elim" = Conj'Elim
str'to'rule'kind "∨-intro" = Disj'Intro
str'to'rule'kind "∨-elim" = Disj'Elim
str'to'rule'kind "¬-elim" = Neg'Elim
str'to'rule'kind "<==>-intro" = Equiv'Intro
str'to'rule'kind "<==>-elim" = Equiv'Elim
str'to'rule'kind "⊤-intro" = True'Intro
str'to'rule'kind "proof-by-contradiction" = Proof'By'Contradiction
str'to'rule'kind "⊥-elim" = Contra'Elim
str'to'rule'kind "∀-intro" = Forall'Intro
str'to'rule'kind "∀-elim" = Forall'Elim
str'to'rule'kind "∃-intro" = Exists'Introduction
str'to'rule'kind "∃-elim" = Exists'Elimination
str'to'rule'kind "repetition" = Repetition
str'to'rule'kind str = Custom str


}
