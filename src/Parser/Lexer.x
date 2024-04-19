{
module Parser.Lexer where -- TODO: export list


import Control.Monad.Except ( Except, runExcept, throwError )
import Control.Monad.State ( MonadState(get, put), gets, StateT( runStateT ) )

import Data.Word ( Word8 )
import Data.Char ( ord )
import Data.List ( uncons )

import Parser.Token ( Token )
import Parser.Token qualified as Token

import Syntax.Term ( Term )


-- import Debug.Trace ( trace, traceM )

}

%wrapper "monadUserState"


$upper                = [A-Z]

$lower                = [a-z]

$digit                = [0-9]

$character            = [!-\' \*-\+ \--Z \\ \^-z \| \~ \¡-\ʯ \Ͱ-\⏿#\ᶜ \⟰-\⟿ \⤀-\⫿ \Ⱡ-\⳿ \꜠-\ꟿ]

-- $special              = [\∀ \∃ \= \> \< \¬ \∧ \∨ \⊥ \⊤ \~ \( \) \{ \} \[ \] \' \- \_ \" \| ]

@ident                = [$lower $upper $digit $character]+

@line                 = \|[\-]+

$space                = [\ \t\f\v]

$newline              = [\n]

$any                  = [\x00-\x10ffff]


detour :-


$space+                 ;

"--".*                  ;

-- "{-"$any*"-}"           ;


<0> {

  @line                   { emit Token.Dash }
  "module"                { emit Token.Module }

  "ᶜ"                     { emit Token.Constant'Before }

  "("                     { emit Token.Paren'Open }
  ")"                     { emit Token.Paren'Close }
  "["                     { emit Token.Box'Open }
  "]"                     { emit Token.Box'Close }
  "{"                     { emit Token.Bracket'Open }
  "}"                     { emit Token.Bracket'Close }

  -- keywords
  ","                     { emit Token.Comma }
  -- "."                     { emit Token.Period }
  "schema"                { emit Token.Schema }
  "judgment"              { emit Token.Judgment }
  "syntax"                { emit Token.Syntax }
  "theorem"               { emit Token.Theorem }
  "constants"             { emit Token.Constants }
  -- "axioms"                { emit Token.Axioms }
  "axiom"                 { emit Token.Axiom }
  "aliases"               { emit Token.Aliases }
  ":"                     { emit Token.Colon }
  "⊢"                     { emit Token.Turnstile }
  "by"                    { emit Token.By }
  "rule"                  { emit Token.Rule }
  "induction"             { emit Token.Induction }
  "unproved"              { emit Token.Unproved }
  "on"                    { emit Token.On }
  "for"                   { emit Token.For }
  "all"                   { emit Token.All }
  "any"                   { emit Token.All }
  "some"                  { emit Token.Some }
  "object"                { emit Token.Object }
  "objects"               { emit Token.Object }
  "proposition"           { emit Token.Proposition }
  "propositions"          { emit Token.Proposition }

  "="                     { emit Token.Equal }

  -- logical connectives
  "⊤"                     { emit Token.Tautology }
  "TRUE"                  { emit Token.Tautology }
  "True"                  { emit Token.Tautology }
  "Tautology"             { emit Token.Tautology }
  "TAUTOLOGY"             { emit Token.Tautology }


  "⊥"                     { emit Token.Contradiction }
  "FALSE"                 { emit Token.Contradiction }
  "FALSE"                 { emit Token.Contradiction }
  "CONTRADICTION"         { emit Token.Contradiction }
  "Contradiction"         { emit Token.Contradiction }

  "∀"                     { emit Token.Forall }
  "forall"                { emit Token.Forall }

  "∃"                     { emit Token.Exists }
  "exists"                { emit Token.Exists }

  "¬"                     { emit Token.Negate }
  "NOT"                   { emit Token.Negate }

  "∧"                     { emit Token.And }
  "&&"                    { emit Token.And }
  "&"                     { emit Token.And }
  "AND"                   { emit Token.And }

  "∨"                     { emit Token.Or }
  "OR"                    { emit Token.Or }

  "=>"                    { emit Token.Implication }
  "==>"                   { emit Token.Implication }
  "⟹"                     { emit Token.Implication }

  "<=>"                   { emit Token.Equivalence }
  "<==>"                  { emit Token.Equivalence }
  "⟺"                     { emit Token.Equivalence }

  "_"                     { emit Token.Underscore }

  "|"                     { pipe'line }


  @ident                  { emit' Token.Ident }

  -- @lowerident             { emit' Token.Lower'Var }

  -- @upperident             { emit' Token.Upper'Var }

  -- @number                 { emit Token.Number }

  $newline                { \ _ _ -> {- traceM "newline at <0>, going <behind>" >> -} alexSetStartCode behind >> alexMonadScan }

}


<behind> {

  $newline              { end'layout }

  @line                 { \ ai l -> alexSetStartCode 0 >> emit Token.Dash ai l }

  "|"                   { pipe'line }
  
  ()                    { end'layout }

}


<eof> ()                { do'EOF }

{

end'layout :: AlexInput -> Int -> Alex Token
end'layout (AlexPn _ line col, _, _, str) len = do
  s@AlexUserState{ layouts } <- alexGetUserState

  -- traceM ("trace [end'layout] line " ++ show line ++ " column " ++ show col ++ " layouts " ++ show layouts)

  --  TODO: all of this is wrong
  --        I can't just pop all of the layouts but only emit one token!!!
  
  --        I think I should do this:
  --          if I should pop a layout
  --          I pop it
  --          I stay at <behind>
  --          I return one end token
  --          I continue scanning
  --          that should lead to this function getting called again
  --          repeating until I can't and shouldn't pop
  --          then I switch to <0>

  case layouts of
    [] -> do
      alexSetStartCode 0
      alexMonadScan

    (l : ls) -> do
      -- alexSetStartCode 0
      if col <= l
      then do
        alexSetUserState s{ layouts = ls }
        return Token.End'Layout
      else do
        --  This doesn't make sense. I do nothing.
        --  Maybe I should raise an error or something.
        -- sc <- alexGetStartCode
        -- alexError ("unthinkable  I am on line " ++ show line ++ " column " ++ show col ++ " the start code is " ++ show sc ++ "  layouts are " ++ show layouts ++  " and the token should be " ++ take len str)
        alexSetStartCode 0
        alexMonadScan



popAllAfter :: Int -> Alex ()
popAllAfter col = do
  s@AlexUserState{ layouts } <- alexGetUserState

  case layouts of
    [] -> do
      return ()

    (l : ls) -> do
      if col < l
      then do
        alexSetUserState s{ layouts = ls }
        popAllAfter col
      else return ()


emit :: Token -> AlexInput -> Int -> Alex Token
emit t (AlexPn _ line col, _, _, _) _ = do
  s@AlexUserState{ layouts } <- alexGetUserState
  sc <- alexGetStartCode
  -- traceM ("trace [emit] line " ++ show line ++ " column " ++ show col ++ " layouts " ++ show layouts ++ " start code " ++ show sc ++ "  | start code for behind is " ++ show behind)

  return t


emit' :: (String -> Token) -> AlexInput -> Int -> Alex Token
emit' mk't (AlexPn _ line col, ch, bytes, input) len  = do
  s@AlexUserState{ layouts } <- alexGetUserState
  sc <- alexGetStartCode
  -- traceM ("trace [emit'] line " ++ show line ++ " column " ++ show col ++ " layouts " ++ show layouts ++ " start code " ++ show sc ++ "  | start code for behind is " ++ show behind)

  return $! mk't (take len input)


alexEOF = handle'EOF


data AlexUserState = AlexUserState{ layouts     :: ![Int]
                                  , constants   :: ![String]
                                  , bound       :: ![[String]]
                                  , consts      :: ![[String]]
                                  , aliases     :: ![(String, Term)]
                                  , counter     :: !Int }


alexInitUserState :: AlexUserState
alexInitUserState = AlexUserState { layouts           = []
                                  , constants         = []
                                  , bound             = []
                                  , consts            = []
                                  , aliases           = []
                                  , counter           = 0 }


fresh'name :: Alex String
fresh'name = do
  us <- alexGetUserState
  let cntr = counter us
  alexSetUserState us{ counter = cntr + 1 }
  return ('_' : show cntr ++ "?")


pipe'line :: AlexInput -> Int -> Alex Token
pipe'line (AlexPn _ line col, _, _, _) _ = do
  s <- alexGetUserState
  let ls = layouts s

  sc <- alexGetStartCode
  
  -- traceM ("trace [pipe'line] line " ++ show line ++ " column " ++ show col ++ " layouts " ++ show ls ++ " sc " ++ show sc)

  case ls of
    [] -> do
      --  No layout seen yet. Acting as if the current position is larger than the current layout.
      -- traceM ("line " ++ show line ++ " column " ++ show col ++ " layouts " ++ show ls ++ " sc " ++ show sc)
      -- traceM ("trace [pipe'line #0] line " ++ show line ++ " column " ++ show col ++ " layouts " ++ show ls ++ " sc " ++ show sc)
      alexSetUserState s{ layouts = col : ls }
      return Token.Begin'Layout

    (p : _) -> do
      if col == p
      then do
        -- traceM ("trace [pipe'line #1] line " ++ show line ++ " column " ++ show col ++ " layouts " ++ show ls ++ " sc " ++ show sc)
        alexSetStartCode 0
        alexMonadScan
      else  if col > p
            then do
              -- traceM ("trace [pipe'line #2] line " ++ show line ++ " column " ++ show col ++ " layouts " ++ show ls ++ " sc " ++ show sc)
              alexSetUserState s{ layouts = col : ls }
              return Token.Begin'Layout
            else do
              -- traceM ("trace [pipe'line #3] line " ++ show line ++ " column " ++ show col ++ " layouts " ++ show ls ++ " sc " ++ show sc)
              -- alexSetStartCode behind
              alexMonadScan


handle'EOF :: Alex Token
handle'EOF = do
  s <- alexGetUserState
  let ls = layouts s
  if not (null ls)
  then do
    alexSetStartCode eof
    alexMonadScan
  else do
    return Token.EOF


do'EOF :: AlexInput -> Int -> Alex Token
do'EOF _ _ = do
  --  So there's nothing on the input but we might still have some layouts open.
  s <- alexGetUserState
  let ls = layouts s

  case ls of
    [] -> do
      --  No layout open. We can emit EOF.
      return Token.EOF

    (p : ps) -> do
      --  We close this one and keep going.
      alexSetUserState s{ layouts = ps }
      return Token.End'Layout


alexGetCol :: Alex Int
alexGetCol = do
  ((AlexPn _ _ c), _, _, _) <- alexGetInput
  return c


alexGetLine :: Alex Int
alexGetLine = do
  ((AlexPn _ l _), _, _, _) <- alexGetInput
  return l


}