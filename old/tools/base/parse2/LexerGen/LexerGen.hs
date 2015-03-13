module LexerGen(lexerGen,OutputFun(..)) where

import RegExp
import FSM
import FSMOpt
import DFA(showDFA,renumberStates)
import DetMachine
import DetMachineToHaskell2
import PPrint(pprint)
import List(sort)
import HaskellChars(HaskellChar)

{-+
The lexer generator takes the name of the module to generate, the
name of the lexer function to export from that module and the regular
expression that defines the lexical syntax. It outputs the generated Haskell
module on the standard output.
<p>
<code>lexerGen</code> also consults the command line arguments. If
the word nocc is present, it does not use character classes to reduce
the size of the code.
-}
lexerGen :: (Ord o,Show o,OutputFun o) =>
            String -> String -> Transducer HaskellChar o -> [String] -> String
lexerGen moduleName functionName program args =
  if "nfa" `elem` args
  then show m
  else if "nocc" `elem` args
       then outputDetm Nothing m
       else outputWithCharClasses m
  where
    m@(n,nfa) = rmeqstate (compileRegExp program)

    outputWithCharClasses (n,nfa) =
        outputDetm (Just ccs) (n,renumberEdges ccs nfa)
      where
        charclasses = sort $ tokenclasses nfa
	ccs = [(c,n)|(n,(cs,_))<-zip [(1::Int)..] charclasses,c<-cs]

    outputDetm optccs nfa =
        if "dfa" `elem` args
	then showDFA dfa
	else "\n-- Automatically generated code for a DFA follows:\n" ++
	     pprint haskellCode
      where
	haskellCode =
          dfaToHaskell optccs moduleName ["Char","HsLexUtils"] functionName dfa
        dfa = renumberStates (deterministicMachine nfa)
