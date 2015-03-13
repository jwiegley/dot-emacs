module LexerGen2(lexerGen,OutputFun(..)) where

import RegExp(Trans(..),Transducer)
import DFA(DFA(..),renumberEdges,tokenClasses,showDFA)
import Minimalize
import CompileRegExp(compile)
import DetMachineToHaskell2(dfaToHaskell,OutputFun(..))
import PPrint(pprint)
import qualified OrdMap as OM(fromList)
import List(sort)
import HaskellChars(HaskellChar)

{-+
The lexer generator takes the name of the module to generate, the
name of the lexer function to export from that module and the regular
expression that defines the lexical syntax. It returns the generated Haskell
module as a string.
<p>
<code>lexerGen</code> also consults the command line arguments. If
the word nocc is present, it does not use character classes to reduce
the size of the code.
-}
lexerGen :: (Ord o,Show o,OutputFun o) =>
            String -> String -> Transducer HaskellChar o -> [String] -> String
lexerGen moduleName functionName program args =
    outputDFA (dfa2old (compile program))
  where
    outDFA = "dfa"  `elem`    args -- output the DFA or generate Haskell?
    useCC  = "nocc" `notElem` args -- use character classes?

    outputDFA = if useCC then outputWithCharClasses else outputDetm Nothing

    outputWithCharClasses (n,dfa) =
        outputDetm (Just ccs) (n,renumberEdges ccs dfa)
      where
        charclasses = sort $ tokenClasses dfa
	ccs = [(c,n)|(n,(cs,_))<-zip [(1::Int)..] charclasses,c<-cs]

    outputDetm optccs dfa0 =
        if outDFA
	then showDFA dfa
	else "\n-- Automatically generated code for a DFA follows:\n" ++
	     "--Equal states: "++show eqs++"\n"++
	     pprint haskellCode
      where
        (eqs,dfa) = minimalize dfa0
	haskellCode =
          dfaToHaskell optccs moduleName ["Char","HsLexUtils"] functionName dfa


{-+
A function to convert from the new to the old DFA represenation...
-}
dfa2old dfa = ((1::Int,final),DFA (OM.fromList states))
  where
    final = [s|(s,(True,_))<-dfa]
    states = map state dfa
    state (n,(_,edges)) = (n,(input,output))
      where
        input  = [(i,n)|(I i,n)<-edges]
	output = [(o,n)|(O o,n)<-edges]
