module Main where

--------------------------------------------------------------------------------
--               `calc` reescrito, agora utiliza "do notation"                --
--------------------------------------------------------------------------------

import LexLI
import ParLI
import AbsLI
import Desugar
import Typechecer  hiding (Environment,push)
import Optimizer
import Interpreter 
import PrintLI
import ErrM

main = do
  interact calc
  putStrLn ""

calcMonadic sourceCode = do
  ast <- pProgram (myLexer sourceCode)
  let astCore = desugarP ast
      typeCheckResult = typeCheckP astCore
   in if (any isError typeCheckResult)
        then return (show (filter isError typeCheckResult))
        else let optProgram = optimizeP astCore
              in return
                   (">>>>>>> Programa original:<<<<<<< \n" ++
                    (printTree ast) ++
                    "\n" ++
                    ">>>>>>> Programa otimizado:<<<<<<< \n" ++
                    (printTree optProgram) ++
                    "\n" ++
                    ">>>>>>> Resultado da execucao:<<<<<<< \n" ++
                    (show (executeP optProgram)))
unwrap (Ok x) = x
unwrap (Bad y) = y

calc = unwrap . calcMonadic
