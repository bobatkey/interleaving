module Lexer where

data Token = TokTrue | TokFalse | TokConj | TokNot | TokLParen | TokRParen deriving Show

lexStr :: String -> [Token]
lexStr []        = []
lexStr (' ':ss)  = lexStr ss
lexStr ('\n':ss) = lexStr ss
lexStr ('~':ss)  = TokNot : lexStr ss
lexStr ('(':ss)  = TokLParen : lexStr ss
lexStr (')':ss)  = TokRParen : lexStr ss
lexStr ('t':'r':'u':'e':ss)     = TokTrue : lexStr ss
lexStr ('f':'a':'l':'s':'e':ss) = TokFalse : lexStr ss
lexStr ('/':'\\':ss)            = TokConj : lexStr ss

