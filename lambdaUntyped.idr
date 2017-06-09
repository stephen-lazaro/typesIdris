module Typable.Untyped.Lambda

-- Use file name to import locally
import arith

data LambdaTerm =
  Primitive Var |
  Lambda Var LambdaTerm |
  Application LambdaTerm LambdaTerm


-- Maybe?
total isPrimitive : Pred LambdaTerm
isVar Lambda x t = False
isVar Applixation t1 t2 = False
isVar _ = True
