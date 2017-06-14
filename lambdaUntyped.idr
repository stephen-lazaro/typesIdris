module Typable.Untyped.Lambda

import arith

Name: Type
Name = String

data LambdaTerm =
  Variable Name |
  Lambda Name LambdaTerm |
  Application LambdaTerm LambdaTerm

-- This is probably too pessimistic
total isVariable : LambdaTerm -> Bool
isVariable (Lambda x t) = False
isVariable (Application t t') = False
isVariable (Variable n) = True

-- Infomrationless Variable Binding
data Binding = NameBind
