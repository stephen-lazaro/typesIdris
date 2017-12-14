module Typable.Untyped.Lambda

Name: Type
Name = String

Info: Type
Info = String

infixr 20 |+|
(|+|): String -> String -> String
(|+|) a b = Prelude.Strings.(++) a b

data LambdaTerm =
  Variable Name Integer Integer |
  Lambda Name LambdaTerm |
  Application LambdaTerm LambdaTerm

Predicate: Type -> Type
Predicate a = a -> Bool

-- This is probably too pessimistic
total isVariable : LambdaTerm -> Bool
isVariable (Lambda x t) = False
isVariable (Application t t') = False
isVariable (Variable n j k) = True

-- Informationless Variable Binding
data Binding = NameBind

total printTerm : LambdaTerm -> String
printTerm (Variable n j k)    = n
printTerm (Lambda n t)        =  "L("  |+| n |+| ")" |+| ".(" |+| (printTerm t) |+| ")"
printTerm (Application t1 t2) = (printTerm t1) |+| " " |+| (printTerm t2)

total isVal : Predicate LambdaTerm
isVal (Lambda n t) = True
isVal _            = False


