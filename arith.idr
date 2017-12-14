module Typable.Untyped.Arithmetic

public export
data Term =
  Wrong  |
  VTrue |
  VFalse |
  VZero |
  Pred Term |
  Succ Term |
  IsZero Term |
  IfThenElse Term Term Term

implementation Eq Term where
  (==) Wrong Wrong            = True
  (==) VTrue VTrue            = True
  (==) VFalse VFalse          = True
  (==) (Pred t) (Pred t')     = t == t'
  (==) (Succ t) (Succ t')     = t == t'
  (==) (IsZero t) (IsZero t') = t == t'
  -- The next condition is too severe...
  (==) (IfThenElse t t' t'') (IfThenElse s s' s'') = result
    where result = if t == s then t' == s' else t'' == s''
  (==) _ _ = False

export
Predicate : Type -> Type
Predicate a = a -> Bool

public export
total isNumeric : Predicate Term
isNumeric VZero    = True
isNumeric (Pred t) = isNumeric t
isNumeric (Succ t) = isNumeric t
isNumeric _        = False

public export
total isBoolean : Predicate Term
isBoolean VTrue   = True
isBoolean VFalse  = True
isBoolean _       = False

public export
total and : Predicate a -> Predicate a -> Predicate a
and f g = \x => (f x) && (g x)

public export
total or : Predicate a -> Predicate a -> Predicate a
or f g = \x => (f x) || (g x)

public export
total isValue : Predicate Term
isValue = or isNumeric isBoolean

public export
Endo : Type -> Type
Endo a = a -> a

export
total evalOne : Endo Term
evalOne (Wrong) = Wrong
evalOne (IfThenElse VTrue t s) = t
evalOne (IfThenElse VFalse t s) = s
evalOne (IfThenElse Wrong t s) = Wrong
evalOne (IfThenElse test t s) = IfThenElse (evalOne test) t s
evalOne (Succ t) = Succ (evalOne t)
evalOne (Pred VZero) = Wrong
evalOne (Pred (Succ v)) = case (isNumeric v) of
  True => v
  False => Wrong
evalOne (Pred t) = Pred (evalOne t)
evalOne (IsZero VZero) = VTrue
evalOne (IsZero (Succ v)) = case (isNumeric v) of
  True => VFalse
  False => Wrong
evalOne (IsZero t) = IsZero (evalOne t)
evalOne VZero = VZero
evalOne _          = Wrong

partial eval : Endo Term
eval Wrong = Wrong
eval VZero = VZero
eval (Succ t) = case (isNumeric t) of
  True => Succ (eval t)
  False => Wrong
eval (Pred t) = case (isNumeric t) of
  True => Pred (eval t)
  False => Wrong
eval VTrue  = VTrue
eval VFalse = VFalse
eval (IfThenElse VTrue t s) = eval t
eval (IfThenElse VFalse t s) = eval s
eval t = eval (evalOne t)
