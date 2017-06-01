data Meta = Empty

data Term =
  Wrong Meta |
  VTrue Meta |
  VFalse Meta |
  VZero Meta |
  Pred Meta Term |
  Succ Meta Term |
  IsZero Meta Term |
  IfThenElse Meta Term Term Term

Predicate : Type -> Type
Predicate a = a -> Bool

total isNumeric : Predicate Term
isNumeric (VZero a) = True
isNumeric (Pred m t) = isNumeric t
isNumeric (Succ m t) = isNumeric t
isNumeric anythingElse = False

total isBoolean : Predicate Term
isBoolean (VTrue a) = True
isBoolean (VFalse a) = True
isBoolean anythingElse = False

total and : Predicate a -> Predicate a -> Predicate a
and f g = \x => (f x) && (g x)

total or : Predicate a -> Predicate a -> Predicate a
or f g = \x => (f x) || (g x)

total isValue : Predicate Term
isValue = or isNumeric isBoolean

Endo : Type -> Type
Endo a = a -> a

total evalOne : Endo Term
evalOne (Wrong m) = Wrong m
evalOne (IfThenElse m (VTrue m') t s) = t
evalOne (IfThenElse m (VFalse m') t s) = s
evalOne (IfThenElse m (Wrong m') t s) = Wrong m'
evalOne (IfThenElse m test t s) = IfThenElse m tested t s
  where
  total tested : Term
  tested = evalOne test
-- ^^ You could be more sophistecated and test
-- that the next step is reduced, to prevent
-- us hanging on an irreducible in eval.
evalOne (Succ m t) = Succ m (evalOne t)
evalOne (Pred m VZero) = VZero
evalOne (Pred m (Succ m' v)) = case (isNumeric v) of
  True => v
  False => Wrong m'
evalOne (Pred m t) = Pred m (evalOne t)
evalOne (IsZero m (VZero m')) = VTrue m'
evalOne (IsZero m (Succ m' v)) = case (isNumeric v) of
  True => VFalse m'
  False => Wrong m'
evalOne (IsZero m t) = IsZero m (evalOne t)
evalOne anythingElse = Wrong Empty

-- Not currently total, if something is not reducible
-- this won't terminate.
-- E.g. if a test in an if is not reducible
eval : Endo Term
eval (Wrong m) = Wrong m
eval (VZero m) = VZero m
eval (VTrue m) = VTrue m
eval (VFalse m) = VFalse m
eval t = eval t'
  where
  total t' : Term
  t' = evalOne t
