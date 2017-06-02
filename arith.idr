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

implementation Eq Term where
  (==) (Wrong m) (Wrong m') = True
  (==) (Wrong m) _ = False
  (==) _ (Wrong m') = False
  (==) (VTrue m) (VTrue m') = True
  (==) _ (VTrue m) = False
  (==) (VTrue m) _ = False
  (==) (VFalse m) (VFalse m') = True
  (==) (VFalse m) _ = False
  (==) _ (VFalse m) = False
  (==) (Pred m t) (Pred m' t') = t == t'
  (==) (Pred m t) _ = False
  (==) _ (Pred m t) = False
  (==) (Succ m t) (Succ m' t') = t == t'
  (==) (Succ m t) _ = False
  (==) _ (Succ m t) = False
  (==) (IsZero m t) (IsZero m' t') = t == t'
  (==) (IsZero m t) _ = False
  (==) _ (IsZero m t) = False
  -- The next condition is too severe...
  (==) (IfThenElse m t t' t'') (IfThenElse m' s s' s'') = result
    where result = t == s && t' == s' && t'' == s''
  (==) (IfThenElse m t t' t'') _ = False
  (==) _ (IfThenElse m t t' t'') = False
  (==) _ _ = False

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
evalOne (IfThenElse m test t s) = case (test == (evalOne test)) of
  False => IfThenElse m (evalOne test) t s
  True => Wrong m
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

-- Not currently provably total, but
-- I believe it in fact is.
-- Need to refactor for totality.
eval : Endo Term
eval (Wrong m) = Wrong m
eval (VZero m) = VZero m
eval (VTrue m) = VTrue m
eval (VFalse m) = VFalse m
eval t = eval t'
  where
  total t' : Term
  t' = evalOne t
