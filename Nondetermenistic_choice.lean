-- Instead of falling when encountering division by zero, it would be sensible to backtrack and try different input.
-- We can use Multisets for that.

inductive Many (α : Type) where
  | none : Many α
  | more : α → (Unit → Many α) → Many α

def Many.one (x : α) : Many α :=
  Many.more x (λ () => Many.none)

def Many.union : Many α → Many α → Many α
  | .none,      ys => ys
  | .more x xs, ys =>
    Many.more x (λ () => union (xs ()) ys)

def Many.fromList : List α → Many α
  | [] => Many.none
  | x :: xs =>
    Many.more x (λ () => fromList xs)

def Many.take : Nat → Many α → List α
  | 0, _     => []
  | _, .none => []
  | n + 1, .more x xs =>
    x :: (xs ()).take n

def Many.takeAll : Many α → List α
  | .none => []
  | .more x xs =>
    x :: (xs ()).takeAll

def Many.bind : Many α → (α → Many β) → Many β
  | .none, _ => Many.none
  | .more x xs, f =>
    (f x).union (bind (xs ()) f)

instance : Monad Many where
  pure := Many.one
  bind := Many.bind

def addsTo (goal : Nat) : List Nat → Many (List Nat)
  | [] =>
    if goal == 0 then
      pure []
    else
      Many.none
  | x :: xs =>
    if x > goal then
      addsTo goal xs
    else
      (addsTo goal xs).union
        (addsTo (goal - x) xs >>= λ answer =>
        pure (x :: answer))

#eval (addsTo 15 [15, 10, 13, 2, 31]).takeAll

inductive NeedsSearch where
  | div | choose

def applySearch : NeedsSearch → Int → Int → Many Int
  | .choose, x, y =>
    Many.fromList [x, y]
  | .div, x, y =>
    if y == 0 then Many.none
    else Many.one (x / y)
