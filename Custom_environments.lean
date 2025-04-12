-- Using a functions as a `Monad` is called a `Reader Monad`

def Reader (ρ : Type) (α : Type) : Type := ρ → α

-- By convention ρ is used for environments.

def read : Reader ρ ρ := λ env => env

def Reader.pure (x : α) : Reader ρ α := λ _ => x

def Reader.bind (result : Reader ρ α) (next : α → Reader ρ β) : Reader ρ β :=
  λ env => next (result env) env

instance : Monad (Reader ρ) where
  pure := Reader.pure
  bind := Reader.bind

abbrev Env : Type := List (String × (Int → Int → Int))
def exampleEvn : Env := [("max", max), ("mod", (· % ·))]

def applyPrimeReader (op : String) (x : Int) (y : Int) : Reader Env Int :=
  read >>= λ env =>
  match env.lookup op with
  | none   => pure 0
  | some f => pure (f x y)

-- Expr and Arith

inductive Prim (special : Type) where
  | plus | minus | times
  | other : special → Prim special

inductive CanFail where
  | div


inductive Expr (op : Type) where
  | const : Int → Expr op
  | prim  : op → Expr op → Expr op → Expr op
deriving Repr

def divOption : CanFail → Int → Int → Option Int
  | .div, x, y =>
    if y == 0 then none
    else pure (x / y)

def divExcept : CanFail → Int → Int → Except String Int
  | .div, x, y =>
    if y == 0 then Except.error s!"Tried to divide {x} by zero!"
    else pure (x / y)

def applyPrim [Monad m] (applySpecial : special → Int → Int → m Int) : Prim special → Int → Int → m Int
  | .plus,  x, y => pure (x + y)
  | .minus, x, y => pure (x - y)
  | .times, x, y => pure (x * y)
  | .other op, x, y => applySpecial op x y

def evaluateM [Monad m] (applySpecial : special → Int → Int → m Int) : Expr (Prim special) → m Int
  | .const i => pure i
  | .prim op x y =>
    evaluateM applySpecial x >>= λ v1 =>
    evaluateM applySpecial y >>= λ v2 =>
    applyPrim applySpecial op v1 v2

open Expr Prim in
#eval evaluateM applyPrimeReader (prim (other "max") (prim plus (const 6) (const 4)) (prim times (const 3) (const 2))) exampleEvn
