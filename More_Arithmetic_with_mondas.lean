-- We can make the Arithmetic with Monads even better to use.
-- First let's move an operation with a potential failure away from Prim type

inductive Prim (special : Type) where
  | plus | minus | times
  | other : special → Prim special

inductive CanFail where
  | div

inductive Expr (op : Type) where
  | const : Int → Expr op
  | prim  : op → Expr op → Expr op → Expr op
deriving Repr

-- the second step is to broaden the scope of the division handler argument to `evaluateM`
-- so it can process any special operator.

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

-- ^Looks really nice btw.

def applyEmpty [Monad m] (op : Empty) (_ : Int) (_ : Int) : m Int :=
  nomatch op

open Expr Prim in
#eval evaluateM (m := Id) applyEmpty (prim plus (const 5) (const (-14)))
