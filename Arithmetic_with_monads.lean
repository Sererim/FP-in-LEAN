/-
Monads are a way of encoding programs with side effects into a language that does not have them.
It seems like such a statement is an admission of missing something important.
However, while using `Monad` API does impose a syntactic cost on a program, it brings two important benefits:

1. Programs must be honest about which effects they use in their types. A quick glance at a type signature
describes everything that the program can do, rather than just what it accepts and what it returns.

2. Not every language provides the same effect. For example, only some languages have exceptions. Other languages
have unique, exotic effects, such as Icon's searching over multiple values and Scheme or Ruby's continuations.
Because monads can encode `any` effect, programmers can choose which ones are the best fit for a given application,
rather than being stuck with the language developers provided.

-/

-- Example of using mondas in Arithmetic Expressions
inductive Expr (op : Type) where
  | const : Int → Expr op
  | prim  : op → Expr op → Expr op → Expr op
deriving Repr

inductive Arith where
  | plus | minus | times | div
deriving Repr

instance : Coe Unit (Expr α) where
  coe
    | () => Expr.const 0

-- Expression 2 + 3 is represented as:
open Expr in
open Arith in
def twoPlusThree : Expr Arith :=
  prim plus (const 2) (const 3)

#eval twoPlusThree

-- And expression 14 / (45 - 5 * 9) as:
open Expr  in
open Arith in
def zeroDivision : Expr Arith :=
  prim div (const 14) (prim minus (const 45) (prim times (const 5) (const 9)))

-- Evaluating expressions.
--- Because expression include devision, and division by zero is undefined, evaluation might fail.
--- One way to represent the failure is to use `Option`
def evaluateOperation : Expr Arith → Option Int
  | Expr.const i => pure i
  | Expr.prim op x y =>
    evaluateOperation x >>= λ value1 =>
    evaluateOperation y >>= λ value2 =>
    match op with
    | .plus  => pure (value1 + value2)
    | .minus => pure (value1 - value2)
    | .times => pure (value1 * value2)
    | .div   =>
      if value2 == 0 then none
      else pure (value1 / value2)

#eval evaluateOperation twoPlusThree
-- Function works, however it mixes two concerns together
-- `evaluating the subexpression`
-- `applying binary operation`
-- It is better to split them.

def applyPrim : Arith → Int → Int → Option Int
  | .plus,  x, y => pure (x + y)
  | .minus, x, y => pure (x - y)
  | .times, x, y => pure (x * y)
  | .div,   x, y =>
    if y == 0 then none
    else pure (x / y)

def evaluateOption : Expr Arith → Option Int
  | Expr.const i   => pure i
  | Expr.prim op x y =>
    evaluateOption x >>= λ v1 =>
    evaluateOption y >>= λ v2 =>
    applyPrim op v1 v2

#eval evaluateOption zeroDivision
#eval evaluateOption twoPlusThree

--- But none is not a good way of handling errors, so we need to modify both functions

def applyPrimExcept : Arith → Int → Int → Except String Int
  | .plus,  x, y => pure (x + y)
  | .minus, x, y => pure (x - y)
  | .times, x, y => pure (x * y)
  | .div,   x, y =>
    if y == 0 then
      Except.error s!"Tried to divide {x} by zero!"
    else
      pure (x / y)

def evaluateExcept : Expr Arith → Except String Int
  | Expr.const i => pure i
  | Expr.prim op x y =>
    evaluateExcept x >>= λ v1 =>
    evaluateExcept y >>= λ v2 =>
    applyPrimExcept op v1 v2

#eval evaluateExcept zeroDivision

-- Because only thing that changed is Monad that is used
--- Both `Option` and `Except` are Monads
-- We can use a single Evaluater

def evaluateM [Monad m] (applyPrim : Arith → Int → Int → m Int) : Expr Arith → m Int
  | Expr.const i     => pure i
  | Expr.prim op x y =>
    evaluateM applyPrim x >>= λ v1 =>
    evaluateM applyPrim y >>= λ v2 =>
    applyPrim op v1 v2

#eval evaluateM applyPrimExcept zeroDivision

-- Still we can make the code better, because of how applyPrim works we can extract the Monad.

def applyDivOption (x : Int) (y : Int) : Option Int :=
  if y == 0 then none
  else pure (x / y)

def applyDivException (x : Int) (y : Int) : Except String Int :=
  if y == 0 then Except.error s!"Tried to divide {x} by a zero"
  else pure (x / y)

def applyPrimM [Monad m] (applyDiv : Int → Int → m Int) : Arith → Int → Int → m Int
  | .plus,  x, y => pure (x + y)
  | .minus, x, y => pure (x - y)
  | .times, x, y => pure (x * y)
  | .div,   x, y => applyDiv x y

def evaluateMM [Monad m] (applyDiv : Int → Int → m Int) : Expr Arith → m Int
  | .const i => pure i
  | .prim op x y =>
    evaluateMM applyDiv x >>= λ v1 =>
    evaluateMM applyDiv y >>= λ v2 =>
    applyPrimM applyDiv op v1 v2

#eval evaluateMM applyDivException zeroDivision
