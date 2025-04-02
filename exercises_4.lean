-- Exercises for 4th Chpater of Functional Programming in LEAN
--- 1st Represent Positive numbers using a structure.
--- define all `Add`, `Mul`, `ToString` and `ofNat` for the structure.

structure Pos where
  succ ::
  pred : Nat
deriving Repr

def Pos.ofNat : Nat → Pos
  | 0 => Pos.succ 0
  | n => Pos.succ (n - 1)

def Pos.toNat : Pos → Nat
  | p => 1 + p.pred

def Pos.ToString : Pos → String
  | p => (Pos.toNat p).toSuperscriptString

def Pos.add : Pos → Pos → Pos
  | p, k => Pos.ofNat (p.pred + k.pred + 2)

def Pos.mul : Pos → Pos → Pos
  | p, k => Pos.ofNat (Pos.toNat p * Pos.toNat k)

-- No in-between conversion to Natural numbers
def Pos.smul : Pos → Pos → Pos
  | p, k => Pos.ofNat (p.pred * k.pred + p.pred + k.pred  + 1)

#eval (Pos.smul (Pos.ofNat 3) (Pos.ofNat 2)).toNat
#eval (Pos.mul (Pos.ofNat 3) (Pos.ofNat 2)).toNat

-- A Datatype that can represent only the Even numbers
inductive Even : Type where
  | zero : Even
  | succ : Even → Even
deriving Repr

def Even.add : Even → Even → Even
  | e, zero   => e
  | e, succ p =>
    succ (Even.add e p)

instance : Add Even where
  add := Even.add

def Even.mul : Even → Even → Even
  | _, zero   => zero
  | e, succ p =>
    add (add p p) (mul e p)

instance : Mul Even where
  mul := Even.mul

def Even.toNat : Even → Nat
  | zero   => 0
  | succ e => 2 + Even.toNat e

def Even.ofNat (n : Nat) : Even :=
  match n % 2 with
  | 0  =>
    if n == 0 then
      zero
    else
      let rec aux (k : Nat) (acc : Even) : Even :=
        if k = 0 then acc
        else aux (k - 1) (Even.succ acc)
      aux (n / 2) zero
  | _ => zero

instance : Zero Even where
  zero := Even.zero

instance : Coe Nat Even where
  coe n := Even.ofNat n

instance : OfNat Even n where
  ofNat := Even.ofNat n
#eval Even.toNat (Even.ofNat 10)

-- HTTP for Requests and Responses
namespace Http

inductive Request : Type where
  | get | post | put | delete
deriving Repr, Hashable, BEq

structure Response where
  statusCode  : Nat
  body        : String
deriving Repr

instance : ToString Response where
  toString resp :=
    s!"Status Code: {resp.statusCode}\nBody: {resp.body}"

def main : IO Unit :=
  IO.println ""

class MethodHandler (req : Request) where
  handle : IO Response

instance : MethodHandler Request.get where
  handle := do
    return { statusCode := 200, body := s!"200 OK"}

instance : MethodHandler Request.post where
  handle := do
    return { statusCode := 201, body := s!"201 Created"}

instance : MethodHandler Request.put where
  handle := do
    return { statusCode := 200, body := s!"200 OK"}

instance : MethodHandler Request.delete where
  handle := do
    return { statusCode := 204, body := s!"No Content"}

end Http

open Http

def main : IO Unit := do
  let response ← MethodHandler.handle Request.get
  IO.println response

def top_scores : IO Unit :=
  let lst := (([980, 7854, 32, 784, 5434534, 45, 9899].mergeSort).reverse).take 3
  IO.println s!"Top 3 High Scores!\n {lst}"

#eval top_scores
