-- Type classes.
--- Positive numbers.

inductive Pos : Type where
  | one  : Pos
  | succ : Pos → Pos
deriving Repr

-- Positive predcessor.
def Pos.pred : Pos → Pos
  | one    => one
  | succ p => p

def Pos.beq : Pos → Pos → Bool
  | one, one       => true
  | one, succ _    => false
  | succ _, one    => false
  | succ p, succ k => beq p k

instance : BEq Pos where
  beq := Pos.beq

-- Function to convert Natural to Positive.
def Pos.ofNat : Nat → Pos
  | 0     => one
  | n + 1 =>
    if n == 0 then one
    else succ (Pos.ofNat n)

instance : OfNat Pos (n + 1) where
  ofNat := Pos.ofNat n

def Pos.toNat : Pos → Nat
  | one    => 1
  | succ p => 1 + Pos.toNat p

#eval (Pos.ofNat 10).toNat

-- Addition
def Pos.plus : Pos → Pos → Pos
  | p,        one => succ p
  | p, Pos.succ k => Pos.succ (p.plus k)

instance : Add Pos where
  add := Pos.plus

-- Multiplicaiton
def Pos.mul : Pos → Pos → Pos
  | p, one    => p
  | p, succ k => p.mul k + k

#eval (Pos.mul (Pos.ofNat 2) (Pos.ofNat 3)).toNat

-- Let's overload over four functions
instance : Mul Pos where
  mul := Pos.mul

-- And other operations too ! ! !
def Pos.sub : Pos → Pos → Pos
  | p, one    => if Pos.pred p == one then one else pred p
  | p, succ k => Pos.pred (Pos.sub p k)

instance : Sub Pos where
  sub := Pos.sub

#eval ((Pos.ofNat 10) - (Pos.ofNat 9)).toNat

def Pos.div : Pos → Pos → Pos
  | p, one => p
  | one, _ => one
  | p, k => Pos.ofNat (p.toNat / k.toNat)

#eval (Pos.div (Pos.ofNat 10) (Pos.ofNat 5)).toNat

def imperative : Nat := Id.run do
  let mut acc := 0
  for i in  [0:10] do
    acc := i + acc
  pure acc

#eval imperative
