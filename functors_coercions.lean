/-
A polymorphic type is a `functor` if it has an overload for a function named `map` that transforms every element
cotained in it by a function.
-/

--- Examples
#eval Functor.map (· + 5) [1, 2, 3, 4]
#eval Functor.map toString [1, 2, 3, 4]
#eval Functor.map Int.toNat [1, 2, 3, 4]

/-
Because Functor.map is a long word you can use `<$>` as a replacement for it.
-/
#eval (· + 5) <$> [1, 2, 3, 4]
#eval toString <$> [1, 2, 3, 4]
#eval Int.toNat <$> [1, 2, 3, 4]

-- Binary Tree
inductive BinTree (α : Type) where
  | leaf
  | branch : BinTree α → α → BinTree α → BinTree α

def eqBinTree {α : Type} [BEq α] : BinTree α → BinTree α → Bool
  | .leaf, .leaf => true
  | .branch l1 v1 r1, .branch l2 v2 r2 =>
    v1 == v2 && eqBinTree l1 l2 && eqBinTree r1 r2
  | _, _ => false

instance [BEq α] : BEq (BinTree α) where
  beq := eqBinTree

def hashBinTree [Hashable α] : BinTree α → UInt64
  | .leaf => 0
  | .branch l v r =>
    mixHash 1 (mixHash (hashBinTree l) (mixHash (hash v) (hashBinTree r)))

instance [Hashable α] : Hashable (BinTree α) where
  hash := hashBinTree

instance : Coe (Unit) (BinTree α) where
  coe
    | _ => BinTree.leaf

--- Let's use a BinTree
def tree : BinTree Nat := BinTree.branch
  (BinTree.branch (BinTree.branch () 1 ()) 2 (BinTree.branch () 3 ()))
    4
  (BinTree.branch (BinTree.branch () 5 ()) 7 (BinTree.branch () 6 ()))

-- NonEmpty list
structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α

def idahoSpiders : NonEmptyList String :=
  ⟨
    "Banded Garden Spider",
    [
      "Long-legged Sac Spider",
      "Wolf Spider",
      "Hobo Spider",
      "Cat-faced Spider",
    ]
  ⟩

-- Functor for NonEmptyList
instance : Functor NonEmptyList where
  map f xs :=
  ⟨
    f xs.head,
    f <$> xs.tail
  ⟩

#eval String.toLower <$> (String.toUpper <$> idahoSpiders)

-- Exercise implement a Functor for a Binary Tree

def binTreeFunctor {α β : Type} : (α → β) → BinTree α → BinTree β
  | _, .leaf => .leaf
  | f, .branch l v r =>
    BinTree.branch (binTreeFunctor f l) (f v) (binTreeFunctor f r)

instance : Functor BinTree where
  map f t :=
    binTreeFunctor f t

#eval toString <$> tree

-- Coercions allow to coerce a Type into another One

instance {α x xs} : CoeDep (List α) (x :: xs) (NonEmptyList α) where
  coe := ⟨ x, xs ⟩

/-
`MONOID` ?! in my LEAN ?!
-/

structure Monoid where
  Carrier : Type
  neutral : Carrier
  op : Carrier → Carrier → Carrier

def natMulMonoid : Monoid :=
  ⟨ Nat, 1, (· * ·) ⟩

def natAddMonoid : Monoid :=
  ⟨ Nat, 0, (· + ·) ⟩

def stringMonoid : Monoid :=
  ⟨ String, "", (· ++ ·) ⟩

def listMonoid (α : Type) : Monoid :=
  ⟨ List α, [], (· ++ ·) ⟩

def foldMap (M : Monoid) (f : α → M.Carrier) (xs : List α) : M.Carrier :=
  let rec go (soFar : M.Carrier) : List α → M.Carrier
    | [] => soFar
    | y :: ys => go (M.op soFar (f y)) ys
  go M.neutral xs

#eval foldMap stringMonoid (·) ["Hello", "World"]

-- We can shorten the foldMap definition with CoeSort which works the same way as Coe, with only difference is that
-- it accepts a Sort (Type | Prop)
instance : CoeSort Monoid Type where
  coe m := m.Carrier

def foldMapShort (M : Monoid) (f : α → M) (xs : List α) : M :=
  let rec go (soFar : M) : List α → M
    | [] => soFar
    | y :: ys => go (M.op soFar (f y)) ys
  go M.neutral xs

-- Coercing to Functions
structure Adder where
  howMuch : Nat
deriving Repr

def add5 : Adder := ⟨ 5 ⟩
-- Because it is not a function applying to to value will yield an error.
-- So we need to somehow transform it into a function
--- CoeFun to the RESCUE
instance : CoeFun Adder (λ _ => Nat → Nat) where
  coe a := (· + a.howMuch)

#eval add5 10
