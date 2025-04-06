/-
  Monad: a Functional Design Pattern
  That allows to work with:
  - A polymorphic type, such as `Option`, `Except ε`, `WithLog` logged, or `State σ`
  - An operator `andThen` that takes care of some repetitive aspect of sequencing programs that have this type
  - An operator `ok` that is (in some sense) the most boring way to use the type
  - A collection of other operations, such as `none`, `fail`, `save`, and `get`, that name ways of using the type
-/

def firstThirdFifthAndSeven {m α} [Monad m] (lookup : List α → Nat → m α) (xs : List α) : m (α × α × α × α) :=
  lookup xs 0 >>= λ first   =>
  lookup xs 2 >>= λ third   =>
  lookup xs 4 >>= λ fifth   =>
  lookup xs 5 >>= λ seventh =>
  pure (first, third, fifth, seventh)

def slowMammals : List String := ["slow loris", "three-toed sloth"]

#eval firstThirdFifthAndSeven (λ xs i => xs[i]?) slowMammals

def fastBirds : List String := [
  "Peregrine falcon",
  "Saker falcon",
  "Golden eagle",
  "Gray-headed albatross",
  "Spur-winged goose",
  "Swift",
  "Anna's hummingbird"
]

#eval firstThirdFifthAndSeven (λ xs i => xs[i]?) fastBirds

def getOrExcept (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none   => Except.error s!"Index {i} not found (maximum is {xs.length - 1})"
  | some x => Except.ok x

#eval getOrExcept fastBirds 2

def State (σ : Type) (α : Type) : Type :=
  σ → (σ × α)

def getS : State σ σ :=
  λ s => (s, s)

def setS (s : σ) : State σ Unit :=
  λ _ => (s, ())

instance : Monad (State σ) where
  pure x := λ s => (s, x)
  bind first next :=
    λ s => let (s', x) := first s
    next x s'

def increment (howMuch : Int) : State Int Int :=
  getS >>= λ i =>
  setS (i + howMuch) >>= λ () =>
  pure i

#eval [1, 2, 3, 4].mapM increment 0

structure WithLog (logged : Type) (α : Type) where
  log : List logged
  val : α
deriving Repr

instance : Monad (WithLog logged) where
  pure x := ⟨ [], x ⟩
  bind result next :=
    let ⟨ thisOut, thisRes ⟩ := result
    let ⟨ nextOut, nextRes ⟩ := next thisRes
    ⟨ thisOut ++ nextOut, nextRes ⟩

def save (data : α) : WithLog α Unit := ⟨ [data], () ⟩

def isEven : Nat → Bool
  | n => n &&& 1 != 1

def saveIfEven (i : Int) : WithLog Int Int :=
  (if isEven i.toNat then save i
    else pure ()) >>=
    λ () => pure i

#eval List.mapM saveIfEven [1, 2, 3, 4, 5]

-- Mondas encode programs with effects, such as failurem exceptions, or logging
-- into explicit representations as data and functions.
-- Sometiems however, an API will be written to use monads for flexibility.
--- One of such Monads is Identity Monad
def ID (t : Type) : Type := t

instance : Monad ID where
  pure x   := x
  bind x f := f x

#eval List.mapM (m := ID) (· + 1) [1, 2, 3, 4]

/-
The Monad Contract.
1. `pure` should be left identity of `bind`. That is, `bind (pure v) f` should be the same as `f v`.
2. `pure` should be right identity of `bind`, so `bind v pure` is the same as `v`
3. `bind` should be associative, so `bind (bind v f) g` is the same as `bind v (λ x => bind (f x) g)`
-/

-- Exercises
--- Mapping Monad to a tree

inductive BinTree (α : Type) where
  | leaf
  | branch : BinTree α → α → BinTree α → BinTree α
deriving Repr, BEq, Hashable

-- Inorder Sum of Binary Tree.
def inorderSum : BinTree Int → List Int × Int
  | BinTree.leaf => ([], 0)
  | .branch l v r =>
    let (leftVisited, leftSum)   := inorderSum l
    let (hereVisited, hereSum)   := ([v], v)
    let (rigthVisited, rightSum) := inorderSum r
    (leftVisited ++ hereVisited ++ rigthVisited, leftSum + hereSum + rightSum)

instance : Coe (Unit) (BinTree α) where
  coe
    | _ => BinTree.leaf

--- Let's use a BinTree
def tree : BinTree Int := BinTree.branch
  (BinTree.branch (BinTree.branch () 1 ()) 2 (BinTree.branch () 3 ()))
    4
  (BinTree.branch (BinTree.branch () 5 ()) 7 (BinTree.branch () 6 ()))

#eval inorderSum tree

def BinTree.mapM [Monad m] (f : α → m β) : BinTree α → m (BinTree β)
  | .leaf => pure ()
  | .branch l v r => do
    let left  ← BinTree.mapM f l
    let here  ← f v
    let right ← BinTree.mapM f r
    return (BinTree.branch left here right)

def mappedTree (t : BinTree Int) : Option (BinTree String) :=
  BinTree.mapM (λ x => some (s!"Hello {x}")) t

#eval mappedTree tree
#eval BinTree.mapM (m := ID) (· + 6) tree
