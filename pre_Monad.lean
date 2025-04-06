-- Lean supports infix, infixl and infixr operators
-- Let's make one that will be used with a function andThen that is used for Option propagation
def andThen (opt : Option α) (next : α → Option β) : Option β :=
  match opt with
  | none => none
  | some x => next x

infixl:55 "~~~>" => andThen

def firstAndThirdInfix (xs : List α) : Option (α × α) :=
  xs[0]? ~~~> λ first =>
  xs[2]? ~~~> λ third =>
  some (first, third)

def firstThirdFifthAndSeventh (xs : List α) : Option (α × α × α × α) :=
  xs[0]? ~~~> λ first   =>
  xs[2]? ~~~> λ third   =>
  xs[4]? ~~~> λ fifth   =>
  xs[6]? ~~~> λ seventh =>
  some (first, third, fifth, seventh)

-- Lean as Pure functional language has no built-in exception mechanism for error handling,
-- because throwing or catching expression is outside of step by step evaluation mode.
-- To accomplish error handling a special datatype is needed.

inductive Exception (ε : Type) (α : Type) where
  | error : ε → Exception ε α
  | ok    : α → Exception ε α
deriving Repr, Hashable, BEq

def get (xs : List α) (i : Nat) : Exception String α :=
  match xs[i]? with
  | none   => Exception.error s!"Index {i} not found (maximum length is {xs.length - 1})"
  | some x => Exception.ok x

def ediblePlants : List String :=
  ["ramsons", "sea plantain", "sea buckthorn", "garden nasturium"]

#eval get ediblePlants 4

-- Logging
--- A number is even if it has no 1 at the end of it
def isEven : Nat → Bool
  | n => n &&& 1 == 1

def sumAndFindEven : List Int → List Int × Int
  | [] => ([], 0)
  | x :: xs =>
    let (moreEven, sum) := sumAndFindEven xs
    (if isEven (x.toNat) then x :: moreEven else moreEven, sum + x)

#eval sumAndFindEven [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

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

-- a similar pattern is present in sumAndFindEven and in inorderSum functions
-- let's optimize them
structure WithLog (logged : Type) (α : Type) where
  log : List logged
  val : α
deriving Repr

def andThenLog (result : WithLog α β) (next : β → WithLog α γ) : WithLog α γ :=
  let { log := thisOut, val := thisRes } := result
  let { log := nextOut, val := nextRes } := next thisRes
  ⟨ thisOut ++ nextOut, nextRes ⟩

def ok (x : β) : WithLog α β := ⟨ [], x ⟩

def save (data : α) : WithLog α Unit := ⟨ [data], () ⟩

def sumAndFindEvens : List Int → WithLog Int Int
  | [] => ok 0
  | i :: is =>
    andThenLog (if isEven i.toNat then save i else ok ()) λ () =>
    andThenLog (sumAndFindEvens is) λ sum =>
    ok (i + sum)

def inorderSumLog : BinTree Int → WithLog Int Int
  | .leaf => ok 0
  | .branch l v r =>
    andThenLog (inorderSumLog l) λ leftSum  =>
    andThenLog (save v)          λ ()       =>
    andThenLog (inorderSumLog r) λ rightSum =>
    ok (leftSum + v + rightSum)

#eval inorderSumLog tree

open BinTree in
def aTree :=
  branch
    (branch
      (branch leaf "a" (branch leaf "a" leaf))
      "c"
      leaf)
    "d"
  (branch leaf "e" leaf)

def number (t : BinTree α) : BinTree (Nat × α) :=
  let rec helper (n : Nat) : BinTree α → (Nat × BinTree (Nat × α))
  | .leaf => (n, .leaf)
  | .branch l v r =>
    let (k, numberedLeft)  := helper n l
    let (i, numberedRight) := helper (k + 1) r
    (i, BinTree.branch numberedLeft (k, v) numberedRight)
  (helper 0 t).snd

#eval number aTree

def State (σ : Type) (α : Type) : Type :=
  σ → (σ × α)

def okS (x : α) : State σ α :=
  λ s => (s, x)

def getS : State σ σ :=
  λ s => (s, s)

def setS (s : σ) : State σ Unit :=
  λ _ => (s, ())
