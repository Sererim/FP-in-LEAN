-- Constructor Syntax for Instances

structure Tree where
  latinName   : String
  commonNames : List String
deriving Repr

def oak : Tree :=
  ⟨ "Quercus rebus", ["common oak", "European oak"] ⟩

def birch : Tree := {
  latinName   := "Betula pendula",
  commonNames := ["silver birch", "warty birch"]
}

def sloe : Tree where
  latinName   := "Prunus spinosa"
  commonNames := ["sloe", "blackthorn"]

-- All three are equivalent

-- Similarly Type classes can be defined as:
class Display (α : Type) where
  displayName : α → String

instance : Display Tree :=
  ⟨ Tree.latinName ⟩

instance : Display Tree :=
  { displayName := Tree.latinName }

instance : Display Tree where
  displayName t := t.latinName

-- Special syntax for an example.
structure NonEmptyList (α : Type) where
  head : α
  tail : List α
deriving Repr

example : NonEmptyList String where
  head := "Sparrow"
  tail := ["Duck", "Swan", "Magpie", "Eurasian coot", "Crow"]
