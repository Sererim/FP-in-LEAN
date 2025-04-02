-- Let's make a JSON serializer in LEAN ! ! !
import Lean

inductive JSON where
  | true | false | null
  | string : String → JSON
  | number : Float → JSON
  | object : List (String × JSON) → JSON
  | array  : List JSON → JSON
deriving Repr

structure Serializer where
  Contents  : Type
  serialize : Contents → JSON

def Str : Serializer :=
  ⟨
    String,
    JSON.string
  ⟩

instance : CoeFun Serializer (λ s => s.Contents → JSON) where
  coe s := s.serialize

def buildResponse (title : String) (R : Serializer) (record : R.Contents) : JSON :=
  JSON.object [
    ("title", JSON.string title),
    ("status", JSON.number 200),
    ("record", R record)
  ]

#eval buildResponse "Functional Programming in Lean" Str "Programming is FUN !"

-- Let's make a function that will convert JSON to String
-- First we need to work with numbers

def dropDecimals (numString : String) : String :=
  if numString.contains '.' then
    let noTrailingZeros := numString.dropRightWhile (· == '0')
    noTrailingZeros.dropRightWhile (· == '.')
  else numString

#eval dropDecimals 5.2.toString

-- A helper function to append a list of strings with a separator in between them
def String.separate (sep : String) (strings : List String) : String :=
  match strings with
  | [] => ""
  | x :: xs => String.join (x :: xs.map (sep ++ ·))

#eval String.separate "," ["hello", "world", "goodbye", "takeWhile"]

partial def JSON.asString (val : JSON) : String :=
  match val with
  | true  => "true"
  | false => "false"
  | null  => "null"
  | string s => "\"" ++ Lean.Json.escape s ++ "\""
  | number n => dropDecimals n.toString
  | object members =>
    let memberToString mem :=
    "\"" ++ Lean.Json.escape mem.fst ++ "\": " ++ asString mem.snd
    "{" ++ ", ".separate (members.map memberToString) ++ "}"
  | array elements =>
    "[" ++ ", ".separate (elements.map asString) ++ "]"

#eval (buildResponse "Functional Programmin in Lean" Str "Programming is FUN !").asString
