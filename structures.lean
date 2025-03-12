structure Point where
  x : Float
  y : Float
deriving Repr

def origin : Point :=
  { x := 0.0, y := 0.0 }

def addPoints (p1 : Point) (p2 : Point) : Point :=
  { x := p1.x + p2.x, y := p1.y + p2.y}

def point_1 : Point := { x := 1.0, y := 2.0}

#eval addPoints origin point_1

def distance (p1 : Point) (p2 : Point) : Float :=
  Float.sqrt (((p2.x - p1.x) ^ 2) + ((p2.y - p1.y) ^ 2))

#eval distance origin point_1

-- Rather than update the existing structure LEAN will create a copy where the field specified with `with` will be replaced with the provided value
-- Intretsting...
def zeroX (p : Point) : Point :=
  { p with x := 0 }

def point_2 : Point :=
  { x := 10, y := 12 }

#eval zeroX point_2
#eval point_2

-- Constructors
#check Point.mk 1.5 2.8
-- mk is an in-build constructor that can be renamed with
-- ::`name`
#check (Point.x)

def modifyBoth (f : Float → Float) (p : Point) : Point :=
  { x := f p.x, y := f p.y}

#eval modifyBoth Float.log2 point_2

-- Exercieses
-- define a structure RectangularPrism
structure RectangularPrism where
  height : Float
  width  : Float
  depth  : Float
deriving Repr

def volume (prism : RectangularPrism) : Float :=
  prism.height * prism.width * prism.depth

def prism : RectangularPrism :=
  { height := 10, width := 5, depth := 10 }

#eval volume prism

def transform (f : Float → Float) (prism : RectangularPrism) : RectangularPrism :=
  {
    height := f prism.height,
    width  := f prism.width,
    depth  := f prism.depth
  }

#eval transform Float.log10 prism


-- define a structure named Segment that represents a line segment by its endpoints.
structure Segment where
  a : Point
  b : Point
deriving Repr

def lenght : Segment → Float
  | segment => distance segment.b segment.a


def seg : Segment :=
  { a := point_1, b := point_2 }

#eval lenght seg

def split_on_camel (lst : List Char) : String :=
  match lst with
  | [] => ""
  | x::xs =>
    if x.isUpper then " " ++ x.toString ++ split_on_camel xs
    else x.toString ++ split_on_camel xs

def split_on_camle_simp : List Char → String
  | []      => ""
  | x :: xs =>
    if x.isUpper then " " ++ x.toString ++ split_on_camle_simp xs
    else x.toString ++ split_on_camle_simp xs

#eval split_on_camel "camelCaseCasedddCase".toList
#eval split_on_camle_simp "OCamlIsMyCaml".toList
