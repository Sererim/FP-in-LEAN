def lst : List String := ["H", "W", "A", "B", "A", "G"]

#eval lst.foldl (λ acc ch => acc.append ch ) ""

def imperative : List Nat := Id.run do
  let mut lst : List Nat := []
  for i in [0:10] do
    lst := lst ++ [i]
  return lst
