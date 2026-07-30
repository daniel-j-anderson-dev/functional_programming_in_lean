module

def firstThirdFifthSeventh
  [Monad m]
  (lookup : List α → Nat → m α)
  (xs : List α)
  : m (α × α × α × α) :=
  lookup xs 0 >>= λ first =>
  lookup xs 2 >>= λ second =>
  lookup xs 4 >>= λ fifth =>
  lookup xs 6 >>= λ seventh =>
  pure (first, second, fifth, seventh)

def slowMammals : List String :=
  ["Three-toed sloth", "Slow loris"]
def fastBirds : List String := [
  "Peregrine falcon",
  "Saker falcon",
  "Golden eagle",
  "Gray-headed albatross",
  "Spur-winged goose",
  "Swift",
  "Anna's hummingbird"
]
#eval firstThirdFifthSeventh (·[·]?) slowMammals
#eval firstThirdFifthSeventh (·[·]?) fastBirds

def getOrExcept (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none =>
    Except.error s!"Index {i} not found (maximum is {xs.length - 1})"
  | some x =>
    Except.ok x
#eval firstThirdFifthSeventh getOrExcept slowMammals


#eval firstThirdFifthSeventh getOrExcept fastBirds

