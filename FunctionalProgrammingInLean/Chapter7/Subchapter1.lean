inductive Vect
  (α : Sort u)
  : Nat → Sort (u + 1) where
  | nil : Vect α 0
  | cons {n : Nat} (head : α) (tail : Vect α n) : Vect α (n + 1)

namespace Vect

def ofList
  (xs : List α)
  : Vect α xs.length :=
  match xs with
  | [] => nil
  | head :: tail => cons head (Vect.ofList tail)

-- macro to allow the syntax `v[1, 2, 3]` to construct `Vect`s
syntax "v[" term,* "]" : term
macro_rules
  |`(v[$e,*]) => `(Vect.ofList [$e,*])

def replicate
  {α : Sort u}
  (n : Nat) (x : α)
  : Vect α n :=
  match n with
  | 0 => nil
  | n' + 1 => cons x (replicate n' x)

def zipWith
  {α : Sort u} {β : Sort v} {γ : Sort w} {n : Nat}
  (f : α → β → γ) (lhs : Vect α n) (rhs : Vect β n)
  : Vect γ n :=
  match lhs, rhs with
  | nil, nil => nil
  | cons l ls, cons r rs =>
    let newHead := f l r
    let newTail := zipWith f ls rs
    cons newHead newTail

def zip
  {α : Type u} {β : Type v} {n : Nat}
  : Vect α n → Vect β n → Vect (α × β) n :=
  zipWith (·, ·)

def fold
  {α : Sort u} {β : Sort v} {n : Nat}
  (initial : β) (update : β → α  → β) (self : Vect α n)
  : β :=
  let state := initial
  match self with
    | nil => state
    | cons head tail =>
      let newState := update state head
      let finalState := fold newState update tail
      finalState

def all
  {α : Sort u} {n : Nat}
  (predicate : α → Bool) (self : Vect α n)
  : Bool :=
  fold true (· && predicate ·) self

def elementWiseBEq
  {α : Type u} {n : Nat}
  [BEq α]
  : Vect α n → Vect α n → Vect Bool n :=
  zipWith (· == ·)

instance instBEq
  {α : Type u} {n : Nat}
  [BEq α]
  : BEq (Vect α n) where
  beq lhs rhs := all id (elementWiseBEq lhs rhs)

instance instForM
  {m  : Type u → Type v} {α : Type w} {n : Nat}
  [Bind m] [Pure m]
  : ForM m (Vect α n) α where
  forM self action := fold (pure .unit) (λ previousActions x => do previousActions; action x) self

instance instForIn
  {m  : Type u → Type v} {α : Type w} {n : Nat}
  [Monad m]
  : ForIn m (Vect α n) α where
  forIn := ForM.forIn

def map
  {α : Sort u} {β : Sort v} {n : Nat}
  (f : α → β) (self : Vect α n)
  : Vect β n :=
  match self with
  | nil => nil
  | cons head tail =>
    let newHead := f head
    let newTail := map f tail
    cons newHead newTail

def unzip
  {α : Type u} {β : Type v} {n : Nat}
  (self : Vect (α × β) n)
  : Vect α n × Vect β n :=
  match self with
  | nil => (nil, nil)
  | cons heads tail =>
    let (lHead, rHead) := heads
    let (lTail, rTail) := unzip tail
    let ls := cons lHead lTail
    let rs := cons rHead rTail
    (ls, rs)

def pushBack
  {α : Sort u} {n : Nat}
  (newLastElement : α) (self : Vect α n)
  : Vect α (n + 1) :=
  match self with
  | nil => cons newLastElement nil
  | cons head tail =>
    let newTail := pushBack newLastElement tail
    cons head newTail

theorem Nat.comm_assoc
  (a b c : Nat)
  : a + (b + c) = (a + c) + b :=
  let Goal := a + (b + c) = (a + c) + b

  let step₀ : (a + c) + b = a + (c + b) := Nat.add_assoc a c b
  let step₁ : a + (c + b) = (a + c) + b := Eq.symm step₀
  let step₂ : b + c = c + b             := Nat.add_comm b c
  let step₃ : a + (b + c) = a + (c + b) := congrArg (a + ·) step₂
  let step₄ : a + (b + c) = (a + c) + b := Eq.trans step₃ step₁

  (step₄ : Goal)

theorem Nat.eq_zero_add
  (n : Nat)
  : n = 0 + n :=
  let Goal := n = 0 + n

  let step₀ : 0 + n = n := Nat.zero_add n
  let step₁ : n = 0 + n := Eq.symm step₀

  (step₁ : Goal)

def castLength
  {α : Type u} {n m : Nat}
  (h : n = m) (self : Vect α n)
  : Vect α m :=
  let Goal := Vect α m

  let step₀ : Vect α n = Vect α m := congrArg (Vect α) h
  let step₁ : Vect α n → Vect α m := Eq.mp step₀
  let step₂ : Vect α m            := step₁ self

  (step₂ : Goal)

def reverse
  {α : Type u} {n : Nat}
  (self : Vect α n)
  : Vect α n :=
  loop .nil self
  where loop
    {α : Type u} {n m : Nat}
    (accumulator : Vect α m) (remaining : Vect α n)
    : Vect α (n + m) :=
    match n, remaining with
    | 0, .nil => castLength (Nat.eq_zero_add m) accumulator
    | k + 1, .cons head tail =>
      let newAccumulator := cons head accumulator
      let recursiveResult := loop newAccumulator tail
      castLength (Nat.comm_assoc k m 1) recursiveResult

def drop
  {α : Sort u} {k : Nat}
  (n : Nat) (self : Vect α (k + n))
  : Vect α k :=
  match n, self with
  | 0, self => self
  | n' + 1, cons _ tail => drop n' tail

def take
  {α : Sort u} {k : Nat}
  (n : Nat) (self : Vect α (k + n))
  : Vect α n :=
  match n, self with
  | 0, _ => nil
  | n' + 1, cons head tail =>
    let newTail := take n' tail
    let output := cons head newTail
    output

end Vect

namespace exercises
-- Double-check that Vect.zip gives the right answer when combining the three highest peaks in Oregon with the three highest peaks in Denmark. Because Vect doesn't have the syntactic sugar that List has, it can be helpful to begin by defining oregonianPeaks : Vect String 3 and danishPeaks : Vect String 3.
#check @Vect.zip

def oregonPeaks := v["Mount Hood", "Mount Jefferson", "South Sister"]

def denmarkPeaks := v["Møllehøj", "Yding Skovhøj", "Ejer Bavnehøj"]

def zip.expected := v[("Mount Hood", "Møllehøj"), ("Mount Jefferson", "Yding Skovhøj"), ("South Sister", "Ejer Bavnehøj")]

def zip.actual := oregonPeaks.zip denmarkPeaks
#eval zip.expected == zip.actual -- true

-- Define a function Vect.map with type (α → β) → Vect α n → Vect β n.
#check @Vect.map

-- Define a function Vect.zipWith that combines the entries in a Vect one at a time with a function. It should have the type (α → β → γ) → Vect α n → Vect β n → Vect γ n.
#check @Vect.zipWith

-- Define a function Vect.unzip that splits a Vect of pairs into a pair of Vects. It should have the type Vect (α × β) n → Vect α n × Vect β n.
#check @Vect.unzip

-- Define a function Vect.pushBack that adds an entry to the end of a Vect. Its type should be Vect α n → α → Vect α (n + 1) and #eval Vect.pushBack (cons "snowy" nil) "peaks" should yield Vect.cons "snowy" (Vect.cons "peaks" (Vect.nil)).
#check @Vect.pushBack
def pushBack.actual := v["snowy"].pushBack "peaks"
def pushBack.expected := v["snowy", "peaks"]
#eval pushBack.actual == pushBack.expected -- true

-- Define a function Vect.reverse that reverses the order of a Vect.
#check @Vect.reverse
#eval (
  do
  for x in v[0, 1, 2].reverse do
    IO.println x
  : IO Unit
)

-- Define a function Vect.drop with the following type: (n : Nat) → Vect α (k + n) → Vect α k. Verify that it works by checking that #eval danishPeaks.drop 2 yields Vect.cons "Ejer Bavnehøj" (Vect.nil).
#check @Vect.drop
def drop.actual := denmarkPeaks.drop 2
def drop.expected := v["Ejer Bavnehøj"]
#eval drop.actual == drop.expected -- true

-- Define a function Vect.take with type (n : Nat) → Vect α (k + n) → Vect α n that returns the first n entries in the Vect. Check that it works on an example.
def take.actual := v['a', 'b', 'c'].take 2
def take.expected := v['a', 'b']
#eval take.actual == take.expected -- true

end exercises
