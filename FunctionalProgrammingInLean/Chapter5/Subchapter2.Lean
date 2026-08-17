module -- ch5.2

public import FunctionalProgrammingInLean.Chapter5.NonemptyList

public section

structure RawInput where
  name : String
  birthYear : String
deriving Repr
#check RawInput
#print RawInput

/-
1. The name may not be empty
2. The birth year must be numeric and non-negative
3. The birth year must be greater than 1900, and less than or equal to the year in which the form is validated
-/

#print Subtype
#check Subtype

abbrev FastPos : Type := {x : Nat // 0 < x}
#print FastPos
#check FastPos

def one : FastPos := ⟨1, by decide⟩
#print one
#check one

#check LT

theorem succ_greater_than_zero
  (n : Nat)
  : 0 < n + 1 :=
  match n with
  | 0 => Nat.le.refl
  | k + 1 =>
    let inductiveHypothesis := succ_greater_than_zero k
    Nat.le.step inductiveHypothesis

instance FastPos.OfNat
  : OfNat FastPos (n + 1) where
  ofNat := ⟨n + 1, succ_greater_than_zero n⟩

def Nat.toFastPos?
  (n : Nat)
  : Option FastPos :=
  if h : n > 0 then
    some ⟨n, h⟩
  else
    none

structure CheckedInput (thisYear : Nat) where
  name : {n : String // n ≠ ""}
  birthYear : {y : Nat // 1900 < y ∧ y ≤ thisYear}
  deriving Repr

inductive Validate -- FunctionalProgrammingInLean.Chapter5.Subchapter2 (Validate)
  (ε : Type u) (α : Type v)
  : Type (max u v) where
  | ok (x : α)
  | errors (es : ε)
deriving Repr

namespace Validate

def map
  (f : α → β) (self : Validate ε α)
  : Validate ε β :=
  match self with
  | .ok x => .ok (f x)
  | .errors es => .errors es

def pure
  (x : α)
  : Validate ε α :=
  .ok x

def throw
  (e : ε)
  : Validate ε α :=
  .errors e

def sequence
  {α : Type u} {β : Type v} {ε : Type w}
  [Append ε]
  (f : Validate ε (α → β)) (makeSelf : (Unit → Validate ε α))
  : Validate ε β :=
  match f with
  | .ok g => (makeSelf ()).map g
  | .errors fErr =>
    match makeSelf () with
    | .ok _ => .errors fErr
    | .errors selfErr => .errors (fErr ++ selfErr)

def andThen
  (current : Validate ε α) (next : α → Validate ε β)
  : Validate ε β :=
  match current with
  | .ok x => next x
  | .errors es => .errors es

protected instance Functor
  : Functor (Validate ε) where
  map := map

protected instance Pure
  : Pure (Validate ε) where
  pure := pure

protected instance Seq
  [Append ε]
  : Seq (Validate ε) where
  seq := sequence

protected instance SeqRight
  [Append ε]
  : SeqRight (Validate ε) where
  seqRight a b := pure (λ _ x => x) <*> a <*> b ()

end Validate

def checkNameNonempty
  (name : String) (err : Unit → ε)
  : Validate ε {n : String // n ≠ ""} :=
  if h : name ≠ "" then
    .ok ⟨name, h⟩
  else
    .errors (err ())

def checkYearIsNat
  (year : String)  (err : Unit → ε)
  : Validate ε Nat :=
  if let .some x := year.trimAscii.toNat? then
    .ok x
  else
    .errors (err ())

def checkBirthYear
  (thisYear year : Nat) (tooLowErr : Unit → ε) (tooHighErr : Unit → ε)
  : Validate ε {y : Nat // 1900 < y ∧ y ≤ thisYear} :=
  if h₀ : 1900 < year then
    if h₁ : year ≤ thisYear then
      .ok ⟨year, ⟨h₀, h₁⟩⟩
    else
      .errors (tooHighErr ())
  else
    .errors (tooLowErr ())

def checkInput
  (thisYear : Nat) (input : RawInput)
  : Validate (List String) (CheckedInput thisYear) :=
  let x := pure CheckedInput.mk
    <*> checkNameNonempty input.name (λ _ => ["name must not be empty"])
    <*> (checkYearIsNat input.birthYear (λ _ => ["birth year must be a natural number"])).andThen
      (checkBirthYear
        thisYear
        (tooLowErr := λ _ => ["birth year must be above 1900"])
        (tooHighErr := λ _ => [s!"birth year must be below {thisYear}"]))
  -- let y := CheckedInput.mk
  --   <$> checkName input.name (λ _ => ["name must not be empty"])
  --   <*> (checkYearIsNat input.birthYear (λ _ => ["birth year must be a natural number"])).andThen
  --     (
  --       checkBirthYear
  --       thisYear
  --       (tooLowErr := λ _ => ["birth year must be above 1900"])
  --       (tooHighErr := λ _ => [s!"birth year must be below {thisYear}"])
  --     )
  -- let z := Validate.sequence
  --   (
  --     Validate.sequence
  --       (pure CheckedInput.mk)
  --       λ _ => checkName input.name (λ _ => ["name must not be empty"])
  --   )
  --   λ _ => (checkYearIsNat input.birthYear (λ _ => ["birth year must be a natural number"])).andThen
  --     (checkBirthYear
  --       thisYear
  --       (tooLowErr := λ _ => ["birth year must be above 1900"])
  --       (tooHighErr := λ _ => [s!"birth year must be below {thisYear}"]))
  x

#eval checkInput 2023 {name := "David", birthYear := "1984"}
#eval checkInput 2023 {name := "", birthYear := "2045"}
#eval checkInput 2023 {name := "David", birthYear := "2045"}
#eval checkInput 2023 {name := "David", birthYear := "syzygy"}

abbrev x : Applicative Option := inferInstance

-- #check x.
