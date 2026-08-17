module

public import FunctionalProgrammingInLean.Chapter5.Subchapter2
public import FunctionalProgrammingInLean.Chapter4.Subchapter3

open nondeterministic_search

public section

abbrev NonemptyString := {s // s ≠ ""}

inductive LegacyCheckedInput where
  | humanBefore1970
    (birthYear : {y // 999 < y ∧ y < 1970})
    (name : String)

  | humanAfter1970
    (birthYear : {y // 1970 < y})
    (name : NonemptyString)

  | company
    (name : NonemptyString)
deriving Repr

def Validate.orElse
  [Append ε]
  (a : Validate ε α)
  (b : Unit → Validate ε α)
  : Validate ε α :=
  match a with
  | .ok a' => .ok a'
  | .errors e₀ =>
    match b () with
    | .ok b' => .ok b'
    | .errors e₁ => .errors (e₀ ++ e₁)

instance Validate.OrElse
  [Append ε]
  : OrElse (Validate ε α) where
  orElse := Validate.orElse

def checkThat
  (condition : Bool) (err : ε)
  : Validate ε Unit :=
  if condition then
    pure ()
  else
    .errors err

def checkCompany
  (input : RawInput)
  : Validate (List String) LegacyCheckedInput :=
  checkThat (input.birthYear == "FIRM") ["birth year must be FIRM if a company"]
     *> pure .company
    <*> checkNameNonempty input.name (λ _ => ["name must be non empty"])

  -- (checkThat (input.birthYear == "FIRM") "birth year must FIRM if a company")
  --    *> pure .company
  --   <*> checkNameNonempty input.name

  -- pure (λ () name => .company name)
  --   <*> checkThat (input.birthYear == "FIRM") "birth year must FIRM if a company"
  --   <*> checkNameNonempty input.name

def checkSubtype
  {α : Type u}
  (v : α) (p : α → Prop)
  [d : Decidable (p v)]
  (err : Unit → ε)
  : Validate ε {x : α // p x} :=
  if h : p v then
    pure ⟨v, h⟩
  else
    .errors (err ())

abbrev exclusiveRange
  (low high : Nat)
  (n : Nat)
  : Prop :=
  low < n ∧ n < high

def checkHumanBefore1970
  (input : RawInput)
  : Validate (List String) LegacyCheckedInput :=
  (checkYearIsNat input.birthYear (λ _ => ["birth year must be a natural number"])
  ).andThen λ birthYear =>
    .humanBefore1970
      <$> checkSubtype birthYear (exclusiveRange 999 1970) (λ _ => ["birth year must be between 999 < y < 1970"])
      <*> pure input.name

def checkHumanAfter1970
  (input : RawInput)
  : Validate (List String) LegacyCheckedInput :=
  (checkYearIsNat input.birthYear (λ _ => ["birth year must be a natural number"])
  ).andThen λ birthYear =>
    .humanAfter1970
      <$> checkSubtype birthYear (1970 < ·) (λ _ => ["birth year must be greater than 1970"])
      <*> checkNameNonempty input.name (λ _ => ["name must be non empty"])

def checkLegacyInput
  (input : RawInput)
  : Validate (List String) LegacyCheckedInput :=
  checkCompany input <|>
  checkHumanBefore1970 input <|>
  checkHumanAfter1970 input

#eval checkLegacyInput ⟨"Johnny's Troll Groomers", "FIRM"⟩
#eval checkLegacyInput ⟨"Johnny", "1963"⟩
#eval checkLegacyInput ⟨"", "1963"⟩
#eval checkLegacyInput ⟨"swag", "1971"⟩
#eval checkLegacyInput ⟨"", "1970"⟩

-- the Alternative class
#check Option.orElse

instance
  : Alternative Option where
  failure := .none
  orElse x f :=
    match x with
    | .some x => .some x
    | .none => f ()

def LazyList.orElse
  (as : LazyList α)
  (f : Unit → LazyList α)
  : sorry :=
  sorry
