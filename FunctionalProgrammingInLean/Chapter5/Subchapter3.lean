module -- ch5.3

public section

/-
lawful applicative

1. It should respect identity, so `pure id <*> v = v`
2. It should respect function composition, so `pure (· ∘ ·) <*> u <*> v <*> w = u <*> (v <*> w)`
3. Sequencing pure operations should be a no-op, so `pure f <*> pure x = pure (f x)`
4. The ordering of pure operations doesn't matter, so `u <*> pure x = pure (λ f => f x) <*> u`
-/

#check (inferInstance : LawfulApplicative Option)

def x
  (v : Option α)
  : Option α :=
  Option.some id <*> v

def y
  (v : Option α)
  : Option α :=
  v

#eval x (some 4)

instance myLawfulApplicativeOption
  : LawfulApplicative Option where
  seqLeft_eq x y := by cases x <;> cases y <;> rfl
  seqRight_eq x y := by cases x <;> cases y <;> rfl
  pure_seq _ _ := rfl
  map_pure _ _ := by simp
  seq_pure g _ := by cases g <;> rfl
  seq_assoc x g h := by cases x <;> cases g <;> cases h <;> rfl
