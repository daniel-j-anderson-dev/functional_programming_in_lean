module

inductive BinaryOperator Other where
  | add
  | sub
  | mul
  | other (x : Other)

namespace BinaryOperator

def toFunction
  [Monad m] [Add α] [Sub α] [Mul α] [Div α]
  (applyOther : Other → α → α → m α)
  (binOp : BinaryOperator Other)
  : α → α → m α :=
  let lift f x y := pure (f x y)
  match binOp with
  | .add => lift Add.add
  | .sub => lift Sub.sub
  | .mul => lift Mul.mul
  | .other x => applyOther x

end BinaryOperator

inductive Expression α κ where
  | literal (x : α)
  | binaryOperator (kind : κ) (lhs rhs : Expression α κ)

namespace Expression

def evaluateM
  [Monad m]
  (getBinOp : κ → α → α → m α)
  (expr : Expression α κ)
  : m α :=
  match expr with
  | .literal x => pure x
  | binaryOperator kind lhs rhs => do
    let lhs' ← lhs.evaluateM getBinOp
    let rhs' ← rhs.evaluateM getBinOp
    let output ← getBinOp kind lhs' rhs'
    pure output

end Expression

def applyEmpty
  [Monad m]
  (op : Empty) (_ _ : α)
  : m α :=
  nomatch op

def Expression.evaluateOtherEmpty
  [Monad m]
  [Add α] [Sub α] [Mul α] [Div α] [Zero α] [BEq α]
  : Expression α (BinaryOperator Empty) → m α :=
  Expression.evaluateM (BinaryOperator.toFunction (nomatch ·))

#eval
  Expression.evaluateM
    (BinaryOperator.toFunction (applyOther := applyEmpty))
    (.binaryOperator .add (.literal 5) (.literal (-14)))

inductive CanFail where
  | div

structure DivideByZero

def divM
  [Monad m] [Div α] [BEq α] [Zero α]
  (failure : m α)
  (n d : α)
  : m α :=
  if d == 0 then failure else pure (n / d)

def div?
  [Div α] [BEq α] [Zero α]
  : α → α → Option α :=
  divM .none

def div!
  [Div α] [BEq α] [Zero α]
  : α → α → Except DivideByZero α :=
  divM (.error ⟨⟩)

namespace nondeterministic_search

inductive LazyList (α : Type u) where
  | nil
  | cons (current : α) (next : Unit → LazyList α)

namespace LazyList

def singleton (x : α) : LazyList α := .cons x λ () => .nil

def union
  (lhs rhs : LazyList α)
  : LazyList α :=
  match lhs with
  | .nil => rhs
  | .cons lhsElement getNextLhsElement =>
    .cons lhsElement λ _ => union (getNextLhsElement ()) rhs

def fromList
  (xs : List α)
  : LazyList α :=
  match xs with
  | [] => .nil
  | head :: tail => .cons head λ _ => fromList tail

def take
  (n : Nat)
  (self : LazyList α)
  : List α :=
  match n, self with
  | 0 , _ | _ + 1, .nil => []
  | nPred + 1, .cons current next => current :: (next ()).take nPred

def takeAll
  (self : LazyList α)
  : List α :=
  match self with
  | .nil => []
  | .cons current next => current :: (next ()).takeAll

def flatMap
  (self : LazyList α)
  (f : α → LazyList β)
  : LazyList β :=
  match self with
  | .nil => .nil
  | .cons current next => (f current).union (flatMap (next ()) f)

instance
  : Monad LazyList where
  pure := singleton
  bind := flatMap

end LazyList

def addsTo
  [BEq  α] [LT α] [DecidableLT α] [Zero α] [Sub α]
  (goal : α) (xs : List α)
  : LazyList (List α) :=
  match xs with
  | [] => if goal == 0 then pure [] else .nil
  | head :: tail =>
    let withoutHead := addsTo goal tail
    if head > goal then
      withoutHead
    else
      let withHead := do
        let sub ← addsTo (goal - head) tail
        pure (head :: sub)
      withoutHead.union withHead

#eval
  let solutions := (addsTo 15 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]).takeAll
  for solution in solutions do
    IO.println solution

inductive DivOrChoose where
  | div
  | choose

namespace DivOrChoose

def toFunction
  [Div α] [BEq α] [Zero α]
  (self : DivOrChoose)
  (lhs rhs : α)
  : LazyList α :=
  match self with
  | .div => divM .nil lhs rhs
  | .choose => .fromList [lhs, rhs]

end DivOrChoose

#eval
  (Expression.evaluateM
    (BinaryOperator.toFunction DivOrChoose.toFunction)
    (.binaryOperator
      .add
      (.literal 1)
      (.binaryOperator
        (.other .choose)
        (.literal 2)
        (.literal 5)
  ))).takeAll

#eval
  (Expression.evaluateM
    (BinaryOperator.toFunction DivOrChoose.toFunction)
    (.binaryOperator
      .add
      (.literal 1)
      (.binaryOperator
       (.other .div)
       (.literal 2)
       (.literal 0)
  ))).takeAll

#eval
  (Expression.evaluateM
    (BinaryOperator.toFunction DivOrChoose.toFunction)
    (.binaryOperator
      (.other .div)
      (.literal 90)
      (.binaryOperator
        .add
        (.binaryOperator
          (.other .choose)
          (.literal (-5))
          (.literal 5)
        )
        (.literal 5)
  ))).takeAll

end nondeterministic_search
