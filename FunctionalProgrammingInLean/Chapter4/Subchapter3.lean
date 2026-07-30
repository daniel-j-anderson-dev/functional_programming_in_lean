module

inductive BinaryOperator Other where
  | add
  | sub
  | mul
  | other (x : Other)

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

def BinaryOperator.toFunction
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

inductive Expression α κ where
  | literal (x : α)
  | binaryOperator (kind : κ) (lhs rhs : Expression α κ)

def Expression.evaluateM
  [Monad m]
  [Add α] [Sub α] [Mul α] [Div α] [Zero α] [BEq α]
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

def applyEmpty
  [Monad m]
  (op : Empty) (_ _ : α)
  : m α :=
  nomatch op

#eval
  Expression.evaluateM
    (BinaryOperator.toFunction (applyOther := applyEmpty))
    (.binaryOperator .add (.literal 5) (.literal (-14)))
