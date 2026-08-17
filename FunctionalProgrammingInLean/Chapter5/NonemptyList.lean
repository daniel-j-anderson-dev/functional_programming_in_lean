module
public section

structure NonemptyList α where
  head : α
  tail : List α
deriving Repr

namespace NonemptyList

abbrev toList
  (self : NonemptyList α)
  : List α :=
  self.head :: self.tail

def append
  (lhs rhs : NonemptyList α)
  : NonemptyList α :=
  ⟨lhs.head, lhs.tail ++ rhs.toList⟩

instance coeFromNonemptyListToList :
  Coe (NonemptyList α) (List α) where
  coe := toList

instance Append
  : Append (NonemptyList α) where
  append lhs rhs := ⟨lhs.head, lhs.tail ++ rhs.toList⟩

end NonemptyList
