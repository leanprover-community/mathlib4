import Mathlib.Data.Finset.Fin

open Nat

/-- `Fintype α` means that `α` is finite, i.e. there are only
  finitely many distinct elements of type `α`. The evidence of this
  is a finset `elems` (a list up to permutation without duplicates),
  together with a proof that everything of type `α` is in the list. -/
class Fintype (α : Type u) :=
  elems : Finset α
  complete : ∀ x : α, x ∈ elems

namespace Fintype

instance (n : ℕ) : Fintype (Fin n) :=
⟨Finset.finRange n, Finset.mem_finRange⟩

end Fintype
