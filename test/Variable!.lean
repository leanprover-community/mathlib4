import Mathlib.Tactic.Variable!
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.LinearMap
import Mathlib.RingTheory.UniqueFactorizationDomain

namespace Tests

--set_option trace.variable! true

section
variable! (x : Nat) [DecidableEq α] -- works like `variable`

example : Nat := x
example : DecidableEq α := inferInstance
end

section
variable! [Module R M]
example : Semiring R := inferInstance
example : AddCommMonoid M := inferInstance
example : Module R M := inferInstance
end

namespace foo
class A (α : Type)
class B (α : Type) [A α]
class C (α : Type) [A α] [B α]
-- Try this: variable [A α] [B α] [C α]
variable!? [C α]

-- Try this: variable [(α : Type) → A α] [(α : Type) → B α] [(α : Type) → C α]
variable!? [(α : Type) → C α]

end foo


section
variable! (f : Nat → Type) [∀ i, Module R (f i)]
example : ∀ i, AddCommMonoid (f i) := inferInstance
end

section
variable! (f : Nat → Type) [∀ i, Module Nat (f i)]
-- Warning since [(i : ℕ) → AddCommMonoid (f i)] is sufficient
end

section
-- Checking that `Algebra` doesn't introduce its own `CommSemiring k`.
variable!? [Field k] [Algebra k A]
example : (inferInstance : Field k).toCommSemiring = (inferInstance : CommSemiring k) := rfl
end

/-- Alias for introducing a vector space using `variable!`. -/
@[variable_alias]
structure VectorSpace (k V : Type _) [Field k] [AddCommGroup V] [Module k V]

section
variable! [VectorSpace R M]
example : Field R := inferInstance
example : AddCommGroup M := inferInstance
example : Module R M := inferInstance
end

section
variable!? [VectorSpace k V] [Algebra k V]
example : Field k := inferInstance
example : AddCommGroup V := inferInstance
example : Module k V := inferInstance
example : Semiring V := inferInstance
example : Algebra k V := inferInstance

end

/-- `variable!` alias for a representation of an algebra over a field. -/
@[variable_alias]
structure Rep (k A V : Type _)
  [Field k] [AddCommGroup A] [Ring A] [Algebra k A] [AddCommGroup V] [Module k V]
  [DistribMulAction A V] [SMulCommClass k A V]

section
variable!? [Rep k A V]
-- Try this: variable [Field k] [AddCommGroup A] [Ring A] [Algebra k A] [AddCommGroup V]
--  [Module k V] [DistribMulAction A V] [SMulCommClass k A V]
end

section
variable!? [VectorSpace k A] [Rep k A V]
end

section
-- variable!? [Rep k A V] [VectorSpace k A]
-- This fails due to requiring `Module k A` with two different sets of instance arguments
end

@[variable_alias]
structure UniqueFactorizationDomain (R : Type _)
  [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]

section
variable!? [UniqueFactorizationDomain R]
end

end Tests
