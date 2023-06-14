import Mathlib.Tactic.Variable?
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.LinearMap
import Mathlib.RingTheory.UniqueFactorizationDomain
import Std.Tactic.GuardMsgs

namespace Tests

-- Note about tests: these are just testing how `variable?` works, and for the algebra hierarchy
-- there is no guarantee that we are testing for the correct typeclass instances. Results
-- might have instances that somehow overlap (for example having multiple incompatible operations).

--set_option trace.variable? true

section
-- works like `variable`
/-- info: Try this: variable (x : Nat) [DecidableEq α] -/
#guard_msgs in
variable? (x : Nat) [DecidableEq α]

example : Nat := x
example : DecidableEq α := inferInstance
end

section
/-- info: Try this: variable [Semiring R] [AddCommMonoid M] [Module R M] -/
#guard_msgs in
variable? [Module R M]
example : Semiring R := inferInstance
example : AddCommMonoid M := inferInstance
example : Module R M := inferInstance
end

namespace foo
class A (α : Type)
class B (α : Type) [A α]
class C (α : Type) [A α] [B α]
/-- info: Try this: variable [A α] [B α] [C α] -/
#guard_msgs in
variable? [C α]

/-- info: Try this: variable [(α : Type) → A α] [(α : Type) → B α] [(α : Type) → C α] -/
#guard_msgs in
variable? [(α : Type) → C α]

end foo

section
-- Example of some bad instances (TODO?)
-- There are two different add operations on `A`.
-- See also the next test.
/--
info: Try this: variable [Semiring R] [AddCommMonoid A] [Module R A] [CommSemiring S] [Semiring A] [Algebra S A]
-/
#guard_msgs in
variable? [Module R A] [Algebra S A]
end

section
-- Similar to the previous test, but this time there is only a single add operation on `A`.
/--
info: Try this: variable [CommSemiring S] [Semiring A] [Algebra S A] [Semiring R] [Module R A]
-/
#guard_msgs in
variable? [Algebra S A] [Module R A]
end

section
/--
info: Try this: variable (f : Nat → Type) [Semiring R] [(i : ℕ) → AddCommMonoid (f i)] [∀ i, Module R (f i)]
-/
#guard_msgs in
variable? (f : Nat → Type) [∀ i, Module R (f i)]
example : ∀ i, AddCommMonoid (f i) := inferInstance
end

section
/--
warning: Instance argument can be inferred from earlier arguments.
f : ℕ → Type
inst✝ : (i : ℕ) → AddCommMonoid (f i)
⊢ (i : ℕ) → Module ℕ (f i)
---
info: Try this: variable (f : Nat → Type) [(i : ℕ) → AddCommMonoid (f i)]
-/
#guard_msgs in
variable? (f : Nat → Type) [∀ i, Module Nat (f i)]
-- Warning since [(i : ℕ) → AddCommMonoid (f i)] is sufficient
end

section
/-- info: Try this: variable [CommSemiring k] [Semiring V] [Algebra k V] -/
#guard_msgs in
variable? [Algebra k V]
end

section
-- Checking that `Algebra` doesn't introduce its own `CommSemiring k`.
/-- info: Try this: variable [Field k] [Semiring A] [Algebra k A] -/
#guard_msgs in
variable? [Field k] [Algebra k A]
example : (inferInstance : Field k).toCommSemiring = (inferInstance : CommSemiring k) := rfl
end

/-- Alias for introducing a vector space using `variable?`. -/
@[variable_alias]
structure VectorSpace (k V : Type _) [Field k] [AddCommGroup V] [Module k V]

section
/-- info: Try this: variable [Field R] [AddCommGroup M] [Module R M] -/
#guard_msgs in
variable? [VectorSpace R M]
example : Field R := inferInstance
example : AddCommGroup M := inferInstance
example : Module R M := inferInstance
end

section
/-- info: Try this: variable [Field k] [AddCommGroup V] [Module k V] [Semiring V] [Algebra k V] -/
#guard_msgs in
variable? [VectorSpace k V] [Algebra k V]
example : Field k := inferInstance
example : AddCommGroup V := inferInstance
example : Module k V := inferInstance
example : Semiring V := inferInstance
example : Algebra k V := inferInstance

end

/-- `variable?` alias for a representation of an algebra over a field. -/
@[variable_alias]
structure Rep (k A V : Type _)
  [Field k] [AddCommGroup A] [Ring A] [Algebra k A] [AddCommGroup V] [Module k V]
  [DistribMulAction A V] [SMulCommClass k A V]

section
/--
info: Try this: variable [Field k] [AddCommGroup A] [Ring A] [Algebra k A] [AddCommGroup V] [Module k V]
  [DistribMulAction A V] [SMulCommClass k A V]
-/
#guard_msgs in
variable? [Rep k A V]
end

section
/--
info: Try this: variable [Field k] [AddCommGroup A] [Module k A] [Ring A] [Algebra k A] [AddCommGroup V] [Module k V]
  [DistribMulAction A V] [SMulCommClass k A V]
-/
#guard_msgs in
variable? [VectorSpace k A] [Rep k A V]
end

section
-- This fails due to requiring `Module k A` with two different sets of instance arguments
-- variable? [Rep k A V] [VectorSpace k A]
end

@[variable_alias]
structure UniqueFactorizationDomain (R : Type _)
  [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]

section
/-- info: Try this: variable [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] -/
#guard_msgs in
variable? [UniqueFactorizationDomain R]
end

end Tests
