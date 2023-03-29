import Mathlib.Tactic.Variable!
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.LinearMap
import Mathlib.RingTheory.UniqueFactorizationDomain

namespace Tests

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

section
-- Checking that `Algebra` doesn't introduce its own `CommSemiring k`.
variable! [Field k] [Algebra k A]
example : (inferInstance : Field k).toCommSemiring = (inferInstance : CommSemiring k) := rfl
end

/-- Alias for introducing a vector space using `variable!`. -/
@[variable_alias]
structure VectorSpace (k V : Type _)
  [Field k] [AddCommGroup V] [Module k V]

section
variable! [VectorSpace R M]
example : Field R := inferInstance
example : AddCommGroup M := inferInstance
example : Module R M := inferInstance
end

section -- TODO fix bug
variable! (k A V : Type _) [Algebra k V] [VectorSpace k V]
--example : Field k := inferInstance
--example : AddCommGroup V := inferInstance

--@[variable_alias]
--structure Rep [DistribMulAction A V] [SMulCommClass k A V]

end

@[variable_alias]
structure UniqueFactorizationDomain (R : Type _) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]

section
variable! [UniqueFactorizationDomain R]

end

section
variable! (k A V : Type _) [Algebra k A] [VectorSpace k V]

@[variable_alias]
structure Rep [DistribMulAction A V] [SMulCommClass k A V]

end

section
variable! [VectorSpace k A] [Rep k A V]
/-
k: Type ?u.53770
A: Type ?u.53773
V: Type ?u.54316
inst✝⁷: Field k
inst✝⁶: AddCommGroup A
inst✝⁵: Module k A
inst✝⁴: Semiring A
inst✝³: AddCommGroup V
inst✝²: Module k V
inst✝¹: DistribMulAction A V
inst✝: SMulCommClass k A V
-/
end

end Tests
