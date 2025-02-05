import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Dual
import Mathlib.LinearAlgebra.Contraction
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RepresentationTheory.Basic

/-!
# Predicates for representation theory

We define `IsRepresentation`, a Prop for an AddCommMonoid `V` with actions of `G` and `k`.

-/


open MonoidAlgebra (lift of)

open LinearMap

section

variable (k G V : Type*) [CommSemiring k] [Nontrivial k] [Group G] [AddCommMonoid V] [Module k V]
  [DistribMulAction G V]

abbrev IsRepresentation : Prop := SMulCommClass k G V

variable (ρ : IsRepresentation k G V)

end

namespace IsRepresentation

section trivial

universe u

variable (k : Type u) {G V : Type u} [CommSemiring k] [Nontrivial k] [Group G] [AddCommMonoid V]
  [Module k V] [DistribMulAction G V]

#synth DistribMulAction kˣ V -- Units.instDistribMulAction

instance : DistribMulAction G V where
  smul := (. • .)
  one_smul b := one_smul G b
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry

variable (ρ : Representation k G V)

#check SMulZeroClass
#print DistribSMul

/-- The trivial representation of `G` on a `k`-module V.
-/
def IsTrivial (ρ : Representation k G V) : Prop := ∀ (g : G), ∀ (v : V), g • v = v

-- Porting note: why is `V` implicit
theorem trivial_def (g : G) (v : V) : Representation.trivial k (V := V) g v = v :=
  rfl

variable {k}

-- TODO find message to Oliver saying what the problem was.

/-- A predicate for representations that fix every element. -/
class IsTrivial (ρ : Representation k G V) : Prop where
  out : ∀ g x, ρ g x = x := by aesop

instance : IsTrivial (trivial k (G := G) (V := V)) where
#exit
