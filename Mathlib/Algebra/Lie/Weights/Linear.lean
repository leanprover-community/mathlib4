/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.Weights.Basic
import Mathlib.LinearAlgebra.Trace

/-!
# Lie modules with linear weights

Given a Lie module `M` over a nilpotent Lie algebra `L` with coefficients in `R`, one frequently
studies `M` via its weights. These are functions `χ : L → R` whose corresponding weight space
`LieModule.weightSpace M χ`, is non-trivial. If `L` is Abelian or if `R` has characteristic zero
(and `M` is finite-dimensional) then such `χ` are necessarily `R`-linear. However in general
non-linear weights do exists. For example if we take:
 * `R`: the field with two elements (or indeed any perfect field of characteristic two),
 * `L`: `sl₂` (this is nilpotent in characteristic two),
 * `M`: the natural two-dimensional representation of `L`,
then there is a single weight and it is non-linear. (See remark following Proposition 9 of
chapter VII, §1.3 in [N. Bourbaki, Chapters 7--9](bourbaki1975b).)

We thus introduce a typeclass `LieModule.LinearWeights` to encode the fact that a Lie module does
have linear weights and provide typeclass instances in the two important cases that `L` is Abelian
or `R` has characteristic zero.

## Main definitions
 * `LieModule.LinearWeights`: a typeclass encoding the fact that a given Lie module has linear
   weights.
 * `LieModule.instLinearWeightsOfCharZero`: a typeclass instance encoding the fact that for an
   Abelian Lie algebra, the weights of any Lie module are linear.
 * `LieModule.instLinearWeightsOfIsLieAbelian`: a typeclass instance encoding the fact that in
   characteristic zero, the weights of any finite-dimensional Lie module are linear.

-/

attribute [local instance]
  isNoetherian_of_isNoetherianRing_of_finite
  Module.free_of_finite_type_torsion_free'

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

namespace LieModule

/-- A typeclass encoding the fact that a given Lie module has linear weights. -/
class LinearWeights [LieAlgebra.IsNilpotent R L] : Prop :=
  map_add : ∀ χ : L → R, weightSpace M χ ≠ ⊥ → ∀ x y, χ (x + y) = χ x + χ y
  map_smul : ∀ χ : L → R, weightSpace M χ ≠ ⊥ → ∀ (t : R) x, χ (t • x) = t • χ x

/-- A weight of a Lie module, bundled as a linear map. -/
@[simps]
def linearWeight [LieAlgebra.IsNilpotent R L] [LinearWeights R L M]
    (χ : L → R) (hχ : weightSpace M χ ≠ ⊥) : L →ₗ[R] R where
  toFun := χ
  map_add' := LinearWeights.map_add χ hχ
  map_smul' := LinearWeights.map_smul χ hχ

/-- For an Abelian Lie algebra, the weights of any Lie module are linear. -/
instance instLinearWeightsOfIsLieAbelian [IsLieAbelian L] [NoZeroSMulDivisors R M] :
    LinearWeights R L M where
  map_add := by
    have h : ∀ x y, Commute (toEndomorphism R L M x) (toEndomorphism R L M y) := fun x y ↦ by
      rw [commute_iff_lie_eq, ← LieHom.map_lie, trivial_lie_zero, LieHom.map_zero]
    intro χ hχ x y
    simp_rw [Ne.def, ← LieSubmodule.coe_toSubmodule_eq_iff, weightSpace, weightSpaceOf,
      LieSubmodule.iInf_coe_toSubmodule, LieSubmodule.bot_coeSubmodule, Submodule.eta] at hχ
    exact Module.End.map_add_of_iInf_generalizedEigenspace_ne_bot_of_commute
      (toEndomorphism R L M).toLinearMap χ hχ h x y
  map_smul := by
    intro χ hχ t x
    simp_rw [Ne.def, ← LieSubmodule.coe_toSubmodule_eq_iff, weightSpace, weightSpaceOf,
      LieSubmodule.iInf_coe_toSubmodule, LieSubmodule.bot_coeSubmodule, Submodule.eta] at hχ
    exact Module.End.map_smul_of_iInf_generalizedEigenspace_ne_bot
      (toEndomorphism R L M).toLinearMap χ hχ t x

section FiniteDimensional

open FiniteDimensional

variable [IsDomain R] [IsPrincipalIdealRing R] [Module.Free R M] [Module.Finite R M]
  [LieAlgebra.IsNilpotent R L]

lemma trace_comp_toEndomorphism_weight_space_eq (χ : L → R) :
    LinearMap.trace R _ ∘ₗ (toEndomorphism R L (weightSpace M χ)).toLinearMap =
    finrank R (weightSpace M χ) • χ := by
  ext x
  let n := toEndomorphism R L (weightSpace M χ) x - χ x • LinearMap.id
  have h₁ : toEndomorphism R L (weightSpace M χ) x = n + χ x • LinearMap.id := eq_add_of_sub_eq rfl
  have h₂ : LinearMap.trace R _ n = 0 := IsReduced.eq_zero _ <|
    LinearMap.isNilpotent_trace_of_isNilpotent <| isNilpotent_toEndomorphism_sub_algebraMap M χ x
  rw [LinearMap.comp_apply, LieHom.coe_toLinearMap, h₁, map_add, h₂]
  simp [mul_comm (χ x)]

variable {R L M} in
lemma zero_lt_finrank_weightSpace {χ : L → R} (hχ : weightSpace M χ ≠ ⊥) :
    0 < finrank R (weightSpace M χ) := by
  rwa [← LieSubmodule.nontrivial_iff_ne_bot, ← rank_pos_iff_nontrivial (R := R), ← finrank_eq_rank,
    Nat.cast_pos] at hχ

/-- In characteristic zero, the weights of any finite-dimensional Lie module are linear. -/
instance instLinearWeightsOfCharZero [CharZero R] :
    LinearWeights R L M where
  map_add := fun χ hχ x y ↦ by
    rw [← smul_right_inj (zero_lt_finrank_weightSpace hχ).ne', smul_add, ← Pi.smul_apply,
      ← Pi.smul_apply, ← Pi.smul_apply, ← trace_comp_toEndomorphism_weight_space_eq, map_add]
  map_smul := fun χ hχ t x ↦ by
    rw [← smul_right_inj (zero_lt_finrank_weightSpace hχ).ne', smul_comm, ← Pi.smul_apply,
      ← Pi.smul_apply (finrank R _), ← trace_comp_toEndomorphism_weight_space_eq, map_smul]

end FiniteDimensional

end LieModule
