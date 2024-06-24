/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.Weights.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Lie modules with linear weights

Given a Lie module `M` over a nilpotent Lie algebra `L` with coefficients in `R`, one frequently
studies `M` via its weights. These are functions `χ : L → R` whose corresponding weight space
`LieModule.weightSpace M χ`, is non-trivial. If `L` is Abelian or if `R` has characteristic zero
(and `M` is finite-dimensional) then such `χ` are necessarily `R`-linear. However in general
non-linear weights do exist. For example if we take:
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
   weights, and furthermore that the weights vanish on the derived ideal.
 * `LieModule.instLinearWeightsOfCharZero`: a typeclass instance encoding the fact that for an
   Abelian Lie algebra, the weights of any Lie module are linear.
 * `LieModule.instLinearWeightsOfIsLieAbelian`: a typeclass instance encoding the fact that in
   characteristic zero, the weights of any finite-dimensional Lie module are linear.
 * `LieModule.exists_forall_lie_eq_smul`: existence of simultaneous
   eigenvectors from existence of simultaneous generalized eigenvectors for Noetherian Lie modules
   with linear weights.

-/

open Set

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

namespace LieModule

/-- A typeclass encoding the fact that a given Lie module has linear weights, vanishing on the
derived ideal. -/
class LinearWeights [LieAlgebra.IsNilpotent R L] : Prop :=
  map_add : ∀ χ : L → R, weightSpace M χ ≠ ⊥ → ∀ x y, χ (x + y) = χ x + χ y
  map_smul : ∀ χ : L → R, weightSpace M χ ≠ ⊥ → ∀ (t : R) x, χ (t • x) = t • χ x
  map_lie : ∀ χ : L → R, weightSpace M χ ≠ ⊥ → ∀ x y : L, χ ⁅x, y⁆ = 0

namespace Weight

variable [LieAlgebra.IsNilpotent R L] [LinearWeights R L M]
    [NoZeroSMulDivisors R M] [IsNoetherian R M] (χ : Weight R L M)

/-- A weight of a Lie module, bundled as a linear map. -/
@[simps]
def toLinear : L →ₗ[R] R where
  toFun := χ
  map_add' := LinearWeights.map_add χ χ.weightSpace_ne_bot
  map_smul' := LinearWeights.map_smul χ χ.weightSpace_ne_bot

instance instCoeLinearMap : CoeOut (Weight R L M) (L →ₗ[R] R) where
  coe := Weight.toLinear R L M

instance instLinearMapClass : LinearMapClass (Weight R L M) R L R where
  map_add χ := LinearWeights.map_add χ χ.weightSpace_ne_bot
  map_smulₛₗ χ := LinearWeights.map_smul χ χ.weightSpace_ne_bot

variable {R L M χ}

@[simp]
lemma apply_lie (x y : L) :
    χ ⁅x, y⁆ = 0 :=
  LinearWeights.map_lie χ χ.weightSpace_ne_bot x y

@[simp] lemma coe_coe : (↑(χ : L →ₗ[R] R) : L → R) = (χ : L → R) := rfl

@[simp] lemma coe_toLinear_eq_zero_iff : (χ : L →ₗ[R] R) = 0 ↔ χ.IsZero :=
  ⟨fun h ↦ funext fun x ↦ LinearMap.congr_fun h x, fun h ↦ by ext; simp [h.eq]⟩

lemma coe_toLinear_ne_zero_iff : (χ : L →ₗ[R] R) ≠ 0 ↔ χ.IsNonZero := by simp

/-- The kernel of a weight of a Lie module with linear weights. -/
abbrev ker := LinearMap.ker (χ : L →ₗ[R] R)

end Weight

/-- For an Abelian Lie algebra, the weights of any Lie module are linear. -/
instance instLinearWeightsOfIsLieAbelian [IsLieAbelian L] [NoZeroSMulDivisors R M] :
    LinearWeights R L M :=
  have aux : ∀ (χ : L → R), weightSpace M χ ≠ ⊥ → ∀ (x y : L), χ (x + y) = χ x + χ y := by
    have h : ∀ x y, Commute (toEnd R L M x) (toEnd R L M y) := fun x y ↦ by
      rw [commute_iff_lie_eq, ← LieHom.map_lie, trivial_lie_zero, LieHom.map_zero]
    intro χ hχ x y
    simp_rw [Ne, ← LieSubmodule.coe_toSubmodule_eq_iff, weightSpace, weightSpaceOf,
      LieSubmodule.iInf_coe_toSubmodule, LieSubmodule.bot_coeSubmodule] at hχ
    exact Module.End.map_add_of_iInf_genEigenspace_ne_bot_of_commute
      (toEnd R L M).toLinearMap χ hχ h x y
  { map_add := aux
    map_smul := fun χ hχ t x ↦ by
      simp_rw [Ne, ← LieSubmodule.coe_toSubmodule_eq_iff, weightSpace, weightSpaceOf,
        LieSubmodule.iInf_coe_toSubmodule, LieSubmodule.bot_coeSubmodule] at hχ
      exact Module.End.map_smul_of_iInf_genEigenspace_ne_bot
        (toEnd R L M).toLinearMap χ hχ t x
    map_lie := fun χ hχ t x ↦ by
      rw [trivial_lie_zero, ← add_left_inj (χ 0), ← aux χ hχ, zero_add, zero_add] }

section FiniteDimensional

open FiniteDimensional

variable [IsDomain R] [IsPrincipalIdealRing R] [Module.Free R M] [Module.Finite R M]
  [LieAlgebra.IsNilpotent R L]

lemma trace_comp_toEnd_weightSpace_eq (χ : L → R) :
    LinearMap.trace R _ ∘ₗ (toEnd R L (weightSpace M χ)).toLinearMap =
    finrank R (weightSpace M χ) • χ := by
  ext x
  let n := toEnd R L (weightSpace M χ) x - χ x • LinearMap.id
  have h₁ : toEnd R L (weightSpace M χ) x = n + χ x • LinearMap.id := eq_add_of_sub_eq rfl
  have h₂ : LinearMap.trace R _ n = 0 := IsReduced.eq_zero _ <|
    LinearMap.isNilpotent_trace_of_isNilpotent <| isNilpotent_toEnd_sub_algebraMap M χ x
  rw [LinearMap.comp_apply, LieHom.coe_toLinearMap, h₁, map_add, h₂]
  simp [mul_comm (χ x)]

@[deprecated (since := "2024-04-06")]
alias trace_comp_toEnd_weight_space_eq := trace_comp_toEnd_weightSpace_eq

variable {R L M} in
lemma zero_lt_finrank_weightSpace {χ : L → R} (hχ : weightSpace M χ ≠ ⊥) :
    0 < finrank R (weightSpace M χ) := by
  rwa [← LieSubmodule.nontrivial_iff_ne_bot, ← rank_pos_iff_nontrivial (R := R), ← finrank_eq_rank,
    Nat.cast_pos] at hχ

/-- In characteristic zero, the weights of any finite-dimensional Lie module are linear and vanish
on the derived ideal. -/
instance instLinearWeightsOfCharZero [CharZero R] :
    LinearWeights R L M where
  map_add χ hχ x y := by
    rw [← smul_right_inj (zero_lt_finrank_weightSpace hχ).ne', smul_add, ← Pi.smul_apply,
      ← Pi.smul_apply, ← Pi.smul_apply, ← trace_comp_toEnd_weightSpace_eq, map_add]
  map_smul χ hχ t x := by
    rw [← smul_right_inj (zero_lt_finrank_weightSpace hχ).ne', smul_comm, ← Pi.smul_apply,
      ← Pi.smul_apply (finrank R _), ← trace_comp_toEnd_weightSpace_eq, map_smul]
  map_lie χ hχ x y := by
    rw [← smul_right_inj (zero_lt_finrank_weightSpace hχ).ne', nsmul_zero, ← Pi.smul_apply,
      ← trace_comp_toEnd_weightSpace_eq, LinearMap.comp_apply, LieHom.coe_toLinearMap,
      LieHom.map_lie, Ring.lie_def, map_sub, LinearMap.trace_mul_comm, sub_self]

end FiniteDimensional

variable [LieAlgebra.IsNilpotent R L] [LinearWeights R L M] (χ : L → R)

/-- A type synonym for the `χ`-weight space but with the action of `x : L` on `m : weightSpace M χ`,
shifted to act as `⁅x, m⁆ - χ x • m`. -/
def shiftedWeightSpace := weightSpace M χ

namespace shiftedWeightSpace

private lemma aux [h : Nontrivial (shiftedWeightSpace R L M χ)] : weightSpace M χ ≠ ⊥ :=
  (LieSubmodule.nontrivial_iff_ne_bot _ _ _).mp h

instance : LieRingModule L (shiftedWeightSpace R L M χ) where
  bracket x m := ⁅x, m⁆ - χ x • m
  add_lie x y m := by
    nontriviality shiftedWeightSpace R L M χ
    simp only [add_lie, LinearWeights.map_add χ (aux R L M χ), add_smul]
    abel
  lie_add x m n := by
    nontriviality shiftedWeightSpace R L M χ
    simp only [lie_add, LinearWeights.map_add χ (aux R L M χ), smul_add]
    abel
  leibniz_lie x y m := by
    nontriviality shiftedWeightSpace R L M χ
    simp only [lie_sub, lie_smul, lie_lie, LinearWeights.map_lie χ (aux R L M χ), zero_smul,
      sub_zero, smul_sub, smul_comm (χ x)]
    abel

@[simp] lemma coe_lie_shiftedWeightSpace_apply (x : L) (m : shiftedWeightSpace R L M χ) :
    ⁅x, m⁆ = ⁅x, (m : M)⁆ - χ x • m :=
  rfl

instance : LieModule R L (shiftedWeightSpace R L M χ) where
  smul_lie t x m := by
    nontriviality shiftedWeightSpace R L M χ
    apply Subtype.ext
    simp only [coe_lie_shiftedWeightSpace_apply, smul_lie, LinearWeights.map_smul χ (aux R L M χ),
      SetLike.val_smul, smul_sub, sub_right_inj, smul_assoc t]
  lie_smul t x m := by
    nontriviality shiftedWeightSpace R L M χ
    apply Subtype.ext
    simp only [coe_lie_shiftedWeightSpace_apply, lie_smul, LinearWeights.map_smul χ (aux R L M χ),
      SetLike.val_smul, smul_sub, sub_right_inj, smul_comm t]

/-- Forgetting the action of `L`, the spaces `weightSpace M χ` and `shiftedWeightSpace R L M χ` are
equivalent. -/
@[simps!] def shift : weightSpace M χ ≃ₗ[R] shiftedWeightSpace R L M χ := LinearEquiv.refl R _

lemma toEnd_eq (x : L) :
    toEnd R L (shiftedWeightSpace R L M χ) x =
    (shift R L M χ).conj (toEnd R L (weightSpace M χ) x - χ x • LinearMap.id) := by
  ext; simp [LinearEquiv.conj_apply]

/-- By Engel's theorem, if `M` is Noetherian, the shifted action `⁅x, m⁆ - χ x • m` makes the
`χ`-weight space into a nilpotent Lie module. -/
instance [IsNoetherian R M] : IsNilpotent R L (shiftedWeightSpace R L M χ) :=
  LieModule.isNilpotent_iff_forall'.mpr fun x ↦ isNilpotent_toEnd_sub_algebraMap M χ x

end shiftedWeightSpace

/-- Given a Lie module `M` of a Lie algebra `L` with coefficients in `R`, if a function `χ : L → R`
has a simultaneous generalized eigenvector for the action of `L` then it has a simultaneous true
eigenvector, provided `M` is Noetherian and has linear weights. -/
lemma exists_forall_lie_eq_smul [IsNoetherian R M] (χ : Weight R L M) :
    ∃ m : M, m ≠ 0 ∧ ∀ x : L, ⁅x, m⁆ = χ x • m := by
  replace hχ : Nontrivial (shiftedWeightSpace R L M χ) :=
    (LieSubmodule.nontrivial_iff_ne_bot R L M).mpr χ.weightSpace_ne_bot
  obtain ⟨⟨⟨m, _⟩, hm₁⟩, hm₂⟩ :=
    @exists_ne _ (nontrivial_max_triv_of_isNilpotent R L (shiftedWeightSpace R L M χ)) 0
  simp_rw [LieSubmodule.mem_coeSubmodule, mem_maxTrivSubmodule, Subtype.ext_iff,
    shiftedWeightSpace.coe_lie_shiftedWeightSpace_apply, ZeroMemClass.coe_zero, sub_eq_zero] at hm₁
  exact ⟨m, by simpa using hm₂, hm₁⟩

end LieModule
