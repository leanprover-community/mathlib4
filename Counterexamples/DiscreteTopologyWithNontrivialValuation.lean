import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.Topology.Algebra.Valued.ValuativeRel

-- MOVE
namespace Valuation

variable {R Γ₀ Γ'₀ : Type*} [Ring R]
  [LinearOrderedCommMonoidWithZero Γ₀] [LinearOrderedCommMonoidWithZero Γ'₀]
  {v₁ : Valuation R Γ₀} {v₂ : Valuation R Γ'₀}

attribute [mk_iff] Valuation.IsNontrivial

lemma IsEquiv.isNontrivial_iff_isNontrivial (hv : v₁.IsEquiv v₂) :
    v₁.IsNontrivial ↔ v₂.IsNontrivial := by
  rw [isNontrivial_iff, isNontrivial_iff]
  simp_rw [ne_eq, ← v₁.map_zero, ← v₁.map_one, ← v₂.map_zero, ← v₂.map_one, hv.val_eq]

lemma IsEquiv.isNontrivial (hv : v₁.IsEquiv v₂) [v₁.IsNontrivial] : v₂.IsNontrivial :=
  hv.isNontrivial_iff_isNontrivial.mp ‹_›

lemma IsEquiv.isNontrivial' (hv : v₁.IsEquiv v₂) [v₂.IsNontrivial] : v₁.IsNontrivial :=
  hv.isNontrivial_iff_isNontrivial.mpr ‹_›

end Valuation

namespace Polynomial

open WithZero WithZeroMulInt NNReal

variable (K : Type*) [Field K]

/-- The valuation on `K[X]` that corresponds to the "point at infinity" on the projective line `ℙ¹`,
sending `X` to `WithZero.exp 1`. -/
noncomputable def infinityValuation : Valuation K[X] ℤᵐ⁰ :=
  ((idealX K).valuation (RatFunc K)).comap <| RingHomClass.toRingHom <| aeval .X⁻¹

@[simp] lemma infinityValuation_X : infinityValuation K X = exp 1 := by
  simp [infinityValuation, exp]

/-- The valuative relation defined by `infinityValuation K`. -/
def infinityValuativeRel : ValuativeRel K[X] :=
  .ofValuation <| infinityValuation K
attribute [local instance] infinityValuativeRel

/-- The discrete topology on `K[X]`. -/
def topology : TopologicalSpace K[X] :=
  ⊥
attribute [local instance] topology

theorem discreteTopology : DiscreteTopology K[X] :=
  discreteTopology_bot K[X]
attribute [local instance] discreteTopology

/-- `X` is sent to `37`. -/
noncomputable def rankOne' : (infinityValuation K).RankOne where
  exists_val_nontrivial := ⟨X, by simpa using by decide⟩
  hom := toNNReal (e := 37) (by norm_num)
  strictMono' := toNNReal_strictMono (by norm_num)
attribute [local instance] rankOne'

open ValuativeRel

theorem compatible : (infinityValuation K).Compatible :=
  .ofValuation _
attribute [local instance] compatible

nonrec theorem isEquiv : (valuation K[X]).IsEquiv (infinityValuation K) :=
  isEquiv _ _

@[simp] theorem valuation_lt_one_iff (p : K[X]) : valuation K[X] p < 1 ↔ p = 0 := by
  rw [(isEquiv K).lt_one_iff_lt_one, infinityValuation, Valuation.comap_apply]
  sorry

theorem isValuativeTopology : IsValuativeTopology K[X] where
  mem_nhds_iff {s x} := ⟨fun hsx ↦ ⟨1, by simp [mem_of_mem_nhds hsx]⟩,
    fun ⟨γ, hγ⟩ ↦ mem_nhds_discrete.mpr <| hγ ⟨0, by simp⟩⟩
attribute [local instance] isValuativeTopology

theorem isNontrivial : IsNontrivial K[X] :=
  isNontrivial_iff_isNontrivial.mpr <| (isEquiv K).isNontrivial'
attribute [local instance] isNontrivial

/-- With the valuation on `K[X]` sending `X` to `37` and `K` to `1`, we get a non-trivial (rank one)
valuation but with a discrete topology. -/
example : IsValuativeTopology K[X] ∧ IsNontrivial K[X] ∧ DiscreteTopology K[X] :=
  ⟨inferInstance, inferInstance, inferInstance⟩

end Polynomial

open ValuativeRel

/-- Does not happen for fields. -/
example {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    (h : IsValuativeTopology F ∧ IsNontrivial F ∧ DiscreteTopology F) :
    False := by
  obtain ⟨_, _, _⟩ := h
  -- This proof can be simplified with other unmerged PR's.
  obtain ⟨γ, -, hγ⟩ := (IsValuativeTopology.hasBasis_nhds_zero F).mem_iff.mp
    (mem_nhds_discrete.mpr (Set.mem_singleton 0))
  have := isNontrivial_iff_isNontrivial.mp (inferInstanceAs (IsNontrivial F))
  obtain ⟨x, h0x, hx1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation F)
  obtain ⟨a, b, hab⟩ := valuation_surjective (R := F) γ
  have := @hγ (x * (a / b)) (by simp [hab, hx1])
  rw [Set.mem_singleton_iff, mul_eq_zero, div_eq_zero_iff] at this
  obtain rfl | rfl | hb0 := this
  · exact h0x (map_zero _)
  · simp [eq_comm] at hab
  · exact val_posSubmonoid_ne_zero b hb0
