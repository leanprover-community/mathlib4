import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.Topology.Algebra.Valued.ValuativeRel

-- Do these belong to another file?
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
  hv.symm.isNontrivial

end Valuation

namespace Polynomial

open WithZero WithZeroMulInt NNReal

variable (K : Type*) [Field K]

/-- The valuation on `K[X]` that corresponds to the "point at infinity" on the projective line `ℙ¹`,
sending `X` to `WithZero.exp 1`. -/
noncomputable def infinityValuation : Valuation K[X] ℤᵐ⁰ :=
  ((idealX K).valuation (RatFunc K)).comap <| RingHomClass.toRingHom <| aeval .X⁻¹

-- There seems to be another pathway via more API on `X ↦ X⁻¹`.
-- using `valuation_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X`.

variable {K}

@[simp] lemma valuation_C (I : IsDedekindDomain.HeightOneSpectrum K[X]) {a : K} (ha : a ≠ 0) :
    I.valuation (RatFunc K) (C a) = 1 :=
  eq_of_le_of_not_lt (I.valuation_le_one _) <| (I.valuation_lt_one_iff_mem _).not.2 fun hai ↦
    I.2.ne_top <| I.1.eq_top_of_isUnit_mem hai <| isUnit_C.mpr <| .mk0 _ ha

@[simp] lemma valuation_C' (I : IsDedekindDomain.HeightOneSpectrum K[X]) {a : K} (ha : a ≠ 0) :
    I.valuation (RatFunc K) (RatFunc.C a) = 1 :=
  valuation_C I ha

@[simp] lemma infinityValuation_C {a : K} (ha : a ≠ 0) : infinityValuation K (C a) = 1 := by
  simp [infinityValuation, ha]

@[simp] lemma infinityValuation_X : infinityValuation K X = exp 1 := by
  simp [infinityValuation, exp]

@[simp] lemma infinityValuation_monomial {n : ℕ} {a : K} (ha : a ≠ 0) :
    infinityValuation K (monomial n a) = exp (n : ℤ) := by
  simp [← C_mul_X_pow_eq_monomial, ← exp_nsmul, ha]

theorem one_le_valuation (p : K[X]) (hp : p ≠ 0) : 1 ≤ infinityValuation K p := by
  have mem_support : p.natDegree ∈ p.support :=
    natDegree_mem_support_of_nonzero hp
  have coeff_natDegree : p.coeff p.natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hp
  rw [p.as_sum_support, (infinityValuation K).map_sum_eq_of_lt mem_support,
    infinityValuation_monomial coeff_natDegree, ← exp_zero, exp_le_exp]
  · exact Nat.cast_nonneg _
  · rw [infinityValuation_monomial coeff_natDegree]; exact exp_ne_zero
  · intro i hip
    simp_rw [Finset.mem_sdiff] at hip
    rw [infinityValuation_monomial (mem_support_iff.mp hip.left),
      infinityValuation_monomial coeff_natDegree, exp_lt_exp, Nat.cast_lt]
    exact lt_natDegree_of_mem_eraseLead_support <|
      by simpa [-mem_support_iff, eraseLead_support, Finset.mem_erase, and_comm] using hip

variable (K)

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
noncomputable def rankOne : (infinityValuation K).RankOne where
  exists_val_nontrivial := ⟨X, by simpa using by decide⟩
  hom := toNNReal (e := 37) (by norm_num)
  strictMono' := toNNReal_strictMono (by norm_num)
attribute [local instance] rankOne

open ValuativeRel

theorem compatible : (infinityValuation K).Compatible :=
  .ofValuation _
attribute [local instance] compatible

nonrec theorem isEquiv : (valuation K[X]).IsEquiv (infinityValuation K) :=
  isEquiv _ _

theorem isNontrivial : (infinityValuation K).IsNontrivial where
  exists_val_nontrivial := ⟨X, by simpa using by decide⟩
attribute [local instance] isNontrivial

theorem isNontrivial' : IsNontrivial K[X] :=
  isNontrivial_iff_isNontrivial.mpr <| (isEquiv K).isNontrivial'
attribute [local instance] isNontrivial'

theorem isRankLeOne' : IsRankLeOne K[X] :=
  .of_compatible_mulArchimedean (infinityValuation K)
attribute [local instance] isRankLeOne'

noncomputable example : (valuation K[X]).RankOne := inferInstance

@[simp] theorem valuation_lt_one_iff (p : K[X]) : valuation K[X] p < 1 ↔ p = 0 := by
  rw [(isEquiv K).lt_one_iff_lt_one]
  exact ⟨fun hp ↦ by_contra fun hp0 ↦ not_le_of_gt hp (one_le_valuation p hp0), (· ▸ by simp)⟩

theorem isValuativeTopology : IsValuativeTopology K[X] where
  mem_nhds_iff {s x} := ⟨fun hsx ↦ ⟨1, by simp [mem_of_mem_nhds hsx]⟩,
    fun ⟨γ, hγ⟩ ↦ mem_nhds_discrete.mpr <| hγ ⟨0, by simp⟩⟩
attribute [local instance] isValuativeTopology

/-- With the valuation on `K[X]` sending `X` to `37` and `K` to `1`, we get a non-trivial (rank one)
valuation but with a discrete topology. -/
example : IsValuativeTopology K[X] ∧ Nonempty (valuation K[X]).RankOne ∧
    IsNontrivial K[X] ∧ DiscreteTopology K[X] :=
  ⟨inferInstance, ⟨inferInstance⟩, inferInstance, inferInstance⟩

end Polynomial

open ValuativeRel

/-- Does not happen for fields (even without assuming rank one). -/
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
