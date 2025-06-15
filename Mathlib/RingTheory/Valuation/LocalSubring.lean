/-
Copyright (c) 2024 Andrew Yang, Yaël Dillies, Javier López-Contreras. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Yaël Dillies, Javier López-Contreras
-/
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.LocalRing.LocalSubring
import Mathlib.RingTheory.Polynomial.Ideal
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!

# Valuation subrings are exactly the maximal local subrings

See `LocalSubring.isMax_iff`.
Note that the order on local subrings is not merely inclusion but domination.

-/

open IsLocalRing

variable {R S K : Type*} [CommRing R] [CommRing S] [Field K]

/-- Cast a valuation subring to a local subring. -/
def ValuationSubring.toLocalSubring (A : ValuationSubring K) : LocalSubring K where
  toSubring := A.toSubring
  isLocalRing := A.isLocalRing

lemma ValuationSubring.toLocalSubring_injective :
    Function.Injective (ValuationSubring.toLocalSubring (K := K)) :=
  fun _ _ h ↦ ValuationSubring.toSubring_injective congr(($h).toSubring)

lemma LocalSubring.map_maximalIdeal_eq_top_of_isMax {R : LocalSubring K}
    (hR : IsMax R) {S : Subring K} (hS : R.toSubring < S) :
    (maximalIdeal R.toSubring).map (Subring.inclusion hS.le) = ⊤ := by
  let mR := (maximalIdeal R.toSubring).map (Subring.inclusion hS.le)
  by_contra h_is_not_top
  obtain ⟨M, h_is_max, h_incl⟩ := Ideal.exists_le_maximal _ h_is_not_top
  let fSₘ : LocalSubring K := LocalSubring.ofPrime S M
  have h_RleSₘ : R ≤ fSₘ := by
    refine ⟨hS.le.trans (LocalSubring.le_ofPrime _ _), ⟨?_⟩⟩
    rintro ⟨a, h_a_inR⟩ h_fa_isUnit
    apply (IsLocalization.AtPrime.isUnit_to_map_iff _ M ⟨a, hS.le h_a_inR⟩).mp at h_fa_isUnit
    by_contra h
    rw [← mem_nonunits_iff, ← mem_maximalIdeal] at h
    apply Ideal.mem_map_of_mem (Subring.inclusion hS.le) at h
    exact h_fa_isUnit (h_incl h)
  have h_RneSₘ : R ≠ fSₘ :=
    fun e ↦ (hS.trans_le (LocalSubring.le_ofPrime S M)).ne congr(($e).toSubring)
  exact h_RneSₘ (hR.eq_of_le h_RleSₘ)

@[stacks 00IC]
lemma LocalSubring.mem_of_isMax_of_isIntegral {R : LocalSubring K}
    (hR : IsMax R) {x : K} (hx : IsIntegral R.toSubring x) : x ∈ R.toSubring := by
  let S := Algebra.adjoin R.toSubring {x}
  have : Algebra.IsIntegral R.toSubring S := Algebra.IsIntegral.adjoin (by simpa)
  have : FaithfulSMul R.toSubring S := NoZeroSMulDivisors.instFaithfulSMulOfNontrivial
  obtain ⟨Q : Ideal S.toSubring, hQ, e⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (R := R.toSubring) (S := S) (maximalIdeal _) (le_maximalIdeal (by simp))
  have : R = .ofPrime S.toSubring Q := by
    have hRS : R.toSubring ≤ S.toSubring := fun r hr ↦ algebraMap_mem S ⟨r, hr⟩
    apply hR.eq_of_le ⟨hRS.trans (LocalSubring.le_ofPrime _ _), ⟨?_⟩⟩
    intro r hr
    have := (IsLocalization.AtPrime.isUnit_to_map_iff (R := S.toSubring) _ Q ⟨_, hRS r.2⟩).mp hr
    by_contra h
    rw [← mem_nonunits_iff, ← mem_maximalIdeal, ← e] at h
    exact this h
  rw [this]
  exact LocalSubring.le_ofPrime _ _ (Algebra.self_mem_adjoin_singleton _ _)

@[stacks 052K]
lemma ValuationSubring.isMax_toLocalSubring (R : ValuationSubring K) :
    IsMax R.toLocalSubring := by
  intro S hS
  suffices R.toLocalSubring = S from this.ge
  refine LocalSubring.toSubring_injective (le_antisymm hS.1 ?_)
  intro x hx
  refine (R.2 x).elim id fun h ↦ ?_
  by_contra h'
  have hx0 : x ≠ 0 := by rintro rfl; exact h' (zero_mem R)
  have : IsUnit (Subring.inclusion hS.1 ⟨x⁻¹, h⟩) :=
    isUnit_iff_exists_inv.mpr ⟨⟨x, hx⟩, Subtype.ext (inv_mul_cancel₀ hx0)⟩
  obtain ⟨x', hx'⟩ := isUnit_iff_exists_inv.mp (hS.2.1 _ this)
  have : x'.1 = x := by simpa [Subtype.ext_iff, inv_mul_eq_iff_eq_mul₀ hx0] using hx'
  exact h' (this ▸ x'.2)

@[stacks 00IB]
lemma LocalSubring.exists_valuationRing_of_isMax {R : LocalSubring K} (hR : IsMax R) :
    ∃ R' : ValuationSubring K, R'.toLocalSubring = R := by
  suffices ∀ x ∉ R.toSubring, x⁻¹ ∈ R.toSubring from
    ⟨⟨R.toSubring, fun x ↦ or_iff_not_imp_left.mpr (this x)⟩, rfl⟩
  intros x hx
  have hx0 : x ≠ 0 := fun e ↦ hx (e ▸ zero_mem _)
  apply mem_of_isMax_of_isIntegral hR
  let S := Algebra.adjoin R.toSubring {x}
  have : R.toSubring < S.toSubring := SetLike.lt_iff_le_and_exists.mpr
    ⟨fun r hr ↦ algebraMap_mem S ⟨r, hr⟩, ⟨x, Algebra.self_mem_adjoin_singleton _ _, hx⟩⟩
  have := map_maximalIdeal_eq_top_of_isMax hR this
  rw [Ideal.eq_top_iff_one] at this
  obtain ⟨p, hp, hp'⟩ := (Algebra.mem_ideal_map_adjoin _ _).mp this
  have := IsUnit.invertible (isUnit_iff_ne_zero.mpr hx0)
  have : Polynomial.aeval (⅟x) (p - 1).reverse = 0 := by
    simpa [← Polynomial.aeval_def, hp'] using
      Polynomial.eval₂_reverse_eq_zero_iff (algebraMap R.toSubring K) x (p - 1)
  rw [invOf_eq_right_inv (mul_inv_cancel₀ hx0)] at this
  have H : IsUnit ((p - 1).coeff 0) := by
    by_contra h
    simpa using sub_mem (hp 0) h
  refine ⟨.C (H.unit⁻¹).1 * (p - 1).reverse, ?_, ?_⟩
  · have : (p - 1).natTrailingDegree = 0 := by
      simp only [Polynomial.natTrailingDegree_eq_zero,
        Polynomial.coeff_sub, Polynomial.coeff_one_zero, ne_eq, sub_eq_zero]
      exact .inr fun h ↦ (IsLocalRing.notMem_maximalIdeal.mpr isUnit_one (h ▸ hp 0))
    rw [Polynomial.Monic.def, Polynomial.leadingCoeff_mul', Polynomial.reverse_leadingCoeff,
      Polynomial.trailingCoeff, this]
    · simp
    · have : p - 1 ≠ 0 := fun e ↦ by simp [e] at H
      simpa
  · simp [← Polynomial.aeval_def, this]

/-- A local subring is maximal with respect to the domination order
  if and only if it is a valuation ring. -/
lemma LocalSubring.isMax_iff {A : LocalSubring K} :
    IsMax A ↔ ∃ B : ValuationSubring K, B.toLocalSubring = A :=
  ⟨exists_valuationRing_of_isMax, fun ⟨B, e⟩ ↦ e ▸ B.isMax_toLocalSubring⟩

@[stacks 00IA]
lemma LocalSubring.exists_le_valuationSubring (A : LocalSubring K) :
    ∃ B : ValuationSubring K, A ≤ B.toLocalSubring := by
  suffices ∃ B, A ≤ B ∧ IsMax B by
    obtain ⟨B, hB, hB'⟩ := this
    obtain ⟨B, rfl⟩ := B.exists_valuationRing_of_isMax hB'
    exact ⟨B, hB⟩
  refine zorn_le_nonempty_Ici₀ _ ?_ _ le_rfl
  intro s hs H y hys
  have inst : Nonempty s := ⟨⟨y, hys⟩⟩
  have hdir := H.directed.mono_comp _ LocalSubring.toSubring_mono
  refine ⟨@LocalSubring.mk _ _ (⨆ i : s, i.1.toSubring) ⟨?_⟩, ?_⟩
  · intro ⟨a, ha⟩ ⟨b, hb⟩ e
    obtain ⟨A, haA : a ∈ A.1.toSubring⟩ := (Subring.mem_iSup_of_directed hdir).mp ha
    obtain ⟨B, hbB : b ∈ B.1.toSubring⟩ := (Subring.mem_iSup_of_directed hdir).mp hb
    obtain ⟨C, hCA, hCB⟩ := hdir A B
    refine (C.1.2.2 (a := ⟨a, hCA haA⟩) (b := ⟨b, hCB hbB⟩) (Subtype.ext congr(($e).1))).imp ?_ ?_
    · exact fun h ↦ h.map (Subring.inclusion (le_iSup (fun i : s ↦ i.1.toSubring) C))
    · exact fun h ↦ h.map (Subring.inclusion (le_iSup (fun i : s ↦ i.1.toSubring) C))
  · intro A hA
    refine ⟨le_iSup (fun i : s ↦ i.1.toSubring) ⟨A, hA⟩, ⟨?_⟩⟩
    rintro ⟨a, haA⟩ h
    obtain ⟨⟨b, hb⟩, e⟩ := isUnit_iff_exists_inv.mp h
    obtain ⟨B, hbB : b ∈ B.1.toSubring⟩ := (Subring.mem_iSup_of_directed hdir).mp hb
    obtain ⟨C, hCA, hCB⟩ := H.directed ⟨A, hA⟩ B
    apply hCA.2.1
    exact isUnit_iff_exists_inv.mpr ⟨⟨b, hCB.1 hbB⟩, Subtype.ext congr(($e).1)⟩

lemma bijective_rangeRestrict_comp_of_valuationRing [IsDomain R] [ValuationRing R]
    [IsLocalRing S] [Algebra R K] [IsFractionRing R K]
    (f : R →+* S) (g : S →+* K) (h : g.comp f = algebraMap R K) [IsLocalHom f] :
    Function.Bijective (g.rangeRestrict.comp f) := by
  refine ⟨?_, ?_⟩
  · exact .of_comp (f := Subtype.val) (by convert (IsFractionRing.injective R K); rw [← h]; rfl)
  · let V : ValuationSubring K :=
      ⟨(algebraMap R K).range, ValuationRing.isInteger_or_isInteger R⟩
    suffices LocalSubring.range g ≤ V.toLocalSubring by
      rintro ⟨_, x, rfl⟩
      obtain ⟨y, hy⟩ := this.1 ⟨x, rfl⟩
      exact ⟨y, Subtype.ext (by simpa [← h] using hy)⟩
    apply V.isMax_toLocalSubring
    have H : (algebraMap R K).range ≤ g.range := fun x ⟨a, ha⟩ ↦ ⟨f a, by simp [← ha, ← h]⟩
    refine ⟨H, ⟨?_⟩⟩
    rintro ⟨_, a, rfl⟩ (ha : IsUnit (M := g.range) ⟨algebraMap R K a, _⟩)
    suffices IsUnit a from this.map (algebraMap R K).rangeRestrict
    apply IsUnit.of_map f
    apply (IsLocalHom.of_surjective g.rangeRestrict g.rangeRestrict_surjective).1
    convert ha
    simp [← h]

lemma IsLocalRing.exists_factor_valuationRing [IsLocalRing R] (f : R →+* K) :
    ∃ (A : ValuationSubring K) (h : _), IsLocalHom (f.codRestrict A.toSubring h) := by
  obtain ⟨B, hB⟩ := (LocalSubring.range f).exists_le_valuationSubring
  refine ⟨B, fun x ↦ hB.1 ⟨x, rfl⟩, ?_⟩
  exact @RingHom.isLocalHom_comp _ _ _ _ _ _ _ _
    hB.2 (.of_surjective _ f.rangeRestrict_surjective)
