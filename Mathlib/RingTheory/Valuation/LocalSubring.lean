/-
Copyright (c) 2024 Andrew Yang, Yaël Dillies, Javier López-Contreras, Daniel Funck, Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Yaël Dillies, Javier López-Contreras, Daniel Funck, Junyan Xu
-/
module

public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.LocalRing.LocalSubring
public import Mathlib.RingTheory.Polynomial.Ideal
public import Mathlib.RingTheory.Valuation.Integral
public import Mathlib.RingTheory.Valuation.ValuationSubring

/-!

# Valuation subrings are exactly the maximal local subrings

See `LocalSubring.isMax_iff`.
Note that the order on local subrings is not merely inclusion but domination.

-/

@[expose] public section

open IsLocalRing

variable {R S K : Type*} [CommRing R] [CommRing S] [Field K]

instance (V : ValuationSubring K) : IsIntegrallyClosed V.toSubring := by
  rw [← V.integer_valuation]; infer_instance

instance (V : ValuationSubring K) : IsIntegrallyClosed V :=
  inferInstanceAs (IsIntegrallyClosed V.toSubring)

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
  set mR := (maximalIdeal R.toSubring).map (Subring.inclusion hS.le)
  by_contra h_is_not_top
  obtain ⟨M, h_is_max, h_incl⟩ := Ideal.exists_le_maximal _ h_is_not_top
  let fSₘ : LocalSubring K := LocalSubring.ofPrime S M
  have h_RleSₘ : R ≤ fSₘ := by
    refine ⟨hS.le.trans (LocalSubring.le_ofPrime ..), ((local_hom_TFAE _).out 2 0).mp ?_⟩
    conv_rhs => rw [← IsLocalization.AtPrime.map_eq_maximalIdeal M]
    refine .trans ?_ (Ideal.map_mono h_incl)
    rw [Ideal.map_map]; rfl
  exact (hR.eq_of_le h_RleSₘ ▸ hS).not_ge (LocalSubring.le_ofPrime ..)

@[stacks 00IC]
-- the conclusion could be `IsIntegrallyClosedIn R.toSubring K`, which has slightly worse defeq.
lemma LocalSubring.mem_of_isMax_of_isIntegral {R : LocalSubring K}
    (hR : IsMax R) {x : K} (hx : IsIntegral R.toSubring x) : x ∈ R.toSubring := by
  let S := Algebra.adjoin R.toSubring {x}
  have : Algebra.IsIntegral R.toSubring S := Algebra.IsIntegral.adjoin (by simpa)
  have : FaithfulSMul R.toSubring S := NoZeroSMulDivisors.instFaithfulSMulOfNontrivial
  obtain ⟨Q : Ideal S.toSubring, hQ, e⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (S := S) (maximalIdeal R.toSubring) (le_maximalIdeal (by simp))
  have : R = .ofPrime S.toSubring Q := by
    have hRS : R.toSubring ≤ S.toSubring := fun r hr ↦ algebraMap_mem S ⟨r, hr⟩
    refine hR.eq_of_le ⟨hRS.trans (LocalSubring.le_ofPrime _ _), ((local_hom_TFAE _).out 2 0).mp ?_⟩
    conv_rhs => rw [← IsLocalization.AtPrime.map_eq_maximalIdeal Q]
    refine .trans ?_ (Ideal.map_mono <| Ideal.map_le_iff_le_comap.mpr e.ge)
    rw [Ideal.map_map]; rfl
  rw [this]
  exact LocalSubring.le_ofPrime _ _ (Algebra.self_mem_adjoin_singleton _ _)

@[stacks 052K]
lemma ValuationSubring.isMax_toLocalSubring (R : ValuationSubring K) :
    IsMax R.toLocalSubring := by
  intro S hS
  refine (LocalSubring.toSubring_injective (hS.1.antisymm fun x hx ↦ (R.2 x).elim id fun h ↦ ?_)).ge
  by_contra h'
  have hx0 : x ≠ 0 := by rintro rfl; exact h' R.zero_mem
  have : IsUnit (Subring.inclusion hS.1 ⟨x⁻¹, h⟩) :=
    isUnit_iff_exists_inv.mpr ⟨⟨x, hx⟩, Subtype.ext (inv_mul_cancel₀ hx0)⟩
  obtain ⟨x', hx'⟩ := isUnit_iff_exists_inv.mp (hS.2.1 _ this)
  have : x' = x := by simpa [Subtype.ext_iff, inv_mul_eq_iff_eq_mul₀ hx0] using hx'
  exact h' (this ▸ x'.2)

@[stacks 00IB]
lemma LocalSubring.exists_valuationRing_of_isMax {R : LocalSubring K} (hR : IsMax R) :
    ∃ R' : ValuationSubring K, R'.toLocalSubring = R := by
  suffices ∀ x ∉ R.toSubring, x⁻¹ ∈ R.toSubring from
    ⟨⟨R.toSubring, fun x ↦ or_iff_not_imp_left.mpr (this x)⟩, rfl⟩
  refine fun x hx ↦ mem_of_isMax_of_isIntegral hR ?_
  have hx0 : x ≠ 0 := fun e ↦ hx (e ▸ zero_mem _)
  let := invertibleOfNonzero hx0
  let S := Algebra.adjoin R.toSubring {x}
  have : R.toSubring < S.toSubring := SetLike.lt_iff_le_and_exists.mpr
    ⟨fun r hr ↦ algebraMap_mem S ⟨r, hr⟩, ⟨x, Algebra.self_mem_adjoin_singleton _ _, hx⟩⟩
  have ⟨p, hp, hpx⟩ := Algebra.exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top x _
    (maximalIdeal.isMaximal R.toSubring).ne_top
    (top_unique <| (map_maximalIdeal_eq_top_of_isMax hR this).ge.trans le_self_add)
  have H : IsUnit p.leadingCoeff := of_not_not fun h ↦ by simpa using sub_mem h hp
  exact ⟨.C H.unit⁻¹.1 * p, by simp [Polynomial.Monic], by simpa using .inr hpx⟩

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

lemma Ideal.image_subset_nonunits_valuationSubring {A : Subring K} (I : Ideal A) (hI : I ≠ ⊤) :
    ∃ B : ValuationSubring K, A ≤ B.toSubring ∧ A.subtype '' I ⊆ B.nonunits := by
  have ⟨M, hM, le⟩ := I.exists_le_maximal hI
  have ⟨V, hV⟩ := (LocalSubring.ofPrime A M).exists_le_valuationSubring
  refine ⟨V, (LocalSubring.le_ofPrime ..).trans hV.1, ?_⟩
  rw [← V.image_maximalIdeal]
  refine .trans ?_ (Set.image_mono <| ((local_hom_TFAE _).out 0 2).mp hV.2)
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal M, map_map]
  refine .trans ?_ (Set.image_mono <| map_mono le)
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨_, mem_map_of_mem _ ha, rfl⟩

open Polynomial in
@[stacks 090P "part (1)"] lemma Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
    {x : K} {R : Subring K} (hxR : x ∉ R) [IsIntegrallyClosedIn R K] :
    ∃ V : ValuationSubring K, R ≤ V.toSubring ∧ x ∉ V := by
  obtain rfl | hx0 := eq_or_ne x 0
  · exact (hxR R.zero_mem).elim
  let := invertibleOfNonzero hx0
  let B := Algebra.adjoin R {x⁻¹}
  let xinv : B.toSubring := ⟨x⁻¹, Algebra.subset_adjoin rfl⟩
  have : Ideal.span {xinv} ≠ ⊤ := fun eq ↦ hxR <|
    have ⟨p, hp, hpx⟩ := Algebra.exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top _
      (⊥ : Ideal R) bot_ne_top (top_unique <| eq.ge.trans le_add_self)
    (Subring.isIntegrallyClosedIn_iff).mp ‹_› ⟨p, by simpa [Monic, sub_eq_zero] using hp, hpx⟩
  have ⟨V, hV⟩ := Ideal.image_subset_nonunits_valuationSubring _ this
  exact ⟨V, fun r hr ↦ hV.1 (B.algebraMap_mem ⟨r, hr⟩),
    (V.inv_mem_nonunits_iff.mp <| hV.2 ⟨_, Ideal.subset_span rfl, rfl⟩).resolve_left hx0⟩

open Polynomial in
@[stacks 090P "part (2)"] lemma LocalSubring.exists_le_valuationSubring_of_isIntegrallyClosedIn
    {x : K} {R : LocalSubring K} (hxR : x ∉ R.toSubring) [IsIntegrallyClosedIn R.toSubring K] :
    ∃ V : ValuationSubring K, R ≤ V.toLocalSubring ∧ x ∉ V := by
  obtain rfl | hx0 := eq_or_ne x 0
  · exact (hxR R.toSubring.zero_mem).elim
  let := invertibleOfNonzero hx0
  let B := Algebra.adjoin R.toSubring {x⁻¹}
  let xinv : B.toSubring := ⟨x⁻¹, Algebra.subset_adjoin rfl⟩
  have : (maximalIdeal R.toSubring).map (algebraMap _ B) + .span {xinv} ≠ ⊤ := fun eq ↦ hxR <|
    have ⟨p, hp, hpx⟩ := Algebra.exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top _ _
      (maximalIdeal.isMaximal R.toSubring).ne_top eq
    have H : IsUnit p.leadingCoeff := of_not_not fun h ↦ by simpa using sub_mem h hp
    (Subring.isIntegrallyClosedIn_iff).mp ‹_›
      ⟨.C H.unit⁻¹.1 * p, by simp [Polynomial.Monic], by simpa using .inr hpx⟩
  have ⟨V, hV⟩ := Ideal.image_subset_nonunits_valuationSubring (A := B.toSubring) _ this
  refine ⟨V, ⟨fun r hr ↦ hV.1 (B.algebraMap_mem ⟨r, hr⟩),
    ((local_hom_TFAE _).out 3 0).mp fun r hr ↦ ?_⟩, (V.inv_mem_nonunits_iff.mp <|
      hV.2 ⟨_, le_add_self (α := Ideal B) (Ideal.subset_span rfl), rfl⟩).resolve_left hx0⟩
  rw [← V.image_maximalIdeal] at hV
  obtain ⟨⟨r, _⟩, hr, rfl⟩ := hV.2 ⟨_, le_self_add (α := Ideal B) (Ideal.mem_map_of_mem _ hr), rfl⟩
  exact hr

/-- A subring integrally closed in a field is the intersection of valuation subrings
containing it. -/
lemma Subring.eq_iInf_of_isIntegrallyClosedIn {R : Subring K} [IsIntegrallyClosedIn R K] :
    R = ⨅ V : {V : ValuationSubring K // R ≤ V.toSubring}, V.1.toSubring :=
  le_antisymm (le_iInf fun V ↦ V.2) fun _ h ↦ of_not_not fun hxR ↦
    have ⟨V, hV⟩ := R.exists_le_valuationSubring_of_isIntegrallyClosedIn hxR
    hV.2 (iInf_le_of_le (α := Subring K) ⟨V, hV.1⟩ le_rfl h)

/-- A local subring integrally closed in a field is the intersection of valuation subrings
dominating it. -/
lemma LocalSubring.eq_iInf_of_isIntegrallyClosedIn {R : LocalSubring K}
    [IsIntegrallyClosedIn R.toSubring K] :
    R.toSubring = ⨅ V : {V : ValuationSubring K // R ≤ V.toLocalSubring}, V.1.toSubring :=
  le_antisymm (le_iInf fun V ↦ V.2.1) fun _ h ↦ of_not_not fun hxR ↦
    have ⟨V, hV⟩ := R.exists_le_valuationSubring_of_isIntegrallyClosedIn hxR
    hV.2 (iInf_le_of_le (α := Subring K) ⟨V, hV.1⟩ le_rfl h)

/-- The integral closure of a subset in a field is the intersection of all valuation subrings
containing it. -/
lemma iInf_valuationSubring_superset {s : Set K} :
    (⨅ V : {V : ValuationSubring K // s ⊆ V.toSubring}, V.1.toSubring) =
    (integralClosure (Subring.closure s) K).toSubring := by
  refine .trans ?_ Subring.eq_iInf_of_isIntegrallyClosedIn.symm
  simp_rw [iInf_subtype]
  congr! with V
  have : IsIntegrallyClosedIn V.toSubring K := inferInstanceAs (IsIntegrallyClosedIn V K)
  rw [Subring.integralClosure_subring_le_iff]
  exact Subring.closure_le.symm

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
  exact @RingHom.isLocalHom_comp _ _ _ _ _ _ _ _ hB.2 (.of_surjective _ f.rangeRestrict_surjective)
