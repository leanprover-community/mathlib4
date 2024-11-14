/-
Copyright (c) 2024 Andrew Yang, Yaël Dillies, Javier López-Contreras. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Yaël Dillies, Javier López-Contreras
-/
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Valuation.ValuationSubring


/-!
# Local subrings of fields

# Main result
- `LocalSubring` : The class of local subrings of a commutative ring.
- `LocalSubring.ofPrime`: The localization of a subring as a `LocalSubring`.
- `LocalSubring.isMax_iff`: A local subring is maximal with respect to the domination order
  if and only if it is a valuation ring.
-/

open IsLocalRing Set

open scoped Polynomial


variable {R S : Type*} [CommRing R] [CommRing S]
variable {K : Type*} [Field K]

instance [Nontrivial S] (f : R →+* S) (s : Subring R) [IsLocalRing s] : IsLocalRing (s.map f) :=
  .of_surjective' (f.restrict s _ (fun _ ↦ Set.mem_image_of_mem f))
    (fun ⟨_, a, ha, e⟩ ↦ ⟨⟨a, ha⟩, Subtype.ext e⟩)

instance isLocalRing_top [IsLocalRing R] : IsLocalRing (⊤ : Subring R) :=
  Subring.topEquiv.symm.isLocalRing

variable (R) in
/-- The class of local subrings of a commutative ring. -/
@[ext]
structure LocalSubring where
  /-- The underlying subring of a local subring. -/
  toSubring : Subring R
  [isLocalRing : IsLocalRing toSubring]

namespace LocalSubring

attribute [instance] isLocalRing

lemma toSubring_injective : Function.Injective (toSubring (R := R)) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ rfl; rfl

/-- Copy of a local subring with a new `carrier` equal to the old one.
Useful to fix definitional equalities. -/
protected def copy (S : LocalSubring R) (s : Set R) (hs : s = ↑S.toSubring) : LocalSubring R :=
  LocalSubring.mk (S.toSubring.copy s hs) (isLocalRing := hs ▸ S.2)

/-- The image of a `LocalSubring` as a `LocalSubring`. -/
@[simps! toSubring]
def map [Nontrivial S] (f : R →+* S) (s : LocalSubring R) : LocalSubring S :=
  mk (s.1.map f)

/-- The range of a ringhom from a local ring as a `LocalSubring`. -/
@[simps! toSubring]
def range [IsLocalRing R] [Nontrivial S] (f : R →+* S) : LocalSubring S :=
  .copy (map f (mk ⊤)) f.range (by ext x; exact congr(x ∈ $(Set.image_univ.symm)))

/--
The domination order on local subrings.
`A` dominates `B` if and only if `B ≤ A` and `m_A ∩ B = m_B`.
-/
@[stacks 00I9]
instance : PartialOrder (LocalSubring R) where
  le A B := ∃ h : A.1 ≤ B.1, IsLocalHom (Subring.inclusion h)
  le_refl a := ⟨le_rfl, ⟨fun _ ↦ id⟩⟩
  le_trans A B C h₁ h₂ := ⟨h₁.1.trans h₂.1, @RingHom.isLocalHom_comp _ _ _ _ _ _ _ _ h₂.2 h₁.2⟩
  le_antisymm A B h₁ h₂ := toSubring_injective (le_antisymm h₁.1 h₂.1)

lemma toSubring_mono : Monotone (toSubring (R := R)) :=
  fun _ _ e ↦ e.1

section ofPrime

variable (A : Subring K) (P : Ideal A) [P.IsPrime]

/-- The localization of a subring at a prime, as a local subring.
Also see `Localization.subalgebra.ofField` -/
noncomputable
def ofPrime (A : Subring K) (P : Ideal A) [P.IsPrime] : LocalSubring K :=
  range (IsLocalization.lift (M := P.primeCompl) (S := Localization.AtPrime P)
    (g := A.subtype) (by simp [Ideal.primeCompl, not_imp_not]))

lemma le_ofPrime : A ≤ (ofPrime A P).toSubring := by
  intro x hx
  exact ⟨algebraMap A _ ⟨x, hx⟩, by simp⟩

noncomputable
instance : Algebra A (ofPrime A P).toSubring := (Subring.inclusion (le_ofPrime A P)).toAlgebra

instance : IsScalarTower A (ofPrime A P).toSubring K := .of_algebraMap_eq (fun _ ↦ rfl)

/-- The localization of a subring at a prime is indeed isomorphic to its abstract localization. -/
noncomputable
def ofPrimeEquiv : Localization.AtPrime P ≃ₐ[A] (ofPrime A P).toSubring := by
  refine AlgEquiv.ofInjective (IsLocalization.liftAlgHom (M := P.primeCompl)
    (S := Localization.AtPrime P) (f := Algebra.ofId A K) _) ?_
  intro x y e
  obtain ⟨x, s, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl x
  obtain ⟨y, t, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl y
  have H (x : P.primeCompl) : x.1 ≠ 0 := by aesop
  have : x.1 = y.1 * t.1.1⁻¹ * s.1.1 := by
    simpa [IsLocalization.lift_mk', Algebra.ofId_apply, H,
      Algebra.algebraMap_ofSubring_apply, IsUnit.coe_liftRight] using congr($e * s.1.1)
  rw [IsLocalization.mk'_eq_iff_eq]
  congr 1
  ext
  field_simp [H t, this, mul_comm]

instance : IsLocalization.AtPrime (ofPrime A P).toSubring P :=
  IsLocalization.isLocalization_of_algEquiv _ (ofPrimeEquiv A P)

end ofPrime

end LocalSubring

variable {K : Type*} [Field K]

/-- Cast a valuation subring to a local subring. -/
def ValuationSubring.toLocalSubring (A : ValuationSubring K) : LocalSubring K where
  toSubring := A.toSubring
  isLocalRing := A.isLocalRing

lemma ValuationSubring.toLocalSubring_injective :
    Function.Injective (ValuationSubring.toLocalSubring (K := K)) := by
  intro a b h
  ext x
  apply_fun (fun a ↦ x ∈ a.toSubring) at h
  rw [eq_iff_iff] at h
  exact h

lemma map_maximalIdeal_eq_top_of_isMax {R : LocalSubring K}
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
lemma mem_of_mem_maximalLocalSubrings_of_isIntegral {R : LocalSubring K}
    (hR : IsMax R) {x : K} (hx : IsIntegral R.toSubring x) : x ∈ R.toSubring := by
  let S := Algebra.adjoin R.toSubring {x}
  have : Algebra.IsIntegral R.toSubring S := Algebra.IsIntegral.adjoin (by simpa)
  obtain ⟨Q : Ideal S.toSubring, hQ, e⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (R := R.toSubring) (S := S) (maximalIdeal _) (le_maximalIdeal (by simp [Ideal.eq_top_iff_one]))
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
  apply mem_of_mem_maximalLocalSubrings_of_isIntegral hR
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
      exact .inr fun h ↦ (IsLocalRing.not_mem_maximalIdeal.mpr isUnit_one (h ▸ hp 0))
    rw [Polynomial.Monic.def, Polynomial.leadingCoeff_mul', Polynomial.reverse_leadingCoeff,
      Polynomial.trailingCoeff, this]
    · simp
    · have : p - 1 ≠ 0 := fun e ↦ by simp [e] at H
      simpa
  · simp [← Polynomial.aeval_def, this]

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

lemma bijective_rangeRestrict_comp_of_valuationRing {R S K : Type*} [CommRing R]
    [IsDomain R] [ValuationRing R]
    [CommRing S] [IsLocalRing S] [Field K] [Algebra R K] [IsFractionRing R K]
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

lemma exists_factor_valuationRing {R : Type*} [CommRing R] [IsLocalRing R] {K : Type*} [Field K]
    (f : R →+* K) :
    ∃ (A : ValuationSubring K) (h : _), IsLocalHom (f.codRestrict A.toSubring h) := by
  obtain ⟨B, hB⟩  := (LocalSubring.range f).exists_le_valuationSubring
  refine ⟨B, fun x ↦ hB.1 ⟨x, rfl⟩, ?_⟩
  exact @RingHom.isLocalHom_comp _ _ _ _ _ _ _ _
    hB.2 (.of_surjective _ f.rangeRestrict_surjective)
