import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring

open LocalRing
open Set

open Polynomial in
/-- useful lemma. move me -/
lemma Algebra.mem_ideal_map_adjoin {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (x : S) (I : Ideal R) {y : adjoin R ({x} : Set S)} :
    y ∈ I.map (algebraMap R (adjoin R ({x} : Set S))) ↔
      ∃ p : R[X], (∀ i, p.coeff i ∈ I) ∧ Polynomial.aeval x p = y := sorry

variable {R S : Type*} [CommRing R] [CommRing S]

-- TODO(jlcontreras): maybe genralizable to [Ring R] [Ring S]
instance [Nontrivial S] (f : R →+* S) (𝓡 : Subring R) [LocalRing 𝓡] : LocalRing <| 𝓡.map f where
  exists_pair_ne := by
    use 0, 1
    apply zero_ne_one
  isUnit_or_isUnit_of_add_one :=  by
    intro ⟨a, x, hx, hfx⟩ ⟨b, y, hy, hfy⟩ h
    have is_restriction r (hr : r ∈ 𝓡) : f r ∈ 𝓡.map f := mem_image_of_mem _ hr
    let f_rest := f.restrict 𝓡 (𝓡.map f) is_restriction
    have is_restriction_surj : Function.Surjective f_rest := surjective_onto_image
    have is_local : LocalRing (Subring.map f 𝓡) := by
      apply LocalRing.of_surjective' f_rest is_restriction_surj
    exact isUnit_or_isUnit_of_add_one h

instance localRing_top [LocalRing R] : LocalRing (⊤ : Subring R) :=
  Subring.topEquiv.symm.localRing

variable (R) in
structure LocalSubring where
  toSubring : Subring R
  [localRing : LocalRing toSubring]

namespace LocalSubring

instance (S : LocalSubring R) : LocalRing S.toSubring := S.localRing

/-- Copy of a local subring with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (S : LocalSubring R) (s : Set R) (hs : s = ↑S.toSubring) : LocalSubring R :=
  LocalSubring.mk (S.toSubring.copy s hs) (localRing := by sorry)

@[simps! toSubring]
def map [Nontrivial S] (f : R →+* S) (s : LocalSubring R) : LocalSubring S :=
  mk (s.1.map f)

@[simps! toSubring]
def range [LocalRing R] [Nontrivial S] (f : R →+* S) : LocalSubring S :=
  map f (mk ⊤)

@[stacks 00I9]
instance : PartialOrder (LocalSubring R) where
  le A B := ∃ h : A.1 ≤ B.1, IsLocalHom (Subring.inclusion h)
  le_refl := by
    rintro ⟨a, x⟩
    dsimp
    use le_rfl
    exact (isLocalHom_iff_comap_closedPoint (Subring.inclusion (le_refl a))).mpr rfl
  le_trans := by
    rintro ⟨a, x⟩ ⟨b, y⟩ ⟨c, z⟩ ⟨hab, hab_local⟩ ⟨hbc, hbc_local⟩
    let f := Subring.inclusion hab
    let g := Subring.inclusion hbc
    use le_trans hab hbc
    apply RingHom.isLocalHom_comp g f
  le_antisymm := by
    rintro ⟨a, x⟩ ⟨b, y⟩ ⟨hab, hab_loc⟩ ⟨hba, hba_loc⟩
    have hab_eq : a = b := le_antisymm hab hba
    subst hab_eq
    rfl

end LocalSubring

variable {K : Type*} [Field K]

def ValuationSubring.toLocalSubring (A : ValuationSubring K) : LocalSubring K where
  toSubring := A.toSubring
  localRing := A.localRing

-- by def
lemma ValuationSubring.toLocalSubring_injective :
    Function.Injective (ValuationSubring.toLocalSubring (K := K)) := by
  intro a b h
  ext x
  apply_fun (fun a ↦ x ∈ a.toSubring) at h
  rw [eq_iff_iff] at h
  exact h

def maximalLocalSubrings (K : Type*) [Field K] : Set (LocalSubring K) :=
  { R | IsMax R }


lemma map_maximalIdeal_eq_top_of_mem_maximalLocalSubrings {R : LocalSubring K}
    (hR : R ∈ maximalLocalSubrings K) {S : Subring K} (hS : R.toSubring < S) :
    (maximalIdeal R.toSubring).map (Subring.inclusion hS.le) = ⊤ := by
  let mR := (maximalIdeal R.toSubring).map (Subring.inclusion hS.le)
  by_contra h_is_not_top
  obtain ⟨M, h_is_max, h_incl⟩ := Ideal.exists_le_maximal _ h_is_not_top
  let Sₘ := Localization.AtPrime M
  let funStoK : S →+* K := S.subtype
  have h_funStoK_invertible_goto_units : ∀ (y : M.primeCompl), IsUnit (funStoK y) := by aesop
  let funSₘtoK : Sₘ →+* K := IsLocalization.lift h_funStoK_invertible_goto_units
  let fSₘ: LocalSubring K := LocalSubring.range funSₘtoK
  let funSₘtofSₘ : Sₘ →+* fSₘ.toSubring := funSₘtoK.rangeRestrict
  have SlefSₘ : S ≤ fSₘ.toSubring := by
    intro x hx
    simp [fSₘ]
    use (algebraMap S Sₘ) ⟨x, hx⟩
    rw [IsLocalization.lift_eq h_funStoK_invertible_goto_units _]
    rfl
  have RlefSₘ : R.toSubring ≤ fSₘ.toSubring := fun x hx => SlefSₘ (hS.le hx)
  have fStoSₘ_eq: (Subring.inclusion SlefSₘ).comp (Subring.inclusion hS.le) =
    (Subring.inclusion RlefSₘ) := by aesop
  have fRtoSₘ_eq : funSₘtofSₘ.comp ((algebraMap S Sₘ).comp (Subring.inclusion hS.le)) =
       (Subring.inclusion RlefSₘ) := by
    ext
    simp [funSₘtofSₘ]
    aesop
  have h_RleSₘ : R ≤ fSₘ := by
    refine ⟨RlefSₘ, ?_⟩
    rw [← fRtoSₘ_eq]
    refine ⟨?_⟩
    rintro ⟨a, h_a_inR⟩ h_fa_isUnit
    rw [RingHom.comp_apply, RingHom.comp_apply] at h_fa_isUnit
    have h_inS : a ∈ S := hS.le h_a_inR
    have SₘtofSₘ_bij : Function.Bijective funSₘtofSₘ := by exact?
    have h_funSₘtofSₘ_units: ∀ x : Sₘ, IsUnit (funSₘtofSₘ x) → IsUnit x := by
      let SₘeqfSₘ := (RingEquiv.ofBijective funSₘtofSₘ SₘtofSₘ_bij)
      exact IsUnit.of_map SₘeqfSₘ
    apply h_funSₘtofSₘ_units at h_fa_isUnit
    apply (IsLocalization.AtPrime.isUnit_to_map_iff Sₘ M _).mp at h_fa_isUnit
    change _ ∉ M at h_fa_isUnit
    have a_notIn_mR : (Subring.inclusion hS.le) ⟨a, h_a_inR⟩ ∉ mR :=
      fun a_1 ↦ h_fa_isUnit (h_incl a_1)
    apply mt (Ideal.mem_map_of_mem (Subring.inclusion hS.le)) at a_notIn_mR
    rw [mem_maximalIdeal, mem_nonunits_iff, not_not] at a_notIn_mR
    exact a_notIn_mR
  have h_RneSₘ : R ≠ fSₘ := by
    obtain ⟨x, hxS, hxR⟩ := (Set.ssubset_iff_of_subset (hS.le)).mp hS
    rintro rfl
    exact hxR (SlefSₘ hxS)
  have h_RltSₘ : R < fSₘ := lt_of_le_of_ne h_RleSₘ h_RneSₘ
  exact ne_of_lt (lt_of_le_of_lt (hR h_RltSₘ.le) h_RltSₘ) rfl
open scoped Polynomial

/--
Uses `map_maximalIdeal_eq_top_of_mem_maximalLocalSubrings`

https://stacks.math.columbia.edu/tag/00IC
-/
lemma mem_of_mem_maximalLocalSubrings_of_isIntegral {R : LocalSubring K}
    (hR : R ∈ maximalLocalSubrings K) {x : K} (hx : IsIntegral R.toSubring x) : x ∈ R.toSubring := sorry

/--
Uses `map_maximalIdeal_eq_top_of_mem_maximalLocalSubrings` and `mem_of_mem_maximalLocalSubrings_of_isIntegral`.

https://stacks.math.columbia.edu/tag/00IB
and
https://stacks.math.columbia.edu/tag/052K
-/
lemma LocalSubring.range_toLocalSubring :
    Set.range ValuationSubring.toLocalSubring = maximalLocalSubrings K := sorry

/--
by Zorn's lemma and `LocalSubring.range_toLocalSubring`

https://stacks.math.columbia.edu/tag/00IA
-/
lemma exists_valuationSubring_le (A : LocalSubring K) :
    ∃ B : ValuationSubring K, A ≤ B.toLocalSubring := sorry

/--
This is a repackaging of all the above.
Reduce to the case `R ⊆ S ⊆ K` using `LocalRing.of_surjective'`, by maximality `R = S`.
-/
lemma bijective_rangeRestrict_comp_of_valuationRing {R S K : Type*} [CommRing R]
    [IsDomain R] [ValuationRing R]
    [CommRing S] [LocalRing S] [Field K] [Algebra R K] [IsFractionRing R K]
    (f : R →+* S) (g : S →+* K) (h : g.comp f = algebraMap R K) [IsLocalHom f] :
    Function.Bijective (g.rangeRestrict.comp f) := sorry


/-- Repackaging of `exists_valuation_subring_dominates`.
Reduce to `R ⊆ K` by `LocalRing.of_surjective'`. -/
lemma exists_factor_valuationRing {R : Type*} [CommRing R] [LocalRing R] {K : Type*} [Field K]
    (f : R →+* K) :
    ∃ (A : ValuationSubring K) (h : _), IsLocalHom (f.codRestrict A.toSubring h) := by sorry

#min_imports
