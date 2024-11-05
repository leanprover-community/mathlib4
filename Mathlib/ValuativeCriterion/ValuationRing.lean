import Mathlib

open LocalRing
open Set

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

instance (S : LocalSubring R) : LocalRing S.1 := S.2

@[simps! toSubring]
def map [Nontrivial S] (f : R →+* S) (s : LocalSubring R) : LocalSubring S := mk (s.1.map f)

@[simps! toSubring]
def range [LocalRing R] [Nontrivial S] (f : R →+* S) : LocalSubring S := map f (mk ⊤)

/-
instance : SetLike (LocalSubring R) R where
  coe A := A.1
  coe_injective' := by
    rintro ⟨_, _⟩ ⟨_, _⟩ h
    apply SetLike.coe_injective' at h
    congr

attribute [local -instance] SetLike.instPartialOrder
-/

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

variable {T : Type*} [CommRing T]

variable {K : Type*} [Field K]

def ValuationSubring.toLocalSubring (A : ValuationSubring K) : LocalSubring K where
  toSubring := A.toSubring
  localRing := A.localRing

-- by def
lemma ValuationSubring.toLocalSubring_injective :
    Function.Injective (ValuationSubring.toLocalSubring (K := K)) := by
  sorry -- TODO(jlcontreras)

def maximalLocalSubrings (K : Type*) [Field K] : Set (LocalSubring K) :=
  {R | Maximal (fun _ => True) R}

/--
If not, then it is contained in some maximal ideal. The localization of that maximal ideal is
a local subring that dominates `R`, contradicting the maximality of `R`.
-/
lemma map_maximalIdeal_eq_top_of_mem_maximalLocalSubrings {R : LocalSubring K}
    (hR : R ∈ maximalLocalSubrings K) {S : Subring K} (hS : R.1 < S) :
    (maximalIdeal R).map (Subring.inclusion hS.le) = ⊤ := sorry

open scoped Polynomial

/-- useful lemma. move me -/
lemma Algebra.mem_ideal_map_adjoin {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (x : S) (I : Ideal R) {y : adjoin R ({x} : Set S)} :
    y ∈ I.map (algebraMap R (adjoin R ({x} : Set S))) ↔
      ∃ p : R[X], (∀ i, p.coeff i ∈ I) ∧ Polynomial.aeval x p = y := sorry

/--
Uses `map_maximalIdeal_eq_top_of_mem_maximalLocalSubrings`

https://stacks.math.columbia.edu/tag/00IC
-/
lemma mem_of_mem_maximalLocalSubrings_of_isIntegral {R : LocalSubring K}
    (hR : R ∈ maximalLocalSubrings K) {x : K} (hx : IsIntegral R x) : x ∈ R := sorry

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

lemma exists_factor_valuationRing' {K : Type*} {R : Type*} [Field K] (R : LocalSubring K) :
    ∃ (A : ValuationSubring K), R ≤ A.toLocalSubring := by
  sorry

/-- Repackaging of `exists_valuation_subring_dominates`.
Reduce to `R ⊆ K` by `LocalRing.of_surjective'`. -/
lemma exists_factor_valuationRing {R : Type*} [CommRing R] [LocalRing R] {K : Type*} [Field K]
    (f : R →+* K) :
      ∃ (A : ValuationSubring K) (h : _), IsLocalHom (f.codRestrict A.toSubring h) := by sorry

lemma val_ring_is_max {K : Type*} [Field K] (A : ValuationSubring K) (B : LocalSubring K)
    (h : A.toLocalSubring ≤ B) : A.toLocalSubring = B := sorry

lemma exists_factor_valuationRing'_is_base {K : Type*} {R : Type*} [Field K]
    {R : ValuationSubring K} {A : ValuationSubring K}
      (h : R.toLocalSubring ≤ A.toLocalSubring) : R = A := by
  have : R.toLocalSubring = A.toLocalSubring := val_ring_is_max R A.toLocalSubring h
  sorry

-- instance {K : Type*} [Field K] (A : ValuationSubring K) :
--     LocalRing A.subtype.range := by sorry

def val_subriing_from_val_ring (R : Type*) [CommRing R] [IsDomain R] [valuationRing : ValuationRing R]
    (K : Type*) [field : Field K] [algebra : Algebra R K] [isFractionRing : IsFractionRing R K] :
      ValuationSubring K where
  carrier := sorry
  mul_mem' := sorry
  one_mem' := sorry
  add_mem' := sorry
  zero_mem' := sorry
  neg_mem' := sorry
  mem_or_inv_mem' := sorry

lemma range_of_local_ring_is_itself {K : Type*} [Field K] (A : LocalSubring K) :
    LocalSubring.range A.1.subtype = A := by
  sorry

lemma range_of_val_ring_is_itself {K : Type*} [Field K] (A : ValuationSubring K) :
    LocalSubring.range A.subtype = A.toLocalSubring := by
  sorry

lemma val_subriing_from_val_ring_eq_local_subring_inclusion (R : Type*) [CommRing R] [IsDomain R]
    [valuationRing : ValuationRing R]
      (K : Type*) [field : Field K] [algebra : Algebra R K] [isFractionRing : IsFractionRing R K] :
        (val_subriing_from_val_ring R K).toLocalSubring = LocalSubring.range (algebraMap R K) := sorry

lemma obivious {R : Type*} {S : Type*} [Ring R] [Ring S] (f : R  →+* S) :
    ∀ (x : R), f x ∈ Subring.map f ⊤ := by
  intro _
  simp only [Subring.mem_map, Subring.mem_top, true_and, exists_apply_eq_apply]

noncomputable def map_to_injective_range {R : Type*} {S : Type*} {K : Type*}
    [Ring R] [Ring S] [Ring K]
      {f : R →+* K} (hf : Function.Injective f) {g : S →+* K}
        (h : Subring.map f ⊤ = Subring.map g ⊤) :=
  (Subring.subtype _).comp <|
    (Subring.equivMapOfInjective ⊤ f hf).symm.toRingHom.comp <|
      (Subring.inclusion <| le_of_eq h.symm).comp <|
        g.codRestrict (Subring.map g ⊤) (obivious g)

lemma map_to_injective_range_comm {R : Type*} {S : Type*} {K : Type*}
    [Ring R] [Ring S][Ring K]
      {f : R→+* K} (hf : Function.Injective f) {g : S →+* K}
        (h : Subring.map f ⊤ = Subring.map g ⊤) :
          (f.comp <| map_to_injective_range hf h) = g := sorry

lemma map_to_injective_range_retract {R : Type*} {S : Type*} {K : Type*}
    [Ring R] [Ring S][Ring K]
      {f : R →+* K} (hf : Function.Injective f) {g : S →+* K}
        (h : Subring.map f ⊤ = Subring.map g ⊤)
          (ι : R →+* S) (is_comp : f = g.comp ι) :
            (map_to_injective_range hf h).comp ι = 1 := sorry
