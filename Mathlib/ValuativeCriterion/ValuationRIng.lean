import Mathlib

universe u

variable {K : Type u} [Field K] (A : ValuationSubring K)

open LocalRing

def LocalSubring (K : Type*) [CommRing K] : Type _ :=
  { s : Subring K // LocalRing s }

/-- https://stacks.math.columbia.edu/tag/00I9 -/
instance : PartialOrder (LocalSubring K) where
  le A B := ∃ h : A.1 ≤ B.1, IsLocalRingHom (Subring.inclusion h)
  le_refl := sorry
  le_trans := sorry
  le_antisymm := sorry

instance : CoeSort (LocalSubring K) (Type u) := ⟨fun s ↦ s.1⟩

instance : Membership K (LocalSubring K) := ⟨fun x K ↦ x ∈ K.1⟩

instance LocalSubring.localRing (A : LocalSubring K) : LocalRing A := A.2

def ValuationSubring.toLocalSubring (A : ValuationSubring K) : LocalSubring K :=
  ⟨A.toSubring, show LocalRing A by infer_instance⟩

-- by def
lemma ValuationSubring.toLocalSubring_injective :
    Function.Injective (ValuationSubring.toLocalSubring (K := K)) := sorry

def maximalLocalSubrings (K : Type*) [Field K] : Set (LocalSubring K) :=
  maximals (· ≤ ·) (Set.univ (α := LocalSubring K))

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
    (f : R →+* S) (g : S →+* K) (h : g.comp f = algebraMap R K) [IsLocalRingHom f] :
    Function.Bijective (g.rangeRestrict.comp f) := sorry

/-- Repackaging of `exists_valuation_subring_dominates`.
Reduce to `R ⊆ K` by `LocalRing.of_surjective'`. -/
lemma exists_factor_valuationRing {R : Type*} [CommRing R] [LocalRing R] {K : Type*} [Field K]
  (f : R →+* K) :
    ∃ (A : ValuationSubring K) (h : _), IsLocalRingHom (f.codRestrict A.toSubring h) := by sorry
