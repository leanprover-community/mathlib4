import Mathlib

universe u

open LocalRing

variable {K : Type*} [Ring K]

def LocalSubring (K : Type*) [Ring K] : Type _ :=
  { s : Subring K // LocalRing s }

def LocalSubring.of {K : Type*} [Ring K] (s : Subring K) [h : LocalRing s] : LocalSubring K := ⟨s, h⟩

-- maybe genralizable to [Ring R] [Ring S]
instance {R : Type*} {S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (s : LocalSubring R) : LocalRing <| Subring.map f s.1 where
  exists_pair_ne := sorry
  isUnit_or_isUnit_of_add_one := sorry

def LocalSubring.map {R : Type*} {S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (s : LocalSubring R) : LocalSubring S := LocalSubring.of (Subring.map f s.1)

instance topislocal (R : Type*) [Ring R] [LocalRing R] : LocalRing (⊤ : Subring R) := sorry

def LocalSubring.range {R : Type*} {S : Type*} [CommRing R] [LocalRing R] [CommRing S]
  (f : R →+* S) : LocalSubring S := LocalSubring.map f (LocalSubring.of ⊤)

lemma LocalSubring.range_eq_range {R : Type*} {S : Type*} [CommRing R] [LocalRing R] [CommRing S]
    (f : R →+* S) : (LocalSubring.range f).1 = Subring.map f ⊤ := by
  exact rfl

instance {K : Type*} [Ring K] (_ : LocalSubring K) : SetLike (LocalSubring K) K where
  coe A := A.1
  coe_injective' := by
    intro ⟨_, _⟩ ⟨_, _⟩ h
    replace h := SetLike.coe_injective' h
    congr

variable {K : Type u} [CommRing K]

/-- https://stacks.math.columbia.edu/tag/00I9 -/
instance : PartialOrder (LocalSubring K) where
  le A B := ∃ h : A.1 ≤ B.1, IsLocalRingHom (Subring.inclusion h)
  le_refl := sorry
  le_trans := sorry
  le_antisymm := sorry

instance : CoeSort (LocalSubring K) (Type u) := ⟨fun s ↦ s.1⟩

instance : Membership K (LocalSubring K) := ⟨fun x K ↦ x ∈ K.1⟩

instance LocalSubring.localRing (A : LocalSubring K) : LocalRing A := A.2

lemma domination_preserved_by_range {R : Type*} {S : Type*} {K : Type*}
    [CommRing R] [LocalRing R] [CommRing S] [LocalRing S] [CommRing K]
      (f : R →+* S) [IsLocalRingHom f] (g : S →+* K):
        (LocalSubring.range (g.comp f)) ≤ (LocalSubring.range g) := by
  sorry

variable {K : Type u} [Field K]

def ValuationSubring.toLocalSubring (A : ValuationSubring K) : LocalSubring K :=
  ⟨A.toSubring, show LocalRing A by infer_instance⟩

-- by def
lemma ValuationSubring.toLocalSubring_injective :
    Function.Injective (ValuationSubring.toLocalSubring (K := K)) := sorry

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
    (f : R →+* S) (g : S →+* K) (h : g.comp f = algebraMap R K) [IsLocalRingHom f] :
    Function.Bijective (g.rangeRestrict.comp f) := sorry

lemma exists_factor_valuationRing' {K : Type*} {R : Type*} [Field K] (R : LocalSubring K) :
    ∃ (A : ValuationSubring K), R ≤ A.toLocalSubring := by
  sorry

/-- Repackaging of `exists_valuation_subring_dominates`.
Reduce to `R ⊆ K` by `LocalRing.of_surjective'`. -/
lemma exists_factor_valuationRing {R : Type*} [CommRing R] [LocalRing R] {K : Type*} [Field K]
    (f : R →+* K) :
      ∃ (A : ValuationSubring K) (h : _), IsLocalRingHom (f.codRestrict A.toSubring h) := by sorry

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
