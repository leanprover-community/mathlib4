/-
Copyright (c) 2026 Yuxuan Xiao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxuan Xiao
-/
module

public import Mathlib.Algebra.MvPolynomial.CharacteristicSet.AscendingSet
public import Mathlib.Algebra.MvPolynomial.CharacteristicSet.PseudoDivision
public import Mathlib.RingTheory.Nullstellensatz

/-!
# Characteristic Set Method (Wu's Method)

This file implements the core algorithms of Wu's Method for solving systems of algebraic equations.

## Main Concepts

1. **Characteristic Set (CS)**: A special triangular set contained in a polynomial set `PS`
  that generates the same ideal up to saturation by initials.
2. **Zero Decomposition**:
  The process of decomposing the zero set of `PS` into the union of zero sets of triangular sets.
  `Zero(PS) = ⋃ Zero(CSᵢ/IPᵢ)` where `CSᵢ` are triangular sets and `IPᵢ` are products of initials.

## Main Algorithms

* `MvPolynomial.List.characteristicSet`: Computes a characteristic set of a list of polynomials.
* `MvPolynomial.List.zeroDecomposition`:
  Decomposes the zero set of a polynomial system into a finite set of triangular systems.

## Main Theorems

* Well-Ordering Principles:
  - `vanishingSet_diff_initialProd_subset`: `Zero(CS/IP) ⊆ Zero(PS)`
  - `vanishingSet_diff_initialProd_eq`: `Zero(CS/IP) = Zero(PS/IP)`
  - `vanishingSet_decomposition`: `Zero(PS) = Zero(CS/IP) ∪ ⋃_{CS} Zero(PS ∪ {init(p)})`
* `characteristicSet_isCharacteristicSet`: The algorithm computes a valid characteristic set
* `vanishingSet_eq_zeroDecomposition_union`: Zero Decomposition Theorem.
  The variety of the input system is exactly the union of the "quasi-varieties"
  defined by the computed triangular sets.

-/

@[expose] public section

open MvPolynomial TriangularSet AscendingSet

variable {R σ : Type*}

namespace MvPolynomial

/-! ### Vanishing Sets -/

section VanishingSet

variable [CommSemiring R] {α : Type*} [Membership (MvPolynomial σ R) α]
variable (K : Type*) [CommSemiring K] [Algebra R K] (p : MvPolynomial σ R) (a : α)

/-- The set of points in `K ^ σ` where all polynomials in `a` vanish.
It is the same as `zeroLocus K (Ideal.span a)` for `a : Set (MvPolynomial σ R)` -/
def vanishingSet : Set (σ → K) := {x | ∀ p ∈ a, p.aeval x = 0}

/-- The set of points where a single polynomial `p` vanishes. -/
def singleVanishingSet : Set (σ → K) := {x | aeval x p = 0}

theorem vanishingSet_singleton_eq_singleVanishingSet :
    vanishingSet K ({p} : Set (MvPolynomial σ R)) = singleVanishingSet K p := by
  simp only [vanishingSet, Set.mem_singleton_iff, forall_eq, singleVanishingSet]

end VanishingSet

variable [Field R] (K : Type*) [Field K] [Algebra R K] (PS : Set (MvPolynomial σ R))

theorem vanishingSet_eq_zeroLocus_span : vanishingSet K PS = zeroLocus K (Ideal.span PS) :=
  (zeroLocus_span PS).symm

theorem vanishingSet_eq_zeroLocus_span' {α : Type*} [Membership (MvPolynomial σ R) α] (a : α) :
    vanishingSet K a = zeroLocus K (Ideal.span {p | p ∈ a}) :=
  vanishingSet_eq_zeroLocus_span K {p | p ∈ a}

end MvPolynomial

variable [Field R] [DecidableEq R] [LinearOrder σ] {α : Type*}
variable [Membership (MvPolynomial σ R) α] (K : Type*)

/-! ### Characteristic Set Properties -/

/-- A Triangular Set `CS` is a Characteristic Set for `a` if:
1. Every element in `a` reduce to 0 modulo `CS`.
2. `Zero(a) ⊆ Zero(CS)` (geometric containment). -/
def TriangularSet.isCharacteristicSet [CommSemiring K] [Algebra R K]
    (CS : TriangularSet σ R) (a : α) : Prop :=
  (∀ g ∈ a, (0 : MvPolynomial σ R).isSetRemainder g CS) ∧ vanishingSet K a ⊆ vanishingSet K CS

namespace CharacteristicSet

variable [Field K] [Algebra R K] {PS : α} {CS : TriangularSet σ R}

/-- Well-Ordering Principle (1): `Zero(CS/IP) ⊆ Zero(PS)`.
If all polynomials in `PS` reduce to 0 modulo `CS`, then any zero of `CS`
that isn't a zero of `IP` must be a zero of `PS`. -/
theorem vanishingSet_diff_initialProd_subset
    (h : (∀ g ∈ PS, (0 : MvPolynomial σ R).isSetRemainder g CS)) :
    vanishingSet K CS \ singleVanishingSet K (initialProd CS.toFinset) ⊆
      vanishingSet K PS := by
  refine Set.diff_subset_iff.mpr (fun x hx ↦ ?_)
  simp only [vanishingSet, singleVanishingSet, Set.mem_setOf_eq, Set.mem_union] at *
  simp only [or_iff_not_imp_right, not_forall, forall_exists_index, initialProd]
  intro p hp1 hp2
  rcases (h p hp1).2 with ⟨es, qs, h1, h2⟩
  rewrite [add_zero] at h2
  -- If x is a zero of CS but not of initials, and rem(p, CS) = 0, then p(x) must be 0.
  have : ∃ i : Fin es.length, (aeval x) (CS i).initial = 0 ∧ ¬es[i] = 0 := by
    have := congr_arg (aeval x) h2
    simpa [(forall_mem_iff_forall_index' h1.2).mp hx, hp2, Finset.prod_eq_zero_iff] using this
  rcases this with ⟨⟨i, hi1⟩, (hi2 : (aeval x) (CS i).initial = 0), _⟩
  rewrite [map_prod, Finset.prod_eq_zero_iff]
  exact ⟨CS i, mem_toFinset_iff.mpr <| apply_mem <| h1.1 ▸ hi1, hi2⟩

/-- Well-Ordering Principle (2): `Zero(CS/IP) = Zero(PS/IP)`. -/
theorem vanishingSet_diff_initialProd_eq (h : CS.isCharacteristicSet K PS) :
    vanishingSet K CS \ singleVanishingSet K (initialProd CS.toFinset) =
      vanishingSet K PS \ singleVanishingSet K (initialProd CS.toFinset) := by
  refine Set.Subset.antisymm ?_ (Set.diff_subset_diff_left h.2)
  refine Set.subset_diff.mpr ⟨?_ ,Set.disjoint_sdiff_left⟩
  exact vanishingSet_diff_initialProd_subset K h.1

/-- Well-Ordering Principle (3): `Zero(PS) = Zero(CS/IP) ∪ ⋃_{CS} Zero(PS ∪ {init(p)})` -/
theorem vanishingSet_decomposition (h : CS.isCharacteristicSet K PS) : vanishingSet K PS =
      vanishingSet K CS \ singleVanishingSet K (initialProd CS.toFinset) ∪
      ⋃ p ∈ CS, vanishingSet K PS ∩ singleVanishingSet K p.initial := by
  have : (⋃ p ∈ CS, vanishingSet K PS ∩ singleVanishingSet K p.initial) =
      vanishingSet K PS ∩ singleVanishingSet K (initialProd CS.toFinset) := Set.ext fun x ↦ by
    simp [vanishingSet, singleVanishingSet, initialProd, Finset.prod_eq_zero_iff]
  rewrite [vanishingSet_diff_initialProd_eq K h, this]
  exact (Set.diff_union_inter _ _).symm

end CharacteristicSet

namespace MvPolynomial
namespace List

variable [Finite σ] [HasBasicSet σ R] (l₀ l : List (MvPolynomial σ R))

/-! ### Characteristic Set Algorithm -/

-- A helper lemma: adding pseudo-remainders strictly decreases the order.
omit [Finite σ] in
lemma characteristicSetGo_decreasing (BS : TriangularSet σ R) (lBS RS : List (MvPolynomial σ R))
    (hRS : RS ≠ []) (hBS : BS = l.basicSet.val) (hlBS : lBS = BS.toList)
    (hRS1 : RS = ((l \ lBS).map fun p ↦ (p.setPseudo BS).remainder).filter (· ≠ 0)) :
    (l₀ ++ RS ++ lBS).basicSet < l.basicSet := by
  rewrite [hRS1, hlBS, hBS] at hRS ⊢
  apply TriangularSet.lt_of_lt_of_equiv ?_ l.basicSet_toList_equiv
  apply basicSet_append_lt_of_exists_reducedToSet
  have ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ hRS
  refine ⟨p, List.mem_append_right _ hp, of_decide_eq_true (List.mem_filter.mp hp).2, ?_⟩
  have ⟨q, _, hq2⟩ := List.mem_map.mp (List.mem_filter.mp hp).1
  suffices l.basicSet ≈ l.basicSet.toList.basicSet by
    apply (reducedToSet_congr_right this).mp
    exact hq2 ▸ q.setPseudo_remainder_reducedToSet _
  exact Setoid.symm l.basicSet_toList_equiv

/-- The recursive algorithm for computing the Characteristic Set -/
noncomputable def characteristicSet.go [Finite σ] (l₀ l : List (MvPolynomial σ R))
    : TriangularSet σ R :=
  let BS := l.basicSet.val
  let lBS := BS.toList
  let RS : List _ := ((l \ lBS).map fun p ↦ (p.setPseudo BS).remainder).filter (· ≠ 0)
  if RS = [] then BS
  else go l₀ (l₀ ++ RS ++ lBS)
  termination_by l.basicSet
  decreasing_by
    exact characteristicSetGo_decreasing l₀ l _ _ _ (by assumption) rfl rfl rfl

/--
Computes the Characteristic Set of a polynomial list `l`.
Algorithm:
1. Let `l₀ = l`.
2. Compute `BS = BasicSet(l)`.
3. Compute remainders `RS` of `l \ BS` with respect to `BS`.
4. If `RS` is empty, `BS` is the characteristic set.
5. If not, set `l = l₀ ++ RS ++ BS` and go to step 2.
Termination is guaranteed by the well-ordering of orders.
-/
noncomputable def characteristicSet : TriangularSet σ R := characteristicSet.go l l

lemma zero_isSetRemainder_characteristicSetGo : l₀ ⊆ l → ∀ p ∈ l₀,
    (0 : MvPolynomial σ R).isSetRemainder p (characteristicSet.go l₀ l) := by
  induction l using characteristicSet.go.induct l₀ with
  | case1 l BS lBS RS h =>
    intro hl p hp1
    rewrite [characteristicSet.go, if_pos h]
    apply isSetRemainder_of_eq_setPseudo_remainder
    rcases em (p ∈ lBS) with hp2 | hp2
    · exact setPseudo_remainder_eq_zero_of_mem BS (mem_toList_iff.mp hp2)
    have h : ∀ a ∈ l \ lBS, (a.setPseudo BS).remainder = 0 := by simpa [RS] using h
    exact (h p <| List.mem_diff_of_mem (hl hp1) hp2)
  | case2 l BS lBS RS h ih =>
    intro hl
    rewrite [characteristicSet.go, if_neg h]
    exact ih (List.subset_append_of_subset_left lBS (List.subset_append_left _ _))

variable (K : Type*) [CommSemiring K] [Algebra R K] (l₀ l : List (MvPolynomial σ R))

lemma characteristicSetGo_vanishingSet_subset : vanishingSet K l₀ = vanishingSet K l →
    vanishingSet K l₀ ⊆ vanishingSet K (characteristicSet.go l₀ l) := by
  simp only [vanishingSet, Set.setOf_subset_setOf]
  induction l using characteristicSet.go.induct l₀ with
  | case1 l BS lBS RS h =>
    intro hl x hx p hp
    rewrite [characteristicSet.go, if_pos h] at hp
    have hx : ∀ p ∈ l, aeval x p = 0 := (Set.ext_iff.mp hl x).mp hx
    exact hx p <| l.basicSet_subset hp
  | case2 l BS lBS RS h ih =>
    intro hl
    rewrite [characteristicSet.go, if_neg h]
    refine ih (Set.ext fun x ↦ ?_)
    simp only [Set.mem_setOf_eq, List.append_assoc, List.mem_append]
    have hl := Set.mem_setOf_eq ▸ Set.mem_setOf_eq ▸ (Set.ext_iff.mp hl x)
    refine ⟨fun hx p hp ↦ ?_, fun hx p hp ↦ hx _ (Or.inl hp)⟩
    refine Or.elim hp (hx _) fun hp ↦ ?_
    have hBS : ∀ ⦃q⦄, q ∈ BS → aeval x q = 0 := fun q hq ↦ (hl.mp hx) q <| l.basicSet_subset hq
    refine Or.elim hp (fun hp ↦ ?_) (fun hp ↦ hBS <| mem_toList_iff.mp hp)
    have ⟨⟨g, hg1, hg2⟩, hp⟩ : (∃ a ∈ l \ lBS, (a.setPseudo BS).remainder = p) ∧ ¬p = 0 :=
        by simpa [RS] using hp
    suffices heq : ∑ i : Fin (g.setPseudo BS).quotients.length,
        (aeval x) (g.setPseudo BS).quotients[i.1] * (aeval x) (BS i) = 0 by
      have := Eq.symm <| congrArg (aeval x) (hg2 ▸ g.setPseudo_equation BS)
      have hg2 : aeval x g = 0 := (hl.mp hx) _ <| (List.diff_subset _ _) hg1
      simpa [hg2, heq] using this
    refine Finset.sum_eq_zero fun ⟨i, hi⟩ _ ↦ ?_
    simp only [hBS (apply_mem <| g.length_setPseudo_quotients BS ▸ hi), mul_zero]

/-- The computed `characteristicSet` satisfies the required properties. -/
theorem characteristicSet_isCharacteristicSet :
    l.characteristicSet.isCharacteristicSet K l where
  left := zero_isSetRemainder_characteristicSetGo l l fun _ ↦ id
  right := characteristicSetGo_vanishingSet_subset K l l rfl

lemma characteristicSetGo_le_basicSet : characteristicSet.go l₀ l ≤ l.basicSet := by
  induction l using characteristicSet.go.induct l₀ with
  | case1 l BS lBS RS h =>
    rewrite [characteristicSet.go, if_pos h]
    exact le_refl _
  | case2 l BS lBS RS h ih =>
    rewrite [characteristicSet.go, if_neg h]
    refine le_trans ih (le_of_lt ?_)
    exact characteristicSetGo_decreasing l₀ l _ _ _ h rfl rfl rfl

theorem characteristicSet_le_basicSet : l.characteristicSet ≤ l.basicSet :=
  characteristicSetGo_le_basicSet l l

lemma characteristicSetGo_isAscendingSet : (characteristicSet.go l₀ l).isAscendingSet := by
  induction l using characteristicSet.go.induct l₀ with
  | case1 l BS lBS =>
    expose_names
    rewrite [characteristicSet.go, if_pos h]
    exact l.basicSet.prop
  | case2 l BS lBS RS =>
    expose_names
    rewrite [characteristicSet.go, if_neg h]
    exact ih1

theorem characteristicSet_isAscendingSet : l.characteristicSet.isAscendingSet :=
  characteristicSetGo_isAscendingSet l l

protected alias cs := characteristicSet
protected alias cs_isCharacteristicSet := characteristicSet_isCharacteristicSet
protected alias cs_le_basicSet := characteristicSet_le_basicSet
protected alias cs_isAscendingSet := characteristicSet_isAscendingSet

/-! ### Zero Decomposition -/

/--
Decomposes the zero set of `l` into a union of zero sets of triangular sets.
The algorithm recursively computes the characteristic set `CS`
and adds branches for the initials of `CS`.
-/
noncomputable def zeroDecomposition (l : List (MvPolynomial σ R)) : List (TriangularSet σ R) :=
  let CS := l.characteristicSet
  -- Recurse on: Initial(p) added to the system
  let subDecomp := (CS.toList.filter fun p ↦ p.mainVariable ≠ ⊥).attach.map
    fun ⟨p, _⟩ ↦ zeroDecomposition (p.initial :: CS.toList ++ l)
  CS :: subDecomp.flatten
  termination_by l.basicSet
  decreasing_by
    -- Proof that order(p.initial :: CS ++ l) < order(l)
    change ([p.initial] ++ CS.toList ++ l).basicSet < l.basicSet
    -- 1. Adding elements can only decrease order
    apply lt_of_le_of_lt (basicSet_ge_of_subset <| List.subset_append_left _ l)
    -- 2. Order(CS) ≤ Order(l)
    apply lt_of_lt_of_le ?_
      (le_trans (basicSet_toList_le_of_isAscendingSet l.cs_isAscendingSet) l.cs_le_basicSet)
    -- 3. Adding initial to CS strictly decreases order because initial is reduced wrt CS
    apply basicSet_append_lt_of_exists_reducedToSet
    use p.initial
    simp only [List.mem_cons, List.not_mem_nil, or_false, ne_eq, true_and]
    -- Get properties of p from filter/attach
    have hp : p ∈ CS ∧ ¬p.mainVariable = ⊥ :=  by expose_names; simpa using property
    refine ⟨initial_ne_zero (ne_zero_of_mem hp.1), fun q hq ↦ ?_⟩
    have : p.initial.reducedToSet CS :=
      AscendingSet.initial_reducedToSet_of_mainVariable_ne_bot' l.cs_isAscendingSet hp.1 hp.2
    exact this q <| mem_toList_iff.mp <| CS.toList.basicSet_subset hq

theorem isAscendingSet_of_mem_zeroDecomposition :
    ∀ CS ∈ l.zeroDecomposition, CS.isAscendingSet := by
  induction l using zeroDecomposition.induct with | case1 l CS ih =>
  intro CS' hCS'
  have hCS' : CS' = CS ∨ ∃ p, (p ∈ CS ∧ ¬p.mainVariable = ⊥) ∧
      CS' ∈ (p.initial :: CS.toList ++ l).zeroDecomposition := by
    unfold zeroDecomposition at hCS'; simpa using hCS'
  rcases hCS' with hCS' | ⟨p, ⟨hp1, hp2⟩, hp3⟩
  · exact hCS' ▸ l.cs_isAscendingSet
  exact ih p (List.mem_filter_of_mem (mem_toList_iff.mpr hp1) (decide_eq_true hp2)) _ hp3

theorem zero_isSetRemainder_of_mem_zeroDecomposition :
    ∀ CS ∈ l.zeroDecomposition, ∀ g ∈ l, (0 : MvPolynomial σ R).isSetRemainder g CS := by
  induction l using zeroDecomposition.induct with | case1 l CS ih =>
  intro CS' hCS'
  have hCS' : CS' = CS ∨ ∃ p, (p ∈ CS ∧ ¬p.mainVariable = ⊥) ∧
      CS' ∈ (p.initial :: CS.toList ++ l).zeroDecomposition := by
    unfold zeroDecomposition at hCS'; simpa using hCS'
  rcases hCS' with hCS' | ⟨p, ⟨hp1, hp2⟩, hp3⟩
  · exact hCS' ▸ zero_isSetRemainder_characteristicSetGo l l fun _ ↦ id
  have := ih p (List.mem_filter_of_mem (mem_toList_iff.mpr hp1) (decide_eq_true hp2)) _ hp3
  intro g hg
  exact this g <| List.mem_cons.mpr <| Or.inr <| List.mem_append.mpr (Or.inr hg)

variable (K : Type*) [Field K] [Algebra R K] (l₀ l : List (MvPolynomial σ R))

/-- **Zero Decomposition Theorem**:
The vanishing set of `l` is the union of the vanishing sets of the triangular sets
in `zeroDecomposition`, excluding the zeros of their initials.
`Zero(l) = ⋃_{CS ∈ ZD(l)} Zero(CS/IP(CS))`.
-/
theorem vanishingSet_eq_zeroDecomposition_union :
    vanishingSet K l = ⋃ CS ∈ l.zeroDecomposition,
      vanishingSet K CS \ singleVanishingSet K (initialProd CS.toFinset) := by
  induction l using zeroDecomposition.induct with | case1 l CS ih =>
  -- 1. Unfold recursion
  suffices vanishingSet K l = vanishingSet K CS \ singleVanishingSet K (initialProd CS.toFinset) ∪
      ⋃ p ∈ CS.toList.filter fun p ↦ p.mainVariable ≠ ⊥,
        ⋃ CS' ∈ (p.initial :: CS.toList ++ l).zeroDecomposition,
          vanishingSet K CS' \ singleVanishingSet K (initialProd CS'.toFinset) by
    rewrite [zeroDecomposition]; simpa using this
  -- 2. Apply decomposition theorem to the recursive structure
  suffices ⋃ p ∈ CS, vanishingSet K l ∩ singleVanishingSet K p.initial =
      ⋃ p ∈ CS.toList.filter fun p ↦ p.mainVariable ≠ ⊥,
        vanishingSet K (p.initial :: CS.toList ++ l) by
    rw [CharacteristicSet.vanishingSet_decomposition K (l.cs_isCharacteristicSet K),
      ← Set.iUnion₂_congr ih, this]
  -- 3. Prove equality of the union components (ignoring constants)
  ext x
  suffices (x ∈ vanishingSet K l ∧ ∃ p ∈ CS, x ∈ singleVanishingSet K p.initial) ↔
      ∃ p, (p ∈ CS ∧ ¬p.mainVariable = ⊥) ∧ x ∈ vanishingSet K (p.initial :: (CS.toList ++ l)) by
    simpa using this
  simp only [vanishingSet, Set.mem_setOf_eq, singleVanishingSet, List.mem_cons, List.mem_append,
    mem_toList_iff, forall_eq_or_imp]
  -- 4. Bidirectional implication
  refine ⟨fun ⟨hx, p, hp1, hp2⟩ ↦ ⟨p, ⟨hp1, ?_⟩, hp2, fun q hq ↦ ?_⟩,
    fun ⟨p, ⟨hp1, _⟩, hx1, hx2⟩ ↦ ⟨fun q hq ↦ hx2 q (Or.inr hq), p, hp1, hx1⟩⟩
  · -- Forward: if p is constant, Zero(p) is empty or total, but here p != 0 (from CS)
    contrapose! hp2
    simp [initial_of_mainVariable_eq_bot (ne_zero_of_mem hp1) hp2]
  · -- Forward: x is zero of everything in CS++l
    rcases hq with hq | hq
    · -- x ∈ Zero(CS) because x ∈ Zero(l) and CS is characteristic
      have := (l.cs_isCharacteristicSet K).2
      simp only [vanishingSet, Set.setOf_subset_setOf] at this
      exact this x hx q hq
    -- x ∈ Zero(l)
    exact hx q hq

end List
end MvPolynomial
