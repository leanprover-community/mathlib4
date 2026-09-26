/-
Copyright (c) 2026 Kristofer Gaudel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kristofer Gaudel
-/
module

public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
public import Mathlib.Data.Set.Card
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The Shapley–Folkman lemma

The **Shapley–Folkman lemma** measures how far a Minkowski sum of many sets in a
`d`-dimensional vector space is from being convex. If `x` lies in the sum
`∑ i, convexHull 𝕜 (t i)` of the convex hulls of finitely many sets `t i`, then `x` can be
written as `∑ i, y i` with `y i ∈ convexHull 𝕜 (t i)` for every `i`, and with the stronger
property `y i ∈ t i` for all but at most `d = finrank 𝕜 E` of the indices.

So when the number of summands greatly exceeds the dimension, the failure of convexity of a
Minkowski sum is confined to at most `d` summands. This underlies Starr's theorem on
approximate equilibria in economies with non-convex preferences, and duality gap estimates in
non-convex optimization.

## Main results

* `shapley_folkman`: the Shapley–Folkman lemma.

## Implementation notes

The proof is the classical lifting argument. Write `n` for the number of summands and
`d = finrank 𝕜 E`.

1. `exists_eq_sum_of_mem_sum_convexHull` splits `x` as `∑ i, y i` with
   `y i ∈ convexHull 𝕜 (t i)`.
2. The argument moves to the product space `E × (ι → 𝕜)`, where each point `z` of the `i`-th
   summand is tagged with the `i`-th standard basis vector as `tag 𝕜 i z = (z, Pi.single i 1)`,
   and `lifted 𝕜 t` collects all the tagged summands. Scaling by `n⁻¹` turns the decomposition
   of `x` into a convex combination, placing `(n⁻¹ • x, fun _ ↦ n⁻¹)` in
   `convexHull 𝕜 (lifted 𝕜 t)`; this is `lifted_mem_convexHull`.
3. Carathéodory's theorem, in the form `eq_pos_convex_span_of_mem_convexHull`, rewrites that
   point as a convex combination with positive weights of an affinely independent family drawn
   from `lifted 𝕜 t`.
4. The second component of every point of `lifted 𝕜 t` sums to `1`, so that family lies in an
   affine hyperplane of the `(d + n)`-dimensional space `E × (ι → 𝕜)` and hence has at most
   `d + n` members; this is `card_le_of_affineIndependent_of_sum_eq_one`.
5. Grouping the family into fibers according to its tags, the second components force the
   weights of each fiber to sum to `n⁻¹`. Rescaling each fiber by `n` yields points
   `y i ∈ convexHull 𝕜 (t i)` summing to `x`.
6. The fibers partition a set of at most `d + n` elements into `n` nonempty parts, so at most
   `d` of them have more than one element; this is `card_two_le_fiber_le`. A fiber consisting
   of a single element contributes a point of `t i` itself.

The `Fintype` instance produced by `eq_pos_convex_span_of_mem_convexHull` has to be introduced
with `let` rather than `have`, since `have` would discard its value and the resulting instance
would no longer match the one appearing in the convex combination already obtained.

## References

* R. Starr, *Quasi-equilibria in markets with non-convex preferences*, Econometrica 37 (1969),
  25–38.
* R. Schneider, *Convex bodies: the Brunn–Minkowski theory*, Theorem 3.1.2.

## Tags

convex hull, Minkowski sum, Shapley-Folkman, Caratheodory
-/

@[expose] public section

open Finset Module Set
open scoped Pointwise

universe u

variable {𝕜 : Type*} {E : Type u} {ι : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]

namespace ShapleyFolkman

/-! ### The lifted configuration

Points of distinct summands are tagged with distinct standard basis vectors of `ι → 𝕜`, so
that a convex combination of tagged points records in its second coordinate the total weight
it assigns to each summand.
-/

variable (𝕜) in
/-- Tag a point `z`, viewed as an element of the `i`-th summand, with the `i`-th standard
basis vector of `ι → 𝕜`. -/
def tag [DecidableEq ι] (i : ι) (z : E) : E × (ι → 𝕜) :=
  (z, Pi.single i 1)

variable (𝕜) in
/-- The union of the tagged copies of the summands `t i`, as a subset of `E × (ι → 𝕜)`. -/
def lifted [DecidableEq ι] (t : ι → Set E) : Set (E × (ι → 𝕜)) :=
  ⋃ i, tag 𝕜 i '' t i

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E] in
/-- Membership in `lifted 𝕜 t`, unfolded. -/
theorem mem_lifted_iff [DecidableEq ι] {t : ι → Set E} {p : E × (ι → 𝕜)} :
    p ∈ lifted 𝕜 t ↔ ∃ i, ∃ z ∈ t i, tag 𝕜 i z = p := by
  simp [lifted]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Evaluated at any index, the sum of all the standard basis vectors of `ι → 𝕜` is `1`. -/
theorem sum_single_apply [Fintype ι] [DecidableEq ι] (j : ι) :
    ∑ i, Pi.single (M := fun _ ↦ 𝕜) i 1 j = 1 := by
  simp

/-! ### Ingredients of the proof -/

omit [IsStrictOrderedRing 𝕜] in
/-- A point of a finite Minkowski sum of convex hulls decomposes as a sum of points of those
hulls. -/
theorem exists_eq_sum_of_mem_sum_convexHull [Fintype ι] {t : ι → Set E} {x : E}
    (hx : x ∈ ∑ i, convexHull 𝕜 (t i)) :
    ∃ y : ι → E, (∀ i, y i ∈ convexHull 𝕜 (t i)) ∧ ∑ i, y i = x := by
  obtain ⟨g, hg, hsum⟩ := (mem_fintype_sum _ _).mp hx
  exact ⟨g, hg, hsum⟩

/-- A combination of points of `s` with nonnegative weights summing to `c > 0` lies in
`convexHull 𝕜 s` after rescaling by `c⁻¹`. -/
theorem inv_smul_sum_mem_convexHull {s : Set E} {κ : Type*} [Fintype κ] {w : κ → 𝕜}
    {z : κ → E} (hw : ∀ j, 0 ≤ w j) {c : 𝕜} (hc : 0 < c) (hsum : ∑ j, w j = c)
    (hz : ∀ j, z j ∈ s) :
    c⁻¹ • ∑ j, w j • z j ∈ convexHull 𝕜 s := by
  rw [Finset.smul_sum]
  simp_rw [smul_smul]
  refine (convex_convexHull 𝕜 s).sum_mem (fun j _ ↦ ?_) ?_ (fun j _ ↦ ?_)
  · exact mul_nonneg (inv_nonneg.2 hc.le) (hw j)
  · rw [← Finset.mul_sum, hsum, inv_mul_cancel₀ hc.ne']
  · exact subset_convexHull 𝕜 s (hz j)

/-- If `y i ∈ convexHull 𝕜 (t i)` for every `i`, then scaling `∑ i, y i` and the all-ones tag
by `n⁻¹`, where `n = Fintype.card ι`, gives a point of `convexHull 𝕜 (lifted 𝕜 t)`.

The tagged copy `tag 𝕜 i '' t i` is the product `t i ×ˢ {Pi.single i 1}`, whose convex hull is
`convexHull 𝕜 (t i) ×ˢ {Pi.single i 1}` and therefore contains `(y i, Pi.single i 1)`.
Averaging those `n` points with equal weights `n⁻¹` stays inside the hull. -/
theorem lifted_mem_convexHull [Fintype ι] [DecidableEq ι] [Nonempty ι] {t : ι → Set E}
    {y : ι → E} (hy : ∀ i, y i ∈ convexHull 𝕜 (t i)) :
    ((Fintype.card ι : 𝕜)⁻¹ • ∑ i, y i, fun _ ↦ (Fintype.card ι : 𝕜)⁻¹) ∈
      convexHull 𝕜 (lifted 𝕜 t) := by
  have hnpos : (0 : 𝕜) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have key : ∀ i, ((y i, Pi.single i 1) : E × (ι → 𝕜)) ∈ convexHull 𝕜 (lifted 𝕜 t) := by
    intro i
    refine convexHull_mono (Set.subset_iUnion (fun i ↦ tag 𝕜 i '' t i) i) ?_
    have himg : tag 𝕜 i '' t i = t i ×ˢ ({Pi.single i 1} : Set (ι → 𝕜)) := by
      ext p
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨hz, rfl⟩
      · rintro ⟨h1, h2⟩
        rw [Set.mem_singleton_iff] at h2
        exact ⟨p.1, h1, Prod.ext rfl h2.symm⟩
    rw [himg, convexHull_prod, convexHull_singleton]
    exact ⟨hy i, rfl⟩
  have hrw : (((Fintype.card ι : 𝕜)⁻¹ • ∑ i, y i, fun _ ↦ (Fintype.card ι : 𝕜)⁻¹) :
        E × (ι → 𝕜))
      = ∑ i, ((Fintype.card ι : 𝕜)⁻¹) • ((y i, Pi.single i 1) : E × (ι → 𝕜)) := by
    refine Prod.ext ?_ ?_
    · simp [Prod.fst_sum, Finset.smul_sum]
    · funext j
      simp [Prod.snd_sum, Finset.sum_apply, ← Finset.mul_sum]
  rw [hrw]
  refine (convex_convexHull 𝕜 _).sum_mem (fun i _ ↦ inv_nonneg.2 hnpos.le) ?_ (fun i _ ↦ key i)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hnpos.ne']

/-- An affinely independent family in `E × (ι → 𝕜)` whose second components all sum to `1` has
at most `finrank 𝕜 E + Fintype.card ι` members.

Such a family lies in the affine hyperplane `{p | ∑ i, p.2 i = 1}`, whose direction is the
kernel of the surjective functional `p ↦ ∑ i, p.2 i`, of dimension one less than that of
`E × (ι → 𝕜)`; an affinely independent family spans an affine subspace of dimension
`card κ - 1` inside it. -/
theorem card_le_of_affineIndependent_of_sum_eq_one [FiniteDimensional 𝕜 E] [Fintype ι]
    {κ : Type*} [Fintype κ] {q : κ → E × (ι → 𝕜)} (hq : AffineIndependent 𝕜 q)
    (hsum : ∀ j, ∑ i, (q j).2 i = 1) :
    Fintype.card κ ≤ finrank 𝕜 E + Fintype.card ι := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  -- With `ι` empty the hypothesis reads `0 = 1`, so `κ` is empty as well.
  · have : IsEmpty κ := ⟨fun j ↦ by simpa using hsum j⟩
    simp
  · set ℓ : (E × (ι → 𝕜)) →ₗ[𝕜] 𝕜 :=
      (∑ i, LinearMap.proj i) ∘ₗ LinearMap.snd 𝕜 E (ι → 𝕜) with hℓ
    have hℓapp : ∀ p : E × (ι → 𝕜), ℓ p = ∑ i, p.2 i := by
      intro p
      simp [hℓ]
    have hsurj : LinearMap.range ℓ = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro c
      obtain ⟨i₀⟩ := hι
      exact ⟨(0, Pi.single i₀ c), by simp [hℓapp]⟩
    have hspan : vectorSpan 𝕜 (Set.range q) ≤ LinearMap.ker ℓ := by
      rw [vectorSpan_def, Submodule.span_le]
      rintro v hv
      rw [Set.mem_vsub] at hv
      obtain ⟨a, ⟨j, rfl⟩, b, ⟨j', rfl⟩, rfl⟩ := hv
      have hd : ℓ (q j -ᵥ q j') = ℓ (q j) - ℓ (q j') := by rw [vsub_eq_sub, map_sub]
      simp only [SetLike.mem_coe, LinearMap.mem_ker, hd, hℓapp, hsum, sub_self]
    have hcard := hq.card_le_finrank_succ
    have hmono : finrank 𝕜 (vectorSpan 𝕜 (Set.range q)) ≤ finrank 𝕜 (LinearMap.ker ℓ) :=
      Submodule.finrank_mono hspan
    have hrank : finrank 𝕜 (LinearMap.range ℓ) + finrank 𝕜 (LinearMap.ker ℓ)
        = finrank 𝕜 (E × (ι → 𝕜)) := LinearMap.finrank_range_add_finrank_ker ℓ
    rw [hsurj, finrank_top, Module.finrank_self, Module.finrank_prod, Module.finrank_pi] at hrank
    omega

/-- If `Fintype.card ι` nonempty parts have sizes summing to at most `d + Fintype.card ι`, then
at most `d` of them have size at least `2`. -/
theorem card_two_le_fiber_le [Fintype ι] {d : ℕ} {k : ι → ℕ} (h1 : ∀ i, 1 ≤ k i)
    (h2 : ∑ i, k i ≤ d + Fintype.card ι) :
    #{i ∈ Finset.univ | 2 ≤ k i} ≤ d := by
  classical
  set s : Finset ι := {i ∈ Finset.univ | 2 ≤ k i}
  have hsplit : ∑ i ∈ s, k i + ∑ i ∈ sᶜ, k i = ∑ i, k i := Finset.sum_add_sum_compl s k
  have hA : #s • 2 ≤ ∑ i ∈ s, k i :=
    Finset.card_nsmul_le_sum s k 2 fun i hi ↦ (Finset.mem_filter.1 hi).2
  have hB : #sᶜ • 1 ≤ ∑ i ∈ sᶜ, k i := Finset.card_nsmul_le_sum _ k 1 fun i _ ↦ h1 i
  have hcard : #s + #sᶜ = Fintype.card ι := Finset.card_add_card_compl s
  simp only [smul_eq_mul] at hA hB
  omega

end ShapleyFolkman

open ShapleyFolkman in
/-- **Shapley–Folkman lemma**: a point of a Minkowski sum of the convex hulls of finitely many
sets in a `d`-dimensional space is a sum of points of those hulls, at most `d` of which fail to
lie in the sets themselves. -/
theorem shapley_folkman [Fintype ι] [FiniteDimensional 𝕜 E] {t : ι → Set E} {x : E}
    (hx : x ∈ ∑ i, convexHull 𝕜 (t i)) :
    ∃ y : ι → E, (∀ i, y i ∈ convexHull 𝕜 (t i)) ∧ ∑ i, y i = x ∧
      {i | y i ∉ t i}.ncard ≤ finrank 𝕜 E := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨0, fun i ↦ (hι.false i).elim, ?_, ?_⟩
    · simp only [Finset.univ_eq_empty, Finset.sum_empty] at hx ⊢
      exact (Set.mem_zero.mp hx).symm
    · have hempty : {i | (0 : ι → E) i ∉ t i} = ∅ := Set.eq_empty_of_isEmpty _
      rw [hempty]
      simp
  obtain ⟨y, hy, hyx⟩ := exists_eq_sum_of_mem_sum_convexHull hx
  have hnpos : (0 : 𝕜) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hp := lifted_mem_convexHull hy
  rw [hyx] at hp
  obtain ⟨κ, hfin, q, w, hrange, hai, hwpos, hwsum, hcomb⟩ :=
    eq_pos_convex_span_of_mem_convexHull hp
  -- `let`, not `have`: `have` discards the value, and the instance would then no longer match
  -- the one inside `hcomb`.
  let := hfin
  -- Componentwise `smul` on the product, as `rfl`-lemmas usable by `simp only`.
  have hsm1 : ∀ (c : 𝕜) (p : E × (ι → 𝕜)), (c • p).1 = c • p.1 := fun _ _ ↦ rfl
  have hsm2 : ∀ (c : 𝕜) (p : E × (ι → 𝕜)), (c • p).2 = c • p.2 := fun _ _ ↦ rfl
  have hmem : ∀ j, ∃ i, ∃ z ∈ t i, tag 𝕜 i z = q j := fun j ↦
    mem_lifted_iff.mp (hrange (Set.mem_range_self j))
  choose idx pt hpt hqeq using hmem
  have hq1 : ∀ j, (q j).1 = pt j := fun j ↦ by rw [← hqeq j]; rfl
  have hq2 : ∀ j, (q j).2 = Pi.single (idx j) 1 := fun j ↦ by rw [← hqeq j]; rfl
  set F : ι → Finset κ := fun i ↦ {j ∈ Finset.univ | idx j = i} with hF
  -- Reading the second coordinate at `i` shows the fiber over `i` has total weight `n⁻¹`.
  have hsnd : ∀ i, ∑ j ∈ F i, w j = (Fintype.card ι : 𝕜)⁻¹ := by
    intro i
    have h := congrArg (fun p : E × (ι → 𝕜) ↦ p.2 i) hcomb
    simp only [Prod.snd_sum, hsm2, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hq2] at h
    simp only [hF, Finset.sum_filter]
    rw [← h]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Pi.single_apply]
    by_cases hji : idx j = i
    · simp [hji]
    · simp [hji, Ne.symm hji]
  have hFne : ∀ i, (F i).Nonempty := by
    intro i
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have h := hsnd i
    rw [hemp, Finset.sum_empty] at h
    exact inv_ne_zero hnpos.ne' h.symm
  refine ⟨fun i ↦ (Fintype.card ι : 𝕜) • ∑ j ∈ F i, w j • pt j, ?_, ?_, ?_⟩
  · intro i
    change (Fintype.card ι : 𝕜) • ∑ j ∈ F i, w j • pt j ∈ convexHull 𝕜 (t i)
    have hexp : (Fintype.card ι : 𝕜) • ∑ j ∈ F i, w j • pt j
        = ∑ j ∈ F i, ((Fintype.card ι : 𝕜) * w j) • pt j := by
      rw [Finset.smul_sum]; simp_rw [smul_smul]
    rw [hexp]
    refine (convex_convexHull 𝕜 (t i)).sum_mem (fun j _ ↦ mul_nonneg hnpos.le (hwpos j).le)
      ?_ (fun j hj ↦ ?_)
    · rw [← Finset.mul_sum, hsnd i, mul_inv_cancel₀ hnpos.ne']
    · have hji : idx j = i := by simp only [hF, Finset.mem_filter] at hj; exact hj.2
      rw [← hji]
      exact subset_convexHull 𝕜 _ (hpt j)
  · have hfst : ∑ j, w j • pt j = (Fintype.card ι : 𝕜)⁻¹ • x := by
      have h := congrArg (fun p : E × (ι → 𝕜) ↦ p.1) hcomb
      simpa only [Prod.fst_sum, hsm1, hq1] using h
    calc ∑ i, (Fintype.card ι : 𝕜) • ∑ j ∈ F i, w j • pt j
        = (Fintype.card ι : 𝕜) • ∑ i, ∑ j ∈ F i, w j • pt j := by rw [Finset.smul_sum]
      _ = (Fintype.card ι : 𝕜) • ∑ j, w j • pt j := by
          simp only [hF]
          exact congrArg _ (Finset.sum_fiberwise Finset.univ idx _)
      _ = x := by rw [hfst, smul_smul, mul_inv_cancel₀ hnpos.ne', one_smul]
  · change {i | ((Fintype.card ι : 𝕜) • ∑ j ∈ F i, w j • pt j) ∉ t i}.ncard ≤ finrank 𝕜 E
    have hcardκ : Fintype.card κ ≤ finrank 𝕜 E + Fintype.card ι := by
      refine card_le_of_affineIndependent_of_sum_eq_one hai (fun j ↦ ?_)
      rw [hq2]
      simp
    have hpart : ∑ i, (F i).card = Fintype.card κ := by
      simp only [hF]
      rw [← Finset.card_univ]
      exact (Finset.card_eq_sum_card_fiberwise (fun j _ ↦ by simp)).symm
    have hbig : #{i ∈ Finset.univ | 2 ≤ (F i).card} ≤ finrank 𝕜 E := by
      refine card_two_le_fiber_le (fun i ↦ Finset.card_pos.mpr (hFne i)) ?_
      rw [hpart]; exact hcardκ
    -- A fiber with a single element `j₀` forces `w j₀ = n⁻¹`, so that summand is `pt j₀`.
    have hsub : {i | ((Fintype.card ι : 𝕜) • ∑ j ∈ F i, w j • pt j) ∉ t i}
        ⊆ (({i ∈ Finset.univ | 2 ≤ (F i).card} : Finset ι) : Set ι) := by
      intro i hi
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨Finset.mem_univ i, ?_⟩
      by_contra hcon
      push Not at hcon
      have hone : (F i).card = 1 := by
        have := Finset.card_pos.mpr (hFne i)
        omega
      obtain ⟨j₀, hj₀⟩ := Finset.card_eq_one.mp hone
      apply hi
      have hw₀ : w j₀ = (Fintype.card ι : 𝕜)⁻¹ := by
        have h := hsnd i
        rwa [hj₀, Finset.sum_singleton] at h
      have hidx : idx j₀ = i := by
        have hmem₀ : j₀ ∈ F i := by rw [hj₀]; exact Finset.mem_singleton_self j₀
        simp only [hF, Finset.mem_filter] at hmem₀
        exact hmem₀.2
      rw [hj₀, Finset.sum_singleton, hw₀, smul_smul, mul_inv_cancel₀ hnpos.ne', one_smul, ← hidx]
      exact hpt j₀
    calc {i | ((Fintype.card ι : 𝕜) • ∑ j ∈ F i, w j • pt j) ∉ t i}.ncard
        ≤ (({i ∈ Finset.univ | 2 ≤ (F i).card} : Finset ι) : Set ι).ncard :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = #{i ∈ Finset.univ | 2 ≤ (F i).card} := Set.ncard_coe_finset _
      _ ≤ finrank 𝕜 E := hbig
