/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.AffineSpace.Pointwise
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Affine equivalences and affine independence

This file proves theorems about the interaction between affine equivalences (automorphisms)
and affinely independent families. The main result is that affinely independent families
of the same size can be mapped to each other by affine automorphisms.

All theorems are formulated for affine spaces over arbitrary division rings, making them
applicable to real, complex, and p-adic spaces, among others. The affine spaces are modeled
as `AddTorsor V P` where `V` is a module over a division ring `𝕜` and `P` is the point space.

## Main results

* `affineIndependent_to_affineIndependent_automorphism`: Two affinely independent families
  `f, g : ι → P` with the same finite index type can be mapped to each other by an affine
  automorphism `T : P ≃ᵃ[𝕜] P`. This is Rockafellar's Theorem 1.6.

* `affineSubspace_automorphism_of_eq_dim`: Affine subspaces of the same dimension can be
  mapped to each other by an affine automorphism. This is Rockafellar's Corollary 1.6.1.

* `AffineIndependent.toBasis_of_span_eq_top`: An affinely independent family spanning the
  entire space gives rise to a linear basis via the difference map from any base point.

The file is organized into two sections:
1. **General Results**: Theorems that hold for any affine space (no finite-dimensionality required)
2. **Finite-Dimensional Results**: Theorems specific to finite-dimensional spaces

## References

* Rockafellar, "Convex Analysis" (1970), Theorem 1.6 and Corollary 1.6.1

## Tags

affine independence, affine automorphism, affine equivalence, affine dimension
-/

open Set AffineSubspace
open scoped Pointwise

/-- The affine dimension of a set in an affine space is the finite rank of the direction
of its affine span. -/
noncomputable def affineDim (𝕜 : Type*) {V : Type*} {P : Type*}
    [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]
    (s : Set P) : ℕ :=
  Module.finrank 𝕜 (affineSpan 𝕜 s).direction

/-!
## General Results

These theorems hold for affine spaces of any dimension (including infinite-dimensional spaces).
-/

section General

/-!
### Helper lemmas for affine independence
-/

/-- A proper affine subspace does not contain all points. -/
lemma AffineSubspace.exists_not_mem_of_ne_top
    {𝕜 : Type*} {V : Type*} {P : Type*}
    [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]
    (S : AffineSubspace 𝕜 P) (h : S ≠ ⊤) :
    ∃ p : P, p ∉ S := by
  have h_ne_univ : (S : Set P) ≠ Set.univ := by
    intro h_eq
    have h_top : S = ⊤ := SetLike.coe_injective h_eq
    exact h h_top
  exact (Set.ne_univ_iff_exists_notMem (S : Set P)).mp h_ne_univ

/-- If the affine span of the range of a function equals the entire space, then the index type
must be nonempty. -/
lemma Nonempty.of_affineSpan_range_eq_top
    {𝕜 : Type*} {V : Type*} {P : Type*}
    [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]
    {ι : Type*} (f : ι → P)
    (h : affineSpan 𝕜 (range f) = ⊤) : Nonempty ι := by
  by_contra h_empty
  rw [not_nonempty_iff] at h_empty
  have h_range_empty : range f = ∅ := range_eq_empty_iff.mpr h_empty
  have h_span_empty : affineSpan 𝕜 (range f) = ⊥ := by
    rw [h_range_empty]
    exact span_empty 𝕜 V P
  rw [h_span_empty] at h
  exact absurd h (bot_ne_top (α := AffineSubspace 𝕜 P))

/-- If two affine maps agree on a set that spans the entire space, then they are equal.

Affine maps are uniquely determined by their values on any spanning set. Affine independence
is not required for uniqueness, only spanning. -/
theorem AffineMap.ext_of_span_eq_top
    {𝕜 : Type*} {V₁ V₂ P₁ P₂ : Type*}
    [Ring 𝕜] [AddCommGroup V₁] [Module 𝕜 V₁] [AddTorsor V₁ P₁]
    [AddCommGroup V₂] [Module 𝕜 V₂] [AddTorsor V₂ P₂]
    {ι : Type*} [Fintype ι]
    (p : ι → P₁)
    (h_span : affineSpan 𝕜 (range p) = ⊤)
    (f g : P₁ →ᵃ[𝕜] P₂)
    (h_agree : ∀ i, f (p i) = g (p i)) :
    f = g := by
  ext x
  have hx : x ∈ affineSpan 𝕜 (range p) := by
    rw [h_span]
    exact AffineSubspace.mem_top 𝕜 V₁ x
  obtain ⟨w, hw_sum, hw_eq⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hx
  rw [hw_eq]
  rw [Finset.map_affineCombination Finset.univ p w hw_sum f,
      Finset.map_affineCombination Finset.univ p w hw_sum g]
  have : (f ∘ p : ι → P₂) = (g ∘ p : ι → P₂) := funext h_agree
  rw [this]

/-- If two affine automorphisms agree on a set that spans the entire space, then they are equal.

Specialization of `AffineMap.ext_of_span_eq_top` to affine automorphisms. -/
theorem AffineEquiv.ext_of_span_eq_top
    {𝕜 : Type*} {V : Type*} {P : Type*}
    [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]
    {ι : Type*} [Fintype ι]
    (p : ι → P)
    (h_span : affineSpan 𝕜 (range p) = ⊤)
    (T₁ T₂ : P ≃ᵃ[𝕜] P)
    (h_agree : ∀ i, T₁ (p i) = T₂ (p i)) :
    T₁ = T₂ := by
  rw [← AffineEquiv.toAffineMap_inj]
  exact AffineMap.ext_of_span_eq_top p h_span T₁.toAffineMap T₂.toAffineMap h_agree

/-!
### Extending affinely independent families
-/

set_option maxHeartbeats 400000 in
-- Type class inference for generalized affine space types requires more computation
-- than the specialized `InnerProductSpace ℝ E` version
/-- Extending an affinely independent family with a point outside its affine span preserves
affine independence.

This uses `Option.elim` to extend `f : ι → P` to `Option ι → P` by designating `p` as the
value at `none`. -/
lemma AffineIndependent.option_extend
    {𝕜 : Type*} {V : Type*} {P : Type*}
    [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {f : ι → P} (hf : AffineIndependent 𝕜 f)
    {p : P} (hp : p ∉ affineSpan 𝕜 (range f)) :
    AffineIndependent 𝕜 (fun o : Option ι => o.elim p f) := by
  let f' : Option ι → P := fun o => o.elim p f

  have h_sub : AffineIndependent 𝕜 (fun x : {y : Option ι // y ≠ none} => f' x) := by
    have : (fun x : {y : Option ι // y ≠ none} => f' x) =
           f ∘ (fun x => Option.get x.val (Option.ne_none_iff_isSome.mp x.prop)) := by
      ext ⟨x, hx⟩
      cases x with
      | some i => rfl
      | none => exact absurd rfl hx
    rw [this]
    let e : {y : Option ι // y ≠ none} ↪ ι :=
      ⟨fun x => Option.get x.val (Option.ne_none_iff_isSome.mp x.prop),
       fun ⟨x, hx⟩ ⟨y, hy⟩ h_eq => by
         simp only [Subtype.mk.injEq]
         cases x with
         | some i =>
           cases y with
           | some j => simp_all
           | none => exact absurd rfl hy
         | none => exact absurd rfl hx⟩
    exact hf.comp_embedding e

  have h_image_eq : f' '' {x : Option ι | x ≠ none} = range f := by
    ext y
    simp only [mem_image, Set.mem_setOf_eq, mem_range]
    constructor
    · intro ⟨x, hx_ne, hx_eq⟩
      cases x with
      | none => contradiction
      | some i => use i; exact hx_eq
    · intro ⟨i, hi⟩
      use some i
      exact ⟨Option.some_ne_none i, hi⟩

  have h_not_mem : f' none ∉ affineSpan 𝕜 (f' '' {x : Option ι | x ≠ none}) := by
    rw [h_image_eq]
    exact hp

  exact AffineIndependent.affineIndependent_of_notMem_span h_sub h_not_mem

set_option maxHeartbeats 400000 in
-- Type class inference for generalized affine space types requires more computation
-- than the specialized `InnerProductSpace ℝ E` version
/-- Two affinely independent families spanning affine subspaces with
equal direction finrank have the same cardinality.

This lemma does not require finite-dimensionality of the ambient space, only that
the affinely independent families are finite (which is automatic in finite-dimensional spaces). -/
lemma affineIndependent_card_eq_of_finrank_direction_eq
    {𝕜 : Type*} {V : Type*} {P : Type*}
    [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]
    {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    {f₁ : ι₁ → P} {f₂ : ι₂ → P}
    {M₁ M₂ : AffineSubspace 𝕜 P}
    (hf₁_span : affineSpan 𝕜 (range f₁) = M₁)
    (hf₂_span : affineSpan 𝕜 (range f₂) = M₂)
    (hf₁_indep : AffineIndependent 𝕜 f₁)
    (hf₂_indep : AffineIndependent 𝕜 f₂)
    (h_finrank_eq : Module.finrank 𝕜 M₁.direction = Module.finrank 𝕜 M₂.direction)
    (h_nonempty₁ : (M₁ : Set P).Nonempty)
    (h_nonempty₂ : (M₂ : Set P).Nonempty) :
    Fintype.card ι₁ = Fintype.card ι₂ := by
  have h_ne₁ : Nonempty ι₁ := by
    by_contra h
    have h_empty : range f₁ = ∅ := range_eq_empty_iff.mpr (not_nonempty_iff.mp h)
    rw [h_empty, AffineSubspace.span_empty] at hf₁_span
    have : (M₁ : Set P) = ∅ := by simp [← hf₁_span]
    exact Set.not_nonempty_empty (this ▸ h_nonempty₁)
  have h_ne₂ : Nonempty ι₂ := by
    by_contra h
    have h_empty : range f₂ = ∅ := range_eq_empty_iff.mpr (not_nonempty_iff.mp h)
    rw [h_empty, AffineSubspace.span_empty] at hf₂_span
    have : (M₂ : Set P) = ∅ := by simp [← hf₂_span]
    exact Set.not_nonempty_empty (this ▸ h_nonempty₂)
  haveI := h_ne₁
  haveI := h_ne₂
  have h₁ := hf₁_indep.finrank_vectorSpan_add_one
  have h₂ := hf₂_indep.finrank_vectorSpan_add_one
  have : vectorSpan 𝕜 (range f₁) = M₁.direction := by
    rw [← direction_affineSpan, hf₁_span]
  rw [this] at h₁
  have : vectorSpan 𝕜 (range f₂) = M₂.direction := by
    rw [← direction_affineSpan, hf₂_span]
  rw [this] at h₂
  omega

end General

/-!
## Finite-Dimensional Results

These theorems require the affine space to be finite-dimensional.
-/

section FiniteDimensional

universe u

/-- Affine dimension is monotone: if `s ⊆ affineSpan 𝕜 t`, then `affineDim 𝕜 s ≤ affineDim 𝕜 t`. -/
theorem affineDim_le_of_subset_affineSpan
    {𝕜 : Type*} {V : Type*} {P : Type*}
    [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P] [FiniteDimensional 𝕜 V]
    {s t : Set P} (h : s ⊆ affineSpan 𝕜 t) :
    affineDim 𝕜 s ≤ affineDim 𝕜 t := by
  have h1 : affineSpan 𝕜 s ≤ affineSpan 𝕜 (affineSpan 𝕜 t) := affineSpan_mono 𝕜 h
  have h2 : affineSpan 𝕜 (affineSpan 𝕜 t) = affineSpan 𝕜 t := AffineSubspace.affineSpan_coe _
  have h3 : affineSpan 𝕜 s ≤ affineSpan 𝕜 t := h2 ▸ h1
  have h4 : (affineSpan 𝕜 s).direction ≤ (affineSpan 𝕜 t).direction :=
    AffineSubspace.direction_le h3
  simp only [affineDim]
  exact_mod_cast Submodule.finrank_mono h4

/-- A linearly independent family whose cardinality equals the ambient dimension
spans the entire space. -/
lemma linearIndependent_card_eq_finrank_span_eq_top
    {𝕜 : Type*} {V : Type*}
    [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
    {ι : Type*} [Fintype ι]
    {f : ι → V}
    (h_indep : LinearIndependent 𝕜 f)
    (h_card : Fintype.card ι = Module.finrank 𝕜 V) :
    Submodule.span 𝕜 (range f) = ⊤ := by
  have h_finrank_span : Fintype.card ι = (range f).finrank 𝕜 :=
    linearIndependent_iff_card_eq_finrank_span.mp h_indep
  have h_span_full : (range f).finrank 𝕜 = Module.finrank 𝕜 V :=
    h_finrank_span.symm.trans h_card
  exact Submodule.eq_top_of_finrank_eq h_span_full

/-- Given an affinely independent family that spans the entire space, the differences from any
base point form a linear basis of the ambient space.

This is a key construction: affine bases correspond to linear bases via the difference map. -/
lemma AffineIndependent.toBasis_of_span_eq_top
    {𝕜 : Type*} {V : Type*} {P : Type*}
    [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P] [FiniteDimensional 𝕜 V]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {f : ι → P}
    (hf : AffineIndependent 𝕜 f)
    (hf_span : affineSpan 𝕜 (range f) = ⊤)
    (i₀ : ι) :
    ∃ (B : Module.Basis {i // i ≠ i₀} 𝕜 V), ∀ i : {i // i ≠ i₀}, B i = f i -ᵥ f i₀ := by
  let f_diff : {i // i ≠ i₀} → V := fun i => f i -ᵥ f i₀

  have h_linear_indep : LinearIndependent 𝕜 f_diff := by
    have h := (affineIndependent_iff_linearIndependent_vsub 𝕜 f i₀).mp hf
    convert h using 2

  have h_span : ⊤ ≤ Submodule.span 𝕜 (range f_diff) := by
    have h_card_ι : Fintype.card ι = Module.finrank 𝕜 V + 1 :=
      hf.affineSpan_eq_top_iff_card_eq_finrank_add_one.mp hf_span
    have h_card : Fintype.card {i // i ≠ i₀} = Module.finrank 𝕜 V := by
      have h_sub : Fintype.card {i // i ≠ i₀} = Fintype.card ι - 1 := Set.card_ne_eq i₀
      rw [h_sub, h_card_ι]
      omega
    exact (linearIndependent_card_eq_finrank_span_eq_top h_linear_indep h_card).ge

  let B : Module.Basis {i // i ≠ i₀} 𝕜 V := Module.Basis.mk h_linear_indep h_span

  use B
  intro i
  exact Module.Basis.mk_apply h_linear_indep h_span i

/-- Construct an affine equivalence from a linear equivalence and two base points.

Given a linear equivalence `A : V ≃ₗ[𝕜] V` and base points `f₀ g₀ : P`, this constructs
the affine equivalence `T x = A (x -ᵥ f₀) +ᵥ g₀`. This is the standard way to convert
a linear automorphism into an affine automorphism with specified base point mapping. -/
def affineEquivOfLinearEquiv
    {𝕜 : Type*} {V : Type*} {P : Type*}
    [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]
    (A : V ≃ₗ[𝕜] V) (f₀ g₀ : P) : P ≃ᵃ[𝕜] P := {
  toFun := fun x => A (x -ᵥ f₀) +ᵥ g₀
  invFun := fun x => A.symm (x -ᵥ g₀) +ᵥ f₀
  left_inv := by
    intro x
    simp [LinearEquiv.symm_apply_apply]
  right_inv := by
    intro x
    simp [LinearEquiv.apply_symm_apply]
  linear := A
  map_vadd' := by
    intro p v
    change A ((v +ᵥ p) -ᵥ f₀) +ᵥ g₀ = A v +ᵥ (A (p -ᵥ f₀) +ᵥ g₀)
    rw [vadd_vsub_assoc, LinearEquiv.map_add, vadd_vadd]
}

/-- Two affinely independent families with the same index type that both span the entire
space can be mapped to each other by an affine automorphism. -/
theorem affineIndependent_indexed
    {𝕜 : Type*} {V : Type*} {P : Type*}
    [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P] [FiniteDimensional 𝕜 V]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f g : ι → P)
    (hf : AffineIndependent 𝕜 f)
    (hg : AffineIndependent 𝕜 g)
    (hf_span : affineSpan 𝕜 (range f) = ⊤)
    (hg_span : affineSpan 𝕜 (range g) = ⊤) :
    ∃ (T : P ≃ᵃ[𝕜] P), ∀ i, T (f i) = g i := by
  let i₀ : ι := Classical.choice (Nonempty.of_affineSpan_range_eq_top f hf_span)
  let f₀ := f i₀
  let g₀ := g i₀

  obtain ⟨B_f, hB_f⟩ := hf.toBasis_of_span_eq_top hf_span i₀
  obtain ⟨B_g, hB_g⟩ := hg.toBasis_of_span_eq_top hg_span i₀

  let A : V ≃ₗ[𝕜] V := B_f.equiv B_g (Equiv.refl _)
  let T : P ≃ᵃ[𝕜] P := affineEquivOfLinearEquiv A f₀ g₀

  use T

  intro i
  by_cases h : i = i₀
  · subst h
    change A (f₀ -ᵥ f₀) +ᵥ g₀ = g₀
    simp
  · have h_basis_map : A (f i -ᵥ f₀) = g i -ᵥ g₀ := by
      have h1 : A (B_f ⟨i, h⟩) = B_g ⟨i, h⟩ := by
        grind [Module.Basis.equiv_apply]
      rw [← hB_f ⟨i, h⟩, ← hB_g ⟨i, h⟩]
      exact h1
    change A (f i -ᵥ f₀) +ᵥ g₀ = g i
    rw [h_basis_map]
    exact vsub_vadd (g i) g₀

/-- An affinely independent family in a finite-dimensional space has cardinality at most
`finrank + 1`. -/
lemma AffineIndependent.card_le_finrank_add_one
    {𝕜 : Type*} {V : Type*} {P : Type*}
    [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P] [FiniteDimensional 𝕜 V]
    {ι : Type*} [Fintype ι] {f : ι → P} (hf : AffineIndependent 𝕜 f) :
    Fintype.card ι ≤ Module.finrank 𝕜 V + 1 := by
  calc Fintype.card ι
      ≤ Module.finrank 𝕜 (vectorSpan 𝕜 (Set.range f)) + 1 := hf.card_le_finrank_succ
    _ ≤ Module.finrank 𝕜 V + 1 := by
        apply Nat.add_le_add_right
        exact Submodule.finrank_le _

/-- If an affinely independent family has cardinality strictly less than `finrank + 1`,
then its affine span is a proper subspace. -/
lemma AffineIndependent.affineSpan_ne_top_of_card_lt_finrank_add_one
    {𝕜 : Type*} {V : Type*} {P : Type*}
    [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P] [FiniteDimensional 𝕜 V]
    {ι : Type*} [Fintype ι] [Nonempty ι] {f : ι → P}
    (hf : AffineIndependent 𝕜 f)
    (h_card : Fintype.card ι < Module.finrank 𝕜 V + 1) :
    affineSpan 𝕜 (range f) ≠ ⊤ := by
  intro h_top
  have h_card_eq := hf.affineSpan_eq_top_iff_card_eq_finrank_add_one.mp h_top
  omega

/-- **Main theorem**: Affinely independent families of the same size can be mapped to each
other by an affine automorphism.

This corresponds to Rockafellar's "Convex Analysis" (1970), Theorem 1.6.

Given two affinely independent families `f, g : ι → P` with the same finite index type,
there exists an affine automorphism `T : P ≃ᵃ[𝕜] P` such that `T (f i) = g i` for all `i`. -/
theorem affineIndependent_to_affineIndependent_automorphism
    {𝕜 : Type*} {V : Type*} {P : Type*}
    [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P] [FiniteDimensional 𝕜 V]
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (f g : ι → P)
    (hf : AffineIndependent 𝕜 f)
    (hg : AffineIndependent 𝕜 g) :
    ∃ (T : P ≃ᵃ[𝕜] P), ∀ i, T (f i) = g i := by
  have h_card_bound : Fintype.card ι ≤ Module.finrank 𝕜 V + 1 := hf.card_le_finrank_add_one
  induction h : Module.finrank 𝕜 V + 1 - Fintype.card ι generalizing ι f g with
  | zero =>
    have h_lower : Module.finrank 𝕜 V + 1 ≤ Fintype.card ι := by
      exact Nat.sub_eq_zero_iff_le.mp h
    by_cases h_empty : IsEmpty ι
    · use AffineEquiv.refl 𝕜 P
      intro i
      exact IsEmpty.elim h_empty i
    · rw [not_isEmpty_iff] at h_empty
      have h_card_eq : Fintype.card ι = Module.finrank 𝕜 V + 1 := by omega
      have h_span_f : affineSpan 𝕜 (range f) = ⊤ := by
        exact hf.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr h_card_eq
      have h_span_g : affineSpan 𝕜 (range g) = ⊤ := by
        exact hg.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr h_card_eq
      exact affineIndependent_indexed f g hf hg h_span_f h_span_g

  | succ n ih =>
    have h_gap : 0 < Module.finrank 𝕜 V + 1 - Fintype.card ι := by
      rw [h]
      omega
    by_cases h_empty : IsEmpty ι
    · use AffineEquiv.refl 𝕜 P
      intro i
      exact IsEmpty.elim h_empty i
    · rw [not_isEmpty_iff] at h_empty
      have h_card_lt : Fintype.card ι < Module.finrank 𝕜 V + 1 := by omega
      have h_span_f_ne_top : affineSpan 𝕜 (range f) ≠ ⊤ :=
        hf.affineSpan_ne_top_of_card_lt_finrank_add_one h_card_lt
      have h_span_g_ne_top : affineSpan 𝕜 (range g) ≠ ⊤ :=
        hg.affineSpan_ne_top_of_card_lt_finrank_add_one h_card_lt
      have h_exists_f : ∃ p_f : P, p_f ∉ affineSpan 𝕜 (range f) :=
        AffineSubspace.exists_not_mem_of_ne_top _ h_span_f_ne_top
      obtain ⟨p_f, hp_f⟩ := h_exists_f
      have h_exists_g : ∃ p_g : P, p_g ∉ affineSpan 𝕜 (range g) :=
        AffineSubspace.exists_not_mem_of_ne_top _ h_span_g_ne_top
      obtain ⟨p_g, hp_g⟩ := h_exists_g
      let f' : Option ι → P := fun o => o.elim p_f f
      let g' : Option ι → P := fun o => o.elim p_g g
      have hf' : AffineIndependent 𝕜 f' := hf.option_extend hp_f
      have hg' : AffineIndependent 𝕜 g' := hg.option_extend hp_g
      have h_card_option : Fintype.card (Option ι) = Fintype.card ι + 1 := by
        exact Fintype.card_option
      have h_card_option_bound : Fintype.card (Option ι) ≤ Module.finrank 𝕜 V + 1 := by omega
      have h_gap_option : Module.finrank 𝕜 V + 1 - Fintype.card (Option ι) = n := by
        rw [h_card_option]
        omega
      obtain ⟨T, hT⟩ := @ih (Option ι) _ _ f' g' hf' hg' h_card_option_bound h_gap_option
      use T
      intro i
      exact hT (some i)

/-!
### Affine subspaces of equal dimension
-/

/-- Every nonempty affine subspace contains an affinely independent spanning family.

Given an affine subspace M, extracts an affinely independent family (indexed
by a type) that spans M. -/
lemma exists_affineIndependent_of_affineSubspace
    {𝕜 : Type*} {V : Type u}
    [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
    (M : AffineSubspace 𝕜 V) :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι) (f : ι → V),
      (∀ i, f i ∈ M) ∧
      affineSpan 𝕜 (range f) = M ∧
      AffineIndependent 𝕜 f := by
  -- Apply exists_affineIndependent to the underlying set of M
  obtain ⟨t, ht_sub, ht_span, ht_indep⟩ := exists_affineIndependent 𝕜 V (M : Set V)

  -- t is finite because it's affinely independent in a finite-dimensional space
  have ht_finite : t.Finite := finite_set_of_fin_dim_affineIndependent 𝕜 ht_indep
  haveI : Fintype t := ht_finite.fintype

  -- Use the subtype {x // x ∈ t} as the index type
  classical
  exact ⟨↥t, inferInstance, inferInstance, Subtype.val,
    fun i => ht_sub i.property,
    by rw [Subtype.range_coe, ht_span, AffineSubspace.affineSpan_coe],
    ht_indep⟩

/-- Affine subspaces of the same dimension can be mapped to each other by an affine
automorphism of the ambient space.

An m-dimensional affine set can be expressed as the affine hull of an affinely independent
set of m+1 points. Since affine hulls are preserved by affine transformations, applying
the main theorem gives the result. -/
theorem affineSubspace_automorphism_of_eq_dim
    {𝕜 : Type*} {V : Type u}
    [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
    (M₁ M₂ : AffineSubspace 𝕜 V)
    (h_nonempty₁ : (M₁ : Set V).Nonempty)
    (h_nonempty₂ : (M₂ : Set V).Nonempty)
    (h_dim : affineDim 𝕜 (M₁ : Set V) = affineDim 𝕜 (M₂ : Set V)) :
    ∃ T : V ≃ᵃ[𝕜] V, M₁.map T = M₂ := by
  -- Step 1: Show that finrank of directions are equal
  have h_finrank_eq : Module.finrank 𝕜 M₁.direction = Module.finrank 𝕜 M₂.direction := by
    have h₁ : affineDim 𝕜 (M₁ : Set V) = Module.finrank 𝕜 M₁.direction := by
      simp only [affineDim]
      rw [AffineSubspace.affineSpan_coe]
    have h₂ : affineDim 𝕜 (M₂ : Set V) = Module.finrank 𝕜 M₂.direction := by
      simp only [affineDim]
      rw [AffineSubspace.affineSpan_coe]
    rw [h₁, h₂] at h_dim
    exact h_dim

  classical
  obtain ⟨ι₁, inst₁, inst₂, f₁, hf₁_mem, hf₁_span, hf₁_indep⟩ :=
    exists_affineIndependent_of_affineSubspace M₁
  haveI := inst₁
  haveI := inst₂

  obtain ⟨ι₂, inst₃, inst₄, f₂, hf₂_mem, hf₂_span, hf₂_indep⟩ :=
    exists_affineIndependent_of_affineSubspace M₂
  haveI := inst₃
  haveI := inst₄

  have h_card_eq : Fintype.card ι₁ = Fintype.card ι₂ :=
    affineIndependent_card_eq_of_finrank_direction_eq
      hf₁_span hf₂_span hf₁_indep hf₂_indep h_finrank_eq h_nonempty₁ h_nonempty₂

  let e : ι₁ ≃ ι₂ := Fintype.equivOfCardEq h_card_eq
  let g : ι₁ → V := f₂ ∘ e

  have hg_indep : AffineIndependent 𝕜 g :=
    hf₂_indep.comp_embedding e.toEmbedding

  have hg_span : affineSpan 𝕜 (range g) = M₂ := by
    have : range g = range f₂ := by
      unfold g
      rw [Set.range_comp]
      have : range (⇑e) = Set.univ := e.surjective.range_eq
      rw [this, Set.image_univ]
    rw [this, hf₂_span]

  obtain ⟨T, hT⟩ := affineIndependent_to_affineIndependent_automorphism ι₁ f₁ g hf₁_indep hg_indep

  use T
  calc M₁.map T
      = (affineSpan 𝕜 (range f₁)).map T := by
          rw [← hf₁_span]
    _ = affineSpan 𝕜 (T '' range f₁) := by
          exact AffineSubspace.map_span T.toAffineMap (range f₁)
    _ = affineSpan 𝕜 (range g) := by
          congr 1
          ext x
          simp only [Set.mem_image, Set.mem_range]
          constructor
          · intro ⟨y, ⟨i, hy⟩, hTy⟩
            use i
            rw [← hTy, ← hy, hT]
          · intro ⟨i, hx⟩
            use f₁ i, ⟨i, rfl⟩
            rw [hT, hx]
    _ = M₂ := by
          rw [hg_span]

end FiniteDimensional
