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
    (s : Set P) : ℤ :=
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
  -- Convert to set reasoning: S ≠ ⊤ as affine subspaces means (S : Set P) ≠ Set.univ
  have h_ne_univ : (S : Set P) ≠ Set.univ := by
    intro h_eq
    have h_top : S = ⊤ := SetLike.coe_injective h_eq
    exact h h_top
  -- Use the fact that a set ≠ univ iff there exists an element not in it
  exact (Set.ne_univ_iff_exists_notMem (S : Set P)).mp h_ne_univ

/-- If the affine span of the range of a function equals the entire space, then the index type
must be nonempty. -/
lemma Nonempty.of_affineSpan_range_eq_top
    {𝕜 : Type*} {V : Type*} {P : Type*}
    [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]
    {ι : Type*} (f : ι → P)
    (h : affineSpan 𝕜 (range f) = ⊤) : Nonempty ι := by
  -- Proof by contradiction
  by_contra h_empty
  -- Convert ¬Nonempty ι to IsEmpty ι
  rw [not_nonempty_iff] at h_empty
  -- If ι is empty, then range f is empty
  have h_range_empty : range f = ∅ := range_eq_empty_iff.mpr h_empty
  -- The affine span of the empty set is ⊥
  have h_span_empty : affineSpan 𝕜 (range f) = ⊥ := by
    rw [h_range_empty]
    exact span_empty 𝕜 V P
  -- But h says it equals ⊤
  rw [h_span_empty] at h
  -- This gives us ⊥ = ⊤, which contradicts bot_ne_top
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
  -- Use AffineMap.ext: it suffices to show f and g agree on all points
  ext x
  -- Since p spans the entire space, x is in the affine span of range p
  have hx : x ∈ affineSpan 𝕜 (range p) := by
    rw [h_span]
    exact AffineSubspace.mem_top 𝕜 V₁ x
  -- By membership in affine span, x can be written as an affine combination
  obtain ⟨w, hw_sum, hw_eq⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hx
  -- Rewrite x using the affine combination
  rw [hw_eq]
  -- Both f and g preserve affine combinations
  rw [Finset.map_affineCombination Finset.univ p w hw_sum f,
      Finset.map_affineCombination Finset.univ p w hw_sum g]
  -- The compositions f ∘ p and g ∘ p are equal
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
  -- Use AffineEquiv.toAffineMap_inj: affine equivalences are equal iff their affine maps are equal
  rw [← AffineEquiv.toAffineMap_inj]
  -- Apply the general theorem for affine maps
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
  -- Define the extended function
  let f' : Option ι → P := fun o => o.elim p f

  -- Show the subfamily excluding `none` is affinely independent
  have h_sub : AffineIndependent 𝕜 (fun x : {y : Option ι // y ≠ none} => f' x) := by
    -- The restricted function equals f composed with Option.get
    have : (fun x : {y : Option ι // y ≠ none} => f' x) =
           f ∘ (fun x => Option.get x.val (Option.ne_none_iff_isSome.mp x.prop)) := by
      ext ⟨x, hx⟩
      cases x with
      | some i => rfl
      | none => exact absurd rfl hx

    rw [this]

    -- Construct the embedding {y : Option ι // y ≠ none} ↪ ι
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

    -- The image equals range f
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

  -- Show f' none ∉ affineSpan 𝕜 (f' '' {x | x ≠ none})
  have h_not_mem : f' none ∉ affineSpan 𝕜 (f' '' {x : Option ι | x ≠ none}) := by
    rw [h_image_eq]
    exact hp

  -- Apply the main theorem
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
  -- Use AffineIndependent.finrank_vectorSpan_add_one to relate cardinality to dimension
  have h_ne₁ : Nonempty ι₁ := by
    by_contra h
    -- If ι₁ is empty, then range f₁ is empty, contradicting M₁ being nonempty
    have h_empty : range f₁ = ∅ := range_eq_empty_iff.mpr (not_nonempty_iff.mp h)
    rw [h_empty, AffineSubspace.span_empty] at hf₁_span
    -- hf₁_span : ⊥ = M₁, so (M₁ : Set P) = ∅
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
  -- vectorSpan (range f) = M.direction for any affine span
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
@[simp]
theorem affineDim_le_of_subset_affineSpan
    {𝕜 : Type*} {V : Type*} {P : Type*}
    [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P] [FiniteDimensional 𝕜 V]
    {s t : Set P} (h : s ⊆ affineSpan 𝕜 t) :
    affineDim 𝕜 s ≤ affineDim 𝕜 t := by
  -- Use affineSpan_mono to get affineSpan 𝕜 s ≤ affineSpan 𝕜 (affineSpan 𝕜 t)
  have h1 : affineSpan 𝕜 s ≤ affineSpan 𝕜 (affineSpan 𝕜 t) := affineSpan_mono 𝕜 h
  -- Use idempotence: affineSpan 𝕜 (affineSpan 𝕜 t) = affineSpan 𝕜 t
  have h2 : affineSpan 𝕜 (affineSpan 𝕜 t) = affineSpan 𝕜 t := AffineSubspace.affineSpan_coe _
  -- Combine to get affineSpan 𝕜 s ≤ affineSpan 𝕜 t
  have h3 : affineSpan 𝕜 s ≤ affineSpan 𝕜 t := h2 ▸ h1
  -- Apply direction_le to get direction ordering
  have h4 : (affineSpan 𝕜 s).direction ≤ (affineSpan 𝕜 t).direction :=
    AffineSubspace.direction_le h3
  -- Use finrank monotonicity on submodules
  -- affineDim is defined as Module.finrank of the direction
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
  -- Linear independence implies card = finrank(span)
  have h_finrank_span : Fintype.card ι = (range f).finrank 𝕜 :=
    linearIndependent_iff_card_eq_finrank_span.mp h_indep
  -- Therefore finrank(span) = Module.finrank V
  have h_span_full : (range f).finrank 𝕜 = Module.finrank 𝕜 V :=
    h_finrank_span.symm.trans h_card
  -- A submodule with full rank must be the whole space
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
  -- Define the difference family
  let f_diff : {i // i ≠ i₀} → V := fun i => f i -ᵥ f i₀

  -- Show that f_diff is linearly independent
  have h_linear_indep : LinearIndependent 𝕜 f_diff := by
    have h := (affineIndependent_iff_linearIndependent_vsub 𝕜 f i₀).mp hf
    convert h using 2

  -- Show that f_diff spans V
  have h_span : ⊤ ≤ Submodule.span 𝕜 (range f_diff) := by
    -- Since affineSpan f = ⊤ and f is affinely independent,
    -- we have Fintype.card ι = Module.finrank 𝕜 V + 1
    have h_card_ι : Fintype.card ι = Module.finrank 𝕜 V + 1 :=
      hf.affineSpan_eq_top_iff_card_eq_finrank_add_one.mp hf_span
    -- The cardinality of {i // i ≠ i₀} is one less
    have h_card : Fintype.card {i // i ≠ i₀} = Module.finrank 𝕜 V := by
      have h_sub : Fintype.card {i // i ≠ i₀} = Fintype.card ι - 1 := Set.card_ne_eq i₀
      rw [h_sub, h_card_ι]
      omega
    -- Apply the helper: linearly independent with full cardinality spans
    exact (linearIndependent_card_eq_finrank_span_eq_top h_linear_indep h_card).ge

  -- Construct the basis
  let B : Module.Basis {i // i ≠ i₀} 𝕜 V := Module.Basis.mk h_linear_indep h_span

  -- Verify that B i = f i -ᵥ f i₀
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

  -- Pick base points (ι is nonempty since the span equals ⊤)
  let i₀ : ι := Classical.choice (Nonempty.of_affineSpan_range_eq_top f hf_span)
  let f₀ := f i₀
  let g₀ := g i₀

  -- Construct linear bases from the affine bases using the helper lemma
  obtain ⟨B_f, hB_f⟩ := hf.toBasis_of_span_eq_top hf_span i₀
  obtain ⟨B_g, hB_g⟩ := hg.toBasis_of_span_eq_top hg_span i₀

  -- Step 3: Construct linear automorphism A mapping B_f to B_g
  -- Use Basis.equiv to construct a linear equivalence that maps B_f i to B_g i
  -- This is automatically bijective since it's a LinearEquiv
  let A : V ≃ₗ[𝕜] V := B_f.equiv B_g (Equiv.refl _)

  -- Step 4: Define affine automorphism using the helper definition
  let T : P ≃ᵃ[𝕜] P := affineEquivOfLinearEquiv A f₀ g₀

  use T

  -- Prove that T maps f i to g i for all i
  intro i
  by_cases h : i = i₀
  · -- Case i = i₀: T(f₀) = g₀
    subst h
    change A (f₀ -ᵥ f₀) +ᵥ g₀ = g₀
    simp
  · -- Case i ≠ i₀: T(f i) = g i
    -- Key: A maps basis B_f to basis B_g, so A(f i -ᵥ f₀) = g i -ᵥ g₀
    -- By definition of Basis.equiv, we have A (B_f j) = B_g j for all j
    -- Since B_f ⟨i, h⟩ = f i -ᵥ f₀ and B_g ⟨i, h⟩ = g i -ᵥ g₀,
    -- we get A(f i -ᵥ f₀) = g i -ᵥ g₀

    -- Basis.equiv maps basis elements to corresponding basis elements
    have h_basis_map : A (f i -ᵥ f₀) = g i -ᵥ g₀ := by
      -- A = B_f.equiv B_g (Equiv.refl _)
      -- By definition, A (B_f j) = B_g ((Equiv.refl _) j) = B_g j
      have h1 : A (B_f ⟨i, h⟩) = B_g ⟨i, h⟩ := by
        grind [Module.Basis.equiv_apply]
      -- Use the helper lemma results: B_f ⟨i, h⟩ = f i -ᵥ f i₀ and B_g ⟨i, h⟩ = g i -ᵥ g i₀
      rw [← hB_f ⟨i, h⟩, ← hB_g ⟨i, h⟩]
      exact h1

    -- Now prove T (f i) = g i using the mapping property
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
  -- Induction on the dimension gap
  induction h : Module.finrank 𝕜 V + 1 - Fintype.card ι generalizing ι f g with
  | zero =>
    -- Base case: dimension gap = 0, so card ι = finrank V + 1
    -- h : Module.finrank 𝕜 V + 1 - Fintype.card ι = 0
    have h_lower : Module.finrank 𝕜 V + 1 ≤ Fintype.card ι := by
      exact Nat.sub_eq_zero_iff_le.mp h
    -- Case split on whether ι is empty
    by_cases h_empty : IsEmpty ι
    · -- If ι is empty, the conclusion is vacuous
      use AffineEquiv.refl 𝕜 P
      intro i
      exact IsEmpty.elim h_empty i
    · -- If ι is nonempty, both families span the entire space
      rw [not_isEmpty_iff] at h_empty
      have h_card_eq : Fintype.card ι = Module.finrank 𝕜 V + 1 := by omega

      -- By affineSpan_eq_top_iff_card_eq_finrank_add_one, this implies affineSpan = ⊤
      have h_span_f : affineSpan 𝕜 (range f) = ⊤ := by
        exact hf.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr h_card_eq

      have h_span_g : affineSpan 𝕜 (range g) = ⊤ := by
        exact hg.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr h_card_eq

      -- Apply affineIndependent_indexed
      exact affineIndependent_indexed f g hf hg h_span_f h_span_g

  | succ n ih =>
    -- Inductive case: dimension gap = n + 1 > 0
    -- h : Module.finrank 𝕜 V + 1 - Fintype.card ι = n + 1
    have h_gap : 0 < Module.finrank 𝕜 V + 1 - Fintype.card ι := by
      rw [h]
      omega
    -- Case split on whether ι is empty
    by_cases h_empty : IsEmpty ι
    · -- If ι is empty, the conclusion is vacuous
      use AffineEquiv.refl 𝕜 P
      intro i
      exact IsEmpty.elim h_empty i
    · -- If ι is nonempty, proceed with the inductive step
      rw [not_isEmpty_iff] at h_empty
      -- This means card ι < finrank V + 1
      -- So the affine spans are proper subspaces
      have h_card_lt : Fintype.card ι < Module.finrank 𝕜 V + 1 := by omega

      -- Since card < finrank + 1, the affine span cannot be the whole space
      have h_span_f_ne_top : affineSpan 𝕜 (range f) ≠ ⊤ := by
        intro h_top
        have h_card_eq := hf.affineSpan_eq_top_iff_card_eq_finrank_add_one.mp h_top
        omega

      have h_span_g_ne_top : affineSpan 𝕜 (range g) ≠ ⊤ := by
        intro h_top
        have h_card_eq := hg.affineSpan_eq_top_iff_card_eq_finrank_add_one.mp h_top
        omega

      -- Find points outside the affine spans
      have h_exists_f : ∃ p_f : P, p_f ∉ affineSpan 𝕜 (range f) :=
        AffineSubspace.exists_not_mem_of_ne_top _ h_span_f_ne_top

      obtain ⟨p_f, hp_f⟩ := h_exists_f

      have h_exists_g : ∃ p_g : P, p_g ∉ affineSpan 𝕜 (range g) :=
        AffineSubspace.exists_not_mem_of_ne_top _ h_span_g_ne_top

      obtain ⟨p_g, hp_g⟩ := h_exists_g

      -- Extend f and g to Option ι using Option.elim
      let f' : Option ι → P := fun o => o.elim p_f f
      let g' : Option ι → P := fun o => o.elim p_g g

      -- Show that f' and g' are affinely independent using the helper lemma
      have hf' : AffineIndependent 𝕜 f' := hf.option_extend hp_f

      have hg' : AffineIndependent 𝕜 g' := hg.option_extend hp_g

      -- The dimension gap for Option ι
      have h_card_option : Fintype.card (Option ι) = Fintype.card ι + 1 := by
        exact Fintype.card_option

      have h_card_option_bound : Fintype.card (Option ι) ≤ Module.finrank 𝕜 V + 1 := by omega

      -- Compute the gap for Option ι
      have h_gap_option : Module.finrank 𝕜 V + 1 - Fintype.card (Option ι) = n := by
        rw [h_card_option]
        omega

      -- Apply IH to f' and g'
      obtain ⟨T, hT⟩ := @ih (Option ι) _ _ f' g' hf' hg' h_card_option_bound h_gap_option

      -- T already maps f i to g i for all i
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
    -- This follows from h_dim: affineDim relates to finrank of the direction subspace
    -- affineDim s is defined as finrank of (affineSpan k s).direction
    -- For affine subspaces, affineSpan is idempotent: affineSpan k (M : Set V) = M
    have h₁ : affineDim 𝕜 (M₁ : Set V) = (Module.finrank 𝕜 M₁.direction : ℤ) := by
      simp only [affineDim]
      rw [AffineSubspace.affineSpan_coe]
    have h₂ : affineDim 𝕜 (M₂ : Set V) = (Module.finrank 𝕜 M₂.direction : ℤ) := by
      simp only [affineDim]
      rw [AffineSubspace.affineSpan_coe]
    -- Now h_dim gives us equality of the casted finranks
    rw [h₁, h₂] at h_dim
    -- Extract equality of natural numbers from equality of integers
    exact Int.ofNat_inj.mp h_dim

  -- Step 2: Extract affinely independent spanning families from M₁ and M₂
  -- Each m-dimensional affine subspace contains an affinely independent spanning family
  classical
  -- For M₁: get ι₁, f₁ : ι₁ → V with affineSpan 𝕜 (range f₁) = M₁ and f₁ affinely independent
  obtain ⟨ι₁, inst₁, inst₂, f₁, hf₁_mem, hf₁_span, hf₁_indep⟩ :=
    exists_affineIndependent_of_affineSubspace M₁
  haveI := inst₁
  haveI := inst₂

  -- For M₂: get ι₂, f₂ : ι₂ → V with affineSpan 𝕜 (range f₂) = M₂ and f₂ affinely independent
  obtain ⟨ι₂, inst₃, inst₄, f₂, hf₂_mem, hf₂_span, hf₂_indep⟩ :=
    exists_affineIndependent_of_affineSubspace M₂
  haveI := inst₃
  haveI := inst₄

  -- Step 3: Show both families have the same cardinality
  have h_card_eq : Fintype.card ι₁ = Fintype.card ι₂ :=
    affineIndependent_card_eq_of_finrank_direction_eq
      hf₁_span hf₂_span hf₁_indep hf₂_indep h_finrank_eq h_nonempty₁ h_nonempty₂

  -- Get an equivalence between ι₁ and ι₂
  let e : ι₁ ≃ ι₂ := Fintype.equivOfCardEq h_card_eq

  -- Reindex f₂ via e to get g : ι₁ → V
  let g : ι₁ → V := f₂ ∘ e

  have hg_indep : AffineIndependent 𝕜 g :=
    -- Reindexing via an embedding preserves affine independence
    hf₂_indep.comp_embedding e.toEmbedding

  have hg_span : affineSpan 𝕜 (range g) = M₂ := by
    -- range (f₂ ∘ e) = range f₂ since e is surjective
    have : range g = range f₂ := by
      unfold g
      rw [Set.range_comp]
      -- Since e is surjective, range e = univ
      have : range (⇑e) = Set.univ := e.surjective.range_eq
      rw [this, Set.image_univ]
    rw [this, hf₂_span]

  -- Step 4: Apply the main theorem
  obtain ⟨T, hT⟩ := affineIndependent_to_affineIndependent_automorphism ι₁ f₁ g hf₁_indep hg_indep

  -- Step 5: Show M₁.map T = M₂ using preservation of affine hulls
  use T
  calc M₁.map T
      = (affineSpan 𝕜 (range f₁)).map T := by
          rw [← hf₁_span]
    _ = affineSpan 𝕜 (T '' range f₁) := by
          exact AffineSubspace.map_span T.toAffineMap (range f₁)
    _ = affineSpan 𝕜 (range g) := by
          -- Show T '' range f₁ = range g
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
