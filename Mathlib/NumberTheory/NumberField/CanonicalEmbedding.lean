/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot

! This file was ported from Lean 3 source module number_theory.number_field.canonical_embedding
! leanprover-community/mathlib commit 60da01b41bbe4206f05d34fd70c8dd7498717a30
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.NumberTheory.NumberField.Embeddings

/-!
# Canonical embedding of a number field

The canonical embedding of a number field `K` of signature `(r₁, r₂)` is the ring homomorphism
`K →+* ℝ^r₁ × ℂ^r₂` that sends `x ∈ K` to `(φ_₁(x),...,φ_r₁(x)) × (ψ_₁(x),..., ψ_r₂(x))` where
`φ_₁,...,φ_r₁` are its real embeddings and `ψ_₁,..., ψ_r₂` are its complex embeddings (up to
complex conjugation).

## Main definitions and results

* `number_field.canonical_embedding.ring_of_integers.inter_ball_finite`: the intersection of the
image of the ring of integers by the canonical embedding and any ball centered at `0` of finite
radius is finite.

## Tags

number field, infinite places
-/


noncomputable section

open Function FiniteDimensional Finset Fintype NumberField NumberField.InfinitePlace Metric Module

open scoped Classical NumberField

variable (K : Type _) [Field K]

namespace NumberField.canonicalEmbedding

-- The ambient space `ℝ^r₁ × ℂ^r₂` with `(r₁, r₂)` the signature of `K`.
scoped[CanonicalEmbedding]
  notation "E" =>
    ({ w : InfinitePlace K // IsReal w } → ℝ) × ({ w : InfinitePlace K // IsComplex w } → ℂ)

theorem space_rank [NumberField K] : finrank ℝ E = finrank ℚ K :=
  by
  haveI : Module.Free ℝ ℂ := inferInstance
  rw [finrank_prod, finrank_pi, finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const,
    Finset.card_univ, ← card_real_embeddings, Algebra.id.smul_eq_mul, mul_comm, ←
    card_complex_embeddings, ← NumberField.Embeddings.card K ℂ, Fintype.card_subtype_compl,
    Nat.add_sub_of_le (Fintype.card_subtype_le _)]
#align number_field.canonical_embedding.space_rank NumberField.CanonicalEmbedding.space_rank

theorem non_trivial_space [NumberField K] : Nontrivial E :=
  by
  obtain ⟨w⟩ := infinite_place.nonempty K
  obtain hw | hw := w.is_real_or_is_complex
  · haveI : Nonempty { w : infinite_place K // is_real w } := ⟨⟨w, hw⟩⟩
    exact nontrivial_prod_left
  · haveI : Nonempty { w : infinite_place K // is_complex w } := ⟨⟨w, hw⟩⟩
    exact nontrivial_prod_right
#align number_field.canonical_embedding.non_trivial_space NumberField.CanonicalEmbedding.non_trivial_space

/-- The canonical embedding of a number field `K` of signature `(r₁, r₂)` into `ℝ^r₁ × ℂ^r₂`. -/
def NumberField.canonicalEmbedding : K →+* E :=
  RingHom.prod (Pi.ringHom fun w => w.Prop.Embedding) (Pi.ringHom fun w => w.val.Embedding)
#align number_field.canonical_embedding NumberField.canonicalEmbedding

theorem NumberField.canonicalEmbedding_injective [NumberField K] :
    Injective (NumberField.canonicalEmbedding K) :=
  @RingHom.injective _ _ _ _ (non_trivial_space K) _
#align number_field.canonical_embedding_injective NumberField.canonicalEmbedding_injective

open NumberField

variable {K}

@[simp]
theorem apply_at_real_infinitePlace (w : { w : InfinitePlace K // IsReal w }) (x : K) :
    (NumberField.canonicalEmbedding K x).1 w = w.Prop.Embedding x := by
  simp only [canonical_embedding, RingHom.prod_apply, Pi.ringHom_apply]
#align number_field.canonical_embedding.apply_at_real_infinite_place NumberField.canonicalEmbedding.apply_at_real_infinitePlace

@[simp]
theorem apply_at_complex_infinitePlace (w : { w : InfinitePlace K // IsComplex w }) (x : K) :
    (NumberField.canonicalEmbedding K x).2 w = Embedding w.val x := by
  simp only [canonical_embedding, RingHom.prod_apply, Pi.ringHom_apply]
#align number_field.canonical_embedding.apply_at_complex_infinite_place NumberField.canonicalEmbedding.apply_at_complex_infinitePlace

theorem nnnorm_eq [NumberField K] (x : K) :
    ‖canonicalEmbedding K x‖₊ = Finset.univ.sup fun w : InfinitePlace K => ⟨w x, map_nonneg w x⟩ :=
  by
  rw [Prod.nnnorm_def', Pi.nnnorm_def, Pi.nnnorm_def]
  rw [(_ :
      Finset.univ =
        {w : infinite_place K | is_real w}.toFinset ∪
          {w : infinite_place K | is_complex w}.toFinset)]
  · rw [Finset.sup_union, sup_eq_max]
    refine' congr_arg₂ _ _ _
    · convert
        (finset.univ.sup_map (Function.Embedding.subtype fun w : infinite_place K => is_real w)
            fun w => (⟨w x, map_nonneg w x⟩ : NNReal)).symm using
        2
      ext w
      simp only [apply_at_real_infinite_place, coe_nnnorm, Real.norm_eq_abs,
        Function.Embedding.coe_subtype, Subtype.coe_mk, is_real.abs_embedding_apply]
    · convert
        (finset.univ.sup_map (Function.Embedding.subtype fun w : infinite_place K => is_complex w)
            fun w => (⟨w x, map_nonneg w x⟩ : NNReal)).symm using
        2
      ext w
      simp only [apply_at_complex_infinite_place, Subtype.val_eq_coe, coe_nnnorm,
        Complex.norm_eq_abs, Function.Embedding.coe_subtype, Subtype.coe_mk, abs_embedding]
  · ext w
    simp only [w.is_real_or_is_complex, Set.mem_setOf_eq, Finset.mem_union, Set.mem_toFinset,
      Finset.mem_univ]
#align number_field.canonical_embedding.nnnorm_eq NumberField.canonicalEmbedding.nnnorm_eq

theorem norm_le_iff [NumberField K] (x : K) (r : ℝ) :
    ‖canonicalEmbedding K x‖ ≤ r ↔ ∀ w : InfinitePlace K, w x ≤ r :=
  by
  obtain hr | hr := lt_or_le r 0
  · obtain ⟨w⟩ := infinite_place.nonempty K
    exact
      iff_of_false (hr.trans_le <| norm_nonneg _).not_le fun h =>
        hr.not_le <| (map_nonneg w _).trans <| h _
  · lift r to NNReal using hr
    simp_rw [← coe_nnnorm, nnnorm_eq, NNReal.coe_le_coe, Finset.sup_le_iff, Finset.mem_univ,
      forall_true_left, ← NNReal.coe_le_coe, Subtype.coe_mk]
#align number_field.canonical_embedding.norm_le_iff NumberField.canonicalEmbedding.norm_le_iff

variable (K)

/-- The image of `𝓞 K` as a subring of `ℝ^r₁ × ℂ^r₂`. -/
def integerLattice : Subring E :=
  (RingHom.range (algebraMap (𝓞 K) K)).map (canonicalEmbedding K)
#align number_field.canonical_embedding.integer_lattice NumberField.canonicalEmbedding.integerLattice

/-- The linear equiv between `𝓞 K` and the integer lattice. -/
def equivIntegerLattice [NumberField K] : 𝓞 K ≃ₗ[ℤ] integerLattice K :=
  LinearEquiv.ofBijective
    { toFun := fun x =>
        ⟨canonicalEmbedding K (algebraMap (𝓞 K) K x), algebraMap (𝓞 K) K x, by
          simp only [Subring.mem_carrier, RingHom.mem_range, exists_apply_eq_apply], rfl⟩
      map_add' := fun x y => by simpa only [map_add]
      map_smul' := fun c x => by simpa only [zsmul_eq_mul, map_mul, map_intCast] }
    (by
      refine' ⟨fun _ _ h => _, fun ⟨_, _, ⟨a, rfl⟩, rfl⟩ => ⟨a, rfl⟩⟩
      rw [LinearMap.coe_mk, Subtype.mk_eq_mk] at h 
      exact IsFractionRing.injective (𝓞 K) K (canonical_embedding_injective K h))
#align number_field.canonical_embedding.equiv_integer_lattice NumberField.canonicalEmbedding.equivIntegerLattice

theorem integerLattice.inter_ball_finite [NumberField K] (r : ℝ) :
    ((integerLattice K : Set E) ∩ closedBall 0 r).Finite :=
  by
  obtain hr | hr := lt_or_le r 0
  · simp [closed_ball_eq_empty.2 hr]
  have heq : ∀ x, canonical_embedding K x ∈ closed_ball (0 : E) r ↔ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ r :=
    by
    simp only [← place_apply, ← infinite_place.coe_mk, mem_closedBall_zero_iff, norm_le_iff]
    exact fun x => le_iff_le x r
  convert (embeddings.finite_of_norm_le K ℂ r).image (canonical_embedding K)
  ext; constructor
  · rintro ⟨⟨_, ⟨x, rfl⟩, rfl⟩, hx2⟩
    exact ⟨x, ⟨SetLike.coe_mem x, (HEq x).mp hx2⟩, rfl⟩
  · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
    exact ⟨⟨x, ⟨⟨x, hx1⟩, rfl⟩, rfl⟩, (HEq x).mpr hx2⟩
#align number_field.canonical_embedding.integer_lattice.inter_ball_finite NumberField.canonicalEmbedding.integerLattice.inter_ball_finite

instance [NumberField K] : Countable (integerLattice K) :=
  by
  have : (⋃ n : ℕ, (integer_lattice K : Set E) ∩ closed_ball 0 n).Countable :=
    Set.countable_iUnion fun n => (integer_lattice.inter_ball_finite K n).Countable
  refine' (this.mono _).to_subtype
  rintro _ ⟨x, hx, rfl⟩
  rw [Set.mem_iUnion]
  exact ⟨⌈‖canonical_embedding K x‖⌉₊, ⟨x, hx, rfl⟩, mem_closedBall_zero_iff.2 (Nat.le_ceil _)⟩

end NumberField.canonicalEmbedding

