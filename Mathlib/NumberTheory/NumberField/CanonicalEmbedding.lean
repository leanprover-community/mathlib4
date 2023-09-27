/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.NumberTheory.NumberField.Embeddings

#align_import number_theory.number_field.canonical_embedding from "leanprover-community/mathlib"@"60da01b41bbe4206f05d34fd70c8dd7498717a30"

/-!
# Canonical embedding of a number field

The canonical embedding of a number field `K` of signature `(r₁, r₂)` is the ring homomorphism
`K →+* ℝ^r₁ × ℂ^r₂` that sends `x ∈ K` to `(φ_₁(x),...,φ_r₁(x)) × (ψ_₁(x),..., ψ_r₂(x))` where
`φ_₁,...,φ_r₁` are its real embeddings and `ψ_₁,..., ψ_r₂` are its complex embeddings (up to
complex conjugation).

## Main definitions and results

* `NumberField.canonicalEmbedding.integerLattice.inter_ball_finite`: the intersection of the
image of the ring of integers by the canonical embedding and any ball centered at `0` of finite
radius is finite.

## Tags

number field, infinite places
-/


noncomputable section

open Function FiniteDimensional Finset Fintype NumberField NumberField.InfinitePlace Metric Module

open scoped Classical NumberField

variable (K : Type*) [Field K]

namespace NumberField.canonicalEmbedding

-- The ambient space `ℝ^r₁ × ℂ^r₂` with `(r₁, r₂)` the signature of `K`.
set_option quotPrecheck false in -- Porting note: Added.
scoped[CanonicalEmbedding]
  notation "E" =>
    ({ w : InfinitePlace K // IsReal w } → ℝ) × ({ w : InfinitePlace K // IsComplex w } → ℂ)

open CanonicalEmbedding

theorem space_rank [NumberField K] : finrank ℝ E = finrank ℚ K := by
  haveI : Module.Free ℝ ℂ := inferInstance
  rw [finrank_prod, finrank_pi, finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const,
    Finset.card_univ, ← card_real_embeddings, Algebra.id.smul_eq_mul, mul_comm,
    ← card_complex_embeddings, ← NumberField.Embeddings.card K ℂ, Fintype.card_subtype_compl,
    Nat.add_sub_of_le (Fintype.card_subtype_le _)]
#align number_field.canonical_embedding.space_rank NumberField.canonicalEmbedding.space_rank

theorem nontrivial_space [NumberField K] : Nontrivial E := by
  have : Nonempty <| InfinitePlace K := inferInstance
  rcases this with ⟨w⟩
  obtain hw | hw := w.isReal_or_isComplex
  · haveI : Nonempty { w : InfinitePlace K // IsReal w } := ⟨⟨w, hw⟩⟩
    exact nontrivial_prod_left
  · haveI : Nonempty { w : InfinitePlace K // IsComplex w } := ⟨⟨w, hw⟩⟩
    exact nontrivial_prod_right
#align number_field.canonical_embedding.non_trivial_space NumberField.canonicalEmbedding.nontrivial_space

/-- The canonical embedding of a number field `K` of signature `(r₁, r₂)` into `ℝ^r₁ × ℂ^r₂`. -/
def _root_.NumberField.canonicalEmbedding : K →+* E :=
  RingHom.prod (Pi.ringHom fun w => embedding_of_isReal w.prop)
    (Pi.ringHom fun w => w.val.embedding)
#align number_field.canonical_embedding NumberField.canonicalEmbedding

theorem _root_.NumberField.canonicalEmbedding_injective [NumberField K] :
    Injective (NumberField.canonicalEmbedding K) :=
  @RingHom.injective _ _ _ _ (nontrivial_space K) _
#align number_field.canonical_embedding_injective NumberField.canonicalEmbedding_injective

open NumberField

variable {K}

@[simp]
theorem apply_at_real_infinitePlace (w : { w : InfinitePlace K // IsReal w }) (x : K) :
    (NumberField.canonicalEmbedding K x).1 w = embedding_of_isReal w.prop x := by
  simp only [canonicalEmbedding, RingHom.prod_apply, Pi.ringHom_apply]
#align number_field.canonical_embedding.apply_at_real_infinite_place NumberField.canonicalEmbedding.apply_at_real_infinitePlace

@[simp]
theorem apply_at_complex_infinitePlace (w : { w : InfinitePlace K // IsComplex w }) (x : K) :
    (NumberField.canonicalEmbedding K x).2 w = embedding w.val x := by
  simp only [canonicalEmbedding, RingHom.prod_apply, Pi.ringHom_apply]
#align number_field.canonical_embedding.apply_at_complex_infinite_place NumberField.canonicalEmbedding.apply_at_complex_infinitePlace

theorem nnnorm_eq [NumberField K] (x : K) :
    ‖canonicalEmbedding K x‖₊ =
      Finset.univ.sup fun w : InfinitePlace K => ⟨w x, map_nonneg w x⟩ := by
  rw [Prod.nnnorm_def', Pi.nnnorm_def, Pi.nnnorm_def]
  rw [(_ : Finset.univ =
        {w : InfinitePlace K | IsReal w}.toFinset ∪ {w : InfinitePlace K | IsComplex w}.toFinset)]
  · rw [Finset.sup_union, sup_eq_max]
    refine' congr_arg₂ _ _ _
    · convert
        (Finset.univ.sup_map (Function.Embedding.subtype fun w : InfinitePlace K => IsReal w)
          fun w => (⟨w x, map_nonneg w x⟩ : NNReal)).symm using 2
      ext w
      dsimp
      rw [apply_at_real_infinitePlace, ← Complex.abs_ofReal, embedding_of_isReal_apply,
        ← Complex.norm_eq_abs, norm_embedding_eq]
    · convert
        (Finset.univ.sup_map (Function.Embedding.subtype fun w : InfinitePlace K => IsComplex w)
          fun w => (⟨w x, map_nonneg w x⟩ : NNReal)).symm using 2
      ext w
      dsimp
      rw [apply_at_complex_infinitePlace, ← Complex.norm_eq_abs, norm_embedding_eq]
  · ext w
    simp_rw [Finset.mem_univ, Finset.mem_union, Set.mem_toFinset, Set.mem_setOf_eq,
      w.isReal_or_isComplex]
#align number_field.canonical_embedding.nnnorm_eq NumberField.canonicalEmbedding.nnnorm_eq

theorem norm_le_iff [NumberField K] (x : K) (r : ℝ) :
    ‖canonicalEmbedding K x‖ ≤ r ↔ ∀ w : InfinitePlace K, w x ≤ r := by
  obtain hr | hr := lt_or_le r 0
  · have : Nonempty <| InfinitePlace K := inferInstance
    rcases this with ⟨w⟩
    exact iff_of_false
      (hr.trans_le <| norm_nonneg _).not_le fun h => hr.not_le <| (map_nonneg w _).trans <| h _
  · lift r to NNReal using hr
    simp_rw [← coe_nnnorm, nnnorm_eq, NNReal.coe_le_coe, Finset.sup_le_iff, Finset.mem_univ,
      forall_true_left, ← NNReal.coe_le_coe, NNReal.toReal]
#align number_field.canonical_embedding.norm_le_iff NumberField.canonicalEmbedding.norm_le_iff

variable (K)

/-- The image of `𝓞 K` as a subring of `ℝ^r₁ × ℂ^r₂`. -/
def integerLattice : Subring E :=
  (RingHom.range (algebraMap (𝓞 K) K)).map (canonicalEmbedding K)
#align number_field.canonical_embedding.integer_lattice NumberField.canonicalEmbedding.integerLattice

-- Porting note: See https://github.com/leanprover-community/mathlib4/issues/5028
set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 50000 in
/-- The linear equiv between `𝓞 K` and the integer lattice. -/
def equivIntegerLattice [NumberField K] : 𝓞 K ≃ₗ[ℤ] integerLattice K :=
  LinearEquiv.ofBijective
    { toFun := fun x => (by
          refine ⟨canonicalEmbedding K (algebraMap (𝓞 K) K x), ⟨algebraMap (𝓞 K) K x, ⟨?_, rfl⟩⟩⟩
          simp only [Subsemiring.coe_carrier_toSubmonoid, Subring.coe_toSubsemiring,
            RingHom.coe_range, Set.mem_range, exists_apply_eq_apply] )
      map_add' := fun x y => (by
          apply Subtype.eq
          simp [map_add] )
      map_smul' := fun c x => (by
          simp only [RingHom.id_apply, zsmul_eq_mul, RingHom.map_mul, map_intCast]
          rfl ) }
   (by
    refine ⟨fun _ _ h => ?_, fun ⟨_, ⟨_, ⟨⟨a, rfl⟩, rfl⟩⟩⟩ => ⟨a, rfl⟩⟩
    dsimp only at h
    rw [LinearMap.coe_mk, Subtype.mk_eq_mk] at h
    exact IsFractionRing.injective (𝓞 K) K (canonicalEmbedding_injective K h))
#align number_field.canonical_embedding.equiv_integer_lattice NumberField.canonicalEmbedding.equivIntegerLattice

theorem integerLattice.inter_ball_finite [NumberField K] (r : ℝ) :
    ((integerLattice K : Set E) ∩ closedBall 0 r).Finite := by
  obtain hr | _ := lt_or_le r 0
  · simp [closedBall_eq_empty.2 hr]
  have heq : ∀ x, canonicalEmbedding K x ∈ closedBall (0 : E) r ↔ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ r := by
    simp_rw [← place_apply, mem_closedBall_zero_iff, norm_le_iff, le_iff_le, place_apply,
      implies_true]
  convert (Embeddings.finite_of_norm_le K ℂ r).image (canonicalEmbedding K)
  ext; constructor
  · rintro ⟨⟨_, ⟨x, rfl⟩, rfl⟩, hx2⟩
    exact ⟨x, ⟨SetLike.coe_mem x, (heq x).mp hx2⟩, rfl⟩
  · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
    exact ⟨⟨x, ⟨⟨x, hx1⟩, rfl⟩, rfl⟩, (heq x).mpr hx2⟩
#align number_field.canonical_embedding.integer_lattice.inter_ball_finite NumberField.canonicalEmbedding.integerLattice.inter_ball_finite

instance [NumberField K] : Countable (integerLattice K) := by
  have : (⋃ n : ℕ, (integerLattice K : Set E) ∩ closedBall 0 n).Countable :=
    Set.countable_iUnion fun n => (integerLattice.inter_ball_finite K n).countable
  refine' (this.mono _).to_subtype
  rintro _ ⟨x, hx, rfl⟩
  rw [Set.mem_iUnion]
  exact ⟨⌈‖canonicalEmbedding K x‖⌉₊, ⟨x, hx, rfl⟩, mem_closedBall_zero_iff.2 (Nat.le_ceil _)⟩

end NumberField.canonicalEmbedding
