/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.NumberTheory.NumberField.Embeddings
import Mathlib.RingTheory.Discriminant

#align_import number_theory.number_field.canonical_embedding from "leanprover-community/mathlib"@"60da01b41bbe4206f05d34fd70c8dd7498717a30"

/-!
# Canonical embedding of a number field

The canonical embedding of a number field `K` of degree `n` is the ring homomorphism
`K →+* ℂ^n` that sends `x ∈ K` to `(φ_₁(x),...,φ_n(x))` where the `φ_i`'s are the complex
embeddings of `K`. Note that we do not choose an ordering of the embeddings, but instead map `K`
into the type `(K →+* ℂ) → ℂ` of `ℂ`-vectors indexed by the complex embeddings.

## Main definitions and results

* `canonicalEmbedding`: the ring homorphism `K →+* ((K →+* ℂ) → ℂ)` defined by sending `x : K` to
the vector `(φ x)` indexed by `φ : K →+* ℂ`.

* `canonicalEmbedding.integerLattice.inter_ball_finite`: the intersection of the
image of the ring of integers by the canonical embedding and any ball centered at `0` of finite
radius is finite.

## Tags

number field, infinite places
-/

variable (K : Type*) [Field K]

namespace NumberField.canonicalEmbedding

open NumberField

/-- The canonical embedding of a number field `K` of degree `n` into `ℂ^n`. -/
def _root_.NumberField.canonicalEmbedding : K →+* ((K →+* ℂ) → ℂ) := Pi.ringHom fun φ => φ

theorem _root_.NumberField.canonicalEmbedding_injective [NumberField K] :
    Function.Injective (NumberField.canonicalEmbedding K) := RingHom.injective _

variable {K}

@[simp]
theorem apply_at (φ : K →+* ℂ) (x : K) : (NumberField.canonicalEmbedding K x) φ = φ x := rfl

open scoped ComplexConjugate

/-- The image of `canonicalEmbedding` lives in the `ℝ`-submodule of the `x ∈ ((K →+* ℂ) → ℂ)` such
that `conj x_φ = x_(conj φ)` for all `∀ φ : K →+* ℂ`. -/
theorem conj_apply {x : ((K →+* ℂ) → ℂ)} (φ : K →+* ℂ)
    (hx : x ∈ Submodule.span ℝ (Set.range (canonicalEmbedding K))) :
    conj (x φ) = x (ComplexEmbedding.conjugate φ) := by
  refine Submodule.span_induction hx ?_ ?_ (fun _ _ hx hy => ?_) (fun a _ hx => ?_)
  · rintro _ ⟨x, rfl⟩
    rw [apply_at, apply_at, ComplexEmbedding.conjugate_coe_eq]
  · rw [Pi.zero_apply, Pi.zero_apply, map_zero]
  · rw [Pi.add_apply, Pi.add_apply, map_add, hx, hy]
  · rw [Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]
    exact congrArg ((a : ℂ) * ·) hx

theorem nnnorm_eq [NumberField K] (x : K) :
    ‖canonicalEmbedding K x‖₊ = Finset.univ.sup (fun φ : K →+* ℂ => ‖φ x‖₊) := by
  simp_rw [Pi.nnnorm_def, apply_at]

theorem norm_le_iff [NumberField K] (x : K) (r : ℝ) :
    ‖canonicalEmbedding K x‖ ≤ r ↔ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ r := by
  obtain hr | hr := lt_or_le r 0
  · obtain ⟨φ⟩ := (inferInstance : Nonempty (K →+* ℂ))
    refine iff_of_false ?_ ?_
    exact (hr.trans_le (norm_nonneg _)).not_le
    exact fun h => hr.not_le (le_trans (norm_nonneg _) (h φ))
  · lift r to NNReal using hr
    simp_rw [← coe_nnnorm, nnnorm_eq, NNReal.coe_le_coe, Finset.sup_le_iff, Finset.mem_univ,
      forall_true_left]

variable (K)

/-- The image of `𝓞 K` as a subring of `ℂ^n`. -/
def integerLattice : Subring ((K →+* ℂ) → ℂ) :=
  (RingHom.range (algebraMap (𝓞 K) K)).map (canonicalEmbedding K)

theorem integerLattice.inter_ball_finite [NumberField K] (r : ℝ) :
    ((integerLattice K : Set ((K →+* ℂ) → ℂ)) ∩ Metric.closedBall 0 r).Finite := by
  obtain hr | _ := lt_or_le r 0
  · simp [Metric.closedBall_eq_empty.2 hr]
  · have heq : ∀ x, canonicalEmbedding K x ∈ Metric.closedBall 0 r ↔
        ∀ φ : K →+* ℂ, ‖φ x‖ ≤ r := by
      intro x; rw [← norm_le_iff, mem_closedBall_zero_iff]
    convert (Embeddings.finite_of_norm_le K ℂ r).image (canonicalEmbedding K)
    ext; constructor
    · rintro ⟨⟨_, ⟨x, rfl⟩, rfl⟩, hx⟩
      exact ⟨↑x, ⟨SetLike.coe_mem x, fun φ => (heq x).mp hx φ⟩, rfl⟩
    · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
      exact ⟨⟨x, ⟨⟨x, hx1⟩, rfl⟩, rfl⟩, (heq x).mpr hx2⟩

open Module Fintype FiniteDimensional

/-- A `ℂ`-basis of `ℂ^n` that is also a `ℤ`-basis of the `integerLattice`. -/
noncomputable def latticeBasis [NumberField K] :
    Basis (Free.ChooseBasisIndex ℤ (𝓞 K)) ℂ ((K →+* ℂ) → ℂ) := by
  classical
  -- Let `B` be the canonical basis of `(K →+* ℂ) → ℂ`. We prove that the determinant of
  -- the image by `canonicalEmbedding` of the integral basis of `K` is nonzero. This
  -- will imply the result.
    let B := Pi.basisFun ℂ (K →+* ℂ)
    let e : (K →+* ℂ) ≃ Free.ChooseBasisIndex ℤ (𝓞 K) :=
      equivOfCardEq ((Embeddings.card K ℂ).trans (finrank_eq_card_basis (integralBasis K)))
    let M := B.toMatrix (fun i => canonicalEmbedding K (integralBasis K (e i)))
    suffices M.det ≠ 0 by
      rw [← isUnit_iff_ne_zero, ← Basis.det_apply, ← is_basis_iff_det] at this
      refine basisOfLinearIndependentOfCardEqFinrank
        ((linearIndependent_equiv e.symm).mpr this.1) ?_
      rw [← finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank, finrank_fintype_fun_eq_card,
        Embeddings.card]
  -- In order to prove that the determinant is nonzero, we show that it is equal to the
  -- square of the discriminant of the integral basis and thus it is not zero
    let N := Algebra.embeddingsMatrixReindex ℚ ℂ (fun i => integralBasis K (e i))
      RingHom.equivRatAlgHom
    rw [show M = N.transpose by { ext:2; rfl }]
    rw [Matrix.det_transpose, ← @pow_ne_zero_iff ℂ _ _ _ 2 (by norm_num)]
    convert (map_ne_zero_iff _ (algebraMap ℚ ℂ).injective).mpr
      (Algebra.discr_not_zero_of_basis ℚ (integralBasis K))
    rw [← Algebra.discr_reindex ℚ (integralBasis K) e.symm]
    exact (Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ
      (fun i => integralBasis K (e i)) RingHom.equivRatAlgHom).symm

@[simp]
theorem latticeBasis_apply [NumberField K] (i : Free.ChooseBasisIndex ℤ (𝓞 K)) :
    latticeBasis K i = (canonicalEmbedding K) (integralBasis K i) := by
  simp only [latticeBasis, integralBasis_apply, coe_basisOfLinearIndependentOfCardEqFinrank,
    Function.comp_apply, Equiv.apply_symm_apply]

theorem mem_span_latticeBasis [NumberField K] (x : (K →+* ℂ) → ℂ) :
    x ∈ Submodule.span ℤ (Set.range (latticeBasis K)) ↔ x ∈ canonicalEmbedding K '' (𝓞 K) := by
  rw [show Set.range (latticeBasis K) =
      (canonicalEmbedding K).toIntAlgHom.toLinearMap '' (Set.range (integralBasis K)) by
    rw [← Set.range_comp]; exact congrArg Set.range (funext (fun i => latticeBasis_apply K i))]
  rw [← Submodule.map_span, ← SetLike.mem_coe, Submodule.map_coe]
  rw [show (Submodule.span ℤ (Set.range (integralBasis K)) : Set K) = 𝓞 K by
    ext; exact mem_span_integralBasis K]
  rfl

end NumberField.canonicalEmbedding
