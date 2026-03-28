/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Norm determinant of a linear map

Given a rectangular matrix $T$, it is common to talk about $\sqrt{det(T^{H}T)}$, where $T^{H}$ is
the conjugate transpose of $T$, as a generalization to the determinant of a square matrix. It is the
$m$-dimensional volume factor for $\mathbb{R}^m \to \mathbb{R}^n$. It is given various names in
literature:
* "Jacobian" (definition 3.4 of [lawrenceronald2025]), in the context of volume factor
  for non-linear map. However, we choose to reserve this name for the matrix consists of
  derivatives.
* "Gram determinant", which is already used by `Matrix.gram`, and it is often referring to the
  $det(T^{H}T)$ without the square root.
* "Nonnegative determinant" (definition 1 of [haruoyoshiohidetoki2006]).

Without a standardized name, we give a descriptive name `LinearMap.normDet` to reflect its
definition and show that it is a generalization of `‖(f : LinearMap 𝕜 U U).det‖`
(See `LinearMap.normDet_eq_norm_det`). We also construct this on linear maps between inner product
spaces instead of matrices, and allow the codomain to have infinite dimension.

## Main definition
* `LinearMap.normDet` : the norm determinant of a linear map.

## Main result
* `ContinuousLinearMap.normDet_sq` and `LinearMap.normDet_sq`: The square of `f.normDet`
  equals to the determinant of `f.adjoint ∘ₗ f`.
* `LinearMap.normDet_sq_eq_det_gram`: The square of `LinearMap.normDet` equals to the determinant of
  the gram matrix formed by vectors mapped from an orthonormal basis.
* `LinearMap.normDet_eq_prod_singularValues`: `LinearMap.normDet` equals to the product of singular
  values.
* `LinearMap.hausdorffMeasure_image`: `LinearMap.normDet` is the volume factor for Hausdorff
  measure.

-/

public section

open Module

namespace LinearMap

variable {𝕜 U V W : Type*} [RCLike 𝕜] [NormedAddCommGroup U] [InnerProductSpace 𝕜 U]
  [FiniteDimensional 𝕜 U] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [NormedAddCommGroup W]
  [InnerProductSpace 𝕜 W]

open Classical in
/--
The norm determinant of a linear map `f : U →ₗ[𝕜] V` is defined as the norm of the determinant of
the square matrix from `U →ₗ[𝕜] f.range` using a pair of orthonormal basis of equal dimensions.
(See `LinearMap.normDet_eq_norm_det_toMatrix_rangeRestrict` for using arbitrary orthonormal basis)

If such basis doesn't exist (i.e. the map is not injective), the norm determinant is zero.
(See `LinearMap.normDet_eq_zero_iff_ker_ne_bot`)
-/
noncomputable def normDet (f : U →ₗ[𝕜] V) : ℝ :=
  if h : Nonempty (OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 f.range) then
    ‖(f.rangeRestrict.toMatrix (stdOrthonormalBasis 𝕜 U).toBasis h.some.toBasis).det‖
  else
    0

theorem normDet_nonneg (f : U →ₗ[𝕜] V) : 0 ≤ f.normDet := by
  unfold normDet
  split <;> simp

/--
`LinearMap.normDet` is well-defined under any pair of orthonormal basis.
-/
theorem normDet_eq_norm_det_toMatrix_rangeRestrict {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : U →ₗ[𝕜] V) (bu : OrthonormalBasis ι 𝕜 U) (bv : OrthonormalBasis ι 𝕜 f.range) :
    f.normDet = ‖(f.rangeRestrict.toMatrix bu.toBasis bv.toBasis).det‖ := by
  have hrank : finrank 𝕜 U = finrank 𝕜 f.range := by
    rw [finrank_eq_nat_card_basis bu.toBasis, finrank_eq_nat_card_basis bv.toBasis]
  have h : Nonempty (OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 f.range) := by
    rw [hrank]
    exact ⟨stdOrthonormalBasis 𝕜 f.range⟩
  simp only [normDet, h, ↓reduceDIte]
  rw [← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix (stdOrthonormalBasis 𝕜 U).toBasis
    bu.toBasis h.some.toBasis bv.toBasis]
  have h1 : bu.toBasis.toMatrix (stdOrthonormalBasis 𝕜 U).toBasis *
      (stdOrthonormalBasis 𝕜 U).toBasis.toMatrix bu.toBasis = 1 :=
    Basis.toMatrix_mul_toMatrix_flip _ _
  have h2 : (stdOrthonormalBasis 𝕜 U).toBasis.toMatrix bu.toBasis *
      bu.toBasis.toMatrix (stdOrthonormalBasis 𝕜 U).toBasis = 1 :=
    Basis.toMatrix_mul_toMatrix_flip _ _
  rw [← Matrix.det_comm' h1 h2, ← Matrix.mul_assoc, Matrix.det_mul, norm_mul]
  suffices ‖(bu.toBasis.toMatrix (stdOrthonormalBasis 𝕜 U).toBasis *
      h.some.toBasis.toMatrix ⇑bv.toBasis).det‖ = 1 by
    rw [this]
    simp
  apply CStarRing.norm_of_mem_unitary
  apply Matrix.det_of_mem_unitary
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
    ← Matrix.mul_assoc, Matrix.mul_assoc (bu.toBasis.toMatrix (stdOrthonormalBasis 𝕜 U).toBasis)]
  simp

/--
`LinearMap.normDet` vanishes iff the map is not injective.
-/
theorem normDet_eq_zero_iff_ker_ne_bot {f : U →ₗ[𝕜] V} :
    f.normDet = 0 ↔ f.ker ≠ ⊥ where
  mp h := by
    contrapose h
    let g : U ≃ₗ[𝕜] f.range := LinearEquiv.ofBijective f.rangeRestrict
      ⟨by simpa using ker_eq_bot.mp h, f.surjective_rangeRestrict⟩
    let bu := stdOrthonormalBasis 𝕜 U
    let bv := g.finrank_eq.symm ▸ stdOrthonormalBasis 𝕜 f.range
    rw [f.normDet_eq_norm_det_toMatrix_rangeRestrict bu bv, norm_eq_zero.not]
    suffices (f.rangeRestrict.adjoint.toMatrix bv.toBasis bu.toBasis).det *
        (f.rangeRestrict.toMatrix bu.toBasis bv.toBasis).det ≠ 0 by
      simpa [toMatrix_adjoint, Matrix.det_conjTranspose] using this
    simpa [← Matrix.det_mul, ← LinearMap.toMatrix_comp, det_eq_zero_iff_ker_ne_bot,
      LinearMap.ker_adjoint_comp_self] using h
  mpr h := by
    suffices ¬ Nonempty (OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 f.range) by
      simp [normDet, this]
    contrapose h
    obtain ⟨b⟩ := h
    have hrank : finrank 𝕜 f.range = finrank 𝕜 U := by
      simpa using finrank_eq_card_basis b.toBasis
    simpa [hrank] using f.finrank_range_add_finrank_ker

theorem normDet_eq_zero_iff_rank_range_ne {f : U →ₗ[𝕜] V} :
    f.normDet = 0 ↔ finrank 𝕜 f.range ≠ finrank 𝕜 U := by
  simp [normDet_eq_zero_iff_ker_ne_bot, ← f.finrank_range_add_finrank_ker]

/--
`LinearMap.normDet` can be calculated with any pair of orthonormal basis of equal dimension,
as long as the range is contained in the span.
-/
theorem normDet_eq_norm_det_toMatrix_codRestrict {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : U →ₗ[𝕜] V} {p : Submodule 𝕜 V} (hp : ∀ (c : U), f c ∈ p)
    (bu : OrthonormalBasis ι 𝕜 U) (bv : OrthonormalBasis ι 𝕜 p) :
    f.normDet = ‖((f.codRestrict p hp).toMatrix bu.toBasis bv.toBasis).det‖ := by
  have hle : f.range ≤ p := by
    intro c
    simp
    grind
  have : FiniteDimensional 𝕜 p := bv.toBasis.finiteDimensional_of_finite
  by_cases! hrank : finrank 𝕜 U = finrank 𝕜 f.range
  · have h : p = f.range := by
      refine (Submodule.eq_of_le_of_finrank_le hle ?_).symm
      rw [finrank_eq_card_basis bv.toBasis, ← hrank, finrank_eq_card_basis bu.toBasis]
    let bv' : OrthonormalBasis ι 𝕜 f.range := bv.map (LinearIsometryEquiv.ofEq _ _ h)
    rw [f.normDet_eq_norm_det_toMatrix_rangeRestrict bu bv']
    rfl
  · symm
    rw [normDet_eq_zero_iff_rank_range_ne.mpr hrank.symm]
    contrapose hrank with hdet
    have h : IsUnit (((codRestrict p f hp).toMatrix bu.toBasis bv.toBasis).det) := by
      simpa using hdet
    let f' := LinearEquiv.ofIsUnitDet h
    have hp : f.range = p := by
      refine le_antisymm hle (fun x hx ↦ mem_range.mpr ?_)
      exact ⟨f'.symm ⟨x, hx⟩, (by simp : f' (f'.symm ⟨x, hx⟩) = x)⟩
    rw [hp]
    exact f'.finrank_eq

/--
`LinearMap.normDet` can be calculated with any pair of orthonormal basis if the domain and the
codomain have equal dimension.
-/
theorem normDet_eq_norm_det_toMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] (f : U →ₗ[𝕜] V)
    (bu : OrthonormalBasis ι 𝕜 U) (bv : OrthonormalBasis ι 𝕜 V) :
    f.normDet = ‖(f.toMatrix bu.toBasis bv.toBasis).det‖ := by
  rw [normDet_eq_norm_det_toMatrix_codRestrict (by simp) bu
    (bv.map (LinearIsometryEquiv.ofTop V _ rfl).symm)]
  rfl

/--
`LinearMap.normDet` equals to the norm of `LinearMap.det` for an endomorphism.
-/
theorem normDet_eq_norm_det (f : U →ₗ[𝕜] U) : f.normDet = ‖f.det‖ := by
  simp [f.normDet_eq_norm_det_toMatrix (stdOrthonormalBasis 𝕜 U) (stdOrthonormalBasis 𝕜 U)]

/--
`LinearMap.normDet` of a linear isometry is 1.
-/
@[simp]
theorem _root_.LinearIsometry.normDet_eq_one (f : U →ₗᵢ[𝕜] V) : f.toLinearMap.normDet = 1 := by
  have hrank : finrank 𝕜 U = finrank 𝕜 f.range :=
    f.equivRange.toLinearEquiv.finrank_eq
  let b := (stdOrthonormalBasis 𝕜 f.toLinearMap.range)
  rw [← hrank] at b
  rw [normDet_eq_norm_det_toMatrix_rangeRestrict _ (stdOrthonormalBasis 𝕜 U) b]
  apply CStarRing.norm_of_mem_unitary
  exact Matrix.det_of_mem_unitary <| (f.equivRange).toMatrix_mem_unitaryGroup _ _

@[simp]
theorem normDet_id : (id : U →ₗ[𝕜] U).normDet = 1 :=
  LinearIsometry.id.normDet_eq_one

@[simp]
theorem normDet_subtype (p : Submodule 𝕜 U) : p.subtype.normDet = 1 :=
  p.subtypeₗᵢ.normDet_eq_one

@[simp]
theorem normDet_of_subsingleton [Subsingleton U] (f : U →ₗ[𝕜] V) : f.normDet = 1 := by
  have h : finrank 𝕜 U = 0 := finrank_zero_iff.mpr ‹_›
  have hf : finrank 𝕜 f.range = 0 := by
    apply Nat.eq_zero_of_le_zero
    rw [← h]
    apply LinearMap.finrank_range_le
  let bu : OrthonormalBasis (Fin 0) 𝕜 U := (stdOrthonormalBasis 𝕜 U).reindex (by rw [h])
  let bv : OrthonormalBasis (Fin 0) 𝕜 f.range :=
    (stdOrthonormalBasis 𝕜 f.range).reindex (by rw [hf])
  rw [normDet_eq_norm_det_toMatrix_rangeRestrict _ bu bv]
  simp

@[simp]
theorem normDet_zero : (0 : U →ₗ[𝕜] V).normDet = 0 ^ finrank 𝕜 U := by
  nontriviality U
  simp [zero_pow finrank_pos.ne.symm, normDet_eq_zero_iff_ker_ne_bot]

@[simp]
theorem normDet_smul (f : U →ₗ[𝕜] V) (c : 𝕜) :
    (c • f).normDet = ‖c‖ ^ finrank 𝕜 U * f.normDet := by
  by_cases hc : c = 0
  · nontriviality U
    simp [hc, zero_pow finrank_pos.ne.symm]
  by_cases h : f.ker = ⊥
  · have hrank : finrank 𝕜 f.range = finrank 𝕜 U := by
      obtain hrank := f.finrank_range_add_finrank_ker
      rw [h] at hrank
      simpa [h] using hrank
    let bu : OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 U := stdOrthonormalBasis 𝕜 U
    let bv : OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 f.range :=
      (stdOrthonormalBasis 𝕜 f.range).reindex (by rw [hrank])
    let bv' : OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 (c • f).range := bv.map
      (LinearIsometryEquiv.ofEq _ _ (LinearMap.range_smul _ _ hc).symm)
    rw [f.normDet_eq_norm_det_toMatrix_rangeRestrict bu bv,
      (c • f).normDet_eq_norm_det_toMatrix_rangeRestrict bu bv', ← norm_pow, ← norm_mul]
    have : finrank 𝕜 U = Fintype.card (Fin (finrank 𝕜 U)) := by simp
    conv in c ^ finrank 𝕜 U => rw [this]
    rw [← Matrix.det_smul, ← map_smul]
    rfl
  · have h' : (c • f).ker ≠ ⊥ := by simpa [f.ker_smul _ hc] using h
    simp [normDet_eq_zero_iff_ker_ne_bot.mpr h, normDet_eq_zero_iff_ker_ne_bot.mpr h']

@[simp]
theorem normDet_neg (f : U →ₗ[𝕜] V) : (-f).normDet = f.normDet := by
  simpa using f.normDet_smul (-1)

set_option backward.isDefEq.respectTransparency false in
/--
The square of `f.normDet` equals to the determinant of `f.adjoint ∘L f`.
-/
theorem _root_.ContinuousLinearMap.normDet_sq [CompleteSpace V] (f : U →L[𝕜] V) :
    haveI : CompleteSpace U := FiniteDimensional.complete 𝕜 U
    ↑(f.normDet ^ 2) = (f.adjoint ∘L f).det := by
  have : CompleteSpace U := FiniteDimensional.complete 𝕜 U
  have : CompleteSpace f.range := FiniteDimensional.complete 𝕜 f.range
  let bu := stdOrthonormalBasis 𝕜 U
  classical
  by_cases! hrank : finrank 𝕜 U = finrank 𝕜 f.range
  · let b : OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 f.range :=
      (stdOrthonormalBasis 𝕜 f.range).reindex (by
      rw [← hrank, finrank_eq_card_basis bu.toBasis])
    have hf : f = f.range.subtypeₗᵢ.toContinuousLinearMap ∘L f.rangeRestrict := rfl
    conv_rhs => rw [hf]
    rw [ContinuousLinearMap.adjoint_comp, ← ContinuousLinearMap.comp_assoc,
      ContinuousLinearMap.comp_assoc (ContinuousLinearMap.adjoint _)]
    suffices f.range.subtypeₗᵢ.toContinuousLinearMap.adjoint ∘L
        f.range.subtypeₗᵢ.toContinuousLinearMap = ContinuousLinearMap.id 𝕜 _ by
      rw [this, ContinuousLinearMap.comp_id, ContinuousLinearMap.det, ContinuousLinearMap.coe_comp,
        ← det_toMatrix bu.toBasis, toMatrix_comp bu.toBasis b.toBasis bu.toBasis]
      rw [show (ContinuousLinearMap.adjoint f.rangeRestrict).toLinearMap =
        f.rangeRestrict.toLinearMap.adjoint by rfl]
      rw [toMatrix_adjoint]
      simp [f.toLinearMap.normDet_eq_norm_det_toMatrix_rangeRestrict bu b, RCLike.conj_mul]
    exact f.range.subtypeₗᵢ.adjoint_comp_self
  · rw [f.normDet_eq_zero_iff_rank_range_ne.mpr hrank.symm]
    trans 0
    · simp
    symm
    rw [det_eq_zero_iff_ker_ne_bot, ContinuousLinearMap.ker_adjoint_comp_self]
    contrapose hrank
    exact (finrank_range_of_inj <| ker_eq_bot.mp hrank).symm

/--
The square of `f.normDet` equals to the determinant of `f.adjoint ∘ₗ f` when the codomain is finite
dimensional.
-/
theorem normDet_sq [FiniteDimensional 𝕜 V] (f : U →ₗ[𝕜] V) :
    ↑(f.normDet ^ 2) = (f.adjoint ∘ₗ f).det := by
  have : CompleteSpace V := FiniteDimensional.complete 𝕜 V
  exact f.toContinuousLinearMap.normDet_sq

/--
The square of `f.normDet` equals to the determinant of the gram matrix formed by vectors mapped from
an orthonormal basis.
-/
theorem normDet_sq_eq_det_gram {ι : Type*} [Fintype ι] [DecidableEq ι] (f : U →ₗ[𝕜] V)
    (b : OrthonormalBasis ι 𝕜 U) :
    ↑(f.normDet ^ 2) = (Matrix.gram 𝕜 (f <| b ·)).det := by
  suffices ↑(f.normDet ^ 2) = (Matrix.gram 𝕜 (f.rangeRestrict <| b ·)).det by
    simpa
  by_cases! hrank : finrank 𝕜 U = finrank 𝕜 f.range
  · let bv : OrthonormalBasis ι 𝕜 f.range := (stdOrthonormalBasis 𝕜 f.range).reindex
      (Fintype.equivFinOfCardEq (by rw [← finrank_eq_card_basis b.toBasis, hrank])).symm
    rw [Matrix.gram_eq_conjTranspose_mul bv, Matrix.det_mul, Matrix.det_conjTranspose]
    rw [RCLike.star_def, RCLike.conj_mul, f.normDet_eq_norm_det_toMatrix_rangeRestrict b bv]
    simp only [map_pow]
    congr
    ext i j
    simp [LinearMap.toMatrix_apply]
  · rw [f.normDet_eq_zero_iff_rank_range_ne.mpr hrank.symm]
    trans 0
    · simp
    symm
    contrapose hrank with h0
    obtain hindep := Matrix.linearIndependent_of_det_gram_ne_zero h0
    apply le_antisymm ?_ (finrank_range_le f)
    rw [finrank_eq_card_basis b.toBasis]
    exact hindep.fintype_card_le_finrank

theorem normDet_comp (f : U →ₗ[𝕜] V) (g : V →ₗ[𝕜] W) :
    (g ∘ₗ f).normDet = (g.domRestrict f.range).normDet * f.normDet := by
  by_cases hrank : finrank 𝕜 U = finrank 𝕜 f.range
  · let bu : OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 U := stdOrthonormalBasis 𝕜 U
    let bv : OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 f.range :=
      (stdOrthonormalBasis 𝕜 f.range).reindex (by
      rw [← hrank, finrank_eq_card_basis bu.toBasis])
    by_cases hrank' : finrank 𝕜 U = finrank 𝕜 (g ∘ₗ f).range
    · let bw : OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 (g ∘ₗ f).range :=
        (stdOrthonormalBasis 𝕜 (g ∘ₗ f).range).reindex (by
        rw [← hrank', finrank_eq_card_basis bu.toBasis])
      let bw' : OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 (g.domRestrict f.range).range :=
        bw.map (LinearIsometryEquiv.ofEq _ _ (by simp [LinearMap.range_comp]))
      rw [(g ∘ₗ f).normDet_eq_norm_det_toMatrix_rangeRestrict bu bw,
        f.normDet_eq_norm_det_toMatrix_rangeRestrict bu bv,
        (g.domRestrict f.range).normDet_eq_norm_det_toMatrix_rangeRestrict bv bw']
      rw [← norm_mul, ← Matrix.det_mul, ← LinearMap.toMatrix_comp]
      rfl
    · have hker : (g ∘ₗ f).ker ≠ ⊥ := by
        contrapose hrank' with hbot
        obtain h := (g ∘ₗ f).finrank_range_add_finrank_ker.symm
        rw [hbot] at h
        simpa using h
      have hker' : (g.domRestrict f.range).ker ≠ ⊥ := by
        contrapose hrank' with hbot
        obtain h := (g.domRestrict f.range).finrank_range_add_finrank_ker.symm
        rw [hbot, range_domRestrict] at h
        rw [hrank, h, range_comp]
        simp
      simp [normDet_eq_zero_iff_ker_ne_bot.mpr hker, normDet_eq_zero_iff_ker_ne_bot.mpr hker']
  · have hker : f.ker ≠ ⊥ := by
      contrapose hrank with hbot
      obtain h := f.finrank_range_add_finrank_ker.symm
      rw [hbot] at h
      simpa using h
    have hker' : (g ∘ₗ f).ker ≠ ⊥ := by
      contrapose hker with hbot
      simpa [hbot] using ker_le_ker_comp f g
    simp [normDet_eq_zero_iff_ker_ne_bot.mpr hker, normDet_eq_zero_iff_ker_ne_bot.mpr hker']

theorem normDet_comp_of_finrank_eq [FiniteDimensional 𝕜 V] (f : U →ₗ[𝕜] V) (g : V →ₗ[𝕜] W)
    (h : finrank 𝕜 U = finrank 𝕜 V) :
    (g ∘ₗ f).normDet = g.normDet * f.normDet := by
  by_cases htop : f.range = ⊤
  · rw [normDet_comp]
    congrm ?_ * _
    suffices (g.domRestrict f.range).normDet * (id : V →ₗ[𝕜] V).normDet = g.normDet by simpa
    have : f.range = id.range := by simp [htop]
    convert (normDet_comp LinearMap.id g).symm
  · have hker : f.ker ≠ ⊥ := by
      simpa [ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank h] using htop
    have hker' : (g ∘ₗ f).ker ≠ ⊥ := by
      contrapose hker with hbot
      simpa [hbot] using ker_le_ker_comp f g
    simp [normDet_eq_zero_iff_ker_ne_bot.mpr hker, normDet_eq_zero_iff_ker_ne_bot.mpr hker']

@[simp]
theorem normDet_codRestrict {p : Submodule 𝕜 V} {f : U →ₗ[𝕜] V} (h : ∀ c, f c ∈ p) :
    (f.codRestrict p h).normDet = f.normDet := by
  have : f = p.subtype ∘ₗ f.codRestrict p h := rfl
  conv_rhs => rw [this]
  rw [normDet_comp]
  have : (p.subtype.domRestrict (codRestrict p f h).range).normDet = 1 :=
    (p.subtypeₗᵢ.comp (codRestrict p f h).range.subtypeₗᵢ).normDet_eq_one
  simp [this]

theorem normDet_eq_prod_singularValues [FiniteDimensional 𝕜 V] (f : U →ₗ[𝕜] V) :
    f.normDet = ∏ i ∈ Finset.range (finrank 𝕜 U), f.singularValues i := by
  rw [← sq_eq_sq₀ f.normDet_nonneg (Finset.prod_nonneg fun i _ ↦ f.singularValues_nonneg i),
    ← RCLike.ofReal_inj (K := 𝕜), ← Finset.prod_pow, ← Fin.prod_univ_eq_prod_range, normDet_sq]
  simp_rw [sq_singularValues_fin]
  push_cast
  rw [← LinearMap.IsSymmetric.det_eq_prod_eigenvalues]

section Real

open MeasureTheory Measure

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem normDet_eq_abs_det (f : U →ₗ[ℝ] U) : f.normDet = |f.det| := by
  simpa using f.normDet_eq_norm_det

set_option backward.isDefEq.respectTransparency false in
/--
Using Hausdorff measure wih the domain dimension, the volume of the image is scaled by
`LinearMap.normDet`.
-/
theorem hausdorffMeasure_image [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
    (f : U →ₗ[ℝ] V) (s : Set U) :
    μH[finrank ℝ U] (f '' s) = ENNReal.ofReal f.normDet * μH[finrank ℝ U] s := by
  by_cases! hrank : finrank ℝ U = finrank ℝ f.range
  · let bu : OrthonormalBasis (Fin (finrank ℝ U)) ℝ U := stdOrthonormalBasis ℝ U
    let bv : OrthonormalBasis (Fin (finrank ℝ U)) ℝ f.range :=
      (stdOrthonormalBasis ℝ f.range).reindex (by
      rw [← hrank, finrank_eq_card_basis bu.toBasis])
    let g : U ≃ₗᵢ[ℝ] f.range := bu.equiv bv (Equiv.refl _)
    suffices μH[finrank ℝ U] ((f.range.subtypeₗᵢ.comp g.toLinearIsometry) ''
        ((g.symm.toLinearIsometry.toLinearMap ∘ₗ f.rangeRestrict) '' s)) =
        ENNReal.ofReal f.normDet * μH[finrank ℝ U] s by
      simpa [Set.image_image]
    rw [(LinearIsometry.isometry _).hausdorffMeasure_image (by simp),
      addHaar_image_linearMap μH[finrank ℝ U], ← normDet_eq_abs_det,
      normDet_comp_of_finrank_eq _ _ hrank, g.symm.toLinearIsometry.normDet_eq_one]
    simp
  · have h : (finrank ℝ f.range : ℝ) < finrank ℝ U := by
      exact_mod_cast lt_of_le_of_ne f.finrank_range_le hrank.symm
    suffices μH[finrank ℝ U] (f.range.subtypeₗᵢ '' (f.rangeRestrict '' s)) = 0 by
      simpa [f.normDet_eq_zero_iff_rank_range_ne.mpr hrank.symm, Set.image_image]
    rw [(LinearIsometry.isometry _).hausdorffMeasure_image (by simp)]
    simp [Real.hausdorffMeasure_of_finrank_lt h]

/--
Using Euclidean Hausdorff measure wih the domain dimension, the volume of the image is scaled by
`LinearMap.normDet`.
-/
theorem euclideanHausdorffMeasure_image [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V]
    [BorelSpace V] (f : U →ₗ[ℝ] V) (s : Set U) :
    μHE[finrank ℝ U] (f '' s) = ENNReal.ofReal f.normDet * μHE[finrank ℝ U] s := by
  simp_rw [euclideanHausdorffMeasure_def, Measure.smul_apply, nnreal_smul_coe_apply,
    hausdorffMeasure_image]
  exact mul_left_comm _ _ _

/--
The volume of the image measured by Euclidean Hausdorff measure is equal to the Lebesgue measure
scaled by `LinearMap.normDet`.
-/
theorem euclideanHausdorffMeasure_image_eq_normDet_mul_volume [MeasurableSpace U] [BorelSpace U]
    [MeasurableSpace V] [BorelSpace V] (f : U →ₗ[ℝ] V) (s : Set U) :
    μHE[finrank ℝ U] (f '' s) = ENNReal.ofReal f.normDet * volume s := by
  rw [f.euclideanHausdorffMeasure_image, InnerProductSpace.euclideanHausdorffMeasure_eq_volume]

end Real

end LinearMap
