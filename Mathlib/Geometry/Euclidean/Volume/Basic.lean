/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Geometry.Euclidean.Volume.Def
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Volume.MeasureSimplex
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Volume of a simplex

This file provides lemma related to the volume of a simplex.
-/

public section

open MeasureTheory Measure

namespace Affine.Simplex

variable {V P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
variable {V₂ P₂ : Type*}
variable [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [MetricSpace P₂] [NormedAddTorsor V₂ P₂]

@[simp]
theorem volume_eq_one (s : Simplex ℝ P 0) : s.volume = 1 := rfl

@[simp]
theorem volume_eq_dist (s : Simplex ℝ P 1) : s.volume = dist (s.points 0) (s.points 1) := by
  simp [volume]

theorem volume_eq {n : ℕ} [NeZero n] (s : Simplex ℝ P n) (i : Fin (n + 1)) :
    s.volume = (↑n)⁻¹ * s.height i * (s.faceOpposite i).volume := by
  obtain ⟨m, rfl⟩ := Nat.exists_add_one_eq.mpr (NeZero.pos n)
  borelize P
  simp [volume_eq_euclideanHausdorffMeasure_real_closedInterior,
    s.euclideanHausdorffMeasure_real_closedInterior i]

@[simp]
theorem volume_reindex {m n : ℕ} (s : Simplex ℝ P n) (e : Fin (n + 1) ≃ Fin (m + 1)) :
    (s.reindex e).volume = s.volume := by
  borelize P
  have hnm : n = m := by simpa using Fin.equiv_iff_eq.mp ⟨e⟩
  simp_rw [volume_eq_euclideanHausdorffMeasure_real_closedInterior, hnm, closedInterior_reindex]

@[simp]
theorem volume_map {n : ℕ} (s : Simplex ℝ P n) (f : P →ᵃⁱ[ℝ] P₂) :
    (s.map f.toAffineMap f.injective).volume = s.volume := by
  by_cases hn : n = 0
  · obtain rfl := hn
    simp
  have : NeZero n := ⟨hn⟩
  conv_lhs => rw [volume_eq _ 0]
  conv_rhs => rw [volume_eq _ 0]
  rw [height_map, faceOpposite_map, volume_map]

@[simp]
theorem volume_map_homothety {n : ℕ} (s : Simplex ℝ P n) (c : P) {r : ℝ} (hr : r ≠ 0) :
    (s.map (AffineMap.homothety c r) (AffineMap.homothety_injective c hr)).volume =
    |r| ^ n * s.volume := by
  borelize P
  simp [volume_eq_euclideanHausdorffMeasure_real_closedInterior, measureReal_def,
    closedInterior_map, euclideanHausdorffMeasure_homothety_image n c hr]

theorem volume_map_linearMap_eq_det_mul [FiniteDimensional ℝ V]
    {n : ℕ} (hn : Module.finrank ℝ V = n) (s : Simplex ℝ V n) (f : V →ₗ[ℝ] V)
    (hf : Function.Injective f) :
    (s.map f.toAffineMap hf).volume = |f.det| * s.volume := by
  borelize V
  simp [volume_eq_volume_real_closedInterior hn, closedInterior_map, measureReal_def]

theorem volume_map_eq_det_mul {P₂ : Type*}
    [MetricSpace P₂] [NormedAddTorsor V P₂] [FiniteDimensional ℝ V]
    {n : ℕ} (hn : Module.finrank ℝ V = n) (s : Simplex ℝ P n) (f : P →ᵃ[ℝ] P₂)
    (hf : Function.Injective f) :
    (s.map f hf).volume = |f.linear.det| * s.volume := by
  obtain p := Classical.arbitrary P
  have hfeq : f = (AffineIsometryEquiv.vaddConst ℝ (f p)).toAffineMap.comp
      (f.linear.toAffineMap.comp (AffineIsometryEquiv.vaddConst ℝ p).symm.toAffineMap) := by
    ext x
    simp
  have hf' : Function.Injective ((AffineIsometryEquiv.vaddConst ℝ (f p)).toAffineMap.comp
      (f.linear.toAffineMap.comp (AffineIsometryEquiv.vaddConst ℝ p).symm) : P →ᵃ[ℝ] P₂) := by
    convert hf
    exact hfeq.symm
  trans (s.map _ hf').volume
  · congr
  rw [map_comp _ _ (by
    rw [AffineMap.coe_comp]
    exact Function.Injective.comp (by simpa using hf) (AffineIsometryEquiv.injective _))
    _ (AffineIsometryEquiv.injective _)]
  simp_rw [show (AffineIsometryEquiv.vaddConst ℝ (f p)).toAffineEquiv.toAffineMap =
    (AffineIsometryEquiv.vaddConst ℝ (f p)).toAffineIsometry.toAffineMap by rfl]
  rw [volume_map, map_comp _ _ (AffineIsometryEquiv.injective _) _ (by simpa using hf),
    volume_map_linearMap_eq_det_mul hn]
  congr
  exact s.volume_map (AffineIsometryEquiv.vaddConst ℝ p).symm.toAffineIsometry

@[simp]
theorem volume_restrict {n : ℕ} (s : Simplex ℝ P n) (S : AffineSubspace ℝ P)
    (hS : affineSpan ℝ (Set.range s.points) ≤ S) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).volume = s.volume := by
  have := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  by_cases hn : n = 0
  · obtain rfl := hn
    simp
  have : NeZero n := ⟨hn⟩
  conv_lhs => rw [volume_eq _ 0]
  conv_rhs => rw [volume_eq _ 0]
  rw [height_restrict, faceOpposite_restrict, volume_restrict]

@[simp]
theorem volume_pos {n : ℕ} (s : Simplex ℝ P n) : 0 < s.volume := by
  by_cases hn : n = 0
  · obtain rfl := hn
    simp
  have : NeZero n := ⟨hn⟩
  rw [volume_eq _ 0]
  have : 0 < (s.faceOpposite 0).volume := volume_pos _
  positivity

open Qq Mathlib.Meta.Positivity in
/-- Extension for the `positivity` tactic: the volume of a simplex is always positive. -/
@[positivity volume _]
meta def evalVolume : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@volume $V $P $i1 $i2 $i3 $i4 $n $s) =>
    assertInstancesCommute
    return .positive q(volume_pos $s)
  | _, _, _ => throwError "not Simplex.volume"

----

-- Move this
theorem EuclideanSpace.linearIndependent_single_one
    {ι : Type*} {𝕜 : Type*} [RCLike 𝕜] [DecidableEq ι] :
    LinearIndependent 𝕜 (fun (i : ι) ↦ EuclideanSpace.single i (1 : 𝕜)) := by
  suffices LinearIndependent 𝕜 ((WithLp.linearEquiv 2 𝕜 _).symm.toLinearMap ∘
      fun (i : ι) ↦ (Pi.single i (1 : 𝕜))) by
    simpa
  rw [LinearMap.linearIndependent_iff_of_injOn _ (by simp)]
  exact Pi.linearIndependent_single_one ι 𝕜

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A simplex in the `EuclideanSpace` where one vertex is at the origin, and other vertices are
at `EuclideanSpace.single j 1` for some `j`. -/
noncomputable def cornerSimplex (n : ℕ) (f : Fin (n + 1) ↪ Option ι) (h : none ∈ Set.range f) :
    Simplex ℝ (EuclideanSpace ℝ ι) n where
  points i := match f i with
    | none => 0
    | some j => EuclideanSpace.single j 1
  independent := by
    obtain ⟨k, hk⟩ := Set.mem_range.mp h
    rw [affineIndependent_iff_linearIndependent_vsub _ _ k]
    simp only [hk, vsub_eq_sub, sub_zero]
    suffices LinearIndependent ℝ (fun (i : ι) ↦ EuclideanSpace.single i (1 : ℝ)) by
      let f : {i // i ≠ k} → ι := fun i ↦ (f i.val).get (by
        obtain hi := i.prop
        contrapose! hi
        apply f.injective
        simpa [hk] using hi
      )
      have hf : Function.Injective f := by
        intro i j h
        ext1
        simpa [f, Option.get_inj] using h
      convert this.comp f hf with i
      simp_rw [f]
      grind
    apply EuclideanSpace.linearIndependent_single_one

theorem faceOpposite_cornerSimplex {n : ℕ} {f : Fin (n + 2) ↪ Option ι} (h : none ∈ Set.range f)
    {i : Fin (n + 2)} (hi : f i ≠ none) :
    (cornerSimplex (n + 1) f h).faceOpposite i =
    cornerSimplex n (i.succAboveEmb.trans f) (by
      rw [Set.mem_range] at ⊢ h
      obtain ⟨j, hj⟩ := h
      have : i ≠ j := by simpa [← f.injective.ne_iff, hj] using hi
      obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq this.symm
      use k
      simp [hk, hj]) := by
  ext1 i
  rw [faceOpposite_point_eq_point_succAbove]
  simp [cornerSimplex]

set_option backward.isDefEq.respectTransparency false in
theorem altitudeFoot_cornerSimplex {n : ℕ} {f : Fin (n + 2) ↪ Option ι} (h : none ∈ Set.range f)
    {i : Fin (n + 2)} (hi : f i ≠ none) :
    (cornerSimplex (n + 1) f h).altitudeFoot i = 0 := by
  obtain ⟨j, hj⟩ := Set.mem_range.mp h
  rw [altitudeFoot, orthogonalProjectionSpan, EuclideanGeometry.coe_orthogonalProjection_eq_iff_mem,
    faceOpposite_cornerSimplex h hi]
  constructor
  · apply mem_affineSpan
    rw [Set.mem_range]
    have : i ≠ j := by simpa [← f.injective.ne_iff, hj] using hi
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq this.symm
    use k
    simp [cornerSimplex, hk, hj]
  rw [Submodule.mem_orthogonal, direction_affineSpan]
  intro u hu
  rw [mem_vectorSpan_iff_eq_weightedVSub] at hu
  obtain ⟨t, w, hw0, rfl⟩ := hu
  rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _ hw0 0,
    Finset.weightedVSubOfPoint_apply, sum_inner]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  cases hk : f (i.succAbove k) with
  | none => simp [cornerSimplex, hk]
  | some k' =>
  cases hi : f i with
  | none => simp [cornerSimplex, hi]
  | some i' =>
  suffices i' ≠ k' by
    simp [cornerSimplex, hk, hi, EuclideanSpace.inner_single_right, this]
  apply_fun Option.some
  simp [← hi, ← hk]

theorem height_cornerSimplex {n : ℕ} {f : Fin (n + 2) ↪ Option ι} (h : none ∈ Set.range f)
    {i : Fin (n + 2)} (hi : f i ≠ none) :
    (cornerSimplex (n + 1) f h).height i = 1 := by
  obtain ⟨j, hj⟩ := Option.ne_none_iff_exists.mp hi
  rw [height, altitudeFoot_cornerSimplex h hi]
  simp [cornerSimplex, ← hj]

set_option backward.isDefEq.respectTransparency false in
theorem volume_cornerSimplex {n : ℕ} {f : Fin (n + 1) ↪ Option ι} (h : none ∈ Set.range f) :
    (cornerSimplex n f h).volume = (n.factorial : ℝ)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨i, hi⟩ := Function.Injective.exists_ne f.injective none
    rw [volume_eq _ i, height_cornerSimplex h hi, faceOpposite_cornerSimplex h hi, ih,
      mul_one, ← mul_inv, ← Nat.cast_mul, Nat.factorial_succ]

theorem volume_eq_det_of_euclideanSpace {n : ℕ}
    (s : Simplex ℝ (EuclideanSpace ℝ ι) n) (f : Option ι ≃ Fin (n + 1)) :
    s.volume = (n.factorial : ℝ)⁻¹ *
    |(Matrix.of fun j i ↦ (s.points (f (some i)) - s.points (f none)) j).det| := by
  have hn : Module.finrank ℝ (EuclideanSpace ℝ ι) = n := by
    simpa using Fintype.card_eq.mpr ⟨f⟩
  let t : Simplex ℝ (EuclideanSpace ℝ ι) n := cornerSimplex n f.symm (by simp)
  let ml : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι:=
    (Matrix.of fun (j i : ι) ↦ (s.points (f (some i)) - s.points (f none)).ofLp j).toEuclideanLin
  let m : EuclideanSpace ℝ ι →ᵃ[ℝ] EuclideanSpace ℝ ι :=
    (AffineIsometryEquiv.vaddConst ℝ (s.points (f none))).toAffineMap.comp ml.toAffineMap
  have hmmap (i : Fin (n + 1)) : s.points i = m (t.points i) := by
    cases h : f.symm i with
    | none =>
      obtain h' : i = f none := by simp [← h]
      simp [t, cornerSimplex, m, h']
    | some j =>
    obtain h' : i = f (some j) := by simp [← h]
    ext
    simp [t, cornerSimplex, m, ml, Matrix.col_eq_transpose, Matrix.transpose, h']
  have hm : Function.Bijective m := by
    obtain hs := s.independent
    obtain ht := t.independent
    rw [affineIndependent_iff_linearIndependent_vsub ℝ _ 0] at hs ht
    have hmmap' :
        (fun (i : { x // x ≠ 0 }) ↦ s.points i.val -ᵥ s.points 0) =
        m.linear ∘ (fun (i : { x // x ≠ 0 }) ↦ t.points i.val -ᵥ t.points 0) := by
      ext1 i
      simp_rw [Function.comp_apply, AffineMap.linearMap_vsub, hmmap]
    rw [hmmap'] at hs
    rw [← AffineMap.linear_bijective_iff]
    refine LinearMap.bijective_of_linearIndependent_of_span_eq_top ?_ hs ?_
    all_goals
    apply Submodule.eq_top_of_finrank_eq
    rw [hn]
    rw [finrank_span_eq_card (by assumption)]
    simp
  have hs : s = t.map m hm.injective := by
    ext1 i
    simp [ hmmap]
  conv_lhs => rw [hs]
  rw [volume_map_eq_det_mul hn]
  unfold t
  rw [volume_cornerSimplex, mul_comm]
  simp [m, ml]

theorem volume_eq_det {n : ℕ} {P : Type*} [MetricSpace P] [NormedAddTorsor (EuclideanSpace ℝ ι) P]
    (s : Simplex ℝ P n) (f : Option ι ≃ Fin (n + 1)) :
    s.volume = (n.factorial : ℝ)⁻¹ *
    |(Matrix.of fun j i ↦ (s.points (f (some i)) -ᵥ s.points (f none)) j).det| := by
  rw [← s.volume_map (AffineIsometryEquiv.vaddConst ℝ (s.points (f none))).symm.toAffineIsometry]
  rw [volume_eq_det_of_euclideanSpace _ f]
  simp

theorem volume_eq_det_of_orthonormalBasis {n : ℕ} (s : Simplex ℝ P n) (f : Option ι ≃ Fin (n + 1))
    (b : OrthonormalBasis ι ℝ V) :
    s.volume = (n.factorial : ℝ)⁻¹ *
    |(Matrix.of fun j i ↦ b.repr (s.points (f (some i)) -ᵥ s.points (f none)) j).det| := by
  let g : P ≃ᵃⁱ[ℝ] EuclideanSpace ℝ ι :=
    (AffineIsometryEquiv.vaddConst ℝ (s.points (f none))).symm.trans
    b.repr.toAffineIsometryEquiv
  rw [← s.volume_map g.toAffineIsometry]
  rw [volume_eq_det_of_euclideanSpace _ f]
  simp [g]

theorem volume_eq_gram {n : ℕ} (s : Simplex ℝ P n) (f : Option ι ≃ Fin (n + 1)) :
    s.volume = (n.factorial : ℝ)⁻¹ *
    √(Matrix.gram ℝ fun i ↦ s.points (f (some i)) -ᵥ s.points (f none)).det := by
  have hc : Fintype.card (Fin (n + 1)) = n + 1 := by simp
  have hrank : Fintype.card ι = Module.finrank ℝ (affineSpan ℝ (Set.range s.points)).direction := by
    rw [direction_affineSpan]
    rw [(affineIndependent_iff_finrank_vectorSpan_eq ℝ _ hc).mp s.independent]
    simpa using (Fintype.card_eq.mpr ⟨f⟩)
  rw [← s.volume_restrict _ le_rfl]
  let b : OrthonormalBasis ι ℝ (affineSpan ℝ (Set.range s.points)).direction :=
    (stdOrthonormalBasis ℝ _).reindex (Fintype.equivFinOfCardEq hrank).symm
  rw [volume_eq_det_of_orthonormalBasis _ f b]
  congr
  symm
  trans √(Matrix.gram ℝ fun i ↦ (⟨s.points (f (some i)) -ᵥ s.points (f none),
    AffineSubspace.vsub_mem_direction (mem_affineSpan _ (by simp)) (mem_affineSpan _ (by simp))⟩ :
    (affineSpan ℝ (Set.range s.points)).direction)).det
  · simp [Matrix.gram] -- extract?
  convert (Real.sqrt_sq_eq_abs _)
  rw [sq]
  nth_rw 2 [← Matrix.det_transpose]
  rw [Matrix.gram_eq_conjTranspose_mul b]
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [Matrix.det_mul]
  rfl

end Affine.Simplex

------------------------------------------------------------------------------------------------
-- experiment

variable {𝕜 U V : Type*} [RCLike 𝕜]
  [NormedAddCommGroup U] [InnerProductSpace 𝕜 U] [FiniteDimensional 𝕜 U]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

open Classical in
noncomputable def normDet (f : U →ₗ[𝕜] V) : ℝ :=
  if h : Nonempty (OrthonormalBasis (Fin (Module.finrank 𝕜 U)) 𝕜 f.range) then
    ‖(f.rangeRestrict.toMatrix (stdOrthonormalBasis 𝕜 U).toBasis h.some.toBasis).det‖
  else
    0

theorem normDet_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (f : U →ₗ[𝕜] V)
    (bu : OrthonormalBasis ι 𝕜 U) (bv : OrthonormalBasis ι 𝕜 f.range) :
    normDet f = ‖(f.rangeRestrict.toMatrix bu.toBasis bv.toBasis).det‖ := by
  have hrank : Module.finrank 𝕜 U = Module.finrank 𝕜 f.range := by
    rw [Module.finrank_eq_nat_card_basis bu.toBasis, Module.finrank_eq_nat_card_basis bv.toBasis]
  have h : Nonempty (OrthonormalBasis (Fin (Module.finrank 𝕜 U)) 𝕜 f.range) := by
    rw [hrank]
    exact ⟨stdOrthonormalBasis 𝕜 f.range⟩
  simp only [normDet, h, ↓reduceDIte]
  rw [← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix (stdOrthonormalBasis 𝕜 U).toBasis
    bu.toBasis h.some.toBasis bv.toBasis]
  have h1 : bu.toBasis.toMatrix (stdOrthonormalBasis 𝕜 U).toBasis *
      (stdOrthonormalBasis 𝕜 U).toBasis.toMatrix bu.toBasis = 1 :=
    Module.Basis.toMatrix_mul_toMatrix_flip _ _
  have h2 : (stdOrthonormalBasis 𝕜 U).toBasis.toMatrix bu.toBasis *
      bu.toBasis.toMatrix (stdOrthonormalBasis 𝕜 U).toBasis = 1 :=
    Module.Basis.toMatrix_mul_toMatrix_flip _ _
  rw [← Matrix.det_comm' h1 h2, ← Matrix.mul_assoc]
  rw [Matrix.det_mul, norm_mul]
  suffices ‖(bu.toBasis.toMatrix (stdOrthonormalBasis 𝕜 U).toBasis *
      h.some.toBasis.toMatrix ⇑bv.toBasis).det‖ = 1 by
    rw [this]
    simp
  apply CStarRing.norm_of_mem_unitary
  apply Matrix.det_of_mem_unitary
  rw [Matrix.mem_unitaryGroup_iff]
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul]
  rw [← Matrix.mul_assoc, Matrix.mul_assoc (bu.toBasis.toMatrix (stdOrthonormalBasis 𝕜 U).toBasis)]
  simp

@[simp]
theorem LinearMap.toMatrix_map_right {R : Type*} [CommSemiring R]
    {m : Type*} {n : Type*}
    [Fintype n] [Finite m] [DecidableEq n]
    {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}
    [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
    [Module R M₁] [Module R M₂] [Module R M₃]
    (v₁ : Module.Basis n R M₁) (v₂ : Module.Basis m R M₂) (f : M₁ →ₗ[R] M₃) (g : M₂ ≃ₗ[R] M₃) :
    f.toMatrix v₁ (v₂.map g) = (g.symm ∘ₗ f).toMatrix v₁ v₂ := by
  rfl

@[simp]
theorem LinearEquiv.ofTop_coe {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M]
    {module_M : Module R M} (p : Submodule R M) {h : p = ⊤} :
  (ofTop p h).toLinearMap = p.subtype := rfl

theorem normDet_eq_norm_det (f : U →ₗ[𝕜] U) : normDet f = ‖f.det‖ := by
  by_cases h : f.range = ⊤
  · let bv : OrthonormalBasis (Fin (Module.finrank 𝕜 U)) 𝕜 f.range :=
      (stdOrthonormalBasis 𝕜 U).map (LinearIsometryEquiv.ofTop U _ h).symm
    rw [normDet_eq f (stdOrthonormalBasis 𝕜 U) bv]
    simp [bv]
  · have hb : ¬ Nonempty (OrthonormalBasis (Fin (Module.finrank 𝕜 U)) 𝕜 f.range) := by
      contrapose! h
      obtain ⟨b⟩ := h
      apply Submodule.eq_top_of_finrank_eq
      conv_lhs => rw [Module.finrank_eq_nat_card_basis b.toBasis]
      conv_rhs => rw [Module.finrank_eq_nat_card_basis (stdOrthonormalBasis 𝕜 U).toBasis]
    suffices f.det = 0 by
      simp [this, normDet, hb]
    rw [LinearMap.det_eq_zero_iff_ker_ne_bot]
    exact LinearMap.ker_eq_bot_iff_range_eq_top.not.mpr h

theorem LinearIsometryEquiv.norm_det_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι] (f : U ≃ₗᵢ[𝕜] V)
    (bu : OrthonormalBasis ι 𝕜 U) (bv : OrthonormalBasis ι 𝕜 V) :
    ‖(f.toMatrix bu.toBasis bv.toBasis).det‖ = 1 := by
  have : FiniteDimensional 𝕜 V := Module.Basis.finiteDimensional_of_finite bv.toBasis
  apply CStarRing.norm_of_mem_unitary
  apply Matrix.det_of_mem_unitary
  rw [Matrix.mem_unitaryGroup_iff]
  rw [Matrix.star_eq_conjTranspose]
  rw [← LinearMap.toMatrix_adjoint]
  rw [← LinearMap.toMatrix_comp]
  simp [LinearIsometryEquiv.adjoint_toLinearMap_eq_symm, -OrthonormalBasis.coe_toBasis]

theorem LinearIsometry.normDet_eq_one (f : U →ₗᵢ[𝕜] V) : normDet f.toLinearMap = 1 := by
  have hrank : Module.finrank 𝕜 U = Module.finrank 𝕜 f.range :=
    f.equivRange.toLinearEquiv.finrank_eq
  let b := (stdOrthonormalBasis 𝕜 f.toLinearMap.range)
  rw [← hrank] at b
  rw [normDet_eq _ (stdOrthonormalBasis 𝕜 U) b]
  exact (f.equivRange).norm_det_eq_one (stdOrthonormalBasis 𝕜 U) b

theorem LinearIsometry.adjoint_comp_self [FiniteDimensional 𝕜 V] (f : U →ₗᵢ[𝕜] V) :
    f.adjoint ∘ₗ f.toLinearMap = LinearMap.id := by
  ext x
  suffices f.toLinearMap.adjoint (f x) = x by simpa
  apply ext_inner_left (𝕜 := 𝕜)
  intro y
  simp [LinearMap.adjoint_inner_right]

theorem normDet_sq [FiniteDimensional 𝕜 V] (f : U →ₗ[𝕜] V) :
    normDet f ^ 2 = (f.adjoint ∘ₗ f).det := by
  let bu := stdOrthonormalBasis 𝕜 U
  classical
  by_cases hrank : Module.finrank 𝕜 U = Module.finrank 𝕜 f.range
  · let b : OrthonormalBasis (Fin (Module.finrank 𝕜 U)) 𝕜 f.range :=
      (stdOrthonormalBasis 𝕜 f.range).reindex (by
      rw [← hrank, Module.finrank_eq_card_basis bu.toBasis])
    have hf : f = f.range.subtypeₗᵢ ∘ₗ f.rangeRestrict := rfl
    conv_rhs => rw [hf]
    rw [LinearMap.adjoint_comp, ← LinearMap.comp_assoc,
      LinearMap.comp_assoc _ _ (LinearMap.adjoint _)]
    suffices (f.range.subtypeₗᵢ : f.range →ₗ[𝕜] V).adjoint ∘ₗ
        (f.range.subtypeₗᵢ : f.range →ₗ[𝕜] V) = LinearMap.id by
      rw [this, LinearMap.comp_id]
      rw [← LinearMap.det_toMatrix bu.toBasis]
      rw [LinearMap.toMatrix_comp bu.toBasis b.toBasis bu.toBasis]
      rw [LinearMap.toMatrix_adjoint]
      simp [normDet_eq f bu b, RCLike.conj_mul]
    apply f.range.subtypeₗᵢ.adjoint_comp_self
  · have hb : ¬ Nonempty (OrthonormalBasis (Fin (Module.finrank 𝕜 U)) 𝕜 f.range) := by
      contrapose! hrank with h
      obtain ⟨bv⟩ := h
      rw [Module.finrank_eq_card_basis bu.toBasis, Module.finrank_eq_card_basis bv.toBasis]
    trans 0
    · simp [normDet, hb]
    symm
    rw [LinearMap.det_eq_zero_iff_ker_ne_bot, LinearMap.ker_adjoint_comp_self]
    contrapose! hrank
    exact (LinearMap.finrank_range_of_inj <| LinearMap.ker_eq_bot.mp hrank).symm
