/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.InnerProductSpace.Orientation
public import Mathlib.Geometry.Euclidean.Altitude

/-!
# Corner simplex

This file introduces `Affine.Simplex.cornerSimplex` which is useful for volume calculation.

-/

@[expose] public section

namespace Affine.Simplex

open EuclideanGeometry AffineMap EuclideanSpace Module Submodule

/-- The corner simplex in a standard Euclidean space, where the 0-th vertex is at the origin, and
the rest are at the unit vector in each direction. All but one of the altitudes of this simplex has
unit length. -/
@[simps]
noncomputable def cornerSimplex (n : ℕ) : Simplex ℝ (EuclideanSpace ℝ (Fin n)) n where
  points i := if h : i = 0 then 0 else single (Fin.pred i h) 1
  independent := by
    rw [affineIndependent_iff_linearIndependent_vsub ℝ _ 0]
    convert_to LinearIndependent ℝ ((fun i : Fin n ↦ single i (1 : ℝ)) ∘
      (fun i : { x : Fin (n + 1) // x ≠ 0 } ↦ Fin.pred i.val i.prop))
    · grind [vsub_eq_sub]
    exact (PiLp.linearIndependent_single_one 2 ℝ).comp _ (fun i j ↦ by grind)

/-- Given an embedding from the `m`-dimensional Euclidean space into
the `n`-deminsional one represented by `f`, this returns the index set to use in
`Affine.Simplex.face` for the induced mapping of `Affine.Simplex.cornerSimplex`. -/
def cornerSimplexFacePoints {m n : ℕ} (f : Fin m ↪o Fin n) : Finset (Fin (n + 1)) :=
  insert 0 ((Finset.univ.map f.toEmbedding).map (Fin.succEmb n))

@[simp]
theorem card_cornerSimplexFacePoints {m n : ℕ} (f : Fin m ↪o Fin n) :
    (cornerSimplexFacePoints f).card = m + 1 := by
  simp [cornerSimplexFacePoints]

@[simp]
theorem cornerSimplexFacePoints_succAboveOrderEmb {n : ℕ} (i : Fin (n + 1)) :
    cornerSimplexFacePoints i.succAboveOrderEmb = {i.succ}ᶜ := by
  ext j
  cases j using Fin.cases
  · simp [cornerSimplexFacePoints, (Fin.succ_ne_zero _).symm]
  · simp [cornerSimplexFacePoints]

@[simp]
theorem orderEmbOfFin_cornerSimplexFacePoints {m n : ℕ} (f : Fin m ↪o Fin n) :
    ⇑((cornerSimplexFacePoints f).orderEmbOfFin (card_cornerSimplexFacePoints f)) =
      Fin.cons 0 fun i ↦ (f i).succ := by
  refine (Finset.orderEmbOfFin_unique _ ?_ ?_).symm
  · apply Fin.cases <;> simp [cornerSimplexFacePoints]
  · simpa [Fin.strictMono_cons] using! Fin.strictMono_succ.comp f.strictMono

/-- A face of an `Affine.Simplex.cornerSimplex` that includes the origin is another
`Affine.Simplex.cornerSimplex` mapped from lower dimensions by an isometry. -/
theorem face_cornerSimplex {m n : ℕ} (f : Fin m ↪o Fin n) :
    let g := (LinearIsometry.piLpExtendByZero 2 ℝ ℝ f.toEmbedding).toAffineIsometry
    (cornerSimplex n).face (card_cornerSimplexFacePoints f) =
      (cornerSimplex m).map g.toAffineMap g.injective := by
  ext i : 1
  cases i using Fin.cases <;> simp [face_points]

theorem faceOpposite_cornerSimplex {n : ℕ} (i : Fin (n + 1)) :
    let g := (LinearIsometry.piLpExtendByZero 2 ℝ ℝ i.succAboveEmb).toAffineIsometry
    (cornerSimplex (n + 1)).faceOpposite i.succ =
      (cornerSimplex n).map g.toAffineMap g.injective := by
  simp only [faceOpposite, Nat.add_one_sub_one, LinearIsometry.toAffineIsometry_toAffineMap]
  convert! face_cornerSimplex i.succAboveOrderEmb
  simp

@[simp]
theorem altitudeFoot_cornerSimplex {n : ℕ} [NeZero n] {i : Fin (n + 1)} (hi : i ≠ 0) :
    (cornerSimplex n).altitudeFoot i = 0 := by
  rw [altitudeFoot, orthogonalProjectionSpan, coe_orthogonalProjection_eq_iff_mem]
  refine ⟨mem_affineSpan _ (by simp [hi.symm]), (mem_orthogonal _ _).mpr fun v hv ↦ ?_⟩
  rw [direction_affineSpan, vectorSpan_eq_span_vsub_set_right ℝ (p := 0) (by simp [hi.symm])] at hv
  induction hv using span_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ : ∃ j, j ≠ i ∧ (if h : j = 0 then 0 else single (j.pred h) 1) = x := by
      simpa using hx
    by_cases hj0 : j = 0
    · simp [hj0]
    · simp [hj0, hj, inner_single_left, hi]
  | zero => simp
  | add x y hx hy ihx ihy => rw [inner_add_left, ihx, ihy, zero_add]
  | smul a x hx ih => rw [inner_smul_left, ih, mul_zero]

@[simp]
theorem height_cornerSimplex {n : ℕ} [NeZero n] {i : Fin (n + 1)} (hi : i ≠ 0) :
    (cornerSimplex n).height i = 1 := by
  simp [height, hi]

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- The `AffineMap` from `Affine.Simplex.cornerSimplex` to an arbitrary `Affine.Simplex`. -/
@[simps!]
noncomputable def cornerMap {n : ℕ} (s : Simplex ℝ P n) :
    EuclideanSpace ℝ (Fin n) →ᵃ[ℝ] P :=
  ((basisFun (Fin n) ℝ).toBasis.constr ℝ fun i ↦ s.points i.succ -ᵥ s.points 0).toAffineMap +ᵥ
    AffineMap.const ℝ (EuclideanSpace ℝ (Fin n)) (s.points 0)

theorem cornerMap_injective {n : ℕ} (s : Simplex ℝ P n) :
    Function.Injective s.cornerMap := by
  intro x y h
  simp_rw [cornerMap, vadd_apply, const_apply, vadd_right_cancel_iff] at h
  refine (Basis.injective_constr_of_linearIndependent _ ?_ (R₂ := ℝ)) h
  convert ((affineIndependent_iff_linearIndependent_vsub ℝ _ 0).mp s.independent).comp
    (fun i : Fin n ↦ ⟨i.succ, by simp⟩) (fun i j ↦ by simp)
  simp

@[simp]
theorem map_cornerSimplex_cornerMap {n : ℕ} (s : Simplex ℝ P n) :
    (cornerSimplex n).map s.cornerMap (cornerMap_injective s) = s := by
  ext i
  by_cases hi : i = 0 <;> simp [hi]

theorem normDet_cornerMap_linear {n : ℕ} [FiniteDimensional ℝ V] [Fact (finrank ℝ V = n)]
    (s : Simplex ℝ P n) (o : Orientation ℝ V (Fin n)) :
    s.cornerMap.linear.normDet = |o.volumeForm fun i ↦ s.cornerMap.linear (single i 1)| := by
  let b : OrthonormalBasis (Fin n) ℝ V :=
    (stdOrthonormalBasis ℝ V).reindex (finCongr ‹Fact (finrank ℝ V = n)›.out)
  rw [s.cornerMap.linear.normDet_eq_norm_det_toMatrix (basisFun (Fin n) ℝ) b, Real.norm_eq_abs,
    o.volumeForm_robust' b]
  rfl

end Affine.Simplex
