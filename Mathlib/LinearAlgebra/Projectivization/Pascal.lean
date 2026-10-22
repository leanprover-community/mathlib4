/-
Copyright (c) 2026 Ari Hallak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ari Hallak
-/
module

public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.Projectivization.Collinear
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.QuadraticForm.Basis
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormDet

/-!
Pascal's hexagon theorem

If six points `a, b, c, d, e, f` lie on a conic, then the intersections of the opposite sides
`ab` and `de`, `bc` and `ef`, and `cd` and `fa` are collinear.

We use homogeneous coordinates in `K³`. A conic is given by the zero set of a nonzero quadratic
form. The cross product of two point representatives gives the coefficients of their joining
line; the cross product of two line representatives gives their intersection. The nonzero
hypotheses in `Projectivization.pascal` ensure these intersections represent projective points.

The proof uses the quadratic Veronese map
`(x, y, z) ↦ (x², y², z², xy, xz, yz)`. The determinant of the three intersection representatives
equals the determinant of the six Veronese images. The coefficients of the conic give a
nonzero vector in the kernel of the latter matrix.

Main results

Projectivization.pascal_det: the homogeneous determinant form of Pascal's theorem.
Projectivization.pascal: Pascal's theorem using projective collinearity.

The results hold over any field, including characteristic two, and allow degenerate conics.

References

https://www.cs.ru.nl/~freek/100/#28
-/

public section

open Matrix

namespace Projectivization

section Identity

variable {K : Type*} [CommRing K]

private def veronese (v : Fin 3 → K) : Fin 6 → K :=
  ![v 0 ^ 2, v 1 ^ 2, v 2 ^ 2, v 0 * v 1, v 0 * v 2, v 1 * v 2]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 4000000 in
-- Expanding the six-by-six determinant and normalizing its polynomial requires extra heartbeats.
set_option maxRecDepth 10000 in
private lemma pascal_identity (a b c d e f : Fin 3 → K) :
    det ![(a ⨯₃ b) ⨯₃ (d ⨯₃ e), (b ⨯₃ c) ⨯₃ (e ⨯₃ f),
      (c ⨯₃ d) ⨯₃ (f ⨯₃ a)] =
      det ![veronese a, veronese b, veronese c, veronese d, veronese e, veronese f] := by
  change _ = det !![a 0 ^ 2, a 1 ^ 2, a 2 ^ 2, a 0 * a 1, a 0 * a 2, a 1 * a 2;
      b 0 ^ 2, b 1 ^ 2, b 2 ^ 2, b 0 * b 1, b 0 * b 2, b 1 * b 2;
      c 0 ^ 2, c 1 ^ 2, c 2 ^ 2, c 0 * c 1, c 0 * c 2, c 1 * c 2;
      d 0 ^ 2, d 1 ^ 2, d 2 ^ 2, d 0 * d 1, d 0 * d 2, d 1 * d 2;
      e 0 ^ 2, e 1 ^ 2, e 2 ^ 2, e 0 * e 1, e 0 * e 2, e 1 * e 2;
      f 0 ^ 2, f 1 ^ 2, f 2 ^ 2, f 0 * f 1, f 0 * f 2, f 1 * f 2]
  conv_rhs => simp only [norm_det]
  simp only [det_fin_three, cross_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one]
  ring

end Identity

variable {K : Type*} [Field K]

private lemma exists_coefficients (Q : QuadraticForm K (Fin 3 → K)) :
    ∃ q : Fin 6 → K, ∀ v, Q v = veronese v ⬝ᵥ q := by
  obtain ⟨B, rfl⟩ := LinearMap.BilinMap.toQuadraticMap_surjective Q
  let e0 : Fin 3 → K := ![1, 0, 0]
  let e1 : Fin 3 → K := ![0, 1, 0]
  let e2 : Fin 3 → K := ![0, 0, 1]
  refine ⟨![B e0 e0, B e1 e1, B e2 e2,
    B e0 e1 + B e1 e0, B e0 e2 + B e2 e0, B e1 e2 + B e2 e1], fun v ↦ ?_⟩
  change B v v = _
  have hv : v = v 0 • e0 + v 1 • e1 + v 2 • e2 := by
    ext i
    fin_cases i <;> simp [e0, e1, e2]
  conv_lhs => rw [hv]
  simp [veronese, dotProduct, Fin.sum_univ_succ, map_add, map_smul,
    LinearMap.add_apply, LinearMap.smul_apply]
  ring

set_option backward.isDefEq.respectTransparency false in
private lemma collinear_of_det_eq_zero (u v w : Fin 3 → K) (hu : u ≠ 0) (hv : v ≠ 0)
    (hw : w ≠ 0) (h : det ![u, v, w] = 0) :
    Projectivization.IsCollinear
      {Projectivization.mk K u hu, Projectivization.mk K v hv, Projectivization.mk K w hw} := by
  classical
  let S := Submodule.span K (Set.range ![u, v, w])
  have hind : ¬ LinearIndependent K ![u, v, w] := by
    intro hi
    have hi' : LinearIndependent K (Matrix.row ![u, v, w]) := hi
    have hunit := Matrix.linearIndependent_row_iff_isUnit.mp hi'
    exact (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hunit)) h
  have hdim : Module.finrank K S ≤ 2 := by
    have hl := finrank_range_le_card (R := K) ![u, v, w]
    have hn := mt (linearIndependent_iff_card_eq_finrank_span (R := K)).mpr hind
    simp only [Fintype.card_fin] at hl hn
    change Module.finrank K S ≤ 3 at hl
    change ¬ 3 = Module.finrank K S at hn
    omega
  refine ⟨S.projectivization, ?_, ?_, ?_⟩
  · rw [Projectivization.Subspace.submodule.apply_symm_apply]
    infer_instance
  · change Module.finrank K (Projectivization.Subspace.submodule
      (Projectivization.Subspace.submodule.symm S)) ≤ 2
    rw [OrderIso.apply_symm_apply]
    exact hdim
  · intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · change u ∈ S
      exact Submodule.mem_span_of_mem ⟨0, rfl⟩
    · change v ∈ S
      exact Submodule.mem_span_of_mem ⟨1, rfl⟩
    · change w ∈ S
      exact Submodule.mem_span_of_mem ⟨2, rfl⟩

/-- **Pascal's hexagon theorem**, in homogeneous determinant form. -/
theorem pascal_det
    (Q : QuadraticForm K (Fin 3 → K)) (hQ : Q ≠ 0)
    (a b c d e f : Fin 3 → K)
    (ha : Q a = 0) (hb : Q b = 0) (hc : Q c = 0)
    (hd : Q d = 0) (he : Q e = 0) (hf : Q f = 0) :
    det ![(a ⨯₃ b) ⨯₃ (d ⨯₃ e), (b ⨯₃ c) ⨯₃ (e ⨯₃ f),
      (c ⨯₃ d) ⨯₃ (f ⨯₃ a)] = 0 := by
  obtain ⟨q, hq⟩ := exists_coefficients Q
  have hq0 : q ≠ 0 := by
    intro h
    apply hQ
    ext v
    simpa [h] using hq v
  rw [pascal_identity]
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨q, hq0, ?_⟩
  ext i
  fin_cases i <;> simp [Matrix.mulVec, ← hq, ha, hb, hc, hd, he, hf]

/-- **Pascal's hexagon theorem**: the intersections of opposite sides of a hexagon lying on
one conic are collinear, whenever the intersection representatives are nonzero. -/
theorem pascal
    (Q : QuadraticForm K (Fin 3 → K)) (hQ : Q ≠ 0)
    (a b c d e f : Fin 3 → K)
    (ha : Q a = 0) (hb : Q b = 0) (hc : Q c = 0)
    (hd : Q d = 0) (he : Q e = 0) (hf : Q f = 0)
    (hx : (a ⨯₃ b) ⨯₃ (d ⨯₃ e) ≠ 0)
    (hy : (b ⨯₃ c) ⨯₃ (e ⨯₃ f) ≠ 0)
    (hz : (c ⨯₃ d) ⨯₃ (f ⨯₃ a) ≠ 0) :
    Projectivization.IsCollinear
      {Projectivization.mk K _ hx, Projectivization.mk K _ hy, Projectivization.mk K _ hz} := by
  exact collinear_of_det_eq_zero _ _ _ hx hy hz
    (pascal_det Q hQ a b c d e f ha hb hc hd he hf)

end Projectivization
