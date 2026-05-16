/-
Copyright (c) 2026 Robert Joseph George. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Desargues's theorem (parallel form)

This file proves a *parallel* (affine) form of Desargues's theorem.

If two triangles are in perspective from a point, and two pairs of corresponding sides are
parallel, then the third pair of corresponding sides are also parallel.

This should be seen as a special case of the usual projective statement: for two triangles in
perspective from a point, the three intersection points of corresponding sides are collinear.
Here we assume two pairs of corresponding sides are parallel (so their intersection points are
"at infinity"), and deduce parallelism of the remaining pair of sides.

More precisely, we consider points `A A' B B' C C' S` in an affine space over a division ring.
The hypotheses say that the pairs `(A, A')`, `(B, B')`, and `(C, C')` are each aligned with the
point `S`, and that the corresponding sides `AB` and `A'B'`, as well as `AC` and `A'C'`, are
parallel. Under the nondegeneracy assumptions that `A, A', B` and `A, A', C` are not collinear,
the conclusion is that `BC` is parallel to `B'C'`.

The theorem is stated synthetically in affine geometry, while the proof uses the affine-parallel
lemma `exists_eq_smul_of_parallel` to compare the side vectors of two triples of points with
corresponding parallel sides. This is close in spirit to the Rocq100 formalization of the same
classical theorem, but adapted to the affine geometry content in mathlib.

## References

For mathematical background on Desargues's theorem, see for example:

* <https://en.wikipedia.org/wiki/Desargues%27s_theorem>
* <https://www.britannica.com/science/Desarguess-theorem>
* <https://planetmath.org/desarguestheorem>
-/

@[expose] public section

open scoped Affine
open AffineSubspace

variable {k V P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V] [AffineSpace V P]

/-- The parallel form of Desargues's theorem: if two triangles are in perspective from a point and
two corresponding sides are parallel, then the third pair of corresponding sides are parallel.

The noncollinearity hypotheses exclude degenerate cases where `B` or `C` lies on the perspective
line through `A`, `S`, and `A'`; in such cases the corresponding parallel-side assumption is just
a comparison of two lines on the same perspective line, so it does not force the same scaling ratio
as the nondegenerate side. -/
theorem parallel_third_side_of_perspective {A A' B B' C C' S : P}
    (hASA' : Collinear k ({A, S, A'} : Set P))
    (hBSB' : Collinear k ({B, S, B'} : Set P))
    (hCSC' : Collinear k ({C, S, C'} : Set P))
    (hAB : line[k, A, B] ∥ line[k, A', B'])
    (hAC : line[k, A, C] ∥ line[k, A', C'])
    (htriB : ¬ Collinear k ({A, A', B} : Set P))
    (htriC : ¬ Collinear k ({A, A', C} : Set P)) :
    line[k, B, C] ∥ line[k, B', C'] := by
  -- The noncollinearity assumptions immediately give the point inequalities we need.
  have hA_ne_B : A ≠ B := ne₁₃_of_not_collinear (k := k) (p₁ := A) (p₂ := A') (p₃ := B) htriB
  -- If one of the remaining vertices were `S`, then `hASA'` would force one of the forbidden
  -- collinearities.
  have ne_S_of_not_collinear {X : P} (htri : ¬ Collinear k ({A, A', X} : Set P)) : X ≠ S := by
    rintro rfl
    exact htri (hASA'.subset (by grind))
  have hB_ne_S : B ≠ S := ne_S_of_not_collinear htriB
  have hC_ne_S : C ≠ S := ne_S_of_not_collinear htriC
  -- If `A = S`, then `B'` lies on `AB`; since `AB ∥ A'B'`, the two lines coincide, forcing
  -- `A'` onto `AB` and contradicting the noncollinearity of `A, A', B`.
  have hA_ne_S : A ≠ S := by
    intro hAS
    have hcol_ABB' : Collinear k ({A, B, B'} : Set P) := by
      exact hBSB'.subset (by grind)
    have hB'_mem_AB : B' ∈ line[k, A, B] :=
      hcol_ABB'.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hA_ne_B
    have hline_eq : line[k, A', B'] = line[k, A, B] := by
      refine (AffineSubspace.eq_iff_direction_eq_of_mem
        (right_mem_affineSpan_pair k A' B') hB'_mem_AB).2 ?_
      simpa using hAB.direction_eq.symm
    have hA'_mem_AB : A' ∈ line[k, A, B] := by
      simpa [hline_eq] using left_mem_affineSpan_pair k A' B'
    exact htriB ((collinear_insert_of_mem_affineSpan_pair (k := k) hA'_mem_AB).subset
      (by grind))
  -- Rewrite the collinearity hypotheses as line-membership statements.
  have hA'_mem_AS : A' ∈ line[k, A, S] :=
    Collinear.mem_affineSpan_of_mem_of_ne hASA' (by simp) (by simp) (by simp) hA_ne_S
  have hA'_mem_SA : A' ∈ line[k, S, A] := by
    simpa [AffineSubspace.affineSpan_pair_comm] using hA'_mem_AS
  have hB'_mem_BS : B' ∈ line[k, B, S] :=
    Collinear.mem_affineSpan_of_mem_of_ne hBSB' (by simp) (by simp) (by simp) hB_ne_S
  have hC'_mem_CS : C' ∈ line[k, C, S] :=
    Collinear.mem_affineSpan_of_mem_of_ne hCSC' (by simp) (by simp) (by simp) hC_ne_S
  -- The points `B` and `C` do not lie on the axis `AS`; otherwise we would again contradict
  -- noncollinearity.
  have not_mem_AS_of_not_collinear {X : P} (htri : ¬ Collinear k ({A, A', X} : Set P)) :
      X ∉ line[k, A, S] := by
    intro hX_mem_AS
    exact htri ((collinear_triple_of_mem_affineSpan_pair (k := k) hA'_mem_AS
      (left_mem_affineSpan_pair k A S) hX_mem_AS).subset (by grind))
  have hB_not_AS : B ∉ line[k, A, S] := not_mem_AS_of_not_collinear htriB
  have hC_not_AS : C ∉ line[k, A, S] := not_mem_AS_of_not_collinear htriC
  -- Apply the affine parallel-comparison lemma to the triples `(A, B, S)` / `(A', B', S)` and
  -- `(A, C, S)` / `(A', C', S)`.
  obtain ⟨rB, hrB0, _, hSB, hSA⟩ :=
    exists_eq_smul_of_parallel (k := k) (p₁ := A) (p₂ := B) (p₃ := S) (p₄ := A') (p₅ := B')
      (p₆ := S) hB_not_AS hAB
      (AffineSubspace.direction_le (affineSpan_pair_le_of_left_mem hB'_mem_BS))
      (AffineSubspace.direction_le (affineSpan_pair_le_of_right_mem hA'_mem_SA))
  obtain ⟨rC, _, _, hSC, hSA'⟩ :=
    exists_eq_smul_of_parallel (k := k) (p₁ := A) (p₂ := C) (p₃ := S) (p₄ := A') (p₅ := C')
      (p₆ := S) hC_not_AS hAC
      (AffineSubspace.direction_le (affineSpan_pair_le_of_left_mem hC'_mem_CS))
      (AffineSubspace.direction_le (affineSpan_pair_le_of_right_mem hA'_mem_SA))
  -- Both applications compare the same segment `SA'` to `SA`, so they must use the same scalar.
  have hrBC : rB = rC := by
    apply smul_left_injective k (vsub_ne_zero.mpr hA_ne_S)
    change rB • (A -ᵥ S) = rC • (A -ᵥ S)
    rw [hSA.symm, hSA']
  -- Therefore the segment `B'C'` is obtained from `BC` by the same nonzero scalar, which is
  -- exactly the affine meaning of parallelism.
  have hCB : C' -ᵥ B' = rB • (C -ᵥ B) := by
    rw [← vsub_add_vsub_cancel C' S B', ← neg_vsub_eq_vsub_rev S C', hSB, hrBC, hSC,
      ← smul_neg, neg_vsub_eq_vsub_rev, ← smul_add, vsub_add_vsub_cancel]
  rw [AffineSubspace.affineSpan_pair_parallel_iff_exists_unit_smul']
  exact ⟨Units.mk0 rB hrB0, by simpa [Units.smul_def] using hCB.symm⟩
