/-
Copyright (c) 2026 Robert Joseph George. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Desargues's theorem

This file proves an affine version of Desargues's theorem.

If two triangles are in perspective from a point, and two pairs of corresponding sides are
parallel, then the third pair of corresponding sides are also parallel.

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

For context Desargues's theorem is entry `#87` on the Lean community's "100
theorems" pages:

* <https://leanprover-community.github.io/100.html>
* <https://leanprover-community.github.io/100-missing.html>
-/

@[expose] public section

open scoped Affine
open AffineSubspace

variable {k V P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V] [AffineSpace V P]

/-- If two triangles are in perspective from a point and two corresponding sides are parallel,
then the third pair of corresponding sides are parallel. -/
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
  -- If `B = S` or `C = S`, then `hASA'` would force one of the forbidden collinearities.
  have hB_ne_S : B ≠ S := by
    rintro rfl
    apply htriB
    convert hASA' using 1
    ext x
    simp [or_comm]
  have hC_ne_S : C ≠ S := by
    rintro rfl
    apply htriC
    convert hASA' using 1
    ext x
    simp [or_comm]
  -- If `A = S`, then `B'` lies on `AB`; since `AB ∥ A'B'`, the two lines coincide, forcing
  -- `A'` onto `AB` and contradicting the noncollinearity of `A, A', B`.
  have hA_ne_S : A ≠ S := by
    intro hAS
    have hcol_ABB' : Collinear k ({A, B, B'} : Set P) := by
      convert hBSB' using 1
      ext x
      simp [hAS, or_comm, or_left_comm]
    have hB'_mem_AB : B' ∈ line[k, A, B] := by
      exact Collinear.mem_affineSpan_of_mem_of_ne hcol_ABB' (by simp) (by simp) (by simp) hA_ne_B
    have hline_eq : line[k, A', B'] = line[k, A, B] := by
      refine (AffineSubspace.eq_iff_direction_eq_of_mem
        (right_mem_affineSpan_pair k A' B') hB'_mem_AB).2 ?_
      simpa using hAB.direction_eq.symm
    have hA'_mem_AB : A' ∈ line[k, A, B] := by
      simpa [hline_eq] using left_mem_affineSpan_pair k A' B'
    apply htriB
    simpa [Set.insert_comm] using
      collinear_insert_of_mem_affineSpan_pair (k := k) hA'_mem_AB
  -- Rewrite the collinearity hypotheses as line-membership statements.
  have hA'_mem_AS : A' ∈ line[k, A, S] :=
    Collinear.mem_affineSpan_of_mem_of_ne hASA' (by simp) (by simp) (by simp) hA_ne_S
  have hA'_mem_SA : A' ∈ line[k, S, A] := by
    simpa [AffineSubspace.affineSpan_pair_comm] using hA'_mem_AS
  have hB'_mem_BS : B' ∈ line[k, B, S] :=
    Collinear.mem_affineSpan_of_mem_of_ne hBSB' (by simp) (by simp) (by simp) hB_ne_S
  have hC'_mem_CS : C' ∈ line[k, C, S] :=
    Collinear.mem_affineSpan_of_mem_of_ne hCSC' (by simp) (by simp) (by simp) hC_ne_S
  -- The points `B` and `C` do not lie on the axis `AS`; otherwise we would again contradict the
  -- noncollinearity assumptions.
  have hB_not_AS : B ∉ line[k, A, S] := by
    intro hB_mem_AS
    apply htriB
    simpa [Set.insert_comm] using
      collinear_triple_of_mem_affineSpan_pair (k := k) hA'_mem_AS
        (left_mem_affineSpan_pair k A S) hB_mem_AS
  have hC_not_AS : C ∉ line[k, A, S] := by
    intro hC_mem_AS
    apply htriC
    simpa [Set.insert_comm] using
      collinear_triple_of_mem_affineSpan_pair (k := k) hA'_mem_AS
        (left_mem_affineSpan_pair k A S) hC_mem_AS
  -- Apply the affine parallel-comparison lemma to the triples `(A, B, S)` / `(A', B', S)` and
  -- `(A, C, S)` / `(A', C', S)`.
  obtain ⟨rB, hrB0, hBA, hSB, hSA⟩ :=
    exists_eq_smul_of_parallel (k := k) (p₁ := A) (p₂ := B) (p₃ := S) (p₄ := A') (p₅ := B')
      (p₆ := S) hB_not_AS hAB
      (AffineSubspace.direction_le (affineSpan_pair_le_of_left_mem hB'_mem_BS))
      (AffineSubspace.direction_le (affineSpan_pair_le_of_right_mem hA'_mem_SA))
  obtain ⟨rC, hrC0, hCA, hSC, hSA'⟩ :=
    exists_eq_smul_of_parallel (k := k) (p₁ := A) (p₂ := C) (p₃ := S) (p₄ := A') (p₅ := C')
      (p₆ := S) hC_not_AS hAC
      (AffineSubspace.direction_le (affineSpan_pair_le_of_left_mem hC'_mem_CS))
      (AffineSubspace.direction_le (affineSpan_pair_le_of_right_mem hA'_mem_SA))
  -- Both applications compare the same segment `SA'` to `SA`, so they must use the same scalar.
  have hrBC : rB = rC := by
    have hEq : rB • (A -ᵥ S) = rC • (A -ᵥ S) := by
      calc
        rB • (A -ᵥ S) = A' -ᵥ S := by simpa using hSA.symm
        _ = rC • (A -ᵥ S) := by simpa using hSA'
    exact smul_left_injective k (vsub_ne_zero.mpr hA_ne_S) hEq
  -- Therefore the segment `B'C'` is obtained from `BC` by the same nonzero scalar, which is
  -- exactly the affine meaning of parallelism.
  have hCB : C' -ᵥ B' = rB • (C -ᵥ B) := by
    calc
      C' -ᵥ B' = (C' -ᵥ S) + (S -ᵥ B') := by rw [vsub_add_vsub_cancel]
      _ = -(S -ᵥ C') + rB • (S -ᵥ B) := by rw [neg_vsub_eq_vsub_rev, hSB]
      _ = -(rB • (S -ᵥ C)) + rB • (S -ᵥ B) := by rw [hrBC, hSC]
      _ = rB • (C -ᵥ S) + rB • (S -ᵥ B) := by rw [← smul_neg, neg_vsub_eq_vsub_rev]
      _ = rB • ((C -ᵥ S) + (S -ᵥ B)) := by rw [smul_add]
      _ = rB • (C -ᵥ B) := by rw [vsub_add_vsub_cancel]
  rw [AffineSubspace.affineSpan_pair_parallel_iff_exists_unit_smul']
  refine ⟨Units.mk0 rB hrB0, ?_⟩
  simpa [Units.smul_def] using hCB.symm
