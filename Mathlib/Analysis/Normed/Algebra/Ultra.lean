/-
Copyright (c) 2024 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
module

public import Mathlib.Analysis.Normed.Field.Ultra
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Normed algebra preserves ultrametricity

This file contains the proof that a normed division ring over an ultrametric field is ultrametric.
-/

@[expose] public section

variable {K L : Type*} [NormedField K]

variable (L) in
/--
The other direction of `IsUltrametricDist.of_normedAlgebra`.
Let `K` be a normed field. If a seminormed ring `L` is a normed `K`-algebra, and `‖1‖ = 1` in `L`,
then `K` is ultrametric (i.e. the norm on `L` is nonarchimedean) if `F` is.
This can be further generalized to the case where `‖1‖ ≠ 0` in `L`.
-/
theorem IsUltrametricDist.of_normedAlgebra' [SeminormedRing L] [NormOneClass L] [NormedAlgebra K L]
    [h : IsUltrametricDist L] : IsUltrametricDist K :=
  ⟨fun x y z => by
    simpa using h.dist_triangle_max (algebraMap K L x) (algebraMap K L y) (algebraMap K L z)⟩

variable (K) in
/--
Let `K` be a normed field. If a normed division ring `L` is a normed `K`-algebra,
then `L` is ultrametric (i.e. the norm on `L` is nonarchimedean) if `K` is.
-/
theorem IsUltrametricDist.of_normedAlgebra [NormedDivisionRing L] [NormedAlgebra K L]
    [h : IsUltrametricDist K] : IsUltrametricDist L := by
  rw [isUltrametricDist_iff_forall_norm_natCast_le_one] at h ⊢
  exact fun n => (algebraMap.coe_natCast (R := K) (A := L) n) ▸ norm_algebraMap' L (n : K) ▸ h n

variable (K L) in
/--
Let `K` be a normed field. If a normed division ring `L` is a normed `K`-algebra,
then `L` is ultrametric (i.e. the norm on `L` is nonarchimedean) if and only if `K` is.
-/
theorem IsUltrametricDist.normedAlgebra_iff [NormedDivisionRing L] [NormedAlgebra K L] :
    IsUltrametricDist L ↔ IsUltrametricDist K :=
  ⟨fun _ => IsUltrametricDist.of_normedAlgebra' L, fun _ => IsUltrametricDist.of_normedAlgebra K⟩
