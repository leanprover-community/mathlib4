/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.Graded
public import Mathlib.RingTheory.GradedAlgebra.Connected

/-!
# Graded bialgebras

Structural lemmas about graded connected bialgebras.

## Main declarations

* `GradedAlgebra.IsConnected.zeroLEquiv`: for a connected graded bialgebra, the counit restricts
  to an isomorphism `𝒜 0 ≃ₗ[R] R`.
* `Bialgebra.comul_sub_tmul_one_mem_lower`: for `x ∈ 𝒜 n`, `Δ(x) - x ⊗ 1` has left tensor
  factors of degree strictly less than `n`.

## References

* [Grinberg, D. and Reiner, V., *Hopf Algebras in Combinatorics*][grinberg-reiner-2020],
  Exercise 1.3.20(h) and the proof of Proposition 1.4.16.
-/

public section

/-! ### The degree-zero part of a connected graded bialgebra -/

namespace GradedAlgebra.IsConnected

variable {R A : Type*} [CommSemiring R] [Semiring A] [Bialgebra R A]
variable {ι : Type*} [Zero ι] (𝒜 : ι → Submodule R A) [GradedAlgebra.IsConnected 𝒜]

open Coalgebra

/-- Every element of the degree-zero part equals its counit times the unit. -/
theorem eq_counit_smul_one {a : A} (ha : a ∈ 𝒜 0) : a = counit (R := R) a • 1 := by
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp (eq_span_one (𝒜 := 𝒜) ▸ ha)
  simp

/-- The degree-zero submodule of a connected graded bialgebra is canonically isomorphic to
the base ring via the counit. -/
@[expose] noncomputable def zeroLEquiv : 𝒜 0 ≃ₗ[R] R where
  toFun a := counit (a : A)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  invFun r := ⟨r • 1, eq_span_one (𝒜 := 𝒜) ▸ Submodule.smul_mem _ r (Submodule.subset_span rfl)⟩
  left_inv := fun ⟨a, ha⟩ => Subtype.ext (eq_counit_smul_one 𝒜 ha).symm
  right_inv _ := by simp

@[simp]
theorem zeroLEquiv_apply (a : 𝒜 0) : zeroLEquiv 𝒜 a = counit (a : A) := rfl

@[simp]
theorem zeroLEquiv_symm_apply_coe (r : R) : ((zeroLEquiv 𝒜).symm r : A) = r • 1 := rfl

end GradedAlgebra.IsConnected

namespace Bialgebra

variable {R A : Type*} [CommSemiring R] [Ring A] [Bialgebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [GradedCoalgebra 𝒜]

open Coalgebra TensorProduct

/-- The counit factors through the degree-zero projection. -/
theorem counit_eq_counit_proj_zero (a : A) :
    counit (R := R) a = counit (GradedAlgebra.proj 𝒜 0 a) := by
  classical
  rw [GradedAlgebra.proj_apply]
  conv_lhs => rw [← DirectSum.sum_support_decompose 𝒜 a, map_sum]
  exact Finset.sum_eq_single 0
    (fun i _ hi =>
      GradedCoalgebra.counit_eq_zero_of_degree_ne_zero hi (DirectSum.decompose 𝒜 a i).2)
    (fun h => by simp [DFinsupp.notMem_support_iff.mp h])

variable [GradedAlgebra.IsConnected 𝒜]

/-- Under connectedness, the degree-zero projection equals `algebraMap ∘ counit`. -/
theorem proj_zero_eq_algebraMap_comp_counit :
    (GradedAlgebra.proj 𝒜 0 : A →ₗ[R] A) = Algebra.linearMap R A ∘ₗ counit := by
  ext x
  have hmem : GradedAlgebra.proj 𝒜 0 x ∈ 𝒜 0 := by
    rw [GradedAlgebra.proj_apply]; exact SetLike.coe_mem _
  rw [LinearMap.comp_apply, Algebra.linearMap_apply,
    GradedAlgebra.IsConnected.eq_counit_smul_one 𝒜 hmem,
    ← counit_eq_counit_proj_zero, ← Algebra.algebraMap_eq_smul_one]

/-- Applying `id ⊗ q_0` to `Δ(x)` gives `x ⊗ 1`, where `q_0 = GradedAlgebra.proj 𝒜 0`. -/
@[simp]
theorem lTensor_proj_zero_comul (x : A) :
    (LinearMap.lTensor A (GradedAlgebra.proj 𝒜 0)) (comul x) = x ⊗ₜ[R] (1 : A) := by
  rw [proj_zero_eq_algebraMap_comp_counit, LinearMap.lTensor_comp_apply,
    Coalgebra.lTensor_counit_comul]
  simp

/-- Applying `q_0 ⊗ id` to `Δ(x)` gives `1 ⊗ x`, where `q_0 = GradedAlgebra.proj 𝒜 0`. -/
@[simp]
theorem rTensor_proj_zero_comul (x : A) :
    (LinearMap.rTensor A (GradedAlgebra.proj 𝒜 0)) (comul x) = (1 : A) ⊗ₜ[R] x := by
  rw [proj_zero_eq_algebraMap_comp_counit, LinearMap.rTensor_comp_apply,
    Coalgebra.rTensor_counit_comul]
  simp

/-- For `x ∈ 𝒜 n`, `Δ(x) - x ⊗ 1` lies in the part of `A ⊗ A` whose left tensor factor has degree
strictly less than `n`. -/
theorem comul_sub_tmul_one_mem_lower {n : ℕ} {x : A} (hx : x ∈ 𝒜 n) :
    comul x - x ⊗ₜ[R] (1 : A) ∈
      ⨆ (p : ℕ) (q : ℕ) (_ : p + q = n) (_ : p < n),
        Submodule.map₂ (TensorProduct.mk R A A) (𝒜 p) (𝒜 q) := by
  classical
  have hΔ : comul x - x ⊗ₜ[R] (1 : A) =
      (LinearMap.id - LinearMap.lTensor A (GradedAlgebra.proj 𝒜 0) :
        A ⊗[R] A →ₗ[R] A ⊗[R] A) (comul x) := by
    simp only [LinearMap.sub_apply, LinearMap.id_coe, id_eq, lTensor_proj_zero_comul]
  rw [hΔ]
  refine apply_mem_of_mem_bigradedPart 𝒜 _ _ (fun p q hpq a ha b hb => ?_)
    (GradedCoalgebra.comul_mem hx)
  simp only [LinearMap.sub_apply, LinearMap.id_coe, id_eq, LinearMap.lTensor_tmul]
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · rw [show GradedAlgebra.proj 𝒜 0 b = b from DirectSum.decompose_of_mem_same _ hb, sub_self]
    exact zero_mem _
  · have hqb : GradedAlgebra.proj 𝒜 0 b = 0 :=
      DirectSum.decompose_of_mem_ne _ hb (Nat.pos_iff_ne_zero.mp hq)
    rw [hqb, TensorProduct.tmul_zero, sub_zero]
    exact Submodule.mem_iSup_of_mem p <| Submodule.mem_iSup_of_mem q <|
      Submodule.mem_iSup_of_mem hpq <| Submodule.mem_iSup_of_mem (by omega) <|
        Submodule.apply_mem_map₂ _ ha hb

end Bialgebra
