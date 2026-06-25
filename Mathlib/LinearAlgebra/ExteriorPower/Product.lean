/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Product
public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!

# Exterior power of product module

-/

@[expose] public section

universe u

variable (R : Type u) [CommRing R]

variable (M N : Type*) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

open TensorProduct

namespace ExteriorAlgebra

section RingHelpers

variable {M} in
@[simp]
lemma algebraMapInv_ι (x : M) : algebraMapInv (ι R x) = (0 : R) := by
  simp [algebraMapInv]

variable {M} in
lemma algebraMapInv_algebraMap (r : R) :
    algebraMapInv (algebraMap R (ExteriorAlgebra R M) r) = r :=
  algebraMap_leftInverse M r

variable {M} in
@[simp]
lemma ιInv_ι (x : M) : ιInv (ι R x : ExteriorAlgebra R M) = x :=
  ι_leftInverse x

variable {M} in
@[simp]
lemma ιInv_one : ιInv (1 : ExteriorAlgebra R M) = 0 := by
  let : Module Rᵐᵒᵖ M := Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)
  have : IsCentralScalar R M := ⟨fun r m => rfl⟩
  simp [ιInv]

variable {M} in
@[simp]
lemma ιInv_algebraMap (r : R) : ιInv (algebraMap R (ExteriorAlgebra R M) r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, ιInv_one, smul_zero]

lemma ι_mul_ι_ring (a b : R) : ι R a * ι R b = 0 := by
  trans a • ι R (1 : R) * b • ι R (1 : R)
  · simp [← map_smul, smul_eq_mul, mul_one]
  · rw [smul_mul_smul_comm, ι_sq_zero, smul_zero]

/-- Every element of the exterior algebra of the base ring decomposes into a scalar part and a
generator part. -/
lemma eq_algebraMap_add_ι (t : ExteriorAlgebra R R) :
    t = algebraMap R _ (algebraMapInv t) + ι R (ιInv t) := by
  induction t using ExteriorAlgebra.induction with
  | algebraMap r => simp
  | ι x => simp
  | add a b ha hb =>
    nth_rw 1 [ha, hb]
    simp [map_add, ← add_assoc, ← add_comm ((ι R) (ιInv a))]
  | mul a b ha hb =>
    obtain ⟨α, x, ha⟩ : ∃ α x, a = algebraMap R _ α + ι R x := ⟨_, _, ha⟩
    obtain ⟨β, y, hb⟩ : ∃ β y, b = algebraMap R _ β + ι R y := ⟨_, _, hb⟩
    subst ha hb
    have e1 : algebraMap R (ExteriorAlgebra R R) α * ι R y = ι R (α • y) := by
      rw [← Algebra.smul_def, ← map_smul]
    have e2 : (ι R x : ExteriorAlgebra R R) * algebraMap R _ β = ι R (β • x) := by
      rw [← Algebra.commutes, ← Algebra.smul_def, ← map_smul]
    rw [add_mul, mul_add, mul_add, ι_mul_ι_ring, e1, e2, ← map_mul, add_zero, add_assoc, ← map_add]
    simp [-map_mul]

variable {R} in
/-- The exterior algebra of the base ring is a free module of rank two, with basis `1, ι 1`. -/
noncomputable def prodRingEquiv : (R × R) ≃ₗ[R] ExteriorAlgebra R R where
  __ := LinearMap.coprod (Algebra.linearMap R (ExteriorAlgebra R R)) (ι R)
  invFun := algebraMapInv.toLinearMap.prod ιInv
  left_inv x := by simp
  right_inv x := by simp [← eq_algebraMap_add_ι R x]

variable {R} in
@[simp]
lemma prodRingEquiv_apply (c : R × R) :
    prodRingEquiv c = algebraMap R (ExteriorAlgebra R R) c.1 + ι R c.2 := rfl

end RingHelpers

variable {N} in
/-- The exterior algebra of `M × R` is, as a module, the product of two copies of the exterior
algebra of `M`; the pair `(x, y)` corresponds to `x + y ∧ ι (0, 1)`. -/
noncomputable def prodEquivProd :
    (ExteriorAlgebra R M × ExteriorAlgebra R M) ≃ₗ[R] ExteriorAlgebra R (M × R) :=
  (LinearEquiv.prodCongr (TensorProduct.rid R (ExteriorAlgebra R M)).symm
      (TensorProduct.rid R (ExteriorAlgebra R M)).symm).trans <|
    ((TensorProduct.prodRight R R (ExteriorAlgebra R M) R R).symm).trans <|
      (TensorProduct.congr (LinearEquiv.refl R _) prodRingEquiv).trans <|
        ((GradedTensorProduct.of R _ _).trans (prodEquivTensor R M R).symm.toLinearEquiv)

lemma prodEquivProd_apply (x y : ExteriorAlgebra R M) :
    prodEquivProd R M (x, y) = ExteriorAlgebra.map (LinearMap.inl R M R) x +
      ExteriorAlgebra.map (LinearMap.inl R M R) y * ι R ((0, 1) : M × R) := by
  have hsplit : (x ⊗ₜ[R] (1 : R), y ⊗ₜ[R] (1 : R)) =
    (x ⊗ₜ[R] 1, x ⊗ₜ[R] 0) + (y ⊗ₜ[R] 0, y ⊗ₜ[R] 1) := by simp
  simp only [prodEquivProd, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    TensorProduct.rid_symm_apply]
  rw [hsplit, map_add, TensorProduct.prodRight_symm_tmul, TensorProduct.prodRight_symm_tmul,
    map_add, TensorProduct.congr_tmul, TensorProduct.congr_tmul, map_add, map_add]
  simp only [LinearEquiv.refl_apply, prodRingEquiv_apply, map_one, map_zero, add_zero, zero_add,
    AlgEquiv.toLinearEquiv_apply]
  simp [prodEquivTensor_symm_tmul, prodEquivTensor_symm_tmul, map_apply_ι]

lemma prodEquivProd_comp_inl :
    (ExteriorAlgebra.prodEquivProd R M).comp (LinearMap.inl R _ _) =
      ExteriorAlgebra.map (LinearMap.inl R M R) := by
  refine LinearMap.ext fun x => ?_
  simp [prodEquivProd_apply]

lemma prodEquivProd_apply_snd (a : ExteriorAlgebra R M) :
    ExteriorAlgebra.prodEquivProd R M (0, a) =
      (ExteriorAlgebra.map (LinearMap.inl R M R) a) * ExteriorAlgebra.ι R ((0, 1) : M × R) := by
  rw [prodEquivProd_apply, map_zero, zero_add]

section MemDecomp

variable {R M N}

lemma map_mem_exteriorPower (f : M →ₗ[R] N) {k : ℕ} {w : ExteriorAlgebra R M} (hw : w ∈ ⋀[R]^k M) :
    ExteriorAlgebra.map f w ∈ ⋀[R]^k N := by
  simpa [exteriorPower.coe_map] using (exteriorPower.map k f ⟨w, hw⟩).2

lemma ι_mul_mem_exteriorPower_anticomm {k : ℕ} {w : ExteriorAlgebra R M} (hw : w ∈ ⋀[R]^k M)
    (z : M) : ι R z * w = ((-1 : ℤ) ^ k) • (w * ι R z) := by
  rw [← ιMulti_span_fixedDegree] at hw
  induction hw using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨v, rfl⟩ := ha
    exact ι_mul_ιMulti_anticomm _ _ _
  | zero => simp
  | add a b _ _ iha ihb => rw [mul_add, iha, ihb, add_mul, smul_add]
  | smul c a _ ih => simp [ih]

/-- Every element of `⋀[R]^(i+1) (M × R)` decomposes as `map inl x + map inl y * ι (0, 1)` with
`x` and `y` of the appropriate degrees. -/
lemma exists_decomp (i : ℕ) :
    ∀ z ∈ ⋀[R]^(i + 1) (M × R), ∃ x ∈ ⋀[R]^(i + 1) M, ∃ y ∈ ⋀[R]^i M,
      z = ExteriorAlgebra.map (LinearMap.inl R M R) x +
        ExteriorAlgebra.map (LinearMap.inl R M R) y * ι R ((0, 1) : M × R) := by
  induction i with
  | zero =>
    intro z hz
    rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hz
    induction hz using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨v, rfl⟩ := hw
      refine ⟨ι R (v 0).1, by simp, algebraMap R _ (v 0).2, ?_, ?_⟩
      · rw [Algebra.algebraMap_eq_smul_one]
        exact Submodule.smul_mem _ _ (SetLike.one_mem_graded _)
      · simp [map_apply_ι, AlgHom.commutes, ← Algebra.smul_def, ← map_smul, ← map_add]
    | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
    | add a b _ _ iha ihb =>
      obtain ⟨xa, hxa, ya, hya, rfl⟩ := iha
      obtain ⟨xb, hxb, yb, hyb, rfl⟩ := ihb
      refine ⟨xa + xb, add_mem hxa hxb, ya + yb, add_mem hya hyb, ?_⟩
      rw [map_add, map_add, add_mul]
      abel
    | smul c a _ ih =>
      obtain ⟨x, hx, y, hy, rfl⟩ := ih
      refine ⟨c • x, Submodule.smul_mem _ _ hx, c • y, Submodule.smul_mem _ _ hy, ?_⟩
      rw [map_smul, map_smul, smul_add, smul_mul_assoc]
  | succ i IH =>
    intro z hz
    rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hz
    induction hz using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨v, rfl⟩ := hw
      obtain ⟨x, hx, y, hy, heq⟩ := IH _
        (ExteriorAlgebra.ιMulti_range R (i + 1) (Set.mem_range_self (Matrix.vecTail v)))
      have hι1 : ι R ((v 0).1) ∈ ⋀[R]^1 M := by simp
      have hv0 : ι R (v 0) = ExteriorAlgebra.map (LinearMap.inl R M R) (ι R (v 0).1) +
          (v 0).2 • ι R ((0, 1) : M × R) := by
        rw [map_apply_ι, ← map_smul, ← map_add]
        simp
      refine ⟨ι R (v 0).1 * x, ?_, ι R (v 0).1 * y + (((-1 : R) ^ (i + 1)) * (v 0).2) • x, ?_, ?_⟩
      · simpa [Nat.add_comm 1 (i + 1)] using SetLike.mul_mem_graded hι1 hx
      · refine add_mem ?_ (Submodule.smul_mem _ _ hx)
        simpa [Nat.add_comm 1 i] using SetLike.mul_mem_graded hι1 hy
      · have hD : ι R (0, 1) * (ExteriorAlgebra.map (LinearMap.inl R M R) y * ι R (0, 1)) = 0 := by
          rw [← mul_assoc, ι_mul_mem_exteriorPower_anticomm (map_mem_exteriorPower _ hy),
            smul_mul_assoc, mul_assoc, ι_sq_zero, mul_zero, smul_zero]
        rw [ιMulti_succ_apply, heq, hv0, add_mul, mul_add, mul_add, smul_mul_assoc, smul_mul_assoc,
          hD, smul_zero, add_zero, ι_mul_mem_exteriorPower_anticomm (map_mem_exteriorPower _ hx)]
        simp [← algebraMap_smul R (R := ℤ), smul_smul, mul_comm ((v 0).2), add_mul, ← mul_assoc,
          add_assoc]
    | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
    | add a b _ _ iha ihb =>
      obtain ⟨xa, hxa, ya, hya, rfl⟩ := iha
      obtain ⟨xb, hxb, yb, hyb, rfl⟩ := ihb
      refine ⟨xa + xb, add_mem hxa hxb, ya + yb, add_mem hya hyb, ?_⟩
      simp only [← add_assoc, map_add, add_mul]
      abel
    | smul c a _ ih =>
      obtain ⟨x, hx, y, hy, rfl⟩ := ih
      refine ⟨c • x, Submodule.smul_mem _ _ hx, c • y, Submodule.smul_mem _ _ hy, ?_⟩
      rw [map_smul, map_smul, smul_add, smul_mul_assoc]

end MemDecomp

lemma prodEquivProd_mem_exteriorPower (i : ℕ) (x y : ExteriorAlgebra R M) :
    ExteriorAlgebra.prodEquivProd R M (x, y) ∈ ⋀[R]^(i + 1) (M × R) ↔
    (x ∈ ⋀[R]^(i + 1) M ∧ y ∈ ⋀[R]^i M) := by
  refine ⟨fun h ↦ ?_, fun ⟨hx, hy⟩ ↦ ?_⟩
  · rw [prodEquivProd_apply] at h
    obtain ⟨x', hx', y', hy', heq⟩ := exists_decomp i _ h
    have hinj : (x, y) = (x', y') := by
      apply (prodEquivProd R M).injective
      rw [prodEquivProd_apply, prodEquivProd_apply, heq]
    obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ hinj
    exact ⟨h1 ▸ hx', h2 ▸ hy'⟩
  · rw [prodEquivProd_apply]
    refine add_mem (map_mem_exteriorPower _ hx) ?_
    have hι : ι R ((0, 1) : M × R) ∈ ⋀[R]^1 (M × R) := by simp
    exact SetLike.mul_mem_graded (map_mem_exteriorPower _ hy) hι

end ExteriorAlgebra

open ExteriorAlgebra in
/-- The `(i+1)`-st exterior power of `M × R` decomposes as the product of the `(i+1)`-st and the
`i`-th exterior powers of `M`. -/
noncomputable def exteriorPowerProdEquivProd (i : ℕ) :
    (⋀[R]^(i + 1) M × ⋀[R]^i M) ≃ₗ[R] ⋀[R]^(i + 1) (M × R) :=
  LinearEquiv.ofBijective
    (LinearMap.codRestrict _ ((prodEquivProd R M).toLinearMap.comp
      ((⋀[R]^(i + 1) M).subtype.prodMap ((⋀[R]^i M).subtype)))
      fun c => (prodEquivProd_mem_exteriorPower R M i c.1 c.2).mpr ⟨c.1.2, c.2.2⟩)
    ⟨by simp [← LinearMap.ker_eq_bot], fun z => by
      obtain ⟨w, hw⟩ := (prodEquivProd R M).surjective z.1
      have hmem := (prodEquivProd_mem_exteriorPower R M i w.1 w.2).mp (by simp [hw])
      exact ⟨(⟨w.1, hmem.1⟩, ⟨w.2, hmem.2⟩), Subtype.ext hw⟩⟩

lemma exteriorPowerProdEquivProd_apply_coe (i : ℕ) (x : ⋀[R]^(i + 1) M) (y : ⋀[R]^i M) :
    (exteriorPowerProdEquivProd R M i) (x, y) = ExteriorAlgebra.prodEquivProd R M (x, y) :=
  rfl

lemma exteriorPowerProdEquivProd_apply_inl_ιMulti (i : ℕ) (m : Fin (i + 1) → M) :
    (exteriorPowerProdEquivProd R M i) (exteriorPower.ιMulti R (i + 1) m, 0) =
      exteriorPower.ιMulti R (i + 1) ((LinearMap.inl R M R) ∘ m) := by
  apply Subtype.ext
  rw [exteriorPowerProdEquivProd_apply_coe, ZeroMemClass.coe_zero,
    ExteriorAlgebra.prodEquivProd_apply, map_zero, zero_mul, add_zero,
    exteriorPower.ιMulti_apply_coe, exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.map_apply_ιMulti]

lemma exteriorPowerProdEquivProd_comp_inl (i : ℕ) :
    (exteriorPowerProdEquivProd R M i).toLinearMap.comp (LinearMap.inl R _ _) =
    exteriorPower.map (i + 1) (LinearMap.inl R _ _) := by
  ext m
  have : Matrix.vecTail ((LinearMap.inl R M R) ∘ m) =
    fun j ↦ Matrix.vecTail (fun i ↦ Prod.mk (m i)) j 0 := rfl
  simp [exteriorPowerProdEquivProd_apply_inl_ιMulti, ← this]

lemma exteriorPowerProdEquivProd_apply_inr_ιMulti (i : ℕ) (m : Fin i → M) :
    (exteriorPowerProdEquivProd R M i) (0, exteriorPower.ιMulti R i m) =
      ExteriorAlgebra.ιMulti R i ((LinearMap.inl R M R) ∘ m) *
        ExteriorAlgebra.ι R ((0, 1) : M × R) := by
  rw [exteriorPowerProdEquivProd_apply_coe, ZeroMemClass.coe_zero,
    ExteriorAlgebra.prodEquivProd_apply, map_zero, zero_add,
    exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.map_apply_ιMulti]
