/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Antoine Chambert-Loir
-/
module

public import Mathlib.Algebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import Mathlib.LinearAlgebra.Finsupp.SumProd

/-!
# Results on finitely supported functions.

* `TensorProduct.finsuppLeft`, the tensor product of `ι →₀ M` and `N`
  is linearly equivalent to `ι →₀ M ⊗[R] N`

* `TensorProduct.finsuppScalarLeft`, the tensor product of `ι →₀ R` and `N`
  is linearly equivalent to `ι →₀ N`

* `TensorProduct.finsuppRight`, the tensor product of `M` and `ι →₀ N`
  is linearly equivalent to `ι →₀ M ⊗[R] N`

* `TensorProduct.finsuppScalarRight`, the tensor product of `M` and `ι →₀ R`
  is linearly equivalent to `ι →₀ N`

* `TensorProduct.finsuppLeft'`, if `M` is an `S`-module,
  then the tensor product of `ι →₀ M` and `N` is `S`-linearly equivalent
  to `ι →₀ M ⊗[R] N`

* `finsuppTensorFinsupp`, the tensor product of `ι →₀ M` and `κ →₀ N`
  is linearly equivalent to `(ι × κ) →₀ (M ⊗ N)`.

-/

@[expose] public section


noncomputable section

open DirectSum TensorProduct

open Set LinearMap Submodule

section TensorProduct

variable (R S : Type*) [CommSemiring R] [Semiring S] [Algebra R S]
  (M : Type*) [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]
  (N : Type*) [AddCommMonoid N] [Module R N]

namespace TensorProduct

variable (ι : Type*) [DecidableEq ι]

/-- The tensor product of `ι →₀ M` and `N` is linearly equivalent to `ι →₀ M ⊗[R] N` -/
noncomputable def finsuppLeft :
    (ι →₀ M) ⊗[R] N ≃ₗ[S] ι →₀ M ⊗[R] N :=
  AlgebraTensorModule.congr (finsuppLEquivDirectSum S M ι) (.refl R N) ≪≫ₗ
    directSumLeft _ S (fun _ ↦ M) N ≪≫ₗ (finsuppLEquivDirectSum _ _ ι).symm

variable {R S M N ι}

lemma finsuppLeft_apply_tmul (p : ι →₀ M) (n : N) :
    finsuppLeft R S M N ι (p ⊗ₜ[R] n) = p.sum fun i m ↦ Finsupp.single i (m ⊗ₜ[R] n) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [add_tmul, map_add, hf, hg, Finsupp.sum_add_index]
  | single => simp [finsuppLeft]

@[simp]
lemma finsuppLeft_apply_tmul_apply (p : ι →₀ M) (n : N) (i : ι) :
    finsuppLeft R S M N ι (p ⊗ₜ[R] n) i = p i ⊗ₜ[R] n := by
  rw [finsuppLeft_apply_tmul, Finsupp.sum_apply,
    Finsupp.sum_eq_single i (fun _ _ ↦ Finsupp.single_eq_of_ne') (by simp), Finsupp.single_eq_same]

theorem finsuppLeft_apply (t : (ι →₀ M) ⊗[R] N) (i : ι) :
    finsuppLeft R S M N ι t i = rTensor N (Finsupp.lapply i) t := by
  induction t with
  | zero => simp
  | tmul f n => simp only [finsuppLeft_apply_tmul_apply, rTensor_tmul, Finsupp.lapply_apply]
  | add x y hx hy => simp [map_add, hx, hy]

@[simp]
lemma finsuppLeft_symm_apply_single (i : ι) (m : M) (n : N) :
    (finsuppLeft R S M N ι).symm (Finsupp.single i (m ⊗ₜ[R] n)) =
      Finsupp.single i m ⊗ₜ[R] n := by
  simp [finsuppLeft]

variable (R S M N ι) in
/-- The tensor product of `M` and `ι →₀ N` is linearly equivalent to `ι →₀ M ⊗[R] N` -/
noncomputable def finsuppRight :
    M ⊗[R] (ι →₀ N) ≃ₗ[S] ι →₀ M ⊗[R] N :=
  AlgebraTensorModule.congr (.refl S M) (finsuppLEquivDirectSum R N ι) ≪≫ₗ
    directSumRight R S M (fun _ : ι ↦ N) ≪≫ₗ (finsuppLEquivDirectSum _ _ ι).symm

lemma finsuppRight_apply_tmul (m : M) (p : ι →₀ N) :
    finsuppRight R S M N ι (m ⊗ₜ[R] p) = p.sum fun i n ↦ Finsupp.single i (m ⊗ₜ[R] n) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [tmul_add, map_add, hf, hg, Finsupp.sum_add_index]
  | single => simp [finsuppRight]

@[simp]
lemma finsuppRight_apply_tmul_apply (m : M) (p : ι →₀ N) (i : ι) :
    finsuppRight R S M N ι (m ⊗ₜ[R] p) i = m ⊗ₜ[R] p i := by
  rw [finsuppRight_apply_tmul, Finsupp.sum_apply,
    Finsupp.sum_eq_single i (fun _ _ ↦ Finsupp.single_eq_of_ne') (by simp), Finsupp.single_eq_same]

theorem finsuppRight_apply (t : M ⊗[R] (ι →₀ N)) (i : ι) :
    finsuppRight R S M N ι t i = lTensor M (Finsupp.lapply i) t := by
  induction t with
  | zero => simp
  | tmul m f => simp [finsuppRight_apply_tmul_apply]
  | add x y hx hy => simp [map_add, hx, hy]

@[simp]
lemma finsuppRight_tmul_single (i : ι) (m : M) (n : N) :
    finsuppRight R S M N ι (m ⊗ₜ[R] Finsupp.single i n) = Finsupp.single i (m ⊗ₜ[R] n) := by
  ext; simp +contextual [Finsupp.single_apply, apply_ite]

@[simp]
lemma finsuppRight_symm_apply_single (i : ι) (m : M) (n : N) :
    (finsuppRight R S M N ι).symm (Finsupp.single i (m ⊗ₜ[R] n)) =
      m ⊗ₜ[R] Finsupp.single i n := by
  simp [LinearEquiv.symm_apply_eq]

lemma finsuppLeft_smul' (s : S) (t : (ι →₀ M) ⊗[R] N) :
    finsuppLeft R S M N ι (s • t) = s • finsuppLeft R S M N ι t := by
  simp

@[deprecated (since := "2026-01-01")] alias finsuppLeft' := finsuppLeft

@[nolint synTaut, deprecated "is syntactic rfl now" (since := "2026-01-01")]
lemma finsuppLeft'_apply (x : (ι →₀ M) ⊗[R] N) :
    finsuppLeft R S M N ι x = finsuppLeft R S M N ι x := rfl

variable (R M N ι) in
/-- The tensor product of `ι →₀ R` and `N` is linearly equivalent to `ι →₀ N` -/
noncomputable def finsuppScalarLeft :
    (ι →₀ R) ⊗[R] N ≃ₗ[R] ι →₀ N :=
  finsuppLeft R R R N ι ≪≫ₗ (Finsupp.mapRange.linearEquiv (TensorProduct.lid R N))

@[simp]
lemma finsuppScalarLeft_apply_tmul_apply (p : ι →₀ R) (n : N) (i : ι) :
    finsuppScalarLeft R N ι (p ⊗ₜ[R] n) i = p i • n := by
  simp [finsuppScalarLeft]

lemma finsuppScalarLeft_apply_tmul (p : ι →₀ R) (n : N) :
    finsuppScalarLeft R N ι (p ⊗ₜ[R] n) = p.sum fun i m ↦ Finsupp.single i (m • n) := by
  ext i
  rw [finsuppScalarLeft_apply_tmul_apply, Finsupp.sum_apply,
    Finsupp.sum_eq_single i (fun _ _ ↦ Finsupp.single_eq_of_ne') (by simp), Finsupp.single_eq_same]

lemma finsuppScalarLeft_apply (pn : (ι →₀ R) ⊗[R] N) (i : ι) :
    finsuppScalarLeft R N ι pn i = TensorProduct.lid R N ((Finsupp.lapply i).rTensor N pn) := by
  simp [finsuppScalarLeft, finsuppLeft_apply]

@[simp]
lemma finsuppScalarLeft_symm_apply_single (i : ι) (n : N) :
    (finsuppScalarLeft R N ι).symm (Finsupp.single i n) =
      (Finsupp.single i 1) ⊗ₜ[R] n := by
  simp [finsuppScalarLeft, finsuppLeft_symm_apply_single]

variable (R S M N ι) in
/-- The tensor product of `M` and `ι →₀ R` is linearly equivalent to `ι →₀ M` -/
noncomputable def finsuppScalarRight :
    M ⊗[R] (ι →₀ R) ≃ₗ[S] ι →₀ M :=
  finsuppRight R S M R ι ≪≫ₗ Finsupp.mapRange.linearEquiv (AlgebraTensorModule.rid R S M)

@[simp]
lemma finsuppScalarRight_apply_tmul_apply (m : M) (p : ι →₀ R) (i : ι) :
    finsuppScalarRight R S M ι (m ⊗ₜ[R] p) i = p i • m := by
  simp [finsuppScalarRight]

lemma finsuppScalarRight_apply_tmul (m : M) (p : ι →₀ R) :
    finsuppScalarRight R S M ι (m ⊗ₜ[R] p) = p.sum fun i n ↦ Finsupp.single i (n • m) := by
  ext i
  rw [finsuppScalarRight_apply_tmul_apply, Finsupp.sum_apply,
    Finsupp.sum_eq_single i (fun _ _ ↦ Finsupp.single_eq_of_ne') (by simp), Finsupp.single_eq_same]

lemma finsuppScalarRight_apply (t : M ⊗[R] (ι →₀ R)) (i : ι) :
    finsuppScalarRight R S M ι t i =
      AlgebraTensorModule.rid R S M ((Finsupp.lapply i).lTensor M t) := by
  simp [finsuppScalarRight, finsuppRight_apply]

@[simp]
lemma finsuppScalarRight_symm_apply_single (i : ι) (m : M) :
    (finsuppScalarRight R S M ι).symm (Finsupp.single i m) =
      m ⊗ₜ[R] (Finsupp.single i 1) := by
  simp [finsuppScalarRight, finsuppRight_symm_apply_single]

theorem finsuppScalarRight_smul (s : S) (t) :
    finsuppScalarRight R S M ι (s • t) = s • finsuppScalarRight R S M ι t :=
  map_smul _ _ _

@[deprecated (since := "2026-01-01")] alias finsuppScalarRight' := finsuppScalarRight

@[nolint synTaut, deprecated "is syntactic rfl now" (since := "2026-01-01")]
theorem coe_finsuppScalarRight' :
    ⇑(finsuppScalarRight R S M ι) = finsuppScalarRight R S M ι :=
  rfl

end TensorProduct

end TensorProduct

variable (R S M N ι κ : Type*)
  [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [Semiring S] [Algebra R S]

theorem Finsupp.linearCombination_one_tmul [DecidableEq ι] {v : ι → M} :
    (linearCombination S ((1 : S) ⊗ₜ[R] v ·)).restrictScalars R =
      (linearCombination R v).lTensor S ∘ₗ (finsuppScalarRight R R S ι).symm := by
  ext; simp [smul_tmul']

variable [Module S M] [IsScalarTower R S M]

open scoped Classical in
/-- The tensor product of `ι →₀ M` and `κ →₀ N` is linearly equivalent to `(ι × κ) →₀ (M ⊗ N)`. -/
def finsuppTensorFinsupp : (ι →₀ M) ⊗[R] (κ →₀ N) ≃ₗ[S] ι × κ →₀ M ⊗[R] N :=
  TensorProduct.AlgebraTensorModule.congr
    (finsuppLEquivDirectSum S M ι) (finsuppLEquivDirectSum R N κ) ≪≫ₗ
    ((TensorProduct.directSum R S (fun _ : ι => M) fun _ : κ => N) ≪≫ₗ
      (finsuppLEquivDirectSum S (M ⊗[R] N) (ι × κ)).symm)

@[simp]
theorem finsuppTensorFinsupp_single (i : ι) (m : M) (k : κ) (n : N) :
    finsuppTensorFinsupp R S M N ι κ (Finsupp.single i m ⊗ₜ Finsupp.single k n) =
      Finsupp.single (i, k) (m ⊗ₜ n) := by
  simp [finsuppTensorFinsupp]

@[simp]
theorem finsuppTensorFinsupp_apply (f : ι →₀ M) (g : κ →₀ N) (i : ι) (k : κ) :
    finsuppTensorFinsupp R S M N ι κ (f ⊗ₜ g) (i, k) = f i ⊗ₜ g k := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ hf₁ hf₂ => simp [add_tmul, hf₁, hf₂]
  | single i' m =>
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g₁ g₂ hg₁ hg₂ => simp [tmul_add, hg₁, hg₂]
    | single k' n =>
      classical
      simp_rw [finsuppTensorFinsupp_single, Finsupp.single_apply, Prod.mk_inj, ite_and]
      split_ifs <;> simp

@[simp]
theorem finsuppTensorFinsupp_symm_single (i : ι × κ) (m : M) (n : N) :
    (finsuppTensorFinsupp R S M N ι κ).symm (Finsupp.single i (m ⊗ₜ n)) =
      Finsupp.single i.1 m ⊗ₜ Finsupp.single i.2 n :=
  Prod.casesOn i fun _ _ =>
    (LinearEquiv.symm_apply_eq _).2 (finsuppTensorFinsupp_single _ _ _ _ _ _ _ _ _ _).symm

/-- A variant of `finsuppTensorFinsupp` where the first module is the ground ring. -/
def finsuppTensorFinsuppLid : (ι →₀ R) ⊗[R] (κ →₀ N) ≃ₗ[R] ι × κ →₀ N :=
  finsuppTensorFinsupp R R R N ι κ ≪≫ₗ Finsupp.lcongr (Equiv.refl _) (TensorProduct.lid R N)

@[simp]
theorem finsuppTensorFinsuppLid_apply_apply (f : ι →₀ R) (g : κ →₀ N) (a : ι) (b : κ) :
    finsuppTensorFinsuppLid R N ι κ (f ⊗ₜ[R] g) (a, b) = f a • g b := by
  simp [finsuppTensorFinsuppLid]

@[simp]
theorem finsuppTensorFinsuppLid_single_tmul_single (a : ι) (b : κ) (r : R) (n : N) :
    finsuppTensorFinsuppLid R N ι κ (Finsupp.single a r ⊗ₜ[R] Finsupp.single b n) =
      Finsupp.single (a, b) (r • n) := by
  simp [finsuppTensorFinsuppLid]

@[simp]
theorem finsuppTensorFinsuppLid_symm_single_smul (i : ι × κ) (r : R) (n : N) :
    (finsuppTensorFinsuppLid R N ι κ).symm (Finsupp.single i (r • n)) =
      Finsupp.single i.1 r ⊗ₜ Finsupp.single i.2 n :=
  Prod.casesOn i fun _ _ =>
    (LinearEquiv.symm_apply_eq _).2 (finsuppTensorFinsuppLid_single_tmul_single ..).symm

/-- A variant of `finsuppTensorFinsupp` where the second module is the ground ring. -/
def finsuppTensorFinsuppRid : (ι →₀ M) ⊗[R] (κ →₀ R) ≃ₗ[R] ι × κ →₀ M :=
  finsuppTensorFinsupp R R M R ι κ ≪≫ₗ Finsupp.lcongr (Equiv.refl _) (TensorProduct.rid R M)

@[simp]
theorem finsuppTensorFinsuppRid_apply_apply (f : ι →₀ M) (g : κ →₀ R) (a : ι) (b : κ) :
    finsuppTensorFinsuppRid R M ι κ (f ⊗ₜ[R] g) (a, b) = g b • f a := by
  simp [finsuppTensorFinsuppRid]

@[simp]
theorem finsuppTensorFinsuppRid_single_tmul_single (a : ι) (b : κ) (m : M) (r : R) :
    finsuppTensorFinsuppRid R M ι κ (Finsupp.single a m ⊗ₜ[R] Finsupp.single b r) =
      Finsupp.single (a, b) (r • m) := by
  simp [finsuppTensorFinsuppRid]

@[simp]
theorem finsuppTensorFinsuppRid_symm_single_smul (i : ι × κ) (m : M) (r : R) :
    (finsuppTensorFinsuppRid R M ι κ).symm (Finsupp.single i (r • m)) =
      Finsupp.single i.1 m ⊗ₜ Finsupp.single i.2 r :=
  Prod.casesOn i fun _ _ =>
    (LinearEquiv.symm_apply_eq _).2 (finsuppTensorFinsuppRid_single_tmul_single ..).symm

/-- A variant of `finsuppTensorFinsupp` where both modules are the ground ring. -/
def finsuppTensorFinsupp' : (ι →₀ R) ⊗[R] (κ →₀ R) ≃ₗ[R] ι × κ →₀ R :=
  finsuppTensorFinsuppLid R R ι κ

@[simp]
theorem finsuppTensorFinsupp'_apply_apply (f : ι →₀ R) (g : κ →₀ R) (a : ι) (b : κ) :
    finsuppTensorFinsupp' R ι κ (f ⊗ₜ[R] g) (a, b) = f a * g b :=
  finsuppTensorFinsuppLid_apply_apply R R ι κ f g a b

@[simp]
theorem finsuppTensorFinsupp'_single_tmul_single (a : ι) (b : κ) (r₁ r₂ : R) :
    finsuppTensorFinsupp' R ι κ (Finsupp.single a r₁ ⊗ₜ[R] Finsupp.single b r₂) =
      Finsupp.single (a, b) (r₁ * r₂) :=
  finsuppTensorFinsuppLid_single_tmul_single R R ι κ a b r₁ r₂

theorem finsuppTensorFinsupp'_symm_single_mul (i : ι × κ) (r₁ r₂ : R) :
    (finsuppTensorFinsupp' R ι κ).symm (Finsupp.single i (r₁ * r₂)) =
      Finsupp.single i.1 r₁ ⊗ₜ Finsupp.single i.2 r₂ :=
  finsuppTensorFinsuppLid_symm_single_smul R R ι κ i r₁ r₂

theorem finsuppTensorFinsupp'_symm_single_eq_single_one_tmul (i : ι × κ) (r : R) :
    (finsuppTensorFinsupp' R ι κ).symm (Finsupp.single i r) =
      Finsupp.single i.1 1 ⊗ₜ Finsupp.single i.2 r := by
  nth_rw 1 [← one_mul r]
  exact finsuppTensorFinsupp'_symm_single_mul R ι κ i _ _

theorem finsuppTensorFinsupp'_symm_single_eq_tmul_single_one (i : ι × κ) (r : R) :
    (finsuppTensorFinsupp' R ι κ).symm (Finsupp.single i r) =
      Finsupp.single i.1 r ⊗ₜ Finsupp.single i.2 1 := by
  nth_rw 1 [← mul_one r]
  exact finsuppTensorFinsupp'_symm_single_mul R ι κ i _ _

theorem finsuppTensorFinsuppLid_self :
    finsuppTensorFinsuppLid R R ι κ = finsuppTensorFinsupp' R ι κ := rfl

theorem finsuppTensorFinsuppRid_self :
    finsuppTensorFinsuppRid R R ι κ = finsuppTensorFinsupp' R ι κ := by
  rw [finsuppTensorFinsupp', finsuppTensorFinsuppLid, finsuppTensorFinsuppRid,
    TensorProduct.lid_eq_rid]

end
