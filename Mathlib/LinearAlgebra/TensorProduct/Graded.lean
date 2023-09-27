/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.RingTheory.TensorProduct
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.Data.ZMod.Basic

/-!
# Graded tensor products over super- (`ZMod 2`-graded) algebras
-/

local notation "ℤ₂" => ZMod 2
open scoped TensorProduct

variable {R A B : Type*}

section external
variable (𝒜 : ZMod 2 → Type*) (ℬ : ZMod 2 → Type*)
variable [CommRing R]
variable [∀ i, AddCommGroup (𝒜 i)] [∀ i, AddCommGroup (ℬ i)]
variable [∀ i, Module R (𝒜 i)] [∀ i, Module R (ℬ i)]
variable [DirectSum.GRing 𝒜] [DirectSum.GRing ℬ]
variable [DirectSum.GAlgebra R 𝒜] [DirectSum.GAlgebra R ℬ]

instance (i : ℤ₂ × ℤ₂) : Module R (𝒜 (Prod.fst i) ⊗[R] ℬ (Prod.snd i)) :=
  TensorProduct.leftModule

instance : Pow ℤˣ (ZMod 2) where
  pow s z₂ := s ^ z₂.val

lemma z₂pow_def (s : ℤˣ) (x : ZMod 2) : s ^ x = s ^ x.val := rfl

@[simp] lemma z₂pow_zero (s : ℤˣ) : (s ^ (0 : ZMod 2) : ℤˣ) = (1 : ℤˣ) := pow_zero _
@[simp] lemma z₂pow_one (s : ℤˣ) : (s ^ (1 : ZMod 2) : ℤˣ) = s := pow_one _
lemma z₂pow_add (s : ℤˣ) (x y : ZMod 2) : s ^ (x + y) = s ^ x * s ^ y := by
  simp only [z₂pow_def]
  rw [ZMod.val_add, ←pow_eq_pow_mod, pow_add]
  fin_cases s <;> simp


local notation "𝒜ℬ" => (fun i : ℤ₂ × ℤ₂ => 𝒜 (Prod.fst i) ⊗[R] ℬ (Prod.snd i))
-- #exit
variable (R) {𝒜} {ℬ} in
noncomputable irreducible_def mulAux :
    (DirectSum _ 𝒜ℬ) →ₗ[R] (DirectSum _ 𝒜ℬ) →ₗ[R] (DirectSum _ 𝒜ℬ) := by
  refine TensorProduct.curry ?_
  refine ?_ ∘ₗ (TensorProduct.directSum R 𝒜ℬ 𝒜ℬ).toLinearMap
  refine DirectSum.toModule R _ _ fun i => ?_
  have o := DirectSum.lof R _ 𝒜ℬ (i.1.1 + i.2.1, i.1.2 + i.2.2)
  have s : ℤˣ := ((-1 : ℤˣ)^(i.1.2 * i.2.1 : ℤ₂) : ℤˣ)
  refine (s • o) ∘ₗ ?_
  refine ?_ ∘ₗ (TensorProduct.tensorTensorTensorComm R _ _ _ _).toLinearMap
  refine TensorProduct.map (TensorProduct.lift ?_) (TensorProduct.lift ?_)
  · exact DirectSum.gMulLHom R _
  · exact DirectSum.gMulLHom R _

open DirectSum (of)
open GradedMonoid (GMul)


theorem mulAux_of_tmul_of_tmul (i₁ j₁ i₂ j₂ : ℤ₂)
    (a₁ : 𝒜 i₁) (b₁ : ℬ j₁) (a₂ : 𝒜 i₂) (b₂ : ℬ j₂) :
    mulAux R (of _ (i₁, j₁) (a₁ ⊗ₜ b₁)) (of _ (i₂, j₂) (a₂ ⊗ₜ b₂)) =
      (-1 : ℤˣ)^(j₁ * i₂)
        • of 𝒜ℬ (_, _) (GMul.mul a₁ a₂ ⊗ₜ GMul.mul b₁ b₂) := by
  rw [mulAux]
  dsimp
  erw [TensorProduct.directSum_lof_tmul_lof]
  simp [DirectSum.lof_eq_of]

theorem mulAux_one (x : ⨁ i : ℤ₂ × ℤ₂, 𝒜 i.1 ⊗[R] ℬ i.2) :
    mulAux R 1 x = x := sorry

theorem one_mulAux (x : ⨁ i : ℤ₂ × ℤ₂, 𝒜 i.1 ⊗[R] ℬ i.2) :
    mulAux R x 1 = x := sorry

theorem mulAux_assoc (x y z : ⨁ i : ℤ₂ × ℤ₂, 𝒜 i.1 ⊗[R] ℬ i.2) :
    mulAux R (mulAux R x y) z = mulAux R x (mulAux R y z) := by
  let mA := mulAux R (𝒜 := 𝒜) (ℬ := ℬ)
    -- restate as an equality of morphisms so that we can use `ext`
  suffices LinearMap.llcomp R _ _ _ mA ∘ₗ mA =
      (LinearMap.llcomp R _ _ _ LinearMap.lflip <| LinearMap.llcomp R _ _ _ mA.flip ∘ₗ mA).flip by
    exact FunLike.congr_fun (FunLike.congr_fun (FunLike.congr_fun this x) y) z
  ext ⟨ixa, ixb⟩ xa xb ⟨iya, iyb⟩ ya yb ⟨iza, izb⟩ za zb
  dsimp [DirectSum.lof_eq_of]
  rw [mulAux_of_tmul_of_tmul, mulAux_of_tmul_of_tmul]
  rw [LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, LinearMap.smul_apply]
  rw [mulAux_of_tmul_of_tmul, mulAux_of_tmul_of_tmul]
  rw [smul_smul, smul_smul, ←z₂pow_add, ←z₂pow_add, add_mul, mul_add]
  congr 1
  · congr 1
    abel
  · erw [←TensorProduct.directSum_lof_tmul_lof]
    erw [←TensorProduct.directSum_lof_tmul_lof]
    congr 1
    · refine of_eq_of_gradedMonoid_eq ?_
      sorry
    · sorry
  -- refine congr_arg₂ (· ⊗ₜ ·)
#check 1

example (a b c : ℕ) : a + b + c = b + a + c := by abel
#exit

end external

section internal
variable [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
variable (𝒜 : ZMod 2 → Submodule R A) (ℬ : ZMod 2 → Submodule R B)
variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

open DirectSum


variable (R) in
def SuperTensorProduct
    (𝒜 : ZMod 2 → Submodule R A) (ℬ : ZMod 2 → Submodule R B)
    [GradedAlgebra 𝒜] [GradedAlgebra ℬ] :
    Type _ :=
  A ⊗[R] B

scoped[TensorProduct] notation:100 𝒜 " ⊗'[" R "] " ℬ:100 => SuperTensorProduct R 𝒜 ℬ

instance : AddCommGroup (𝒜 ⊗'[R] ℬ) := TensorProduct.addCommGroup
instance : Module R (𝒜 ⊗'[R] ℬ) := TensorProduct.leftModule

instance : One (𝒜 ⊗'[R] ℬ) where one := 1 ⊗ₜ 1


local notation "↥" P => { x // x ∈ P}

#exit

def mul : (𝒜 ⊗'[R] ℬ) →ₗ[R] (𝒜 ⊗'[R] ℬ) →ₗ[R] (𝒜 ⊗'[R] ℬ) := by
  let fA := (decomposeAlgEquiv 𝒜).toLinearEquiv
  let fB := (decomposeAlgEquiv ℬ).toLinearEquiv
  let fAB1 := TensorProduct.congr fA fB
  let fAB2 := TensorProduct.directSum R (𝒜 ·) (ℬ ·)
  let fAB := fAB1 ≪≫ₗ fAB2
  let fAB' := TensorProduct.congr fAB fAB
  letI tAB := fun i : ZMod 2 × ZMod 2 => 𝒜 i.1 ⊗[R] ℬ i.2
  let fAB'' := fAB' ≪≫ₗ TensorProduct.directSum R tAB tAB
  -- refine TensorProduct.curry ?_
  -- refine ?_ ∘ₗ TensorProduct.map fAB.toLinearMap fAB.toLinearMap
  -- `(a_i ⊗ b_j) * (a_k ⊗ b_l) = -1^(jk) • (a_i*a_k ⊗ b_j*b_l)``

  -- refine TensorProduct.uncurry R _ _ _ ∘ₗ TensorProduct.lift ?_
  -- refine TensorProduct.homTensorHomMap R A B A B ∘ₗ TensorProduct.lift ?_
  sorry
