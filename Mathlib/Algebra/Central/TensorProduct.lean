/-
Copyright (c) 2025 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Yunzhou Xie
-/

import Mathlib.Algebra.Central.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!

## Main Results

- `Algebra.IsCentral.left_of_tensor`: If `B` and `C` are nontrivial finite dimensional
  `K`-algebras, and `B ⊗[K] C` is a central algebra over `K`, then `B` is a
  central algebra over `K`.
- `Algebra.IsCentral.right_of_tensor`: If `B` and `C` are nontrivial finite dimensional
  `K`-algebras, and `B ⊗[K] C` is a central algebra over `K`, then `C` is a
  central algebra over `K`.

## Tags
Central Algebras, Central Simple Algebras, Noncommutative Algebra
-/

universe u v

open TensorProduct

variable (K : Type u) [Field K]

namespace Algebra.IsCentral

lemma left_of_tensor (B C : Type v)
    [Ring B] [Ring C] [Nontrivial B] [Nontrivial C] [Algebra K C] [Algebra K B]
    [FiniteDimensional K B] [hbc : Algebra.IsCentral K (B ⊗[K] C)] :
    IsCentral K B := by
  letI : Nontrivial (B ⊗[K] C) := Module.FaithfullyFlat.lTensor_nontrivial _ _ _
  have : (Algebra.TensorProduct.includeLeft.comp (Subalgebra.center K B).val).range ≤
    Subalgebra.center K (B ⊗[K] C) := fun x hx ↦ by
    simp only [AlgHom.mem_range, AlgHom.coe_comp, Subalgebra.coe_val, Function.comp_apply,
      Algebra.TensorProduct.includeLeft_apply, Subtype.exists, exists_prop] at hx
    obtain ⟨b, hb0, hb⟩ := hx
    rw [Subalgebra.mem_center_iff] at hb0 ⊢
    intro bc
    induction bc using TensorProduct.induction_on with
    | zero => simp
    | tmul b' c =>
      subst hb
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      congr 1
      exact hb0 b'
    | add _ _ _ _ => simp_all [add_mul, mul_add]
  have eq: (Algebra.TensorProduct.includeLeft.comp (Subalgebra.center K B).val).range =
      (⊥ : Subalgebra K (B ⊗[K] C)) := by
    refine le_antisymm ?_ <| OrderBot.bot_le _
    rw [← hbc.center_eq_bot]; exact this
  let f : Subalgebra.center K B →ₐ[K] ((Algebra.TensorProduct.includeLeft (R := K) (B := C)).comp
    (Subalgebra.center K B).val).range := {
      toFun := fun ⟨b, hb⟩ ↦ ⟨b ⊗ₜ 1, ⟨⟨b, hb⟩, rfl⟩⟩
      map_one' := by simp; rfl
      map_mul' := fun _ _ ↦ by ext : 1; simp
      map_zero' := by ext; simp
      map_add' := fun _ _ ↦ by ext; simp [add_tmul]
      commutes' := fun _ ↦ rfl}
  have f_surj : Function.Surjective f := fun ⟨bc, ⟨⟨b, hb⟩, h⟩⟩ ↦ ⟨⟨b, hb⟩, by
    simp [f]
    change _ ⊗ₜ _ = _ at h
    simp only [RingHom.coe_coe, Subalgebra.coe_val] at h⊢
    exact h⟩
  have e : ((Algebra.TensorProduct.includeLeft (R := K) (B := C)).comp
    (Subalgebra.center K B).val).range ≃ₐ[K] (Subalgebra.center K B) :=
    (AlgEquiv.ofBijective f
    ⟨fun ⟨b1, hb1⟩ ⟨b2, hb2⟩ h12 ↦ by
      simp only [AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
        Subtype.mk.injEq, f] at h12
      ext ; simp only [f]
      exact Algebra.TensorProduct.includeLeft_injective (R := K) (S := K)
        (NoZeroSMulDivisors.algebraMap_injective K C) h12,
    f_surj⟩).symm
  have e2 := Subalgebra.equivOfEq _ _ eq |>.trans <| Algebra.botEquiv K _
  have ee : Subalgebra.center K B ≃ₐ[K] K := e.symm.trans e2
  exact ⟨le_of_eq <| Subalgebra.eq_of_le_of_finrank_eq (OrderBot.bot_le _)
    (by rw [ee.toLinearEquiv.finrank_eq, Subalgebra.finrank_bot, Module.finrank_self])|>.symm⟩

lemma right_of_tensor (B C : Type v) [Ring B] [Ring C] [Nontrivial B] [Nontrivial C]
    [Algebra K C] [Algebra K B] [FiniteDimensional K C] [Algebra.IsCentral K (B ⊗[K] C)] :
    IsCentral K C :=
  letI : IsCentral K (C ⊗[K] B) := IsCentral.of_algEquiv K _ _ <| Algebra.TensorProduct.comm _ _ _
  left_of_tensor K C B

end Algebra.IsCentral
