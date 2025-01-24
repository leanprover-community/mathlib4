/-
Copyright (c) 2024 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison
-/

import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Generators

/-!
Documentation
-/

namespace exteriorPower

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem mul_ιMulti {k l : ℕ} (v : Fin k → M) (w : Fin l → M) :
  (ιMulti R k v : ExteriorAlgebra R M) * (ιMulti R l w) =
  (ιMulti R (k+l) <| Fin.append v w) := by
  simp only [ιMulti_apply, ExteriorAlgebra.ιMulti_apply]
  rw [← List.prod_append]
  congr
  rw [← List.ofFn_fin_append]
  congr
  ext x
  cases' lt_or_ge (x : ℕ) k with h h
  · rw [← Fin.castAdd_castLT (i := x) l h]
    simp only [Fin.append_left]
  · rw [← Fin.natAdd_subNat_cast h]
    simp only [Fin.append_right]

theorem mul_ιMulti_degree {k l : ℕ} (v : Fin k → M) (w : Fin l → M) :
  ((ιMulti R k v) : ExteriorAlgebra R M) * (ιMulti R l w) ∈ ⋀[R]^(k+l) M := by
  rw [mul_ιMulti]
  exact (Set.range_subset_iff.mp (ExteriorAlgebra.ιMulti_range R _)) _

theorem mul_degreeAux {k l : ℕ} (v : Fin k → M) (β : ⋀[R]^l M) [Module.Finite R M] :
  ((ιMulti R k v) : ExteriorAlgebra R M) * β ∈ ⋀[R]^(k+l) M := by
  obtain ⟨n, s, h⟩ := Module.Finite.exists_fin (R := R) (M := M)
  apply Submodule.span_induction (R := R) (M := ⋀[R]^l M) (p := fun b _ ↦
    ((ιMulti R k v) : ExteriorAlgebra R M) * b ∈ ⋀[R]^(k+l) M)
    (s := Set.range (ιMulti_family R l s))
  · intro x hx
    obtain ⟨s, rfl⟩ := Set.mem_range.mp hx
    unfold ιMulti_family
    apply mul_ιMulti_degree
  · simp_all only [ιMulti_apply, ZeroMemClass.coe_zero, mul_zero, Submodule.zero_mem]
  · intro x y _ _ h1 h2
    simp only [Submodule.coe_add, mul_add, Submodule.add_mem (⋀[R]^(k + l) M) h1 h2]
  · intro a x _ h1
    simp only [Submodule.coe_smul, mul_smul_comm, Submodule.smul_mem _ a h1]
  · simp only [h, span_top_of_span_top', Submodule.mem_top]

theorem mul_degree {k l : ℕ} (α : ⋀[R]^k M) (β : ⋀[R]^l M) [Module.Finite R M] :
  (α : ExteriorAlgebra R M) * β ∈ ⋀[R]^(k+l) M := by
  obtain ⟨n, s, h⟩ := Module.Finite.exists_fin (R := R) (M := M)
  apply Submodule.span_induction (R := R) (M := ⋀[R]^k M) (p := fun a _ ↦
    (a : ExteriorAlgebra R M) * β ∈ ⋀[R]^(k+l) M)
    (s := Set.range (ιMulti_family R k s))
  · intro x hx
    obtain ⟨s, rfl⟩ := Set.mem_range.mp hx
    unfold ιMulti_family
    apply mul_degreeAux
  · simp_all only [ιMulti_apply, ZeroMemClass.coe_zero, zero_mul, Submodule.zero_mem]
  · intro x y _ _ h1 h2
    simp only [Submodule.coe_add, add_mul, Submodule.add_mem (⋀[R]^(k + l) M) h1 h2]
  · intro a x _ h1
    simp only [SetLike.val_smul, Algebra.smul_mul_assoc, Submodule.smul_mem _ a h1]
  · simp only [h, span_top_of_span_top', Submodule.mem_top]

def WedgeProduct {k l : ℕ} [Module.Finite R M] :
  (⋀[R]^k M) →ₗ[R] (⋀[R]^l M) →ₗ[R] (⋀[R]^(k+l) M) where
  toFun α := {
    toFun := fun β ↦ ⟨α * β, mul_degree α β⟩
    map_add' := by
      intro x y
      simp only [Submodule.coe_add, mul_add, AddMemClass.mk_add_mk]
    map_smul' := by
      intro a x
      simp only [SetLike.val_smul, Algebra.mul_smul_comm, RingHom.id_apply, SetLike.mk_smul_mk]
  }
  map_add' := by
    intro x y
    ext z
    dsimp
    rw [add_mul]
  map_smul' := by
    intro a x
    ext y
    dsimp
    rw [Algebra.smul_mul_assoc]

end exteriorPower
