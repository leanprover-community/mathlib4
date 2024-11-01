/-
Copyright (c) 2024 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison
-/

import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.ExteriorAlgebra.Temp

/-!
Documentation
-/

open ExteriorAlgebra BigOperators

namespace exteriorPower

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable {I : Type*} [LinearOrder I] [Fintype I]
variable {k : ℕ}

section inducedForm

noncomputable def inducedForm (B : LinearMap.BilinForm R M) (b₁ b₂ : Basis I R M) :
  ⋀[R]^k M → ⋀[R]^k M → R := fun v w ↦ ∑ s : {s : Finset I // Finset.card s = k},
  ∑ t : {s : Finset I // Finset.card s = k},
  (b₁.exteriorPower.coord s v * b₂.exteriorPower.coord t w) *
  Matrix.det (fun i j ↦ B (b₁ (Finset.orderIsoOfFin s.val s.property i))
  (b₂ (Finset.orderIsoOfFin t.val t.property j)) )

theorem induced_add_left (B : LinearMap.BilinForm R M) (b₁ b₂ : Basis I R M) : ∀ u v w : ⋀[R]^k M,
  inducedForm B b₁ b₂ (u + v) w = inducedForm B b₁ b₂ u w + inducedForm B b₁ b₂ v w := by
  intro u v w
  unfold inducedForm
  simp only [map_add, add_mul, add_smul, Finset.sum_add_distrib]

theorem induced_add_right (B : LinearMap.BilinForm R M) (b₁ b₂ : Basis I R M) : ∀ u v w : ⋀[R]^k M,
  inducedForm B b₁ b₂ u (v + w) = inducedForm B b₁ b₂ u v + inducedForm B b₁ b₂ u w := by
  intro u v w
  unfold inducedForm
  simp only [map_add, mul_add, add_mul, Finset.sum_add_distrib]

theorem induced_smul_left (B : LinearMap.BilinForm R M) (b₁ b₂ : Basis I R M) :
  ∀ r : R, ∀ v w : ⋀[R]^k M, inducedForm B b₁ b₂ (r • v) w = r • inducedForm B b₁ b₂ v w := by
  intro r v w
  unfold inducedForm
  simp only [map_smul, smul_mul_assoc, smul_assoc, Finset.smul_sum]

theorem induced_smul_right (B : LinearMap.BilinForm R M) (b₁ b₂ : Basis I R M) :
  ∀ r : R, ∀ v w : ⋀[R]^k M, inducedForm B b₁ b₂ v (r • w) = r • inducedForm B b₁ b₂ v w := by
  intro r v w
  unfold inducedForm
  simp only [map_smul, smul_mul_assoc, mul_smul_comm, Finset.smul_sum]

noncomputable def inducedBilinForm (k : ℕ) (B : LinearMap.BilinForm R M) (b₁ b₂ : Basis I R M) :
  LinearMap.BilinForm R <| ⋀[R]^k M where
  toFun := fun v ↦ {
    toFun := fun w ↦ inducedForm B b₁ b₂ v w,
    map_add' := induced_add_right B b₁ b₂ v,
    map_smul' := fun r w ↦ induced_smul_right B b₁ b₂ r v w
  }
  map_add' := by intro u v; ext w; exact induced_add_left B b₁ b₂ u v w
  map_smul' := by intro r v; ext w; exact induced_smul_left B b₁ b₂ r v w

theorem inducedBilin_apply (k : ℕ) (B : LinearMap.BilinForm R M) (b₁ b₂ : Basis I R M) :
  ∀ v w : ⋀[R]^k M, inducedBilinForm k B b₁ b₂ v w = inducedForm B b₁ b₂ v w := by
  intro v w
  rfl

end inducedForm

section equivalence

variable (B : LinearMap.BilinForm R M) (b₁ c₁ b₂ c₂ : Basis I R M) {k : ℕ}
local notation "⟪" x ", " y "⟫₁" => @inducedForm _ _ _ _ _ _ _ _ k B b₁ c₁ x y
local notation "⟪" x ", " y "⟫₂" => @inducedForm _ _ _ _ _ _ _ _ k B b₂ c₂ x y

theorem independent_of_basis : inducedBilinForm k B b₁ c₁ = inducedBilinForm k B b₂ c₂ := by
  apply LinearMap.ext_basis b₁.exteriorPower c₁.exteriorPower
  intro s t
  simp only [inducedBilin_apply]
  unfold inducedForm
  congr; ext u; congr; ext v



  sorry

#check LinearMap.ext_basis
#check LinearMap.BilinForm.ext_basis
#check Basis.sum_repr

end equivalence

section ringProperties

variable (B : LinearMap.BilinForm R M) (b : Basis I R M)
local notation "⟪" x ", " y "⟫" => @inducedForm _ _ _ _ _ _ _ _ k B b b x y

theorem induced_symm (h : B.IsSymm) :
  ∀ v w : ⋀[R]^k M, ⟪v, w⟫ = ⟪w, v⟫ := by
  intro v w
  unfold inducedForm
  rw [Finset.sum_comm]
  congr; ext s; congr; ext t
  nth_rw 2 [mul_comm]
  rw [← Matrix.det_transpose]
  congr; ext i j
  rw [Matrix.transpose_apply]
  rw [LinearMap.BilinForm.IsSymm.eq h]

theorem inducedBilin_symm (h : B.IsSymm) :
  (@inducedBilinForm _ _ _ _ _ _ _ _ k B b b).IsSymm := by
  intro v w
  rw [RingHom.id_apply]
  unfold inducedBilinForm
  dsimp
  exact induced_symm B b h v w

theorem inducedForm_basis (s t : {a : Finset I // a.card = k}) :
  ⟪b.exteriorPower s, b.exteriorPower t⟫ = Matrix.det (fun i j ↦
  B (b (s.1.orderIsoOfFin s.property i)) (b (t.1.orderIsoOfFin t.property j)) ) := by
  unfold inducedForm
  simp only [Basis.coord_apply, Basis.repr_self_apply, ite_smul, mul_ite,
  mul_one, Finset.coe_orderIsoOfFin_apply, smul_eq_mul, ite_mul, one_mul, zero_mul,
  mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

end ringProperties

end exteriorPower
