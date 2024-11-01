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

noncomputable def inducedForm (B : LinearMap.BilinForm R M) (b : Basis I R M) :
  ⋀[R]^k M → ⋀[R]^k M → R := fun v w ↦ ∑ s : {s : Finset I // Finset.card s = k},
  ∑ t : {s : Finset I // Finset.card s = k},
  (b.exteriorPower.coord s v * b.exteriorPower.coord t w) *
  Matrix.det (fun i j ↦ B (b (Finset.orderIsoOfFin s.val s.property i))
  (b (Finset.orderIsoOfFin t.val t.property j)) )

theorem induced_add_left (B : LinearMap.BilinForm R M) (b : Basis I R M) : ∀ u v w : ⋀[R]^k M,
  inducedForm B b (u + v) w = inducedForm B b u w + inducedForm B b v w := by
  intro u v w
  unfold inducedForm
  simp only [map_add, add_mul, add_smul, Finset.sum_add_distrib]

theorem induced_add_right (B : LinearMap.BilinForm R M) (b : Basis I R M) : ∀ u v w : ⋀[R]^k M,
  inducedForm B b u (v + w) = inducedForm B b u v + inducedForm B b u w := by
  intro u v w
  unfold inducedForm
  simp only [map_add, mul_add, add_mul, Finset.sum_add_distrib]

theorem induced_smul_left (B : LinearMap.BilinForm R M) (b : Basis I R M) :
  ∀ r : R, ∀ v w : ⋀[R]^k M, inducedForm B b (r • v) w = r • inducedForm B b v w := by
  intro r v w
  unfold inducedForm
  simp only [map_smul, smul_mul_assoc, smul_assoc, Finset.smul_sum]

theorem induced_smul_right (B : LinearMap.BilinForm R M) (b : Basis I R M) :
  ∀ r : R, ∀ v w : ⋀[R]^k M, inducedForm B b v (r • w) = r • inducedForm B b v w := by
  intro r v w
  unfold inducedForm
  simp only [map_smul, smul_mul_assoc, mul_smul_comm, Finset.smul_sum]


noncomputable def inducedBilinForm (k : ℕ) (B : LinearMap.BilinForm R M) (b : Basis I R M) :
  LinearMap.BilinForm R <| ⋀[R]^k M where
  toFun := fun v ↦ {
    toFun := fun w ↦ inducedForm B b v w,
    map_add' := induced_add_right B b v,
    map_smul' := fun r w ↦ induced_smul_right B b r v w
  }
  map_add' := by intro u v; ext w; exact induced_add_left B b u v w
  map_smul' := by intro r v; ext w; exact induced_smul_left B b r v w

theorem inducedBilin_apply (k : ℕ) (B : LinearMap.BilinForm R M) (b : Basis I R M) :
  ∀ v w : ⋀[R]^k M, inducedBilinForm k B b v w = inducedForm B b v w := by
  intro v w
  rfl

end inducedForm

section ringProperties

variable (B : LinearMap.BilinForm R M) (b : Basis I R M)
local notation "⟪" x ", " y "⟫" => @inducedForm _ _ _ _ _ _ _ _ k B b x y

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
  (@inducedBilinForm _ _ _ _ _ _ _ _ k B b).IsSymm := by
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

#check ιMulti_family

theorem inducedForm_ιMulti_basis (s t : {a : Finset I // a.card = k}) :
  ⟪ιMulti_family b s, ιMulti_family b t⟫ = ⟪b.exteriorPower s, b.exteriorPower t⟫ := by
  simp only [← ιMulti_family_of_basis]

theorem inducedForm_ιMulti_family (v w : I → M) (s t : {a : Finset I // a.card = k}) :
  ⟪ιMulti_family v s, ιMulti_family w t⟫ = Matrix.det (fun i j ↦
  B (v (s.1.orderIsoOfFin s.property i)) (w (t.1.orderIsoOfFin t.property j)) ) := by


  sorry

end ringProperties

end exteriorPower
