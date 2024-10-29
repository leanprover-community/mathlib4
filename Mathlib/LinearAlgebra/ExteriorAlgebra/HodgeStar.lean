/-
Copyright (c) 2024 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison
-/

import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
Documentation
-/
/-
Hodge star operator or Hodge star is a linear map defined on the exterior algebra of a
finite-dimensional oriented vector space endowed with a nondegenerate symmetric bilinear form.

α = ⋀ α_i , β = ⋀ β_i ∈ ⋀ᵏ V
⟨α , β⟩ = det( ⟨α_i , β_j⟩ )

{e_i} orthonormal basis for V
ω = ⋀ e_i
α ∧ ⋆β = ⟨α , β⟩ ω
-/

open ExteriorAlgebra BigOperators

namespace exteriorPower

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable {I : Type*} [LinearOrder I] [Fintype I]
variable {n : ℕ}

/-- If `b` is a basis of `M` (indexed by a linearly ordered type), the basis of the `n`th
exterior power of `M` formed by the `n`-fold exterior products of elements of `b`. -/
noncomputable def _root_.Basis.exteriorPower {I : Type*} [LinearOrder I] (b : Basis I R M) :
    Basis {s : Finset I // Finset.card s = n} R (⋀[R]^n M) := sorry --From SM.ExteriorPower

def ιMulti : M [⋀^Fin n]→ₗ[R] (⋀[R]^n M) :=
  (ExteriorAlgebra.ιMulti R n).codRestrict (⋀[R]^n M) fun _ =>
    ExteriorAlgebra.ιMulti_range R n <| Set.mem_range_self _

noncomputable def ιMulti_family {I : Type*} [LinearOrder I] (v : I → M) :
    {s : Finset I // Finset.card s = n} → ⋀[R]^n M :=
  fun ⟨s, hs⟩ => ιMulti (fun i => v (Finset.orderIsoOfFin s hs i))

/-
noncomputable def preForm (b : Basis I R M) (B : LinearMap.BilinForm R M)
  (s t : Finset I) (hs : Finset.card s = n) (ht : Finset.card t = n) : R :=
  ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ •
  ∏ i : Fin n, B (b (Finset.orderIsoOfFin s hs (σ i))) (b (Finset.orderIsoOfFin t ht i))

noncomputable def inducedForm' (B : LinearMap.BilinForm R M) (b : Basis I R M) :
  ⋀[R]^n M → ⋀[R]^n M → R := fun v w ↦ ∑ i : {s : Finset I // Finset.card s = n},
  ∑ j : {s : Finset I // Finset.card s = n},
  (b.exteriorPower.coord i v * b.exteriorPower.coord j w) •
  preForm b B i.val j.val i.property j.property

noncomputable def inducedForm' (B : LinearMap.BilinForm R M) (b : Basis I R M) :
  ⋀[R]^n M → ⋀[R]^n M → R := fun v w ↦ ∑ i : {s : Finset I // Finset.card s = n},
  ∑ j : {s : Finset I // Finset.card s = n},
  (b.exteriorPower.coord i v * b.exteriorPower.coord j w) •
  ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ •
  ∏ k : Fin n, B (b (Finset.orderIsoOfFin i.val i.property (σ k)))
  (b (Finset.orderIsoOfFin j.val j.property k))
-/

section inducedForm

noncomputable def inducedForm (B : LinearMap.BilinForm R M) (b : Basis I R M) :
  ⋀[R]^n M → ⋀[R]^n M → R := fun v w ↦ ∑ s : {s : Finset I // Finset.card s = n},
  ∑ t : {s : Finset I // Finset.card s = n},
  (b.exteriorPower.coord s v * b.exteriorPower.coord t w) •
  Matrix.det (fun i j ↦ B (b (Finset.orderIsoOfFin s.val s.property i))
  (b (Finset.orderIsoOfFin t.val t.property j)) )

theorem induced_add_left (B : LinearMap.BilinForm R M) (b : Basis I R M) : ∀ u v w : ⋀[R]^n M,
  inducedForm B b (u + v) w = inducedForm B b u w + inducedForm B b v w := by
  intro u v w
  unfold inducedForm
  simp only [map_add, add_mul, add_smul, Finset.sum_add_distrib]

theorem induced_add_right (B : LinearMap.BilinForm R M) (b : Basis I R M) : ∀ u v w : ⋀[R]^n M,
  inducedForm B b u (v + w) = inducedForm B b u v + inducedForm B b u w := by
  intro u v w
  unfold inducedForm
  simp only [map_add, mul_add, add_smul, Finset.sum_add_distrib]

theorem induced_smul_left (B : LinearMap.BilinForm R M) (b : Basis I R M) : ∀ r : R,
  ∀ v w : ⋀[R]^n M, inducedForm B b (r • v) w = r • inducedForm B b v w := by
  intro r v w
  unfold inducedForm
  simp only [map_smul, smul_mul_assoc, smul_assoc, Finset.smul_sum]

theorem induced_smul_right (B : LinearMap.BilinForm R M) (b : Basis I R M) : ∀ r : R,
  ∀ v w : ⋀[R]^n M, inducedForm B b v (r • w) = r • inducedForm B b v w := by
  intro r v w
  unfold inducedForm
  simp only [map_smul, mul_smul_comm, smul_assoc, Finset.smul_sum]

noncomputable def inducedBilinForm (B : LinearMap.BilinForm R M) (b : Basis I R M) :
  LinearMap.BilinForm R <| ⋀[R]^n M where
  toFun := fun v ↦ {
    toFun := fun w ↦ inducedForm B b v w,
    map_add' := induced_add_right B b v,
    map_smul' := fun r w ↦ induced_smul_right B b r v w
  }
  map_add' := by intro u v; ext w; exact induced_add_left B b u v w
  map_smul' := by intro r v; ext w; exact induced_smul_left B b r v w

end inducedForm

section ringProperties

noncomputable abbrev bExterior (n : ℕ) (b : Basis I R M) := @Basis.exteriorPower _ _ _ _ _ n _ _ b
variable (B : LinearMap.BilinForm R M) (b : Basis I R M)
local notation "⟪" x ", " y "⟫" => @inducedForm _ _ _ _ _ _ _ _ n B b x y

theorem induced_symm (h : B.IsSymm) :
  ∀ v w : ⋀[R]^n M, ⟪v, w⟫ = ⟪w, v⟫ := by
  intro v w
  unfold inducedForm
  rw [Finset.sum_comm]
  congr; ext s; congr; ext t
  rw [mul_comm, ← Matrix.det_transpose]
  congr; ext i j
  rw [LinearMap.BilinForm.IsSymm.eq h, Matrix.transpose_apply]

theorem inducedBilin_symm (h : B.IsSymm) :
  (@inducedBilinForm _ _ _ _ _ _ _ _ n B b).IsSymm := by
  intro v w
  rw [RingHom.id_apply]
  unfold inducedBilinForm
  dsimp
  exact induced_symm B b h v w

theorem inducedForm_basis (s t : {a : Finset I // a.card = n}) :
  ⟪bExterior n b s, bExterior n b t⟫ = Matrix.det (fun i j ↦
  B (b (s.1.orderIsoOfFin s.property i)) (b (t.1.orderIsoOfFin t.property j)) ) := by
  unfold inducedForm
  simp only [Basis.coord_apply, Basis.repr_self_apply, ite_smul, mul_ite,
  mul_one, Finset.coe_orderIsoOfFin_apply, smul_eq_mul, ite_mul, one_mul, zero_mul,
  mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

end ringProperties

section fieldOrthoProperties

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {I : Type*} [LinearOrder I] [Fintype I]
variable (B : LinearMap.BilinForm K V) (b : Basis I K V)

local notation "⟪" x ", " y "⟫" => @inducedForm _ _ _ _ _ _ _ _ n B b x y

theorem ortho_aux (s t : {a : Finset I // a.card = n}) (h : s ≠ t) :
  ∃ (i : Fin n), (∀ (j : Fin n), 1=1) := by


  sorry

theorem inducedBilin_ortho (h : LinearMap.IsOrthoᵢ B b) :
  LinearMap.IsOrthoᵢ (inducedBilinForm B b) (bExterior n b) := by
  rw [LinearMap.isOrthoᵢ_def]
  intro s t hst
  unfold inducedBilinForm
  dsimp
  simp only [inducedForm_basis, Finset.coe_orderIsoOfFin_apply]

  sorry

theorem induced_nondegenerate (hB : B.Nondegenerate) :
  ∀ (v : ⋀[K]^n V), (∀ (w : ⋀[K]^n V), ⟪v, w⟫ = 0) → v = 0 := by
  intro v h'


  sorry

theorem inducedBilin_nondegenerate (hB : B.Nondegenerate) :
  (@inducedBilinForm _ _ _ _ _ _ _ _ n B b).Nondegenerate := induced_nondegenerate B b hB



end fieldOrthoProperties

end exteriorPower
