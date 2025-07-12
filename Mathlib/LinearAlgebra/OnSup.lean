/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/

import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Extending linear maps to sums of modules

Let `R` be a ring, `M, N` be `A`-modules, and `P, Q` be `A`-submodules of `X`.

Given two linear maps `f : P →ₗ[A] N` and `g : Q →ₗ[A] N` that agree on `P ⊓ Q`,
there is a unique linear map `P ⊔ Q →ₗ[R] N` that simultaneously extends `f` and `g`.

## Main definitions
* `Submodule.quotientCoprodAddEquiv`: if `P` and `Q` are two `R`-submodules of `M`, then the
  quotient `(P × Q) / ker (fun ((p, q) : P × Q) ↦ p + q)` is isomorphic to `P ⊔ Q` as an `R`-module.
* `LinearMap.onSup`: given two linear maps `f : P →ₗ[R] N` and `g : Q →ₗ[R] N` that agree on
  `P ⊓ Q`, this is the linear map `P ⊔ Q →ₗ[R] N` that simultaneously extends `f` and `g`.
* `LinearMap.onSupEquiv`: the bijection between the set of linear maps `P + Q →ₗ[R] N` and the
  set of pairs of linear maps `(P →ₗ[R] N) × (Q →ₗ[R] N))` that agree on the intersection `P ⊓ Q`.
* `LinearMap.onSupLinearEquiv`: the `R`-linear equivalence between the module of linear maps
  `P ⊔ Q →ₗ[R] N` and the module of pairs of linear maps `(P →ₗ[R] N) × (Q →ₗ[R] N))` that agree
  on the intersection `M ⊓ N`. This requires `R` to be commutative.

## Main results
* `LinearMap.onSup_unique` : if `u : P ⊔ R →ₗ[R] N` extends both `f` and `g`, then it agrees
  with `LinearMap.onSup`.

-/

section onSup

open Function LinearEquiv LinearMap Submodule

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {P Q : Submodule R M}

/-- If `P` and `Q` are two `R`-submodules of `M`, then the quotient
  `(P × Q) / ker (fun ((p, q) : P × Q) ↦ p + q)` is isomorphic to `P ⊔ Q` as an `R`-module. -/
noncomputable def Submodule.quotientCoprodAddEquiv :
    ((P × Q) ⧸ (ker ((inclusion (le_sup_left (b := Q))).coprod
      (inclusion (le_sup_right (a := P)))))) ≃ₗ[R] (P + Q) :=
  quotKerEquivOfSurjective _ (by
    rw [← range_eq_top, eq_top_iff]
    rintro ⟨x, hx⟩ _
    obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup.mp hx
    use ⟨⟨y, hy⟩, ⟨z, hz⟩⟩
    simp [coprod_apply, ← Subtype.coe_inj, coe_add, coe_inclusion])

namespace LinearMap

variable {N : Type*} [AddCommGroup N] [Module R N] {f : P →ₗ[R] N} {g : Q →ₗ[R] N}

/-- Given two linear maps `f : P →ₗ[R] N` and `g : Q →ₗ[R] N` that agree on `P ⊓ Q`, this is
the linear map `P ⊔ Q →ₗ[R] N` that simultaneously extends `f` and `g`. -/
noncomputable def onSup
    (h : f ∘ₗ inclusion inf_le_left = g ∘ₗ inclusion inf_le_right) :
    ↥(P ⊔ Q) →ₗ[R] N := by
  apply comp ((ker _).liftQ (f.coprod g) ?_) quotientCoprodAddEquiv.symm.toLinearMap
  rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ hxy
  simp only [mem_ker, coprod_apply, add_eq_zero_iff_eq_neg, ← Subtype.coe_inj, coe_inclusion,
    NegMemClass.coe_neg] at hxy
  simp only [mem_ker, coprod_apply, add_eq_zero_iff_eq_neg, ← map_neg]
  have hx' : x ∈ P ⊓ Q := ⟨hx, by simp [hxy, hy]⟩
  rw [show ⟨x, hx⟩ = inclusion inf_le_left ⟨x , hx'⟩ by simp [← Subtype.coe_inj]]
  rw [show -⟨y, hy⟩ = inclusion inf_le_right ⟨x, hx'⟩ by simp [← Subtype.coe_inj, hxy]]
  simp only [← LinearMap.comp_apply, h]

theorem onSup_apply_left
    (h : f ∘ₗ inclusion inf_le_left = g ∘ₗ inclusion inf_le_right)
    {x : M} (hx : x ∈ P) : onSup h ⟨x, le_sup_left (b := Q) hx⟩ = f ⟨x, hx⟩ := by
  have h : (quotientCoprodAddEquiv (P := P) (Q := Q)).symm ⟨x, le_sup_left (b := Q) hx⟩ =
      Submodule.Quotient.mk ⟨⟨x, hx⟩, (0 : Q)⟩ := by
    simp [symm_apply_eq, quotientCoprodAddEquiv, quotKerEquivOfSurjective, inclusion_apply]
  simp only [add_eq_sup, onSup, comp_apply] at h ⊢
  simp [h, liftQ_apply]

theorem onSup_apply_right
    (h : f ∘ₗ inclusion inf_le_left = g ∘ₗ inclusion inf_le_right)
    {x} (hx : x ∈ Q) : onSup h ⟨x, le_sup_right (a := P) hx⟩ = g ⟨x, hx⟩ := by
  have h : (quotientCoprodAddEquiv (P := P) (Q := Q)).symm ⟨x, le_sup_right (a := P) hx⟩ =
      Submodule.Quotient.mk ⟨(0 : P), ⟨x, hx⟩⟩ := by
    simp [symm_apply_eq, quotientCoprodAddEquiv, quotKerEquivOfSurjective, inclusion_apply]
  simp only [add_eq_sup, onSup, comp_apply] at h ⊢
  simp [h, liftQ_apply]

theorem onSup_apply
    (h : f ∘ₗ inclusion inf_le_left = g ∘ₗ inclusion inf_le_right)
    {x y} (hx : x ∈ P) (hy : y ∈ Q) :
    onSup h ⟨x + y, add_mem_sup hx hy⟩ = f ⟨x, hx⟩ + g ⟨y, hy⟩ := by
  simp [← onSup_apply_left h hx, ← onSup_apply_right h hy, ← map_add]

theorem onSup_comp_left (h : f ∘ₗ inclusion inf_le_left = g ∘ₗ inclusion inf_le_right) :
    (onSup h).comp (inclusion le_sup_left) = f := by
  ext ⟨x, hx⟩
  simp [← onSup_apply_left h, inclusion_apply]

theorem onSup_comp_right (h : f ∘ₗ inclusion inf_le_left = g ∘ₗ inclusion inf_le_right) :
    (onSup h).comp (inclusion le_sup_right) = g := by
  ext ⟨x, hx⟩
  simp [← onSup_apply_right h, inclusion_apply]

@[ext]
theorem sup_ext {f g : ↥(P ⊔ Q) →ₗ[R] N}
    (left : f.comp (inclusion le_sup_left) = g.comp (inclusion le_sup_left))
    (right : f.comp (inclusion le_sup_right) = g.comp (inclusion le_sup_right)) :
    f = g := by
  ext ⟨x, hx⟩
  obtain ⟨y, z, hx'⟩ := Submodule.mem_sup'.mp hx
  suffices (⟨x, hx⟩ : ↥(P ⊔ Q)) = inclusion le_sup_left y + inclusion le_sup_right z by
    simp only [this, map_add, ← LinearMap.comp_apply, left, right]
  simp only [← Subtype.coe_inj, coe_add, coe_inclusion, hx']

theorem onSup_unique
    (h : f ∘ₗ inclusion inf_le_left = g ∘ₗ inclusion inf_le_right)
    {u : ↥(P ⊔ Q) →ₗ[R] N}
    (huf : u.comp (inclusion le_sup_left) = f) (hug : u.comp (inclusion le_sup_right) = g) :
    onSup h = u := by
  ext ⟨x, hx⟩ <;>
    simp only [huf, hug, ← onSup_apply_left h, ← onSup_apply_right h,
      coe_comp, Function.comp_apply] <;>
    congr

variable (M N Y)

/-- The bijection between the set of maps `P ⊔ Q →ₗ[R] N` and the set of pairs of maps
  `(P →ₗ[R] N) × (Q →ₗ[R] N))` that agree on the intersection `P ⊓ Q`. -/
noncomputable def onSupEquiv : (↥(P ⊔ Q) →ₗ[R] N) ≃
    {(fg : (P →ₗ[R] N) × (Q →ₗ[R] N)) | fg.1.comp (inclusion inf_le_left) =
      fg.2.comp (inclusion inf_le_right)} where
  toFun u := ⟨⟨u.comp (inclusion le_sup_left), u.comp (inclusion le_sup_right)⟩, rfl⟩
  invFun h := onSup h.prop
  left_inv u := by
    apply onSup_unique <;> ext <;> rfl
  right_inv h := by
    ext ⟨x, hx⟩ <;> simp
    · rw [← onSup_apply_left h.prop hx]; rfl
    · rw [← onSup_apply_right h.prop hx]; rfl

section Comm

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (P Q : Submodule R M)

/-- The `R`-linear equivalence between the module of linear maps `P ⊔ Q →ₗ[R] N` and the module of
  pairs of linear maps `(P →ₗ[R] N) × (Q →ₗ[R] N))` that agree on the intersection `P ⊓ Q`. -/
noncomputable def onSupLinearEquiv : (↥(P ⊔ Q) →ₗ[R] N) ≃ₗ[R] eqLocus
    ((lcomp R N (inclusion (inf_le_left (a := P) (b := Q)))).comp (fst R _ _))
    ((lcomp R N (inclusion (inf_le_right (a := P) (b := Q)))).comp (snd R _ _)) := {
  onSupEquiv M N (P := P) (Q := Q) (R := R) with
  map_add' u v := by ext <;> rfl
  map_smul' r u := by ext <;> rfl }

end Comm

end LinearMap

end onSup
