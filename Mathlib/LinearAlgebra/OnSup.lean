/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/

import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Extending linear maps to sums of modules

Let `A` be a ring, `X, Y` be `A`-modules, and `M, N` be `A`-submodules of `X`.

Given two linear maps `f : M →ₗ[A] Y` and `g : N →ₗ[A] Y` that agree on `M ∩ N`, there is a unique
linear map `M + N →ₗ[A] Y` that simultaneously extends `f` and `g`.

## Main definitions
* `Submodule.quotientCoprodAddEquiv`: if `M` and `N` are two `A`-submodules of `X`, then the
  quotient `(M × N) / ker (fun ((m, n) : M × N) ↦ m + n)` is isomorphic to `M + N` as an `A`-module.
* `LinearMap.onSup`: given two linear maps `f : M →ₗ[A] Y` and `g : N →ₗ[A] Y` that agree on
  `M ∩ N`, this is the linear map `M + N →ₗ[A] Y` that simultaneously extends `f` and `g`.
* `LinearMap.onSupEquiv`: the bijection between the set of linear maps `M + N →ₗ[A] Y` and the
  set of pairs of linear maps `(M →ₗ[A] Y) × (N →ₗ[A] Y))` that agree on the intersection `M ⊓ N`.
* `LinearMap.onSupLinearEquiv`: the `A`-linear equivalence between the module of linear maps
  `M + N →ₗ[A] Y` and the module of pairs of linear maps `(M →ₗ[A] Y) × (N →ₗ[A] Y))` that agree
  on the intersection `M ⊓ N`. This requires `A` to be commutative.

## Main results
* `LinearMap.onSup_unique` : if `u : M + N →ₗ[A] Y` extends both `f` and `g`, then it agrees
  with `LinearMap.onSup`.

-/

section onSup

open Function LinearEquiv LinearMap Submodule

variable {A X : Type*} [Ring A] [AddCommGroup X] [Module A X] {M N : Submodule A X}

/-- If `M` and `N` are two `A`-submodules of `X`, then the quotient
  `(M × N) / ker (fun ((m, n) : M × N) ↦ m + n)` is isomorphic to `M + N` as an `A`-module. -/
noncomputable def Submodule.quotientCoprodAddEquiv :
    ((M × N) ⧸ (ker ((inclusion (le_sup_left (b := N))).coprod
      (inclusion (le_sup_right (a := M)))))) ≃ₗ[A] (M + N) :=
  quotKerEquivOfSurjective _ (by
    rw [← range_eq_top, eq_top_iff]
    rintro ⟨x, hx⟩ _
    obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup.mp hx
    use ⟨⟨y, hy⟩, ⟨z, hz⟩⟩
    simp [coprod_apply, ← Subtype.coe_inj, coe_add, coe_inclusion])

namespace LinearMap

variable {Y : Type*} [AddCommGroup Y] [Module A Y] {f : M →ₗ[A] Y} {g : N →ₗ[A] Y}

/-- Given two linear maps `f : M →ₗ[A] Y` and `g : N →ₗ[A] Y` that agree on `M ∩ N`, this is
the linear map `M + N →ₗ[A] Y` that simultaneously extends `f` and `g`. -/
noncomputable def onSup (h : ∀ x (hM : x ∈ M) (hN : x ∈ N), f ⟨x, hM⟩ = g ⟨x, hN⟩) :
    M + N →ₗ[A] Y := by
  apply comp ?_ quotientCoprodAddEquiv.symm.toLinearMap
  apply (ker _).liftQ (f.coprod g)
  rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ hxy
  simp only [mem_ker, coprod_apply, add_eq_zero_iff_eq_neg, ← Subtype.coe_inj, coe_inclusion,
    NegMemClass.coe_neg] at hxy
  simp only [mem_ker, coprod_apply, add_eq_zero_iff_eq_neg, ← map_neg]
  have hneg : - (⟨y, hy⟩ : N) = ⟨-y, N.neg_mem hy⟩ := by simp [← Subtype.coe_inj]
  simp_rw [hneg, hxy]
  exact h (-y) (hxy ▸ hx) (N.neg_mem hy)

theorem onSup_apply_left (h : ∀ x (hM : x ∈ M) (hN : x ∈ N), f ⟨x, hM⟩ = g ⟨x, hN⟩)
    {x : X} (hx : x ∈ M) : onSup h ⟨x, le_sup_left (b := N) hx⟩ = f ⟨x, hx⟩ := by
  have h : (quotientCoprodAddEquiv (M := M) (N := N)).symm ⟨x, le_sup_left (b := N) hx⟩ =
      Submodule.Quotient.mk ⟨⟨x, hx⟩, (0 : N)⟩ := by
    rw [symm_apply_eq]
    simp only [add_eq_sup, quotientCoprodAddEquiv, quotKerEquivOfSurjective, trans_apply,
      ofTop_apply, quotKerEquivRange_apply_mk, coprod_apply, map_zero, add_zero, inclusion_apply]
  simp only [add_eq_sup, onSup, comp_apply] at h ⊢
  simp [h, liftQ_apply]

theorem onSup_apply_right (h : ∀ x (hM : x ∈ M) (hN : x ∈ N), f ⟨x, hM⟩ = g ⟨x, hN⟩)
    {x} (hx : x ∈ N) : onSup h ⟨x, le_sup_right (a := M) hx⟩ = g ⟨x, hx⟩ := by
  have h : (quotientCoprodAddEquiv (M := M) (N := N)).symm ⟨x, le_sup_right (a := M) hx⟩ =
      Submodule.Quotient.mk ⟨(0 : M), ⟨x, hx⟩⟩ := by
    rw [symm_apply_eq]
    simp only [add_eq_sup, quotientCoprodAddEquiv, quotKerEquivOfSurjective, trans_apply,
      ofTop_apply, quotKerEquivRange_apply_mk, coprod_apply, map_zero, zero_add, inclusion_apply]
  simp only [add_eq_sup, onSup, comp_apply] at h ⊢
  simp [h, liftQ_apply]

theorem onSup_apply (h : ∀ x (hM : x ∈ M) (hN : x ∈ N), f ⟨x, hM⟩ = g ⟨x, hN⟩)
    {x y} (hx : x ∈ M) (hy : y ∈ N) :
    onSup h ⟨x + y, add_mem_sup hx hy⟩ = f ⟨x, hx⟩ + g ⟨y, hy⟩ := by
  rw [← onSup_apply_left h hx, ← onSup_apply_right h hy, ← map_add, AddMemClass.mk_add_mk]

theorem onSup_comp_left (h : ∀ x (hM : x ∈ M) (hN : x ∈ N), f ⟨x, hM⟩ = g ⟨x, hN⟩) :
    (onSup h).comp (inclusion le_sup_left) = f := by
  ext ⟨x, hx⟩
  rw [← onSup_apply_left h, comp_apply, inclusion_apply]

theorem onSup_comp_right (h : ∀ x (hM : x ∈ M) (hN : x ∈ N), f ⟨x, hM⟩ = g ⟨x, hN⟩) :
    (onSup h).comp (inclusion le_sup_right) = g := by
  ext ⟨x, hx⟩
  rw [← onSup_apply_right h, comp_apply, inclusion_apply]

theorem onSup_unique (h : ∀ x (hM : x ∈ M) (hN : x ∈ N), f ⟨x, hM⟩ = g ⟨x, hN⟩) {u : M + N →ₗ[A] Y}
    (huf : u.comp (inclusion le_sup_left) = f) (hug : u.comp (inclusion le_sup_right) = g) :
    u = onSup h := by
  ext ⟨x, hx⟩
  obtain ⟨y, hy, z, hz, heq⟩ := mem_sup.mp hx
  have heq : (⟨x, hx⟩ : M + N) = ⟨y, le_sup_left (b := N) hy⟩ + ⟨z, le_sup_right (a := M) hz⟩ := by
    simp [heq]
  rw [heq, map_add, map_add, onSup_apply_left h hy, onSup_apply_right h hz]
  simp only [add_eq_sup, LinearMap.ext_iff, comp_apply, inclusion_apply,
    Subtype.forall] at huf hug ⊢
  rw [huf y hy, hug z hz]


variable (M N Y)

/-- The bijection between the set of maps `M + N →ₗ[A] Y` and the set of pairs of maps
  `(M →ₗ[A] Y) × (N →ₗ[A] Y))` that agree on the intersection `M ⊓ N`. -/
noncomputable def onSupEquiv : (M + N →ₗ[A] Y) ≃
  {(fg : (M →ₗ[A] Y) × (N →ₗ[A] Y)) | fg.1.comp (inclusion inf_le_left) =
    fg.2.comp (inclusion inf_le_right)} := by
  apply Equiv.ofBijective (fun fg ↦ ⟨⟨fg.comp (inclusion (le_sup_left (a := M) (b := N))),
      fg.comp (inclusion (le_sup_right (a := M) (b := N)))⟩, by ext; simp [inclusion_apply]⟩)
  · constructor
    · intros f g hfg
      simp only [Set.coe_setOf, Set.mem_setOf_eq, add_eq_sup, Subtype.mk.injEq, Prod.mk.injEq,
        LinearMap.ext_iff, coe_comp, Function.comp_apply, inclusion_apply] at hfg
      ext ⟨mn, hmn⟩
      simp only [add_eq_sup, sup_eq_range, mem_range] at hmn
      obtain ⟨mn, rfl⟩ := hmn
      have heq : (⟨(mn.1 : X) + (mn.2 : X), hmn⟩ : M + N) =
        ⟨mn.1, le_sup_left (a := M) mn.1.2⟩ + ⟨mn.2, le_sup_right (a := M) mn.2.2⟩ := rfl
      simp only [add_eq_sup, coprod_apply, subtype_apply]
      rw [heq, map_add, map_add, hfg.1 mn.1, hfg.2 mn.2]
    · rintro ⟨fg, hfg⟩
      have h : ∀ x (hM : x ∈ M) (hN : x ∈ N), fg.1 ⟨x, hM⟩ = fg.2 ⟨x, hN⟩ := by
        simp only [Set.mem_setOf_eq] at hfg
        intro x hxM hxN
        have hf1 : fg.1 (⟨x, hxM⟩ : M) = (fg.1 ∘ₗ (inclusion inf_le_left)) ⟨x, ⟨hxM, hxN⟩⟩ := rfl
        rw [hf1, hfg]
        rfl
      use onSup h
      simp only [Set.coe_setOf, Set.mem_setOf_eq, add_eq_sup, Subtype.mk.injEq]
      rw [onSup_comp_left, onSup_comp_right]

section Comm

variable {A X Y : Type*} [CommRing A] [AddCommGroup X] [Module A X]
  [AddCommGroup Y] [Module A Y] (M N : Submodule A X)

/-- The `A`-linear equivalence between the module of linear maps `M + N →ₗ[A] Y` and the module of
  pairs of linear maps `(M →ₗ[A] Y) × (N →ₗ[A] Y))` that agree on the intersection `M ⊓ N`. -/
noncomputable def onSupLinearEquiv : (M + N →ₗ[A] Y) ≃ₗ[A] eqLocus
    ((lcomp A Y (inclusion (inf_le_left (a := M) (b := N)))).comp (fst A _ _))
    ((lcomp A Y (inclusion (inf_le_right (a := M) (b := N)))).comp (snd A _ _)) :=
  ofBijective (codRestrict _ ((lcomp A Y (inclusion le_sup_left)).prod
      (lcomp A Y (inclusion le_sup_right))) (fun _ ↦ by ext; simp [inclusion_apply]))
    (onSupEquiv M N Y).bijective

end Comm

end LinearMap

end onSup
