/-
Copyright (c) 2023 Antoine Chambetr-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambetr-Loir
-/

import Mathlib.LinearAlgebra.TensorProduct
import Mathlib.LinearAlgebra.Quotient

/-! # Right exactness properties of tensor product

* For linear maps `f : M →ₗ[R] N`  and `g : N →ₗ[R] P`, `Exact f g` says that `range f = ker g``

* `TensorProduct.rTensor_exact` says that one can tensor a short exact sequence on the right

* `TensorProduct.lTensor_exact` says that one can tensor a short exact sequence on the left

* `TensorProduct.map_ker` computes the kernel of `TensorProduct.map g g'`
in the presence of two short exact sequences.

The proofs are those of Bourbaki, Algèbre, chap. 2, §3, n°6

## TODO

Add

* Special case for short exact sequences of the form `M → N → N/M → 0`

* Analogue for morphisms of algebras

* Treat the noncommutative case

* Treat the case of semirings (need to know what a short exact sequence is)

-/


namespace AddMonoidHom

def Exact {M N P : Type _} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  (f : outParam (M →+ N)) (g : outParam (N →+ P)) :=
  ∀ y, y ∈ g.ker ↔ y ∈ f.range

end AddMonoidHom

namespace LinearMap

open AddMonoidHom LinearMap

variable (R : Type _) [CommRing R]
variable {M N P : Type _} [AddCommGroup M] [AddCommGroup N][AddCommGroup P]
  [Module R M] [Module R N] [Module R P]

variable (f : M →ₗ[R] N) (g : N →ₗ[R] P)

variable {R}
def Exact := LinearMap.range f = LinearMap.ker g

namespace Exact

variable {f g}
lemma comp_eq_zero (h : Exact f g) : g.comp f = 0 := by
  ext x
  simp only [coe_comp, Function.comp_apply, zero_apply]
  rw [← mem_ker, ← h]
  apply mem_range_self

section rTensor


open scoped TensorProduct

example (N' : Submodule R N) : N' →ₗ[R] N := by
  exact Submodule.subtype N'

example (N' : Submodule R N) : Submodule R (N ⊗[R] P) :=
  LinearMap.range (rTensorHom P (N'.subtype))


variable (Q : Type _) [AddCommGroup Q] [Module R Q]

variable (q : Q)

example (R : Type _) [CommSemiring R]
    (M N P : Type _) [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
      [Module R M] [Module R N] [Module R P]
      (f : M →ₗ[R] N →ₗ[R] P) (m : M) :
  N →ₗ[R] P := f m

example (R : Type _) [CommSemiring R]
    (M N P : Type _) [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
      [Module R M] [Module R N] [Module R P]
      (f : M →ₗ[R] N →ₗ[R] P) (n : N) :
  M →ₗ[R] P := f.flip n

variable {Q} (g)
lemma le_comap_range_rTensor (q : Q) :
    LinearMap.range g ≤ (LinearMap.range (rTensor Q g)).comap ((TensorProduct.mk R P Q).flip q) := by
  rintro x ⟨n, rfl⟩
  exact ⟨n ⊗ₜ[R] q, rfl⟩

variable (Q) {g}

variable (hg : Function.Surjective g) (hfg : Exact f g)

theorem rTensor.Surjective : Function.Surjective (rTensor Q g) := by
  intro z
  induction z using TensorProduct.induction_on with
  | C0 => use 0; rw [map_zero]
  | C1 p q =>
      obtain ⟨n, rfl⟩ := hg p
      use n ⊗ₜ[R] q
      simp only [rTensor_tmul]
  | Cp x y hx hy =>
      obtain ⟨x, rfl⟩ := hx
      obtain ⟨y, rfl⟩ := hy
      use x + y
      rw [map_add]

private noncomputable
def rTensor.inverse_ofRightInverse {h : P → N} (hgh : Function.RightInverse h g) :
  P ⊗[R] Q →ₗ[R] N ⊗[R] Q ⧸ (LinearMap.range (rTensor Q f)) := by
  apply TensorProduct.lift
  apply LinearMap.mk₂ R (fun p q ↦ Submodule.Quotient.mk (h p ⊗ₜ[R] q))
  . intro p p' q
    rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
    rw [← TensorProduct.add_tmul, ← TensorProduct.sub_tmul]
    apply le_comap_range_rTensor f
    rw [hfg, mem_ker, map_sub, map_add]
    simp only [hgh _, sub_self]
  . intro r p q
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    rw [TensorProduct.smul_tmul', ← TensorProduct.sub_tmul]
    apply le_comap_range_rTensor f
    rw [hfg, mem_ker, map_sub, map_smul]
    simp only [hgh _, sub_self]
  . intro p q q'
    rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
    rw [TensorProduct.tmul_add]
    rw [add_sub_add_comm]
    simp only [← TensorProduct.sub_tmul]
    apply Submodule.add_mem
    all_goals {
      apply le_comap_range_rTensor f
      rw [hfg, mem_ker, map_sub]
      simp only [hgh _, sub_self] }
  . intro r p q
    simp only [TensorProduct.tmul_smul, Submodule.Quotient.mk_smul]

private noncomputable
def rTensor.inverse :
  P ⊗[R] Q →ₗ[R] N ⊗[R] Q ⧸ (LinearMap.range (rTensor Q f)) :=
  rTensor.inverse_ofRightInverse Q hfg
    (Function.Surjective.hasRightInverse hg).choose_spec

private lemma rTensor.inverse_apply (y : N ⊗[R] Q) :
  (rTensor.inverse Q hg hfg) ((rTensor Q g) y) =
    Submodule.Quotient.mk (p := (LinearMap.range (rTensor Q f))) y := by
  simp only [← LinearMap.comp_apply, ← Submodule.mkQ_apply]
  apply LinearMap.congr_fun
  apply TensorProduct.ext'
  intro n q
  simp only [coe_comp, Function.comp_apply, rTensor_tmul, Submodule.mkQ_apply]
  simp only [rTensor.inverse, rTensor.inverse_ofRightInverse]
  simp only [TensorProduct.lift.tmul, coe_mk, AddHom.coe_mk, mk₂_apply]
  rw [Submodule.Quotient.eq]
  rw [← TensorProduct.sub_tmul]
  apply le_comap_range_rTensor f
  rw [hfg, mem_ker, map_sub, sub_eq_zero]
  rw [Exists.choose_spec (Function.Surjective.hasRightInverse hg) _]

/-- Tensoring an exact pair on the right gives an exact pair -/
theorem rTensor_exact : Exact (rTensor Q f) (rTensor Q g) := by
  dsimp only [Exact]
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    rw [mem_ker, ← rTensor_comp_apply, comp_eq_zero hfg]
    simp only [rTensor_zero, zero_apply]
  · intro x hx
    rw [mem_ker] at hx
    rw [← Submodule.Quotient.mk_eq_zero, ← rTensor.inverse_apply Q hg hfg, hx, map_zero]

end rTensor

section lTensor

open scoped TensorProduct

variable (Q : Type _) [AddCommGroup Q] [Module R Q]

variable (g) {Q}
lemma le_comap_range_lTensor (q : Q) :
    LinearMap.range g ≤ (LinearMap.range (lTensor Q g)).comap (TensorProduct.mk R Q P q) := by
  rintro x ⟨n, rfl⟩
  exact ⟨q ⊗ₜ[R] n, rfl⟩

variable (Q) {g}

variable (hg : Function.Surjective g) (hfg : Exact f g)

theorem lTensor.Surjective : Function.Surjective (lTensor Q g) := by
  intro z
  induction z using TensorProduct.induction_on with
  | C0 => use 0; rw [map_zero]
  | C1 q p =>
      obtain ⟨n, rfl⟩ := hg p
      use q ⊗ₜ[R] n
      simp only [lTensor_tmul]
  | Cp x y hx hy =>
      obtain ⟨x, rfl⟩ := hx
      obtain ⟨y, rfl⟩ := hy
      use x + y
      rw [map_add]

private noncomputable
def lTensor.inverse_ofRightInverse {h : P → N} (hgh : Function.RightInverse h g) :
  Q ⊗[R] P →ₗ[R] Q ⊗[R] N ⧸ (LinearMap.range (lTensor Q f)) := by
  apply TensorProduct.lift
  apply LinearMap.mk₂ R (fun q p ↦ Submodule.Quotient.mk (q ⊗ₜ[R] (h p)))
  . intro q q' p
    rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
    rw [TensorProduct.add_tmul]
    rw [add_sub_add_comm]
    simp only [← TensorProduct.tmul_sub]
    apply Submodule.add_mem
    all_goals {
      apply le_comap_range_lTensor f
      rw [hfg, mem_ker, map_sub]
      simp only [hgh _, sub_self] }
  . intro r p q
    rw [← TensorProduct.smul_tmul', ← Submodule.Quotient.mk_smul]
  . intro q p p'
    rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
    rw [← TensorProduct.tmul_add, ← TensorProduct.tmul_sub]
    apply le_comap_range_lTensor f
    rw [hfg, mem_ker, map_sub, map_add]
    simp only [hgh _, sub_self]
  . intro r q p
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    rw [← TensorProduct.tmul_smul, ← TensorProduct.tmul_sub]
    apply le_comap_range_lTensor f
    rw [hfg, mem_ker, map_sub, map_smul]
    simp only [hgh _, sub_self]

private noncomputable
def lTensor.inverse :
  Q ⊗[R] P →ₗ[R] Q ⊗[R] N ⧸ (LinearMap.range (lTensor Q f)) :=
  lTensor.inverse_ofRightInverse Q hfg
    (Function.Surjective.hasRightInverse hg).choose_spec

private lemma lTensor.inverse_apply (y : Q ⊗[R] N) :
  (lTensor.inverse Q hg hfg) ((lTensor Q g) y) =
    Submodule.Quotient.mk (p := (LinearMap.range (lTensor Q f))) y := by
  simp only [← LinearMap.comp_apply, ← Submodule.mkQ_apply]
  apply LinearMap.congr_fun
  apply TensorProduct.ext'
  intro n q
  simp only [coe_comp, Function.comp_apply, lTensor_tmul, Submodule.mkQ_apply]
  simp only [lTensor.inverse, lTensor.inverse_ofRightInverse]
  simp only [TensorProduct.lift.tmul, coe_mk, AddHom.coe_mk, mk₂_apply]
  rw [Submodule.Quotient.eq]
  rw [← TensorProduct.tmul_sub]
  apply le_comap_range_lTensor f n
  rw [hfg, mem_ker, map_sub, sub_eq_zero]
  rw [Exists.choose_spec (Function.Surjective.hasRightInverse hg) _]

/-- Tensoring an exact pair on the left gives an exact pair -/
theorem lTensor_exact : Exact (lTensor Q f) (lTensor Q g) := by
  dsimp only [Exact]
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    rw [mem_ker, ← lTensor_comp_apply, comp_eq_zero hfg]
    simp only [lTensor_zero, zero_apply]
  · intro x hx
    rw [mem_ker] at hx
    rw [← Submodule.Quotient.mk_eq_zero, ← lTensor.inverse_apply Q hg hfg, hx, map_zero]

end lTensor

section TensorProduct_map

variable {M' N' P' : Type _} [AddCommGroup M'] [AddCommGroup N'] [AddCommGroup P']
  [Module R M'] [Module R N'] [Module R P']
variable {f' : M' →ₗ[R] N'} {g' : N' →ₗ[R] P'}

variable (hg : Function.Surjective g) (hfg : Exact f g)
  (hg' : Function.Surjective g') (hfg' : Exact f' g')

theorem TensorProduct.map_surjective : Function.Surjective (TensorProduct.map g g') := by
  rw [← LinearMap.lTensor_comp_rTensor]
  rw [LinearMap.coe_comp]
  exact Function.Surjective.comp (lTensor.Surjective _ hg') (rTensor.Surjective _ hg)

theorem TensorProduct.map_ker :
  LinearMap.ker (TensorProduct.map g g') =
    LinearMap.range (lTensor N f') ⊔ LinearMap.range (rTensor N' f) := by
  ext y
  rw [← LinearMap.lTensor_comp_rTensor]
  rw [mem_ker, comp_apply, ← mem_ker]
  rw [rTensor_exact N' hg hfg]
  -- rw [← lTensor_exact P hg' hfg']
  rw [← Submodule.comap_map_eq]
  rw [Submodule.mem_comap]
  generalize rTensor N' g y = z
  rw [← lTensor_exact P hg' hfg']
  conv_rhs =>
    rw [LinearMap.range_eq_map, ← Submodule.map_comp,
      LinearMap.rTensor_comp_lTensor, Submodule.map_top]
    rw [← LinearMap.lTensor_comp_rTensor, LinearMap.range_eq_map,
      Submodule.map_comp, Submodule.map_top]
  rw [LinearMap.range_eq_top.mpr (rTensor.Surjective M' hg), Submodule.map_top]
