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

* `TensorProduct.map_ker` computes the kernel of `TensorProduct.map g g'` in the presence of two short exact sequences.

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
  g.ker = f.range

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

variable (g)
lemma rTensor.mem_range {p : P} {q : Q} (hp : p ∈ LinearMap.range g) :
  p ⊗ₜ[R] q ∈  LinearMap.range (rTensor Q g) := by
  simp only [mem_range] at hp ⊢
  obtain ⟨n, rfl⟩ := hp
  use n ⊗ₜ[R] q
  simp only [rTensor_tmul]

variable {g}

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

/-
private noncomputable
def inverse : P →ₗ[R] (N ⧸ (LinearMap.range f)) := {
  toFun := fun z ↦ Submodule.Quotient.mk ((hg z).choose)
  map_add' := fun z z' ↦ by
    dsimp
    rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq, hfg, mem_ker]
    simp only [map_sub, map_add, Exists.choose_spec (hg _), sub_self]
  map_smul' := fun r z ↦ by
    dsimp
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, hfg, mem_ker]
    simp only [map_sub, map_smul, Exists.choose_spec (hg _), sub_self] } -/

private noncomputable
def rTensor.inverse : P ⊗[R] Q →ₗ[R] N ⊗[R] Q ⧸ (LinearMap.range (rTensor Q f)) := by
  apply TensorProduct.lift
  exact {
    toFun := fun z ↦ {
      toFun := fun q ↦ Submodule.Quotient.mk ((hg z).choose ⊗ₜ[R] q)
      map_add' := fun q q' ↦ by
        dsimp
        rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
        rw [TensorProduct.tmul_add]
        rw [add_sub_add_comm]
        simp only [← TensorProduct.sub_tmul]
        apply Submodule.add_mem
        all_goals {
          apply rTensor.mem_range
          rw [hfg, mem_ker, map_sub]
          simp only [Exists.choose_spec (hg _), sub_self] }
      map_smul' := fun r q ↦ by
        dsimp
        simp only [TensorProduct.tmul_smul, Submodule.Quotient.mk_smul] }
    map_add' := fun p p' ↦ by
      ext q
      simp only [coe_mk, AddHom.coe_mk, add_apply]
      rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
      rw [← TensorProduct.add_tmul, ← TensorProduct.sub_tmul]
      apply rTensor.mem_range
      rw [hfg, mem_ker, map_sub, map_add]
      simp only [Exists.choose_spec (hg _), sub_self]
    map_smul' := fun r p ↦ by
      ext q
      simp only [coe_mk, AddHom.coe_mk,RingHom.id_apply, smul_apply]
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
      rw [TensorProduct.smul_tmul', ← TensorProduct.sub_tmul]
      apply rTensor.mem_range
      rw [hfg, mem_ker, map_sub, map_smul]
      simp only [Exists.choose_spec (hg _), sub_self] }

private lemma rTensor.inverse_apply (y : N ⊗[R] Q) :
  (rTensor.inverse Q hg hfg) ((rTensor Q g) y) =
    Submodule.Quotient.mk (p := (LinearMap.range (rTensor Q f))) y := by
  simp only [← LinearMap.comp_apply, ← Submodule.mkQ_apply]
  apply LinearMap.congr_fun
  apply TensorProduct.ext'
  intro n q
  simp only [coe_comp, Function.comp_apply, rTensor_tmul, Submodule.mkQ_apply]
  simp only [rTensor.inverse, TensorProduct.lift.tmul, coe_mk, AddHom.coe_mk]
  rw [Submodule.Quotient.eq]
  rw [← TensorProduct.sub_tmul]
  apply rTensor.mem_range
  rw [hfg, mem_ker, map_sub, Exists.choose_spec (hg _), sub_self]

/-- Tensoring an exact pair on the right gives an exact pair -/
theorem rTensor_exact : Exact (rTensor Q f) (rTensor Q g) := by
  dsimp only [Exact]
  apply le_antisymm
  . rintro y ⟨x, rfl⟩
    rw [mem_ker, ← rTensor_comp_apply, comp_eq_zero hfg]
    simp only [rTensor_zero, zero_apply]
  . intro x hx
    rw [mem_ker] at hx
    rw [← Submodule.Quotient.mk_eq_zero, ← rTensor.inverse_apply Q hg hfg, hx, map_zero]



end rTensor

section lTensor

open scoped TensorProduct

variable (Q : Type _) [AddCommGroup Q] [Module R Q]

variable (g)
lemma lTensor.mem_range {p : P} {q : Q} (hp : p ∈ LinearMap.range g) :
  q ⊗ₜ[R] p ∈  LinearMap.range (lTensor Q g) := by
  simp only [mem_range] at hp ⊢
  obtain ⟨n, rfl⟩ := hp
  use q ⊗ₜ[R] n
  simp only [lTensor_tmul]

variable {g}
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
def lTensor.inverse_aux (q : Q) : P →ₗ[R] Q ⊗[R] N ⧸ (LinearMap.range (lTensor Q f)) := {
  toFun := fun p ↦ Submodule.Quotient.mk (q ⊗ₜ[R] (hg p).choose)
  map_add' := fun p p' ↦ by
    simp only [coe_mk, AddHom.coe_mk, add_apply]
    rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
    rw [← TensorProduct.tmul_add, ← TensorProduct.tmul_sub]
    apply lTensor.mem_range
    rw [hfg, mem_ker, map_sub, map_add]
    simp only [Exists.choose_spec (hg _), sub_self]
  map_smul' := fun r p ↦ by
    simp only [coe_mk, AddHom.coe_mk,RingHom.id_apply, smul_apply]
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    rw [← TensorProduct.tmul_smul, ← TensorProduct.tmul_sub]
    apply lTensor.mem_range
    rw [hfg, mem_ker, map_sub, map_smul]
    simp only [Exists.choose_spec (hg _), sub_self] }

private noncomputable
def lTensor.inverse : Q ⊗[R] P →ₗ[R] Q ⊗[R] N ⧸ (LinearMap.range (lTensor Q f)) := by
  apply TensorProduct.lift
  exact {
    toFun := lTensor.inverse_aux Q hg hfg
    map_smul' := fun r q ↦ by
      ext p
      dsimp only [lTensor.inverse_aux]
      simp only [coe_mk, AddHom.coe_mk, RingHom.id_apply, smul_apply]
      rw [← Submodule.Quotient.mk_smul]
      rfl
    map_add' := fun q q' ↦ by
      ext p
      dsimp [lTensor.inverse_aux]
      rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
      rw [TensorProduct.add_tmul]
      rw [add_sub_add_comm]
      simp only [← TensorProduct.tmul_sub]
      apply Submodule.add_mem
      all_goals {
        apply lTensor.mem_range
        rw [hfg, mem_ker, map_sub]
        simp only [Exists.choose_spec (hg _), sub_self] } }

private lemma lTensor.inverse_apply (y : Q ⊗[R] N) :
  (lTensor.inverse Q hg hfg) ((lTensor Q g) y) =
    Submodule.Quotient.mk (p := (LinearMap.range (lTensor Q f))) y := by
  simp only [← LinearMap.comp_apply, ← Submodule.mkQ_apply]
  apply LinearMap.congr_fun
  apply TensorProduct.ext'
  intro n q
  simp only [coe_comp, Function.comp_apply, lTensor_tmul, Submodule.mkQ_apply]
  simp only [lTensor.inverse, lTensor.inverse_aux, TensorProduct.lift.tmul, coe_mk, AddHom.coe_mk]
  rw [Submodule.Quotient.eq]
  rw [← TensorProduct.tmul_sub]
  apply lTensor.mem_range
  rw [hfg, mem_ker, map_sub, Exists.choose_spec (hg _), sub_self]

/-- Tensoring an exact pair on the left gives an exact pair -/
theorem lTensor_exact : Exact (lTensor Q f) (lTensor Q g) := by
  dsimp only [Exact]
  apply le_antisymm
  . rintro y ⟨x, rfl⟩
    rw [mem_ker, ← lTensor_comp_apply, comp_eq_zero hfg]
    simp only [lTensor_zero, zero_apply]
  . intro x hx
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
