/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.OfCommRing
public import Mathlib.CategoryTheory.Sites.LocallyInjective

/-!
# Trivializations from tensor pairings

A locally injective tensor pairing trivializes a sheaf of modules wherever it takes the
value one on a pure tensor.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite

universe u v w

namespace SheafOfModulesOfCommRing

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{w}}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {F G : SheafOfModulesOfCommRing.{w} R}
  (b : F.val ⊗ G.val ⟶ PresheafOfModulesOfCommRing.unit R.obj)
  [Presheaf.IsLocallyInjective J ((PresheafOfModulesOfCommRing.toPresheaf R.obj).map b)]

set_option backward.isDefEq.respectTransparency false in
/-- A pure tensor of value one under a locally injective pairing supplies a generator. -/
lemma eq_smul_of_tensor_pairing {U : Cᵒᵖ} (m : F.obj U) (n : G.obj U)
    (h : b.app' U (m ⊗ₜ[R.obj.obj U] n) = (1 : R.obj.obj U)) (x : F.obj U) :
    x = (show R.obj.obj U from b.app' U (x ⊗ₜ[R.obj.obj U] n)) • m := by
  let a : R.obj.obj U := b.app' U (x ⊗ₜ[R.obj.obj U] n)
  have heq : b.app' U (x ⊗ₜ[R.obj.obj U] n) =
      b.app' U ((a • m) ⊗ₜ[R.obj.obj U] n) := by
    rw [← TensorProduct.smul_tmul', map_smul, h]
    exact (mul_one a).symm
  apply F.isSheaf.isSeparated _ _
    (Presheaf.equalizerSieve_mem J
      ((PresheafOfModulesOfCommRing.toPresheaf R.obj).map b) _ _ heq)
  intro V f hf
  let m' := F.map f.op m
  let n' := G.map f.op n
  have h' : b.app' (op V) (m' ⊗ₜ[R.obj.obj (op V)] n') = (1 : R.obj.obj (op V)) := by
    change b.app' (op V) ((F.val ⊗ G.val).map f.op (m ⊗ₜ[R.obj.obj U] n)) = (1 : R.obj.obj (op V))
    rw [PresheafOfModulesOfCommRing.naturality_apply, h]
    exact (R.obj.map f.op).hom.map_one
  let g : G.obj (op V) →ₗ[R.obj.obj (op V)] R.obj.obj (op V) :=
    TensorProduct.curry (b.app' (op V)).hom m'
  have hg : g n' = 1 := h'
  change F.map f.op x ⊗ₜ[R.obj.obj (op V)] n' =
    F.map f.op (a • m) ⊗ₜ[R.obj.obj (op V)] n' at hf
  have hh := congrArg
    (fun z ↦ TensorProduct.rid (R.obj.obj (op V)) (F.obj (op V))
      (TensorProduct.map LinearMap.id g z)) hf
  simp only [TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.rid_tmul, hg, one_smul] at hh
  exact hh

set_option backward.isDefEq.respectTransparency false in
/-- A locally injective tensor pairing taking the value one on a pure tensor gives a
trivialization over the domain of the corresponding sections. -/
def isoUnitOfTensorPairing {U : Cᵒᵖ} (m : F.obj U) (n : G.obj U)
    (h : b.app' U (m ⊗ₜ[R.obj.obj U] n) = (1 : R.obj.obj U)) :
    F.over U.unop ≅ (unit R).over U.unop := by
  let f : F.over U.unop ⟶ (unit R).over U.unop :=
    ⟨PresheafOfModulesOfCommRing.homMk (R := (Over.forget U.unop).op ⋙ R.obj)
      (M₁ := (F.over U.unop).val) (M₂ := ((unit R).over U.unop).val)
      (fun V ↦ ModuleCat.ofHom (R := R.obj.obj (op V.unop.left)) {
        toFun x := b.app' _ (x ⊗ₜ G.map V.unop.hom.op n)
        map_add' := by intro x y; simp +instances [TensorProduct.add_tmul]
        map_smul' := by intro r x; simp [← TensorProduct.smul_tmul'] })
      (fun {V V'} g ↦ by
        ext x
        calc
          b.app' (op V'.unop.left) (F.map g.unop.left.op x ⊗ₜ
              G.map V'.unop.hom.op n) =
              b.app' (op V'.unop.left) (F.map g.unop.left.op x ⊗ₜ
                G.map g.unop.left.op (G.map V.unop.hom.op n)) := by
            congr 2
            exact (G.val.congr_map_apply (congrArg Quiver.Hom.op g.unop.w).symm n).trans
              (G.val.map_comp_apply V.unop.hom.op g.unop.left.op n)
          _ = _ := PresheafOfModulesOfCommRing.naturality_apply b g.unop.left.op
            (x ⊗ₜ G.map V.unop.hom.op n))⟩
  have hf (V : (Over U.unop)ᵒᵖ) : Function.Bijective (f.val.app V) := by
    let m' : F.obj (op V.unop.left) := F.map V.unop.hom.op m
    let n' : G.obj (op V.unop.left) := G.map V.unop.hom.op n
    have h' : b.app' (op V.unop.left) (m' ⊗ₜ[R.obj.obj (op V.unop.left)] n') =
        (1 : R.obj.obj (op V.unop.left)) := by
      change b.app' _ ((F.val ⊗ G.val).map V.unop.hom.op
        (m ⊗ₜ[R.obj.obj U] n)) = (1 : R.obj.obj (op V.unop.left))
      rw [PresheafOfModulesOfCommRing.naturality_apply, h]
      exact (R.obj.map V.unop.hom.op).hom.map_one
    constructor
    · intro x y hxy
      change b.app' _ (x ⊗ₜ[R.obj.obj (op V.unop.left)] n') =
        b.app' _ (y ⊗ₜ[R.obj.obj (op V.unop.left)] n') at hxy
      rw [eq_smul_of_tensor_pairing b m' n' h' x,
        eq_smul_of_tensor_pairing b m' n' h' y, hxy]
    · intro a
      refine ⟨(show R.obj.obj (op V.unop.left) from a) • m', ?_⟩
      change b.app' _
        (((show R.obj.obj (op V.unop.left) from a) • m') ⊗ₜ[R.obj.obj (op V.unop.left)] n') = a
      rw [← TensorProduct.smul_tmul', map_smul, h']
      exact mul_one (show R.obj.obj (op V.unop.left) from a)
  have : ∀ V, IsIso
      (((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map f).app V) :=
    fun V ↦ (ConcreteCategory.isIso_iff_bijective _).2 (hf V)
  have : IsIso ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map f) :=
    NatIso.isIso_of_isIso_app _
  have : IsIso f := isIso_of_reflects_iso f
    (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _)
  exact asIso f

end SheafOfModulesOfCommRing
