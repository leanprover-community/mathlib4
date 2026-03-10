/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie
-/
module

public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.CategoryTheory.Action.Monoidal

/-!

## Main Purpose
This file is the preliminary for the `linearize` functor from `Action (Type w) G` to `Rep k G`,
constructing the functor from the `Representation` would reduce the amount of DefEq abuses that we
currently are doing in the `Rep` file.

TODO (Edison) : Refactor `Rep` to be a concrete category of `Representation` and
reconstruct the current `lineaization` functor using this file.

-/

universe w w' u u' v v'
@[expose] public section
namespace Representation

open Representation.IntertwiningMap Representation.TensorProduct

noncomputable section

variable {k : Type u} {G : Type v} {V : Type u'} {W : Type v'} [Monoid G] [Semiring k]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  {σ : Representation k G V} {ρ : Representation k G W} {X Y Z : Action (Type w) G}

open CategoryTheory

variable (k G X) in
/-- Every Set `X` that has a `G`-action on it can be made into a `G`-rep by using `X →₀ k` as
  the base module and `G`-action on it is induced by the `G`-action on `X`. -/
@[simps]
def linearize : Representation k G (X.V →₀ k) where
  toFun g := Finsupp.lmapDomain k k (X.ρ g)
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

lemma linearize_single (g : G) (x : X.V) :
    linearize k G X g (Finsupp.single x 1) = Finsupp.single (X.ρ g x) 1 := by
  simp

/-- Every morphism between `G`-sets could be made into an intertwining map between
  `Representation`s by the linear map induced on the indexing sets. -/
def linearizeMap (f : X ⟶ Y) : IntertwiningMap (A := k) (linearize k G X) (linearize k G Y) where
  __ := Finsupp.lmapDomain k k f.hom
  isIntertwining' g := by ext x y; simp [(congr($(f.comm g) x) : f.hom (X.ρ g x) = Y.ρ g (f.hom x))]

@[simp]
lemma linearizeMap_single (f : X ⟶ Y) (x : X.V) :
    (linearizeMap f).toLinearMap (Finsupp.single x (1 : k)) = Finsupp.single (f.hom x) 1 := by
  simp [linearizeMap]

lemma linearizeMap_toLinearMap (f : X ⟶ Y) :
    (linearizeMap f).toLinearMap = Finsupp.lmapDomain k k f.hom := rfl

namespace LinearizeMonoidal

open scoped MonoidalCategory

attribute [local simp] types_tensorObj_def types_tensorUnit_def

-- These two unification hints are to help lean understand the underlying types of these actions
-- which it fails without them because `types` abuses defeq.
unif_hint (X Y : Action (Type w) G) where ⊢ (X ⊗ Y).V ≟ X.V × Y.V
unif_hint where ⊢ (𝟙_ (Action (Type w) G)).V ≟ PUnit

lemma _root_.Action.tensor_ρ_apply (g : G) (xy : (X ⊗ Y).V) :
    (X ⊗ Y).ρ g xy = (X.ρ g xy.1, Y.ρ g xy.2) := rfl

variable (k G) in
-- I could use `Action.trivial G (PUnit)` but that's not reducibly equal to the tensor unit
/-- The counit of the linearize functor. -/
@[simps toLinearMap]
def ε : (trivial k G k).IntertwiningMap (linearize k G (MonoidalCategoryStruct.tensorUnit
    (Action (Type w) G))) where
  __ := Finsupp.LinearEquiv.finsuppUnique k k PUnit|>.symm.toLinearMap
  isIntertwining' g := by ext1; simp [linearize_single _]

lemma ε_one : ε k G 1 = Finsupp.single PUnit.unit 1 := by
  simp [← toLinearMap_apply, types_tensorUnit_def]

open scoped MonoidalCategory

variable (k G) in
/-- The unit of the linearize functor. -/
@[simps toLinearMap]
def η : (linearize k G (𝟙_ (Action (Type u) G))).IntertwiningMap (trivial k G k) where
  __ := (Finsupp.LinearEquiv.finsuppUnique k k PUnit).toLinearMap
  isIntertwining' g := by ext; simp [linearize_single _]

lemma η_single (x : PUnit) : η k G (Finsupp.single x 1) = 1 := by
  simp [← toLinearMap_apply, types_tensorUnit_def]

variable (k G) in
lemma ε_η : (ε k G).comp (η k G) = .id _ := by ext; simp

variable (k G) in
lemma η_ε : (η k G).comp (ε k G) = .id _ := by ext; simp

section comm

open scoped MonoidalCategory

variable {k : Type u} [CommSemiring k] [Module k V] [Module k W] {σ : Representation k G V}
  {ρ : Representation k G W}

variable (X Y) in
/-- The tensor (multiplication) of the linearize functor. -/
@[simps toLinearMap]
def μ : ((linearize k G X).tprod (linearize k G Y)).IntertwiningMap
    (linearize k G (X ⊗ Y)) where
  __ := finsuppTensorFinsupp' k X.V Y.V
  isIntertwining' g := by ext; simp [linearize_single _, Action.tensor_ρ_apply _]

lemma μ_apply_single_single (x : X.V) (y : Y.V) :
    μ (k := k) X Y (Finsupp.single x 1 ⊗ₜ Finsupp.single y 1) = Finsupp.single (x, y) 1 := by
  ext; simp [← toLinearMap_apply]

open TensorProduct in
lemma μ_apply_apply (l1 : X.V →₀ k) (l2 : Y.V →₀ k) (xy : (X ⊗ Y).V) :
    μ X Y (l1 ⊗ₜ l2) xy = l1 xy.1 * l2 xy.2 := by
  simp [← toLinearMap_apply, types_tensorObj_def, finsuppTensorFinsupp'_apply_apply _]

lemma μ_comp_rTensor (f : X ⟶ Y) (Z : Action (Type w) G) :
    (μ Y Z).comp (rTensor (linearize k G Z) (linearizeMap f)) =
      (linearizeMap (f ▷ Z)).comp (μ X Z) := by
  ext; simp [linearizeMap_single _]

lemma μ_comp_lTensor (f : X ⟶ Y) (Z : Action (Type w) G) :
    (μ Z Y).comp ((linearizeMap f).lTensor (linearize k G Z)) =
      (linearizeMap (Z ◁ f)).comp (μ Z X) := by
  ext : 6; simp [linearizeMap_single _]

variable (X Y Z) in
set_option backward.isDefEq.respectTransparency false in
lemma μ_comp_assoc : ((linearizeMap (α_ X Y Z).hom).comp
    (μ (X ⊗ Y) Z)).comp ((μ X Y).rTensor (linearize k G Z)) = ((μ X (Y ⊗ Z)).comp
    ((μ Y Z).lTensor (linearize k G X))).comp (assoc (linearize k G X) (linearize k G Y)
    (linearize k G Z)).toIntertwiningMap := by
  ext x y z : 9
  -- experiment with monoidal structure of `Action` on `Type`
  simp only [Action.tensorObj_V, types_tensorObj_def, comp_toLinearMap, μ_toLinearMap,
    toLinearMap_rTensor, LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply,
    TensorProduct.AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_self,
    TensorProduct.curry_apply, LinearEquiv.coe_coe, LinearMap.rTensor_tmul,
    finsuppTensorFinsupp'_single_tmul_single, mul_one, toLinearMap_lTensor, toLinearMap_assoc,
    TensorProduct.assoc_tmul, LinearMap.lTensor_tmul]
  -- after fixing the defeq problems in `Action` and in the monoidal category structure of `types`
  -- this line should close the goal so this is left as an indicator.
  with_reducible convert linearizeMap_single (α_ X Y Z).hom ((x, y), z)
  with_reducible simp only [Action.tensorObj_V, types_tensorObj_def, Action.associator_hom_hom]
  with_reducible refine Prod.ext ?_ (Prod.ext ?_ ?_)
  <;>  with_reducible simp

variable (X) in
lemma μ_leftUnitor : (lid k (linearize k G X)).toIntertwiningMap =
    ((linearizeMap (λ_ X).hom).comp (μ (𝟙_ (Action (Type w) G)) X)).comp (rTensor
    (linearize k G X) (ε k G)) := by
  ext x1 : 5
  simpa [types_tensorObj_def, types_tensorUnit_def] using
    linearizeMap_single (k := k) (λ_ X).hom (PUnit.unit, x1) |>.symm

variable (X) in
set_option backward.isDefEq.respectTransparency false in
lemma μ_rightUnitor : (rid k (linearize k G X)).toIntertwiningMap =
    ((linearizeMap (ρ_ X).hom).comp (μ X (𝟙_ (Action (Type w) G)))).comp ((ε k G).lTensor
    (linearize k G X)) := by
  ext x; simp [types_tensorObj_def, types_tensorUnit_def, Action.tensorObj_V, linearizeMap,
    Action.rightUnitor_hom_hom, rightUnitor_hom_apply (p := PUnit.unit)]

variable (X Y) in
/-- The comultiplication of the linearize functor. -/
def δ : (linearize k G (X ⊗ Y)).IntertwiningMap
    ((linearize k G X).tprod (linearize k G Y)) where
  __ := (finsuppTensorFinsupp' k X.V Y.V).symm
  isIntertwining' g := by
    ext; simp [types_tensorObj_def, linearize_single _, Action.tensor_ρ_apply g,
      finsuppTensorFinsupp'_symm_single_eq_single_one_tmul k]

set_option backward.isDefEq.respectTransparency false in
lemma δ_apply_single (xy : (X ⊗ Y).V) :
    (δ (k := k) X Y).toLinearMap (Finsupp.single xy 1) = Finsupp.single xy.1 1 ⊗ₜ
      Finsupp.single xy.2 1 := by
  simp [δ, finsuppTensorFinsupp'_symm_single_eq_single_one_tmul k]

variable (Z) in
lemma rTensor_comp_δ (f : X ⟶ Y) :
    ((linearizeMap f).rTensor (linearize k G Z)).comp (δ X Z) =
      (δ Y Z).comp (linearizeMap (f ▷ Z)) := by
  ext;
  simp [linearizeMap_single _, δ_apply_single _]

variable (Z) in
lemma lTensor_comp_δ (f : X ⟶ Y) :
    ((linearizeMap f).lTensor (linearize k G Z)).comp (δ Z X) =
      (δ Z Y).comp (linearizeMap (Z ◁ f)) := by
  ext; simp [linearizeMap_single _, δ_apply_single _]

variable (X Y Z) in
lemma assoc_comp_δ : ((assoc (linearize k G X) (linearize k G Y)
    (linearize k G Z)).toIntertwiningMap.comp ((δ X Y).rTensor (linearize k G Z))).comp
    (δ (X ⊗ Y) Z) = (((δ Y Z).lTensor (linearize k G X)).comp (δ X (Y ⊗ Z))).comp
    (linearizeMap (α_ X Y Z).hom) := by
  ext
  -- TODO : try not to `simp` with `δ` and `linearizeMap` directly here
  simp [linearizeMap, δ, finsuppTensorFinsupp'_symm_single_eq_single_one_tmul k]

lemma leftUnitor_δ (X : Action (Type u) G) : (lid k (linearize k G X)).symm.toIntertwiningMap =
    (((η k G).rTensor (linearize k G X) ).comp (δ (𝟙_ (Action (Type u) G)) X)).comp
      (linearizeMap (λ_ X).inv) := by
  ext
  -- TODO : try not to `simp` with `δ` and `linearizeMap` directly here
  simp [linearizeMap, δ, finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]

unif_hint (X : Action (Type u) G) where ⊢ (X ⊗ 𝟙_ (Action (Type u) G)).V ≟ X.V × PUnit in
lemma rightUnitor_δ (X : Action (Type u) G) : (rid k (linearize k G X)).symm.toIntertwiningMap =
    (((η k G).lTensor (linearize k G X)).comp (δ X (𝟙_ (Action (Type u) G)))).comp
      (linearizeMap (ρ_ X).inv) := by
  ext; simp [linearizeMap_single _, δ_apply_single _]

variable (X Y) in
lemma μ_δ : (μ X Y).comp (δ (k := k) X Y) = .id _ := by
  ext; simp [δ_apply_single _]

variable (X Y) in
lemma δ_μ : (δ X Y).comp (μ (k := k) X Y) = .id _ := by
  ext; simp [δ_apply_single _]

end comm

lemma linearizeTrivial_def (X : Type w) (g : G) :
    linearize k G (Action.trivial _ X) g = LinearMap.id := by
  ext (x : X) : 2
  rw [LinearMap.comp_apply, LinearMap.id_comp, Finsupp.lsingle_apply, linearize_single]
  simp only [Action.trivial_V, Action.trivial_ρ]
  rfl

variable (k G) in
/-- This a type-changing equivalence (which requires a non-trivial proof that
  `LinearEquiv.refl _ _` is `G`-equivariant) to avoid abusing defeq. -/
def linearizeTrivialIso (X : Type w) : (linearize k G (Action.trivial _ X)).Equiv
    (trivial k G (X →₀ k)) :=
  .mk (LinearEquiv.refl _ _) fun g ↦ by
    simpa using linearizeTrivial_def (k := k) X g

open CategoryTheory
lemma linearizeTrivialIso_apply {X : Type w} (f : (Action.trivial _ X).V →₀ k) :
    (linearizeTrivialIso k G X) f = f := rfl

lemma linearizeTrivialIso_symm_apply {X : Type w} (f : X →₀ k) :
    (linearizeTrivialIso k G X).symm f = f := rfl

variable (k G) in
/-- This a type-changing equivalence to avoid abusing defeq. -/
def linearizeOfMulActionIso (H : Type w) [MulAction G H] :
    (linearize k G (Action.ofMulAction G H)).Equiv (ofMulAction k G H) :=
    .mk (LinearEquiv.refl _ _) fun g ↦ by rfl

variable (k G) in
/-- This a type-changing equivalence to avoid abusing defeq. -/
def linearizeDiagonalEquiv (n : ℕ) : (linearize k G (Action.diagonal G n)).Equiv
    (diagonal k G n) :=
  .mk (LinearEquiv.refl _ _) fun g ↦ by rfl

end LinearizeMonoidal

end

end Representation
