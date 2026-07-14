/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie
-/
module

public import Mathlib.CategoryTheory.Action.Monoidal
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RingTheory.TensorProduct.MonoidAlgebra

/-!

## Main Purpose
This file is the preliminary for the `linearize` functor from `Action (Type w) G` to `Rep k G`,
constructing the functor from the `Representation` would reduce the amount of DefEq abuses that we
currently are doing in the `Rep` file.

TODO (Edison) : Refactor `Rep` to be a concrete category of `Representation` and
reconstruct the current `linearize` functor using this file.

-/

universe w w' u u' v v'
@[expose] public section
namespace Representation

open Representation.IntertwiningMap Representation.TensorProduct
open scoped MonoidAlgebra

noncomputable section

variable {k : Type u} {G : Type v} {V : Type u'} {W : Type v'} [Monoid G] [Semiring k]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  {σ : Representation k G V} {ρ : Representation k G W} {X Y Z : Action (Type w) G}

open CategoryTheory

variable (k G X) in
/-- Every Set `X` that has a `G`-action on it can be made into a `G`-rep by using `X →₀ k` as
  the base module and `G`-action on it is induced by the `G`-action on `X`. -/
@[simps]
def linearize : Representation k G k[X.V] where
  toFun g := MonoidAlgebra.mapDomainLinearMap k k (X.ρ g)
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

lemma linearize_single (g : G) (x : X.V) :
    linearize k G X g (.single x 1) = .single (X.ρ g x) 1 := by
  simp

/-- Every morphism between `G`-sets could be made into an intertwining map between
  `Representation`s by the linear map induced on the indexing sets. -/
@[simps toLinearMap]
def linearizeMap (f : X ⟶ Y) : IntertwiningMap (A := k) (linearize k G X) (linearize k G Y) where
  toLinearMap := MonoidAlgebra.mapDomainLinearMap k k f.hom
  isIntertwining' g := by ext x y; simp [(congr($(f.comm g) x) : f.hom (X.ρ g x) = Y.ρ g (f.hom x))]

@[simp]
lemma linearizeMap_single (f : X ⟶ Y) (x : X.V) (r : k) :
    (linearizeMap f) (.single x r) = .single (f.hom x) r := by
  simp [linearizeMap]

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
  __ := MonoidAlgebra.uniqueLinearEquiv k PUnit |>.symm.toLinearMap
  isIntertwining' g := by ext1; simp [linearize_single _]

lemma ε_one : ε k G 1 = .single PUnit.unit 1 := by
  simp [← toLinearMap_apply, types_tensorUnit_def]

open scoped MonoidalCategory

variable (k G) in
/-- The unit of the linearize functor. -/
@[simps toLinearMap]
def η : (linearize k G (𝟙_ (Action (Type u) G))).IntertwiningMap (trivial k G k) where
  toLinearMap := (MonoidAlgebra.uniqueLinearEquiv k PUnit).toLinearMap
  isIntertwining' g := by ext; simp [linearize_single _]

lemma η_single (x : PUnit) : η k G (.single x 1) = 1 := by
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
def μ : ((linearize k G X).tprod (linearize k G Y)).IntertwiningMap (linearize k G (X ⊗ Y)) where
  toLinearMap := (MonoidAlgebra.tensorEquiv k).toLinearMap
  isIntertwining' g := by ext; simp [linearize_single _]; rfl

lemma μ_apply_single_single (x : X.V) (y : Y.V) (r s : k) :
    μ (k := k) X Y (.single x r ⊗ₜ .single y s) = .single (x, y) (r * s) := by
  ext; simp [← toLinearMap_apply]

open TensorProduct in
lemma coeff_μ_tmul (l1 : k[X.V]) (l2 : k[Y.V]) (xy : (X ⊗ Y).V) :
    (μ X Y (l1 ⊗ₜ l2)).coeff xy = l1.coeff xy.1 * l2.coeff xy.2 := by
  simp [← toLinearMap_apply, types_tensorObj_def, finsuppTensorFinsupp'_apply_apply _]

lemma μ_comp_rTensor (f : X ⟶ Y) (Z : Action (Type w) G) :
    (μ Y Z).comp (rTensor (linearize k G Z) (linearizeMap f)) =
      (linearizeMap (f ▷ Z)).comp (μ X Z) := by
  ext; simp

lemma μ_comp_lTensor (f : X ⟶ Y) (Z : Action (Type w) G) :
    (μ Z Y).comp ((linearizeMap f).lTensor (linearize k G Z)) =
      (linearizeMap (Z ◁ f)).comp (μ Z X) := by
  ext; simp

variable (X Y Z) in
lemma μ_comp_assoc : ((linearizeMap (α_ X Y Z).hom).comp
    (μ (X ⊗ Y) Z)).comp ((μ X Y).rTensor (linearize k G Z)) = ((μ X (Y ⊗ Z)).comp
    ((μ Y Z).lTensor (linearize k G X))).comp (assoc (linearize k G X) (linearize k G Y)
    (linearize k G Z)).toIntertwiningMap := by
  ext x y z : 9
  -- experiment with monoidal structure of `Action` on `Type`
  simp only [Action.tensorObj_V, types_tensorObj_def, comp_toLinearMap, μ_toLinearMap,
    toLinearMap_rTensor, LinearMap.coe_comp, Function.comp_apply,
    TensorProduct.AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_self,
    TensorProduct.curry_apply, LinearEquiv.coe_coe, LinearMap.rTensor_tmul, toLinearMap_apply,
    toLinearMap_lTensor, toLinearMap_assoc, TensorProduct.assoc_tmul, LinearMap.lTensor_tmul]
  -- after fixing the defeq problems in `Action` and in the monoidal category structure of `types`
  -- this line should close the goal so this is left as an indicator.
  convert dsimp% linearizeMap_single (α_ X Y Z).hom ((x, y), z) (1 : k)
  all_goals with_reducible simp

variable (X) in
lemma μ_leftUnitor : (lid k (linearize k G X)).toIntertwiningMap =
    ((linearizeMap (λ_ X).hom).comp (μ (𝟙_ (Action (Type w) G)) X)).comp (rTensor
    (linearize k G X) (ε k G)) := by
  ext; simp

variable (X) in
lemma μ_rightUnitor : (rid k (linearize k G X)).toIntertwiningMap =
    ((linearizeMap (ρ_ X).hom).comp (μ X (𝟙_ (Action (Type w) G)))).comp ((ε k G).lTensor
    (linearize k G X)) := by
  ext x; simp [types_tensorObj_def, types_tensorUnit_def, Action.tensorObj_V, linearizeMap,
    Action.rightUnitor_hom_hom]

variable (X Y) in
/-- The comultiplication of the linearize functor. -/
def δ : (linearize k G (X ⊗ Y)).IntertwiningMap
    ((linearize k G X).tprod (linearize k G Y)) where
  toLinearMap := (MonoidAlgebra.tensorEquiv k).symm.toLinearMap
  isIntertwining' g := by
    ext; simp [linearize_single _, MonoidAlgebra.tensorEquiv_symm_single_eq_single_one_tmul]; rfl

lemma δ_apply_single (xy : (X ⊗ Y).V) :
    (δ (k := k) X Y) (.single xy 1) = .single xy.1 1 ⊗ₜ .single xy.2 1 := by
  simp [δ, MonoidAlgebra.tensorEquiv_symm_single_eq_single_one_tmul]

variable (Z) in
lemma rTensor_comp_δ (f : X ⟶ Y) :
    ((linearizeMap f).rTensor (linearize k G Z)).comp (δ X Z) =
      (δ Y Z).comp (linearizeMap (f ▷ Z)) := by
  ext; simp [δ_apply_single _]

variable (Z) in
lemma lTensor_comp_δ (f : X ⟶ Y) :
    ((linearizeMap f).lTensor (linearize k G Z)).comp (δ Z X) =
      (δ Z Y).comp (linearizeMap (Z ◁ f)) := by
  ext; simp [δ_apply_single _]

variable (X Y Z) in
lemma assoc_comp_δ : ((assoc (linearize k G X) (linearize k G Y)
    (linearize k G Z)).toIntertwiningMap.comp ((δ X Y).rTensor (linearize k G Z))).comp
    (δ (X ⊗ Y) Z) = (((δ Y Z).lTensor (linearize k G X)).comp (δ X (Y ⊗ Z))).comp
    (linearizeMap (α_ X Y Z).hom) := by
  ext
  -- TODO : try not to `simp` with `δ` and `linearizeMap` directly here
  simp [linearizeMap, δ, MonoidAlgebra.tensorEquiv_symm_single_eq_single_one_tmul]

lemma leftUnitor_δ (X : Action (Type u) G) : (lid k (linearize k G X)).symm.toIntertwiningMap =
    (((η k G).rTensor (linearize k G X)).comp (δ (𝟙_ (Action (Type u) G)) X)).comp
      (linearizeMap (λ_ X).inv) := by
  ext
  -- TODO : try not to `simp` with `δ` and `linearizeMap` directly here
  simp [linearizeMap, δ, MonoidAlgebra.tensorEquiv_symm_single_eq_single_one_tmul]

unif_hint (X : Action (Type u) G) where ⊢ (X ⊗ 𝟙_ (Action (Type u) G)).V ≟ X.V × PUnit in
lemma rightUnitor_δ (X : Action (Type u) G) : (rid k (linearize k G X)).symm.toIntertwiningMap =
    (((η k G).lTensor (linearize k G X)).comp (δ X (𝟙_ (Action (Type u) G)))).comp
      (linearizeMap (ρ_ X).inv) := by
  ext; simp [δ_apply_single _]

variable (X Y) in
lemma μ_δ : (μ X Y).comp (δ (k := k) X Y) = .id _ := by
  ext; simp [δ_apply_single _]

variable (X Y) in
lemma δ_μ : (δ X Y).comp (μ (k := k) X Y) = .id _ := by
  ext; simp [δ_apply_single _]

end comm

end LinearizeMonoidal

lemma linearizeTrivial_def (X : Type w) (g : G) :
    linearize k G (Action.trivial _ X) g = LinearMap.id := by
  ext (x : X) : 2
  rw [LinearMap.comp_apply, LinearMap.id_comp, MonoidAlgebra.lsingle_apply, linearize_single]
  simp only [Action.trivial_ρ]
  rfl

variable (k G) in
/-- This a type-changing equivalence (which requires a non-trivial proof that
  `LinearEquiv.refl _ _` is `G`-equivariant) to avoid abusing defeq. -/
def linearizeTrivialIso (X : Type w) : (linearize k G (.trivial _ X)).Equiv (trivial k G k[X]) :=
  .mk (.refl ..) fun g ↦ by erw [linearizeTrivial_def, LinearMap.comp_id]

open CategoryTheory
lemma linearizeTrivialIso_apply {X : Type w} (f : k[(Action.trivial _ X).V]) :
    linearizeTrivialIso k G X f = f := rfl

lemma linearizeTrivialIso_symm_apply {X : Type w} (f : k[X]) :
    (linearizeTrivialIso k G X).symm f = f := rfl

variable (k G) in
/-- This a type-changing equivalence to avoid abusing defeq. -/
def linearizeOfMulActionIso (H : Type w) [MulAction G H] :
    (linearize k G (Action.ofMulAction G H)).Equiv (ofMulAction k G H) :=
  .mk (.refl ..) fun _ ↦ rfl

variable (k G) in
/-- This a type-changing equivalence to avoid abusing defeq. -/
abbrev linearizeDiagonalEquiv (n : ℕ) : (linearize k G (Action.diagonal G n)).Equiv
    (diagonal k G n) := linearizeOfMulActionIso k G (Fin n → G)

end

end Representation
