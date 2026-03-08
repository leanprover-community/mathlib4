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
  {σ : Representation k G V} {ρ : Representation k G W}

open CategoryTheory

variable (k G) in
/-- Every Set `X` that has a `G`-action on it can be made into a `G`-rep by using `X →₀ k` as
  the base module and `G`-action on it is induced by the `G`-action on `X`. -/
@[simps]
def linearize (X : Action (Type w) G) : Representation k G (X.V →₀ k) where
  toFun g := Finsupp.lmapDomain k k (X.ρ g)
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

lemma linearize_single (X : Action (Type w) G) (g : G) (x : X.V) :
    linearize k G X g (Finsupp.single x 1) = Finsupp.single (X.ρ g x) 1 := by
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Every morphism between `G`-sets could be made into an intertwining map between
  `Representation`s by the linear map induced on the indexing sets. -/
def linearizeMap {X Y : Action (Type w) G} (f : X ⟶ Y) :
  IntertwiningMap (A := k) (linearize k G X)
    (linearize k G Y) where
  __ := Finsupp.lmapDomain k k f.hom
  isIntertwining' g := by ext x y; simp [(congr($(f.comm g) x) : f.hom (X.ρ g x) = Y.ρ g (f.hom x))]

@[simp]
lemma linearizeMap_single {X Y : Action (Type w) G} (f : X ⟶ Y) (x : X.V) :
    (linearizeMap f).toLinearMap (Finsupp.single x (1 : k)) = Finsupp.single (f.hom x) 1 := by
  simp [linearizeMap]

lemma linearizeMap_toLinearMap {X Y : Action (Type w) G} (f : X ⟶ Y) :
    (linearizeMap f).toLinearMap = Finsupp.lmapDomain k k f.hom := rfl

namespace LinearizeMonoidal

open scoped MonoidalCategory

attribute [local simp] types_tensorObj_def types_tensorUnit_def

unif_hint (X Y : Action (Type w) G) where ⊢ (X ⊗ Y).V ≟ X.V × Y.V
unif_hint where ⊢ (𝟙_ (Action (Type w) G)).V ≟ PUnit
unif_hint (X Y Z : Action (Type w) G) where ⊢ (X ⊗ (Y ⊗ Z)).V ≟ X.V × Y.V × Z.V

lemma _root_.Action.tensor_ρ_apply {X Y : Action (Type w) G} (g : G) (xy : (X ⊗ Y).V) :
    (X ⊗ Y).ρ g xy = (X.ρ g xy.1, Y.ρ g xy.2) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
variable (k G) in
-- I could use `Action.trivial G (PUnit)` but that's not reducibly equal to the tensor unit
/-- The counit of the linearize functor. -/
@[simps toLinearMap]
def ε : (trivial k G k).IntertwiningMap (linearize k G (MonoidalCategoryStruct.tensorUnit
    (Action (Type w) G))) where
  __ := Finsupp.LinearEquiv.finsuppUnique k k PUnit|>.symm.toLinearMap
  isIntertwining' g := by ext1; simp [linearize_single _]

lemma ε_one : ε k G 1 = Finsupp.single PUnit.unit 1 := by
  simp [apply_toLinearMap, types_tensorUnit_def]

open scoped MonoidalCategory

variable (k G) in
/-- The unit of the linearize functor. -/
@[simps toLinearMap]
def η : (linearize k G (𝟙_ (Action (Type u) G))).IntertwiningMap (trivial k G k) where
  __ := (Finsupp.LinearEquiv.finsuppUnique k k PUnit).toLinearMap
  isIntertwining' g := by ext; simp [linearize_single _]

lemma η_single (x : PUnit) : η k G (Finsupp.single x 1) = 1 := by
  simp [apply_toLinearMap, types_tensorUnit_def]

variable (k G) in
lemma ε_η : (ε k G).comp (η k G) = .id _ := by ext; simp

variable (k G) in
lemma η_ε : (η k G).comp (ε k G) = .id _ := by ext; simp

section comm

open scoped MonoidalCategory

variable {k : Type u} [CommSemiring k] [Module k V] [Module k W] {σ : Representation k G V}
  {ρ : Representation k G W}

/-- The tensor (multiplication) of the linearize functor. -/
@[simps toLinearMap]
def μ (X Y : Action (Type w) G) : ((linearize k G X).tprod (linearize k G Y)).IntertwiningMap
    (linearize k G (X ⊗ Y)) where
  __ := finsuppTensorFinsupp' k X.V Y.V
  isIntertwining' g := by ext; simp [linearize_single _, Action.tensor_ρ_apply _]

lemma μ_apply_single_single {X Y : Action (Type w) G} (x : X.V) (y : Y.V) :
    μ (k := k) X Y (Finsupp.single x 1 ⊗ₜ Finsupp.single y 1) = Finsupp.single (x, y) 1 := by
  ext; simp [apply_toLinearMap]

open TensorProduct in
lemma μ_apply_apply {X Y : Action (Type w) G} (l1 : X.V →₀ k) (l2 : Y.V →₀ k)
    (xy : (X ⊗ Y).V) : μ X Y (l1 ⊗ₜ l2) xy = l1 xy.1 * l2 xy.2 := by
  simp [apply_toLinearMap, types_tensorObj_def, finsuppTensorFinsupp'_apply_apply _]

lemma μ_comp_rTensor {X Y : Action (Type w) G} (f : X ⟶ Y)
    (Z : Action (Type w) G) : (μ Y Z).comp (rTensor (linearize k G Z) (linearizeMap f)) =
    (linearizeMap (f ▷ Z)).comp (μ X Z) := by
  ext; simp [linearizeMap_single _]

lemma μ_comp_lTensor {X Y : Action (Type w) G} (f : X ⟶ Y)
    (Z : Action (Type w) G) : (μ Z Y).comp ((linearizeMap f).lTensor (linearize k G Z)) =
    (linearizeMap (Z ◁ f)).comp (μ Z X) := by
  ext : 6; simp [linearizeMap_single _]

set_option backward.isDefEq.respectTransparency false in
lemma μ_comp_assoc (X Y Z : Action (Type w) G) : ((linearizeMap (α_ X Y Z).hom).comp
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
  with_reducible convert linearizeMap_single (α_ X Y Z).hom ((x, y), z) using 5
  <;> with_reducible simp

lemma μ_leftUnitor (X : Action (Type w) G) : (lid k (linearize k G X)).toIntertwiningMap =
    ((linearizeMap (λ_ X).hom).comp (μ (𝟙_ (Action (Type w) G)) X)).comp (rTensor
    (linearize k G X) (ε k G)) := by
  ext x1 : 5
  simpa [types_tensorObj_def, types_tensorUnit_def] using
    linearizeMap_single (k := k) (λ_ X).hom (PUnit.unit, x1) |>.symm

set_option backward.isDefEq.respectTransparency false in
lemma μ_rightUnitor (X : Action (Type w) G) : (rid k (linearize k G X)).toIntertwiningMap =
    ((linearizeMap (ρ_ X).hom).comp (μ X (𝟙_ (Action (Type w) G)))).comp ((ε k G).lTensor
    (linearize k G X)) := by
  ext x; simp [types_tensorObj_def, types_tensorUnit_def, Action.tensorObj_V, linearizeMap,
    Action.rightUnitor_hom_hom, rightUnitor_hom_apply (p := PUnit.unit)]

/-- The comultiplication of the linearize functor. -/
def δ (X Y : Action (Type w) G) : (linearize k G (X ⊗ Y)).IntertwiningMap
    ((linearize k G X).tprod (linearize k G Y)) where
  __ := (finsuppTensorFinsupp' k X.V Y.V).symm
  isIntertwining' g := by
    ext; simp [types_tensorObj_def, linearize_single _, Action.tensor_ρ_apply g,
      finsuppTensorFinsupp'_symm_single_eq_single_one_tmul k]

set_option backward.isDefEq.respectTransparency false in
lemma δ_apply_single {X Y : Action (Type w) G} (xy : (X ⊗ Y).V) :
    (δ (k := k) X Y).toLinearMap (Finsupp.single xy 1) = Finsupp.single xy.1 1 ⊗ₜ
      Finsupp.single xy.2 1 := by
  simp [δ, finsuppTensorFinsupp'_symm_single_eq_single_one_tmul k]

lemma rTensor_comp_δ {X Y : Action (Type w) G} (f : X ⟶ Y) (Z : Action (Type w) G) :
    ((linearizeMap f).rTensor (linearize k G Z)).comp (δ X Z) =
      (δ Y Z).comp (linearizeMap (f ▷ Z)) := by
  ext;
  simp [linearizeMap_single _, δ_apply_single _]

lemma lTensor_comp_δ {X Y : Action (Type w) G} (f : X ⟶ Y) (Z : Action (Type w) G) :
    ((linearizeMap f).lTensor (linearize k G Z)).comp (δ Z X) =
      (δ Z Y).comp (linearizeMap (Z ◁ f)) := by
  ext; simp [linearizeMap_single _, δ_apply_single _]

lemma assoc_comp_δ (X Y Z : Action (Type w) G) : ((assoc (linearize k G X) (linearize k G Y)
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

lemma μ_δ (X Y : Action (Type w) G) : (μ X Y).comp (δ (k := k) X Y) = .id _ := by
  ext; simp [δ_apply_single _]

lemma δ_μ (X Y : Action (Type w) G) : (δ X Y).comp (μ (k := k) X Y) = .id _ := by
  ext; simp [δ_apply_single _]

end comm

end LinearizeMonoidal

variable (k G) in
/-- The equivalence of representations between `(Fin 1 → G) →₀ k` and `G →₀ k`. -/
def diagonalOneEquivLeftRegular : (diagonal k G 1).Equiv (leftRegular k G) :=
  .mk (Finsupp.domLCongr (Equiv.funUnique (Fin 1) G)) fun g ↦ by ext; simp

/-- If there exists `G`-action on a trivial monoid `H` then the induced representation
  on `k[H]` is equivalent to the trivial representation. -/
def ofMulActionSubsingletonEquivTrivial (k : Type u) (G : Type v) [Monoid G] [Semiring k]
    (H : Type w) [Subsingleton H] [MulOneClass H]
    [MulAction G H] : (ofMulAction k G H).Equiv (trivial k G k) :=
  letI : Unique H := uniqueOfSubsingleton 1
  .mk (Finsupp.LinearEquiv.finsuppUnique _ _ _) fun g ↦ by
    ext a; simp [Subsingleton.elim (g • a) a]

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

lemma linearizeTrivialIso_single {X : Type w} (x : X) (r : k) :
    (linearizeTrivialIso k G X) (Finsupp.single x r) = Finsupp.single x r := rfl

lemma linearizeTrivialIso_symm_single {X : Type w} (x : X) (r : k) :
    (linearizeTrivialIso k G X).symm (Finsupp.single x r) = Finsupp.single x r := rfl

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

section comm

variable {k : Type u} [CommSemiring k] [Module k V] [Module k W] (σ : Representation k G V)
  (ρ : Representation k G W)

section finsupp

open Finsupp

/-- Every `f : α → V` can induce an intertwining map between `(α →₀ G →₀ k)` and `V`. -/
@[simps! toLinearMap]
def freeLift {α : Type w'} (f : α → V) : (free k G α).IntertwiningMap σ where
  __ := linearCombination k (fun x => σ x.2 (f x.1)) ∘ₗ
    (curryLinearEquiv k).symm.toLinearMap
  isIntertwining' g := by ext; simp

/-- Equiv between the intertwing map module `(α →₀ G →₀ k) → V` and `V`. -/
@[simps]
def freeLiftLEquiv (α : Type w') : ((free k G α).IntertwiningMap σ) ≃ₗ[k] (α → V) where
  toFun f i := f (single i (single 1 1))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := freeLift σ
  left_inv f := by
    have := f.2
    simp only [LinearMap.ext_iff, LinearMap.coe_comp, Function.comp_apply] at this
    ext; simp [apply_toLinearMap, ← this]
  right_inv f := by simp [apply_toLinearMap]

/-- Equiv between representations induced by linear equiv between `(α →₀ V) ⊗[k] W` and
  `α →₀ (V ⊗[k] W)`. -/
def finsuppTensorLeft (α : Type w') [DecidableEq α] :
    ((σ.finsupp α).tprod ρ).Equiv ((σ.tprod ρ).finsupp α) :=
  .mk (TensorProduct.finsuppLeft _ _ _ _ _) fun g ↦ by
    ext; simp [TensorProduct.finsuppLeft_apply_tmul]

/-- Equiv between representations induced by linear equiv between `V ⊗[k] (α →₀ W)` and
  `α →₀ (V ⊗[k] W)`. -/
def finsuppTensorRight (α : Type w') [DecidableEq α] :
    (σ.tprod (ρ.finsupp α)).Equiv ((σ.tprod ρ).finsupp α) :=
  .mk (TensorProduct.finsuppRight _ _ _ _ _) fun g ↦ by
    ext; simp [TensorProduct.finsuppRight_apply_tmul]

/-- Equiv between representations induced by linear equiv between `(G →₀ k) ⊗[k] (α →₀ k)` and
  `α →₀ G →₀ k`. -/
def leftRegularTensorTrivialIsoFree (α : Type w') :
    ((leftRegular k G).tprod (trivial k G (α →₀ k))).Equiv (free k G α) :=
  .mk (finsuppTensorFinsupp' k G α ≪≫ₗ Finsupp.domLCongr (Equiv.prodComm G α) ≪≫ₗ
    curryLinearEquiv k) <| fun g ↦ by ext; simp

end finsupp

/-- The linear equiv between the hom module `k[G] ⟶ᵍ V` and `V` itself. -/
@[simps!]
def leftRegularMapEquiv : ((leftRegular k G).IntertwiningMap σ) ≃ₗ[k] V where
  toFun f := (Finsupp.llift V k k G).symm f.toLinearMap (1 : G)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun v := ⟨Finsupp.llift _ _ k _ (fun g ↦ σ g v), fun g ↦ by ext g'; simp⟩
  left_inv x := by ext; simp [← x.isIntertwining]
  right_inv v := by simp

lemma leftRegularMapEquiv_symm_single (g : G) (v : V) :
    ((leftRegularMapEquiv σ).symm v) (Finsupp.single g 1) = σ g v := by
  simp

end comm

end

end Representation
