/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Sébastien Gouëzel, Zhouhang Zhou, Reid Barton
-/
import Mathlib.Topology.Constructions
import Mathlib.Topology.HomeoDefs
import Mathlib.Topology.Bases -- only for piUnique

/-!
# Homeomorphisms and constructions yada yada

This file defines homeomorphisms between two topological spaces. They are bijections with both
directions continuous. We denote homeomorphisms with the notation `≃ₜ`.

# Main definitions



# Main results

* Pretty much every topological property is preserved under homeomorphisms.

-/

open Filter Function Set Topology

variable {X Y W Z : Type*}

namespace Homeomorph

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace W] [TopologicalSpace Z]
  {X' Y' : Type*} [TopologicalSpace X'] [TopologicalSpace Y']

/-- Sum of two homeomorphisms. -/
def sumCongr (h₁ : X ≃ₜ X') (h₂ : Y ≃ₜ Y') : X ⊕ Y ≃ₜ X' ⊕ Y' where
  continuous_toFun := h₁.continuous.sumMap h₂.continuous
  continuous_invFun := h₁.symm.continuous.sumMap h₂.symm.continuous
  toEquiv := h₁.toEquiv.sumCongr h₂.toEquiv

@[simp]
lemma sumCongr_symm (h₁ : X ≃ₜ X') (h₂ : Y ≃ₜ Y') :
  (sumCongr h₁ h₂).symm = sumCongr h₁.symm h₂.symm := rfl

@[simp]
theorem sumCongr_refl : sumCongr (.refl X) (.refl Y) = .refl (X ⊕ Y) := by
  ext i
  cases i <;> rfl

@[simp]
theorem sumCongr_trans {X'' Y'' : Type*} [TopologicalSpace X''] [TopologicalSpace Y'']
    (h₁ : X ≃ₜ X') (h₂ : Y ≃ₜ Y') (h₃ : X' ≃ₜ X'') (h₄ : Y' ≃ₜ Y'') :
    (sumCongr h₁ h₂).trans (sumCongr h₃ h₄) = sumCongr (h₁.trans h₃) (h₂.trans h₄) := by
  ext i
  cases i <;> rfl

/-- Product of two homeomorphisms. -/
def prodCongr (h₁ : X ≃ₜ X') (h₂ : Y ≃ₜ Y') : X × Y ≃ₜ X' × Y' where
  toEquiv := h₁.toEquiv.prodCongr h₂.toEquiv

@[simp]
theorem prodCongr_symm (h₁ : X ≃ₜ X') (h₂ : Y ≃ₜ Y') :
    (h₁.prodCongr h₂).symm = h₁.symm.prodCongr h₂.symm :=
  rfl

@[simp]
theorem coe_prodCongr (h₁ : X ≃ₜ X') (h₂ : Y ≃ₜ Y') : ⇑(h₁.prodCongr h₂) = Prod.map h₁ h₂ :=
  rfl

-- Commutativity and associativity of the disjoint union of topological spaces,
-- and the sum with an empty space.
section sum

variable (X Y W Z)

/-- `X ⊕ Y` is homeomorphic to `Y ⊕ X`. -/
def sumComm : X ⊕ Y ≃ₜ Y ⊕ X where
  toEquiv := Equiv.sumComm X Y
  continuous_toFun := continuous_sum_swap
  continuous_invFun := continuous_sum_swap

@[simp]
theorem sumComm_symm : (sumComm X Y).symm = sumComm Y X :=
  rfl

@[simp]
theorem coe_sumComm : ⇑(sumComm X Y) = Sum.swap :=
  rfl

@[continuity, fun_prop]
lemma continuous_sumAssoc : Continuous (Equiv.sumAssoc X Y Z) :=
  Continuous.sumElim (by fun_prop) (by fun_prop)

@[continuity, fun_prop]
lemma continuous_sumAssoc_symm : Continuous (Equiv.sumAssoc X Y Z).symm :=
  Continuous.sumElim (by fun_prop) (by fun_prop)

/-- `(X ⊕ Y) ⊕ Z` is homeomorphic to `X ⊕ (Y ⊕ Z)`. -/
def sumAssoc : (X ⊕ Y) ⊕ Z ≃ₜ X ⊕ Y ⊕ Z where
  toEquiv := Equiv.sumAssoc X Y Z
  continuous_toFun := continuous_sumAssoc X Y Z
  continuous_invFun := continuous_sumAssoc_symm X Y Z

@[simp]
lemma sumAssoc_toEquiv : (sumAssoc X Y Z).toEquiv = Equiv.sumAssoc X Y Z := rfl

/-- Four-way commutativity of the disjoint union. The name matches `add_add_add_comm`. -/
def sumSumSumComm : (X ⊕ Y) ⊕ W ⊕ Z ≃ₜ (X ⊕ W) ⊕ Y ⊕ Z where
  toEquiv := Equiv.sumSumSumComm X Y W Z
  continuous_toFun := by
    unfold Equiv.sumSumSumComm
    dsimp only
    have : Continuous (Sum.map (Sum.map (@id X) ⇑(Equiv.sumComm Y W)) (@id Z)) := by continuity
    fun_prop
  continuous_invFun := by
    unfold Equiv.sumSumSumComm
    dsimp only
    have : Continuous (Sum.map (Sum.map (@id X) (Equiv.sumComm Y W).symm) (@id Z)) := by continuity
    fun_prop

@[simp]
lemma sumSumSumComm_toEquiv : (sumSumSumComm X Y W Z).toEquiv = (Equiv.sumSumSumComm X Y W Z) := rfl

@[simp]
lemma sumSumSumComm_symm : (sumSumSumComm X Y W Z).symm = (sumSumSumComm X W Y Z) := rfl

/-- The sum of `X` with any empty topological space is homeomorphic to `X`. -/
@[simps! (config := .asFn) apply]
def sumEmpty [IsEmpty Y] : X ⊕ Y ≃ₜ X where
  toEquiv := Equiv.sumEmpty X Y
  continuous_toFun := Continuous.sumElim continuous_id (by fun_prop)
  continuous_invFun := continuous_inl

/-- The sum of `X` with any empty topological space is homeomorphic to `X`. -/
def emptySum [IsEmpty Y] : Y ⊕ X ≃ₜ X := (sumComm Y X).trans (sumEmpty X Y)

@[simp] theorem coe_emptySum [IsEmpty Y] : (emptySum X Y).toEquiv = Equiv.emptySum Y X := rfl

end sum

-- Commutativity and associativity of the product of top. spaces, and the product with `PUnit`.
section prod

variable (X Y W Z)

/-- `X × Y` is homeomorphic to `Y × X`. -/
def prodComm : X × Y ≃ₜ Y × X where
  continuous_toFun := continuous_snd.prod_mk continuous_fst
  continuous_invFun := continuous_snd.prod_mk continuous_fst
  toEquiv := Equiv.prodComm X Y

@[simp]
theorem prodComm_symm : (prodComm X Y).symm = prodComm Y X :=
  rfl

@[simp]
theorem coe_prodComm : ⇑(prodComm X Y) = Prod.swap :=
  rfl

/-- `(X × Y) × Z` is homeomorphic to `X × (Y × Z)`. -/
def prodAssoc : (X × Y) × Z ≃ₜ X × Y × Z where
  continuous_toFun := continuous_fst.fst.prod_mk (continuous_fst.snd.prod_mk continuous_snd)
  continuous_invFun := (continuous_fst.prod_mk continuous_snd.fst).prod_mk continuous_snd.snd
  toEquiv := Equiv.prodAssoc X Y Z

@[simp]
lemma prodAssoc_toEquiv : (prodAssoc X Y Z).toEquiv = Equiv.prodAssoc X Y Z := rfl

/-- Four-way commutativity of `prod`. The name matches `mul_mul_mul_comm`. -/
def prodProdProdComm : (X × Y) × W × Z ≃ₜ (X × W) × Y × Z where
  toEquiv := Equiv.prodProdProdComm X Y W Z
  continuous_toFun := by
    unfold Equiv.prodProdProdComm
    dsimp only
    fun_prop
  continuous_invFun := by
    unfold Equiv.prodProdProdComm
    dsimp only
    fun_prop

@[simp]
theorem prodProdProdComm_symm : (prodProdProdComm X Y W Z).symm = prodProdProdComm X W Y Z :=
  rfl

/-- `X × {*}` is homeomorphic to `X`. -/
@[simps! (config := .asFn) apply]
def prodPUnit : X × PUnit ≃ₜ X where
  toEquiv := Equiv.prodPUnit X
  continuous_toFun := continuous_fst
  continuous_invFun := continuous_id.prod_mk continuous_const

/-- `{*} × X` is homeomorphic to `X`. -/
def punitProd : PUnit × X ≃ₜ X :=
  (prodComm _ _).trans (prodPUnit _)

@[simp] theorem coe_punitProd : ⇑(punitProd X) = Prod.snd := rfl

/-- The product over `S ⊕ T` of a family of topological spaces
is homeomorphic to the product of (the product over `S`) and (the product over `T`).

This is `Equiv.sumPiEquivProdPi` as a `Homeomorph`.
-/
def sumPiEquivProdPi (S T : Type*) (A : S ⊕ T → Type*)
    [∀ st, TopologicalSpace (A st)] :
    (Π (st : S ⊕ T), A st) ≃ₜ (Π (s : S), A (.inl s)) × (Π (t : T), A (.inr t)) where
  __ := Equiv.sumPiEquivProdPi _
  continuous_toFun := Continuous.prod_mk (by fun_prop) (by fun_prop)
  continuous_invFun := continuous_pi <| by rintro (s | t) <;> simp <;> fun_prop

/-- The product `Π t : α, f t` of a family of topological spaces is homeomorphic to the
space `f ⬝` when `α` only contains `⬝`.

This is `Equiv.piUnique` as a `Homeomorph`.
-/
@[simps! (config := .asFn)]
def piUnique {α : Type*} [Unique α] (f : α → Type*) [∀ x, TopologicalSpace (f x)] :
    (Π t, f t) ≃ₜ f default :=
  homeomorphOfContinuousOpen (Equiv.piUnique f) (continuous_apply default) (isOpenMap_eval _)

end prod

section Distrib

/-- `(X ⊕ Y) × Z` is homeomorphic to `X × Z ⊕ Y × Z`. -/
@[simps!]
def sumProdDistrib : (X ⊕ Y) × Z ≃ₜ (X × Z) ⊕ (Y × Z) :=
  Homeomorph.symm <|
    homeomorphOfContinuousOpen (Equiv.sumProdDistrib X Y Z).symm
        ((continuous_inl.prodMap continuous_id).sumElim
          (continuous_inr.prodMap continuous_id)) <|
      (isOpenMap_inl.prodMap IsOpenMap.id).sumElim (isOpenMap_inr.prodMap IsOpenMap.id)

/-- `X × (Y ⊕ Z)` is homeomorphic to `X × Y ⊕ X × Z`. -/
def prodSumDistrib : X × (Y ⊕ Z) ≃ₜ (X × Y) ⊕ (X × Z) :=
  (prodComm _ _).trans <| sumProdDistrib.trans <| sumCongr (prodComm _ _) (prodComm _ _)

variable {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]

/-- `(Σ i, X i) × Y` is homeomorphic to `Σ i, (X i × Y)`. -/
@[simps! apply symm_apply toEquiv]
def sigmaProdDistrib : (Σ i, X i) × Y ≃ₜ Σ i, X i × Y :=
  Homeomorph.symm <|
    homeomorphOfContinuousOpen (Equiv.sigmaProdDistrib X Y).symm
      (continuous_sigma fun _ => continuous_sigmaMk.fst'.prod_mk continuous_snd)
      (isOpenMap_sigma.2 fun _ => isOpenMap_sigmaMk.prodMap IsOpenMap.id)

end Distrib

/-- If `ι` has a unique element, then `ι → X` is homeomorphic to `X`. -/
@[simps! (config := .asFn)]
def funUnique (ι X : Type*) [Unique ι] [TopologicalSpace X] : (ι → X) ≃ₜ X where
  toEquiv := Equiv.funUnique ι X
  continuous_toFun := continuous_apply _
  continuous_invFun := continuous_pi fun _ => continuous_id

/-- A subset of a topological space is homeomorphic to its image under a homeomorphism.
-/
@[simps!]
def image (e : X ≃ₜ Y) (s : Set X) : s ≃ₜ e '' s where
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: by continuity!
  continuous_toFun := e.continuous.continuousOn.restrict_mapsTo (mapsTo_image _ _)
  continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).codRestrict _
  toEquiv := e.toEquiv.image s

/-- `Set.univ X` is homeomorphic to `X`. -/
@[simps! (config := .asFn)]
def Set.univ (X : Type*) [TopologicalSpace X] : (univ : Set X) ≃ₜ X where
  toEquiv := Equiv.Set.univ X
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _

/-- `s ×ˢ t` is homeomorphic to `s × t`. -/
@[simps!]
def Set.prod (s : Set X) (t : Set Y) : ↥(s ×ˢ t) ≃ₜ s × t where
  toEquiv := Equiv.Set.prod s t
  continuous_toFun :=
    (continuous_subtype_val.fst.subtype_mk _).prod_mk (continuous_subtype_val.snd.subtype_mk _)
  continuous_invFun :=
    (continuous_subtype_val.fst'.prod_mk continuous_subtype_val.snd').subtype_mk _

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: align the order of universes with `Equiv.ulift`
/-- `ULift X` is homeomorphic to `X`. -/
def ulift.{u, v} {X : Type u} [TopologicalSpace X] : ULift.{v, u} X ≃ₜ X where
  continuous_toFun := continuous_uliftDown
  continuous_invFun := continuous_uliftUp
  toEquiv := Equiv.ulift

/-- `Equiv.piCongrLeft` as a homeomorphism: this is the natural homeomorphism
`Π i, Y (e i) ≃ₜ Π j, Y j` obtained from a bijection `ι ≃ ι'`. -/
@[simps! apply toEquiv]
def piCongrLeft {ι ι' : Type*} {Y : ι' → Type*} [∀ j, TopologicalSpace (Y j)]
    (e : ι ≃ ι') : (∀ i, Y (e i)) ≃ₜ ∀ j, Y j where
  continuous_toFun := continuous_pi <| e.forall_congr_right.mp fun i ↦ by
    simpa only [Equiv.toFun_as_coe, Equiv.piCongrLeft_apply_apply] using continuous_apply i
  continuous_invFun := Pi.continuous_precomp' e
  toEquiv := Equiv.piCongrLeft _ e

/-- `Equiv.piCongrRight` as a homeomorphism: this is the natural homeomorphism
`Π i, Y₁ i ≃ₜ Π j, Y₂ i` obtained from homeomorphisms `Y₁ i ≃ₜ Y₂ i` for each `i`. -/
@[simps! apply toEquiv]
def piCongrRight {ι : Type*} {Y₁ Y₂ : ι → Type*} [∀ i, TopologicalSpace (Y₁ i)]
    [∀ i, TopologicalSpace (Y₂ i)] (F : ∀ i, Y₁ i ≃ₜ Y₂ i) : (∀ i, Y₁ i) ≃ₜ ∀ i, Y₂ i where
  continuous_toFun := Pi.continuous_postcomp' fun i ↦ (F i).continuous
  continuous_invFun := Pi.continuous_postcomp' fun i ↦ (F i).symm.continuous
  toEquiv := Equiv.piCongrRight fun i => (F i).toEquiv

@[simp]
theorem piCongrRight_symm {ι : Type*} {Y₁ Y₂ : ι → Type*} [∀ i, TopologicalSpace (Y₁ i)]
    [∀ i, TopologicalSpace (Y₂ i)] (F : ∀ i, Y₁ i ≃ₜ Y₂ i) :
    (piCongrRight F).symm = piCongrRight fun i => (F i).symm :=
  rfl

/-- `Equiv.piCongr` as a homeomorphism: this is the natural homeomorphism
`Π i₁, Y₁ i ≃ₜ Π i₂, Y₂ i₂` obtained from a bijection `ι₁ ≃ ι₂` and homeomorphisms
`Y₁ i₁ ≃ₜ Y₂ (e i₁)` for each `i₁ : ι₁`. -/
@[simps! apply toEquiv]
def piCongr {ι₁ ι₂ : Type*} {Y₁ : ι₁ → Type*} {Y₂ : ι₂ → Type*}
    [∀ i₁, TopologicalSpace (Y₁ i₁)] [∀ i₂, TopologicalSpace (Y₂ i₂)]
    (e : ι₁ ≃ ι₂) (F : ∀ i₁, Y₁ i₁ ≃ₜ Y₂ (e i₁)) : (∀ i₁, Y₁ i₁) ≃ₜ ∀ i₂, Y₂ i₂ :=
  (Homeomorph.piCongrRight F).trans (Homeomorph.piCongrLeft e)

/-- The natural homeomorphism `(ι ⊕ ι' → X) ≃ₜ (ι → X) × (ι' → X)`.
`Equiv.sumArrowEquivProdArrow` as a homeomorphism. -/
@[simps!]
def sumArrowHomeomorphProdArrow {ι ι' : Type*} : (ι ⊕ ι' → X) ≃ₜ (ι → X) × (ι' → X)  where
  toEquiv := Equiv.sumArrowEquivProdArrow _ _ _
  continuous_toFun := by
    simp only [Equiv.sumArrowEquivProdArrow, Equiv.coe_fn_mk, continuous_prod_mk]
    continuity
  continuous_invFun := continuous_pi fun i ↦ match i with
    | .inl i => by apply (continuous_apply _).comp' continuous_fst
    | .inr i => by apply (continuous_apply _).comp' continuous_snd

end Homeomorph
