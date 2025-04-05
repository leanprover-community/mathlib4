/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Sébastien Gouëzel, Zhouhang Zhou, Reid Barton
-/
import Mathlib.Topology.ContinuousMap.Defs
import Mathlib.Topology.Maps.Basic

/-!
# Homeomorphisms

This file defines homeomorphisms between two topological spaces. They are bijections with both
directions continuous. We denote homeomorphisms with the notation `≃ₜ`.

# Main definitions and results

* `Homeomorph X Y`: The type of homeomorphisms from `X` to `Y`.
  This type can be denoted using the following notation: `X ≃ₜ Y`.
* `HomeomorphClass`: `HomeomorphClass F A B` states that `F` is a type of homeomorphisms.

* `Homeomorph.symm`: the inverse of a homeomorphism
* `Homeomorph.trans`: composing two homeomorphisms
* Homeomorphisms are open and closed embeddings, inducing, quotient maps etc.
* `Homeomorph.homeomorphOfContinuousOpen`: A continuous bijection that is
  an open map is a homeomorphism.
* `Homeomorph.homeomorphOfUnique`: if both `X` and `Y` have a unique element, then `X ≃ₜ Y`.
* `Equiv.toHomeomorph`: an equivalence between topological spaces respecting openness
  is a homeomorphism.

-/

open Set Topology

variable {X Y W Z : Type*}

/-- Homeomorphism between `X` and `Y`, also called topological isomorphism -/
structure Homeomorph (X : Type*) (Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    extends X ≃ Y where
  /-- The forward map of a homeomorphism is a continuous function. -/
  continuous_toFun : Continuous toFun := by continuity
  /-- The inverse map of a homeomorphism is a continuous function. -/
  continuous_invFun : Continuous invFun := by continuity

@[inherit_doc]
infixl:25 " ≃ₜ " => Homeomorph

namespace Homeomorph

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace W] [TopologicalSpace Z]
  {X' Y' : Type*} [TopologicalSpace X'] [TopologicalSpace Y']

theorem toEquiv_injective : Function.Injective (toEquiv : X ≃ₜ Y → X ≃ Y)
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl => rfl

instance : EquivLike (X ≃ₜ Y) X Y where
  coe h := h.toEquiv
  inv h := h.toEquiv.symm
  left_inv h := h.left_inv
  right_inv h := h.right_inv
  coe_injective' _ _ H _ := toEquiv_injective <| DFunLike.ext' H

@[simp] theorem homeomorph_mk_coe (a : X ≃ Y) (b c) : (Homeomorph.mk a b c : X → Y) = a :=
  rfl

/-- The unique homeomorphism between two empty types. -/
protected def empty [IsEmpty X] [IsEmpty Y] : X ≃ₜ Y where
  __ := Equiv.equivOfIsEmpty X Y

/-- Inverse of a homeomorphism. -/
@[symm]
protected def symm (h : X ≃ₜ Y) : Y ≃ₜ X where
  continuous_toFun := h.continuous_invFun
  continuous_invFun := h.continuous_toFun
  toEquiv := h.toEquiv.symm

@[simp] theorem symm_symm (h : X ≃ₜ Y) : h.symm.symm = h := rfl

theorem symm_bijective : Function.Bijective (Homeomorph.symm : (X ≃ₜ Y) → Y ≃ₜ X) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

/-- See Note [custom simps projection] -/
def Simps.symm_apply (h : X ≃ₜ Y) : Y → X :=
  h.symm

initialize_simps_projections Homeomorph (toFun → apply, invFun → symm_apply)

@[simp]
theorem coe_toEquiv (h : X ≃ₜ Y) : ⇑h.toEquiv = h :=
  rfl

@[simp]
theorem coe_symm_toEquiv (h : X ≃ₜ Y) : ⇑h.toEquiv.symm = h.symm :=
  rfl

@[ext]
theorem ext {h h' : X ≃ₜ Y} (H : ∀ x, h x = h' x) : h = h' :=
  DFunLike.ext _ _ H

/-- Identity map as a homeomorphism. -/
@[simps! -fullyApplied apply]
protected def refl (X : Type*) [TopologicalSpace X] : X ≃ₜ X where
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id
  toEquiv := Equiv.refl X

/-- Composition of two homeomorphisms. -/
@[trans]
protected def trans (h₁ : X ≃ₜ Y) (h₂ : Y ≃ₜ Z) : X ≃ₜ Z where
  continuous_toFun := h₂.continuous_toFun.comp h₁.continuous_toFun
  continuous_invFun := h₁.continuous_invFun.comp h₂.continuous_invFun
  toEquiv := Equiv.trans h₁.toEquiv h₂.toEquiv

@[simp]
theorem trans_apply (h₁ : X ≃ₜ Y) (h₂ : Y ≃ₜ Z) (x : X) : h₁.trans h₂ x = h₂ (h₁ x) :=
  rfl

@[simp]
theorem symm_trans_apply (f : X ≃ₜ Y) (g : Y ≃ₜ Z) (z : Z) :
    (f.trans g).symm z = f.symm (g.symm z) := rfl

@[simp]
theorem homeomorph_mk_coe_symm (a : X ≃ Y) (b c) :
    ((Homeomorph.mk a b c).symm : Y → X) = a.symm :=
  rfl

@[simp]
theorem refl_symm : (Homeomorph.refl X).symm = Homeomorph.refl X :=
  rfl

@[continuity, fun_prop]
protected theorem continuous (h : X ≃ₜ Y) : Continuous h :=
  h.continuous_toFun

-- otherwise `by continuity` can't prove continuity of `h.to_equiv.symm`
@[continuity]
protected theorem continuous_symm (h : X ≃ₜ Y) : Continuous h.symm :=
  h.continuous_invFun

@[simp]
theorem apply_symm_apply (h : X ≃ₜ Y) (y : Y) : h (h.symm y) = y :=
  h.toEquiv.apply_symm_apply y

@[simp]
theorem symm_apply_apply (h : X ≃ₜ Y) (x : X) : h.symm (h x) = x :=
  h.toEquiv.symm_apply_apply x

@[simp]
theorem self_trans_symm (h : X ≃ₜ Y) : h.trans h.symm = Homeomorph.refl X := by
  ext
  apply symm_apply_apply

@[simp]
theorem symm_trans_self (h : X ≃ₜ Y) : h.symm.trans h = Homeomorph.refl Y := by
  ext
  apply apply_symm_apply

protected theorem bijective (h : X ≃ₜ Y) : Function.Bijective h :=
  h.toEquiv.bijective

protected theorem injective (h : X ≃ₜ Y) : Function.Injective h :=
  h.toEquiv.injective

protected theorem surjective (h : X ≃ₜ Y) : Function.Surjective h :=
  h.toEquiv.surjective

/-- Change the homeomorphism `f` to make the inverse function definitionally equal to `g`. -/
def changeInv (f : X ≃ₜ Y) (g : Y → X) (hg : Function.RightInverse g f) : X ≃ₜ Y :=
  haveI : g = f.symm := (f.left_inv.eq_rightInverse hg).symm
  { toFun := f
    invFun := g
    left_inv := by convert f.left_inv
    right_inv := by convert f.right_inv using 1
    continuous_toFun := f.continuous
    continuous_invFun := by convert f.symm.continuous }

@[simp]
theorem symm_comp_self (h : X ≃ₜ Y) : h.symm ∘ h = id :=
  funext h.symm_apply_apply

@[simp]
theorem self_comp_symm (h : X ≃ₜ Y) : h ∘ h.symm = id :=
  funext h.apply_symm_apply

theorem range_coe (h : X ≃ₜ Y) : range h = univ := by simp

theorem image_symm (h : X ≃ₜ Y) : image h.symm = preimage h :=
  funext h.symm.toEquiv.image_eq_preimage

theorem preimage_symm (h : X ≃ₜ Y) : preimage h.symm = image h :=
  (funext h.toEquiv.image_eq_preimage).symm

@[simp]
theorem image_preimage (h : X ≃ₜ Y) (s : Set Y) : h '' (h ⁻¹' s) = s :=
  h.toEquiv.image_preimage s

@[simp]
theorem preimage_image (h : X ≃ₜ Y) (s : Set X) : h ⁻¹' (h '' s) = s :=
  h.toEquiv.preimage_image s

theorem image_eq_preimage (h : X ≃ₜ Y) (s : Set X) : h '' s = h.symm ⁻¹' s :=
  h.toEquiv.image_eq_preimage s

lemma image_compl (h : X ≃ₜ Y) (s : Set X) : h '' (sᶜ) = (h '' s)ᶜ :=
  h.toEquiv.image_compl s

lemma isInducing (h : X ≃ₜ Y) : IsInducing h :=
  .of_comp h.continuous h.symm.continuous <| by simp only [symm_comp_self, IsInducing.id]

@[deprecated (since := "2024-10-28")] alias inducing := isInducing

theorem induced_eq (h : X ≃ₜ Y) : TopologicalSpace.induced h ‹_› = ‹_› := h.isInducing.1.symm

theorem isQuotientMap (h : X ≃ₜ Y) : IsQuotientMap h :=
  IsQuotientMap.of_comp h.symm.continuous h.continuous <| by
    simp only [self_comp_symm, IsQuotientMap.id]

@[deprecated (since := "2024-10-22")]
alias quotientMap := isQuotientMap

theorem coinduced_eq (h : X ≃ₜ Y) : TopologicalSpace.coinduced h ‹_› = ‹_› :=
  h.isQuotientMap.2.symm

theorem isEmbedding (h : X ≃ₜ Y) : IsEmbedding h := ⟨h.isInducing, h.injective⟩

@[deprecated (since := "2024-10-26")]
alias embedding := isEmbedding

@[simp]
theorem isOpen_preimage (h : X ≃ₜ Y) {s : Set Y} : IsOpen (h ⁻¹' s) ↔ IsOpen s :=
  h.isQuotientMap.isOpen_preimage

@[simp]
theorem isOpen_image (h : X ≃ₜ Y) {s : Set X} : IsOpen (h '' s) ↔ IsOpen s := by
  rw [← preimage_symm, isOpen_preimage]

protected theorem isOpenMap (h : X ≃ₜ Y) : IsOpenMap h := fun _ => h.isOpen_image.2

protected theorem isOpenQuotientMap (h : X ≃ₜ Y) : IsOpenQuotientMap h :=
  ⟨h.surjective, h.continuous, h.isOpenMap⟩

@[simp]
theorem isClosed_preimage (h : X ≃ₜ Y) {s : Set Y} : IsClosed (h ⁻¹' s) ↔ IsClosed s := by
  simp only [← isOpen_compl_iff, ← preimage_compl, isOpen_preimage]

@[simp]
theorem isClosed_image (h : X ≃ₜ Y) {s : Set X} : IsClosed (h '' s) ↔ IsClosed s := by
  rw [← preimage_symm, isClosed_preimage]

protected theorem isClosedMap (h : X ≃ₜ Y) : IsClosedMap h := fun _ => h.isClosed_image.2

theorem isOpenEmbedding (h : X ≃ₜ Y) : IsOpenEmbedding h :=
  .of_isEmbedding_isOpenMap h.isEmbedding h.isOpenMap

@[deprecated (since := "2024-10-18")]
alias openEmbedding := isOpenEmbedding

theorem isClosedEmbedding (h : X ≃ₜ Y) : IsClosedEmbedding h :=
  .of_isEmbedding_isClosedMap h.isEmbedding h.isClosedMap

@[deprecated (since := "2024-10-20")]
alias closedEmbedding := isClosedEmbedding

theorem preimage_closure (h : X ≃ₜ Y) (s : Set Y) : h ⁻¹' closure s = closure (h ⁻¹' s) :=
  h.isOpenMap.preimage_closure_eq_closure_preimage h.continuous _

theorem image_closure (h : X ≃ₜ Y) (s : Set X) : h '' closure s = closure (h '' s) := by
  rw [← preimage_symm, preimage_closure]

theorem preimage_interior (h : X ≃ₜ Y) (s : Set Y) : h ⁻¹' interior s = interior (h ⁻¹' s) :=
  h.isOpenMap.preimage_interior_eq_interior_preimage h.continuous _

theorem image_interior (h : X ≃ₜ Y) (s : Set X) : h '' interior s = interior (h '' s) := by
  rw [← preimage_symm, preimage_interior]

theorem preimage_frontier (h : X ≃ₜ Y) (s : Set Y) : h ⁻¹' frontier s = frontier (h ⁻¹' s) :=
  h.isOpenMap.preimage_frontier_eq_frontier_preimage h.continuous _

theorem image_frontier (h : X ≃ₜ Y) (s : Set X) : h '' frontier s = frontier (h '' s) := by
  rw [← preimage_symm, preimage_frontier]

/-- If a bijective map `e : X ≃ Y` is continuous and open, then it is a homeomorphism. -/
@[simps toEquiv]
def homeomorphOfContinuousOpen (e : X ≃ Y) (h₁ : Continuous e) (h₂ : IsOpenMap e) : X ≃ₜ Y where
  continuous_toFun := h₁
  continuous_invFun := e.continuous_symm_iff.2 h₂
  toEquiv := e

/-- If a bijective map `e : X ≃ Y` is continuous and closed, then it is a homeomorphism. -/
def homeomorphOfContinuousClosed (e : X ≃ Y) (h₁ : Continuous e) (h₂ : IsClosedMap e) : X ≃ₜ Y where
  continuous_toFun := h₁
  continuous_invFun := by
    rw [continuous_iff_isClosed]
    intro s hs
    convert ← h₂ s hs using 1
    apply e.image_eq_preimage
  toEquiv := e

@[simp]
theorem homeomorphOfContinuousOpen_apply (e : X ≃ Y) (h₁ : Continuous e) (h₂ : IsOpenMap e) :
    ⇑(homeomorphOfContinuousOpen e h₁ h₂) = e := rfl

@[simp]
theorem homeomorphOfContinuousOpen_symm_apply (e : X ≃ Y) (h₁ : Continuous e) (h₂ : IsOpenMap e) :
    ⇑(homeomorphOfContinuousOpen e h₁ h₂).symm = e.symm := rfl

@[simp]
theorem comp_continuous_iff (h : X ≃ₜ Y) {f : Z → X} : Continuous (h ∘ f) ↔ Continuous f :=
  h.isInducing.continuous_iff.symm

@[simp]
theorem comp_continuous_iff' (h : X ≃ₜ Y) {f : Y → Z} : Continuous (f ∘ h) ↔ Continuous f :=
  h.isQuotientMap.continuous_iff.symm

theorem comp_continuousAt_iff (h : X ≃ₜ Y) (f : Z → X) (z : Z) :
    ContinuousAt (h ∘ f) z ↔ ContinuousAt f z :=
  h.isInducing.continuousAt_iff.symm

theorem comp_continuousAt_iff' (h : X ≃ₜ Y) (f : Y → Z) (x : X) :
    ContinuousAt (f ∘ h) x ↔ ContinuousAt f (h x) :=
  h.isInducing.continuousAt_iff' (by simp)

@[simp]
theorem comp_isOpenMap_iff (h : X ≃ₜ Y) {f : Z → X} : IsOpenMap (h ∘ f) ↔ IsOpenMap f := by
  refine ⟨?_, fun hf => h.isOpenMap.comp hf⟩
  intro hf
  rw [← Function.id_comp f, ← h.symm_comp_self, Function.comp_assoc]
  exact h.symm.isOpenMap.comp hf

@[simp]
theorem comp_isOpenMap_iff' (h : X ≃ₜ Y) {f : Y → Z} : IsOpenMap (f ∘ h) ↔ IsOpenMap f := by
  refine ⟨?_, fun hf => hf.comp h.isOpenMap⟩
  intro hf
  rw [← Function.comp_id f, ← h.self_comp_symm, ← Function.comp_assoc]
  exact hf.comp h.symm.isOpenMap

variable (X Y) in
/-- If both `X` and `Y` have a unique element, then `X ≃ₜ Y`. -/
@[simps!]
def homeomorphOfUnique [Unique X] [Unique Y] : X ≃ₜ Y :=
  { Equiv.ofUnique X Y with
    continuous_toFun := continuous_const
    continuous_invFun := continuous_const }

end Homeomorph

namespace Equiv
variable {Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- An equivalence between topological spaces respecting openness is a homeomorphism. -/
@[simps toEquiv]
def toHomeomorph (e : X ≃ Y) (he : ∀ s, IsOpen (e ⁻¹' s) ↔ IsOpen s) : X ≃ₜ Y where
  toEquiv := e
  continuous_toFun := continuous_def.2 fun _ ↦ (he _).2
  continuous_invFun := continuous_def.2 fun s ↦ by convert (he _).1; simp

@[simp] lemma coe_toHomeomorph (e : X ≃ Y) (he) : ⇑(e.toHomeomorph he) = e := rfl
lemma toHomeomorph_apply (e : X ≃ Y) (he) (x : X) : e.toHomeomorph he x = e x := rfl

@[simp] lemma toHomeomorph_refl :
  (Equiv.refl X).toHomeomorph (fun _s ↦ Iff.rfl) = Homeomorph.refl _ := rfl

@[simp] lemma toHomeomorph_symm (e : X ≃ Y) (he) :
  (e.toHomeomorph he).symm = e.symm.toHomeomorph fun s ↦ by convert (he _).symm; simp := rfl

lemma toHomeomorph_trans (e : X ≃ Y) (f : Y ≃ Z) (he hf) :
    (e.trans f).toHomeomorph (fun _s ↦ (he _).trans (hf _)) =
    (e.toHomeomorph he).trans (f.toHomeomorph hf) := rfl

/-- An inducing equiv between topological spaces is a homeomorphism. -/
@[simps toEquiv]
def toHomeomorphOfIsInducing (f : X ≃ Y) (hf : IsInducing f) : X ≃ₜ Y :=
  { f with
    continuous_toFun := hf.continuous
    continuous_invFun := hf.continuous_iff.2 <| by simpa using continuous_id }

@[deprecated (since := "2024-10-28")] alias toHomeomorphOfInducing := toHomeomorphOfIsInducing

end Equiv

/-- `HomeomorphClass F A B` states that `F` is a type of homeomorphisms. -/
class HomeomorphClass (F : Type*) (A B : outParam Type*)
    [TopologicalSpace A] [TopologicalSpace B] [h : EquivLike F A B] : Prop where
  map_continuous : ∀ (f : F), Continuous f
  inv_continuous : ∀ (f : F), Continuous (h.inv f)

namespace HomeomorphClass

variable {F α β : Type*} [TopologicalSpace α] [TopologicalSpace β] [EquivLike F α β]

/-- Turn an element of a type `F` satisfying `HomeomorphClass F α β` into an actual
`Homeomorph`. This is declared as the default coercion from `F` to `α ≃ₜ β`. -/
@[coe]
def toHomeomorph [h : HomeomorphClass F α β] (f : F) : α ≃ₜ β :=
  { (f : α ≃ β) with
    continuous_toFun := h.map_continuous f
    continuous_invFun := h.inv_continuous f }

@[simp]
theorem coe_coe [h : HomeomorphClass F α β] (f : F) : ⇑(h.toHomeomorph f) = ⇑f := rfl

instance [HomeomorphClass F α β] : CoeOut F (α ≃ₜ β) :=
  ⟨HomeomorphClass.toHomeomorph⟩

theorem toHomeomorph_injective [HomeomorphClass F α β] : Function.Injective ((↑) : F → α ≃ₜ β) :=
  fun _ _ e ↦ DFunLike.ext _ _ fun a ↦ congr_arg (fun e : α ≃ₜ β ↦ e.toFun a) e

instance [HomeomorphClass F α β] : ContinuousMapClass F α β where
  map_continuous  f := map_continuous f

instance : HomeomorphClass (α ≃ₜ β) α β where
  map_continuous e := e.continuous_toFun
  inv_continuous e := e.continuous_invFun

end HomeomorphClass
