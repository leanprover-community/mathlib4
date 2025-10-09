/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Sébastien Gouëzel, Zhouhang Zhou, Reid Barton,
Anatole Dedecker
-/
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.Topology.UniformSpace.Pi

/-!
# Uniform isomorphisms

This file defines uniform isomorphisms between two uniform spaces. They are bijections with both
directions uniformly continuous. We denote uniform isomorphisms with the notation `≃ᵤ`.

# Main definitions

* `UniformEquiv α β`: The type of uniform isomorphisms from `α` to `β`.
  This type can be denoted using the following notation: `α ≃ᵤ β`.

-/


open Set Filter

universe u v

variable {α : Type u} {β : Type*} {γ : Type*} {δ : Type*}

-- not all spaces are homeomorphic to each other
/-- Uniform isomorphism between `α` and `β` -/
structure UniformEquiv (α : Type*) (β : Type*) [UniformSpace α] [UniformSpace β] extends
  α ≃ β where
  /-- Uniform continuity of the function -/
  uniformContinuous_toFun : UniformContinuous toFun
  /-- Uniform continuity of the inverse -/
  uniformContinuous_invFun : UniformContinuous invFun

/-- Uniform isomorphism between `α` and `β` -/
infixl:25 " ≃ᵤ " => UniformEquiv

namespace UniformEquiv

variable [UniformSpace α] [UniformSpace β] [UniformSpace γ] [UniformSpace δ]

theorem toEquiv_injective : Function.Injective (toEquiv : α ≃ᵤ β → α ≃ β)
  | ⟨e, h₁, h₂⟩, ⟨e', h₁', h₂'⟩, h => by simpa only [mk.injEq]

instance : EquivLike (α ≃ᵤ β) α β where
  coe h := h.toEquiv
  inv h := h.toEquiv.symm
  left_inv h := h.left_inv
  right_inv h := h.right_inv
  coe_injective' _ _ H _ := toEquiv_injective <| DFunLike.ext' H

@[simp]
theorem uniformEquiv_mk_coe (a : Equiv α β) (b c) : (UniformEquiv.mk a b c : α → β) = a :=
  rfl

/-- Inverse of a uniform isomorphism. -/
protected def symm (h : α ≃ᵤ β) : β ≃ᵤ α where
  uniformContinuous_toFun := h.uniformContinuous_invFun
  uniformContinuous_invFun := h.uniformContinuous_toFun
  toEquiv := h.toEquiv.symm

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def Simps.apply (h : α ≃ᵤ β) : α → β :=
  h

/-- See Note [custom simps projection] -/
def Simps.symm_apply (h : α ≃ᵤ β) : β → α :=
  h.symm

initialize_simps_projections UniformEquiv (toFun → apply, invFun → symm_apply)

@[simp]
theorem coe_toEquiv (h : α ≃ᵤ β) : ⇑h.toEquiv = h :=
  rfl

@[simp]
theorem coe_symm_toEquiv (h : α ≃ᵤ β) : ⇑h.toEquiv.symm = h.symm :=
  rfl

@[ext]
theorem ext {h h' : α ≃ᵤ β} (H : ∀ x, h x = h' x) : h = h' :=
  toEquiv_injective <| Equiv.ext H

/-- Identity map as a uniform isomorphism. -/
@[simps! -fullyApplied apply]
protected def refl (α : Type*) [UniformSpace α] : α ≃ᵤ α where
  uniformContinuous_toFun := uniformContinuous_id
  uniformContinuous_invFun := uniformContinuous_id
  toEquiv := Equiv.refl α

/-- Composition of two uniform isomorphisms. -/
protected def trans (h₁ : α ≃ᵤ β) (h₂ : β ≃ᵤ γ) : α ≃ᵤ γ where
  uniformContinuous_toFun := h₂.uniformContinuous_toFun.comp h₁.uniformContinuous_toFun
  uniformContinuous_invFun := h₁.uniformContinuous_invFun.comp h₂.uniformContinuous_invFun
  toEquiv := Equiv.trans h₁.toEquiv h₂.toEquiv

@[simp]
theorem trans_apply (h₁ : α ≃ᵤ β) (h₂ : β ≃ᵤ γ) (a : α) : h₁.trans h₂ a = h₂ (h₁ a) :=
  rfl

@[simp]
theorem uniformEquiv_mk_coe_symm (a : Equiv α β) (b c) :
    ((UniformEquiv.mk a b c).symm : β → α) = a.symm :=
  rfl

@[simp]
theorem refl_symm : (UniformEquiv.refl α).symm = UniformEquiv.refl α :=
  rfl

protected theorem uniformContinuous (h : α ≃ᵤ β) : UniformContinuous h :=
  h.uniformContinuous_toFun

@[continuity]
protected theorem continuous (h : α ≃ᵤ β) : Continuous h :=
  h.uniformContinuous.continuous

protected theorem uniformContinuous_symm (h : α ≃ᵤ β) : UniformContinuous h.symm :=
  h.uniformContinuous_invFun

-- otherwise `by continuity` can't prove continuity of `h.to_equiv.symm`
@[continuity]
protected theorem continuous_symm (h : α ≃ᵤ β) : Continuous h.symm :=
  h.uniformContinuous_symm.continuous

/-- A uniform isomorphism as a homeomorphism. -/
protected def toHomeomorph (e : α ≃ᵤ β) : α ≃ₜ β :=
  { e.toEquiv with
    continuous_toFun := e.continuous
    continuous_invFun := e.continuous_symm }

lemma toHomeomorph_apply (e : α ≃ᵤ β) : (e.toHomeomorph : α → β) = e := rfl

lemma toHomeomorph_symm_apply (e : α ≃ᵤ β) : (e.toHomeomorph.symm : β → α) = e.symm := rfl

@[simp]
theorem apply_symm_apply (h : α ≃ᵤ β) (x : β) : h (h.symm x) = x :=
  h.toEquiv.apply_symm_apply x

@[simp]
theorem symm_apply_apply (h : α ≃ᵤ β) (x : α) : h.symm (h x) = x :=
  h.toEquiv.symm_apply_apply x

protected theorem bijective (h : α ≃ᵤ β) : Function.Bijective h :=
  h.toEquiv.bijective

protected theorem injective (h : α ≃ᵤ β) : Function.Injective h :=
  h.toEquiv.injective

protected theorem surjective (h : α ≃ᵤ β) : Function.Surjective h :=
  h.toEquiv.surjective

/-- Change the uniform equiv `f` to make the inverse function definitionally equal to `g`. -/
def changeInv (f : α ≃ᵤ β) (g : β → α) (hg : Function.RightInverse g f) : α ≃ᵤ β :=
  have : g = f.symm :=
    funext fun x => calc
      g x = f.symm (f (g x)) := (f.left_inv (g x)).symm
      _ = f.symm x := by rw [hg x]
  { toFun := f
    invFun := g
    left_inv := by convert f.left_inv
    right_inv := by convert f.right_inv using 1
    uniformContinuous_toFun := f.uniformContinuous
    uniformContinuous_invFun := by convert f.symm.uniformContinuous }

@[simp]
theorem symm_comp_self (h : α ≃ᵤ β) : (h.symm : β → α) ∘ h = id :=
  funext h.symm_apply_apply

@[simp]
theorem self_comp_symm (h : α ≃ᵤ β) : (h : α → β) ∘ h.symm = id :=
  funext h.apply_symm_apply

theorem range_coe (h : α ≃ᵤ β) : range h = univ := by simp

theorem image_symm (h : α ≃ᵤ β) : image h.symm = preimage h :=
  funext h.symm.toEquiv.image_eq_preimage

theorem preimage_symm (h : α ≃ᵤ β) : preimage h.symm = image h :=
  (funext h.toEquiv.image_eq_preimage).symm

@[simp]
theorem image_preimage (h : α ≃ᵤ β) (s : Set β) : h '' (h ⁻¹' s) = s :=
  h.toEquiv.image_preimage s

@[simp]
theorem preimage_image (h : α ≃ᵤ β) (s : Set α) : h ⁻¹' (h '' s) = s :=
  h.toEquiv.preimage_image s

theorem isUniformInducing (h : α ≃ᵤ β) : IsUniformInducing h :=
  IsUniformInducing.of_comp h.uniformContinuous h.symm.uniformContinuous <| by
    simp only [symm_comp_self, IsUniformInducing.id]

theorem comap_eq (h : α ≃ᵤ β) : UniformSpace.comap h ‹_› = ‹_› :=
  h.isUniformInducing.comap_uniformSpace

lemma isUniformEmbedding (h : α ≃ᵤ β) : IsUniformEmbedding h := ⟨h.isUniformInducing, h.injective⟩

theorem completeSpace_iff (h : α ≃ᵤ β) : CompleteSpace α ↔ CompleteSpace β :=
  completeSpace_congr h.isUniformEmbedding

/-- Uniform equiv given a uniform embedding. -/
noncomputable def ofIsUniformEmbedding (f : α → β) (hf : IsUniformEmbedding f) :
    α ≃ᵤ Set.range f where
  uniformContinuous_toFun := hf.isUniformInducing.uniformContinuous.subtype_mk _
  uniformContinuous_invFun := by
    rw [hf.isUniformInducing.uniformContinuous_iff, Equiv.invFun_as_coe,
      Equiv.self_comp_ofInjective_symm]
    exact uniformContinuous_subtype_val
  toEquiv := Equiv.ofInjective f hf.injective

/-- If two sets are equal, then they are uniformly equivalent. -/
def setCongr {s t : Set α} (h : s = t) : s ≃ᵤ t where
  uniformContinuous_toFun := uniformContinuous_subtype_val.subtype_mk _
  uniformContinuous_invFun := uniformContinuous_subtype_val.subtype_mk _
  toEquiv := Equiv.setCongr h

/-- Product of two uniform isomorphisms. -/
def prodCongr (h₁ : α ≃ᵤ β) (h₂ : γ ≃ᵤ δ) : α × γ ≃ᵤ β × δ where
  uniformContinuous_toFun :=
    (h₁.uniformContinuous.comp uniformContinuous_fst).prodMk
      (h₂.uniformContinuous.comp uniformContinuous_snd)
  uniformContinuous_invFun :=
    (h₁.symm.uniformContinuous.comp uniformContinuous_fst).prodMk
      (h₂.symm.uniformContinuous.comp uniformContinuous_snd)
  toEquiv := h₁.toEquiv.prodCongr h₂.toEquiv

@[simp]
theorem prodCongr_symm (h₁ : α ≃ᵤ β) (h₂ : γ ≃ᵤ δ) :
    (h₁.prodCongr h₂).symm = h₁.symm.prodCongr h₂.symm :=
  rfl

@[simp]
theorem coe_prodCongr (h₁ : α ≃ᵤ β) (h₂ : γ ≃ᵤ δ) : ⇑(h₁.prodCongr h₂) = Prod.map h₁ h₂ :=
  rfl

section

variable (α β γ)

/-- `α × β` is uniformly isomorphic to `β × α`. -/
def prodComm : α × β ≃ᵤ β × α where
  uniformContinuous_toFun := uniformContinuous_snd.prodMk uniformContinuous_fst
  uniformContinuous_invFun := uniformContinuous_snd.prodMk uniformContinuous_fst
  toEquiv := Equiv.prodComm α β

@[simp]
theorem prodComm_symm : (prodComm α β).symm = prodComm β α :=
  rfl

@[simp]
theorem coe_prodComm : ⇑(prodComm α β) = Prod.swap :=
  rfl

/-- `(α × β) × γ` is uniformly isomorphic to `α × (β × γ)`. -/
def prodAssoc : (α × β) × γ ≃ᵤ α × β × γ where
  uniformContinuous_toFun :=
    (uniformContinuous_fst.comp uniformContinuous_fst).prodMk
      ((uniformContinuous_snd.comp uniformContinuous_fst).prodMk uniformContinuous_snd)
  uniformContinuous_invFun :=
    (uniformContinuous_fst.prodMk (uniformContinuous_fst.comp
      uniformContinuous_snd)).prodMk (uniformContinuous_snd.comp uniformContinuous_snd)
  toEquiv := Equiv.prodAssoc α β γ

/-- `α × {*}` is uniformly isomorphic to `α`. -/
@[simps! -fullyApplied apply]
def prodPunit : α × PUnit ≃ᵤ α where
  toEquiv := Equiv.prodPUnit α
  uniformContinuous_toFun := uniformContinuous_fst
  uniformContinuous_invFun := uniformContinuous_id.prodMk uniformContinuous_const

/-- `{*} × α` is uniformly isomorphic to `α`. -/
def punitProd : PUnit × α ≃ᵤ α :=
  (prodComm _ _).trans (prodPunit _)

@[simp]
theorem coe_punitProd : ⇑(punitProd α) = Prod.snd :=
  rfl

/-- `Equiv.piCongrLeft` as a uniform isomorphism: this is the natural isomorphism
`Π i, β (e i) ≃ᵤ Π j, β j` obtained from a bijection `ι ≃ ι'`. -/
@[simps toEquiv, simps! -isSimp apply]
def piCongrLeft {ι ι' : Type*} {β : ι' → Type*} [∀ j, UniformSpace (β j)]
    (e : ι ≃ ι') : (∀ i, β (e i)) ≃ᵤ ∀ j, β j where
  uniformContinuous_toFun := uniformContinuous_pi.mpr <| e.forall_congr_right.mp fun i ↦ by
    simpa only [Equiv.toFun_as_coe, Equiv.piCongrLeft_apply_apply] using
      Pi.uniformContinuous_proj _ i
  uniformContinuous_invFun := Pi.uniformContinuous_precomp' _ e
  toEquiv := Equiv.piCongrLeft _ e

@[simp]
lemma piCongrLeft_refl {ι : Type*} {X : ι → Type*} [∀ i, UniformSpace (X i)] :
    piCongrLeft (.refl ι) = .refl (∀ i, X i) :=
  rfl

@[simp]
lemma piCongrLeft_symm_apply {ι ι' : Type*} {X : ι' → Type*} [∀ j, UniformSpace (X j)]
    (e : ι ≃ ι') : ⇑(piCongrLeft (β := X) e).symm = (· <| e ·) :=
  rfl

@[simp]
lemma piCongrLeft_apply_apply {ι ι' : Type*} {X : ι' → Type*} [∀ j, UniformSpace (X j)]
    (e : ι ≃ ι') (x : ∀ i, X (e i)) i : piCongrLeft e x (e i) = x i :=
  Equiv.piCongrLeft_apply_apply ..

/-- `Equiv.piCongrRight` as a uniform isomorphism: this is the natural isomorphism
`Π i, β₁ i ≃ᵤ Π j, β₂ i` obtained from uniform isomorphisms `β₁ i ≃ᵤ β₂ i` for each `i`. -/
@[simps! apply toEquiv]
def piCongrRight {ι : Type*} {β₁ β₂ : ι → Type*} [∀ i, UniformSpace (β₁ i)]
    [∀ i, UniformSpace (β₂ i)] (F : ∀ i, β₁ i ≃ᵤ β₂ i) : (∀ i, β₁ i) ≃ᵤ ∀ i, β₂ i where
  uniformContinuous_toFun := Pi.uniformContinuous_postcomp' _ fun i ↦ (F i).uniformContinuous
  uniformContinuous_invFun := Pi.uniformContinuous_postcomp' _ fun i ↦ (F i).symm.uniformContinuous
  toEquiv := Equiv.piCongrRight fun i => (F i).toEquiv

@[simp]
theorem piCongrRight_symm {ι : Type*} {β₁ β₂ : ι → Type*} [∀ i, UniformSpace (β₁ i)]
    [∀ i, UniformSpace (β₂ i)] (F : ∀ i, β₁ i ≃ᵤ β₂ i) :
    (piCongrRight F).symm = piCongrRight fun i => (F i).symm :=
  rfl

@[simp]
theorem piCongrRight_refl {ι : Type*} {X : ι → Type*} [∀ i, UniformSpace (X i)] :
    piCongrRight (fun i ↦ .refl (X i)) = .refl (∀ i, X i) :=
  rfl

/-- `Equiv.piCongr` as a uniform isomorphism: this is the natural isomorphism
`Π i₁, β₁ i ≃ᵤ Π i₂, β₂ i₂` obtained from a bijection `ι₁ ≃ ι₂` and isomorphisms
`β₁ i₁ ≃ᵤ β₂ (e i₁)` for each `i₁ : ι₁`. -/
@[simps! apply toEquiv]
def piCongr {ι₁ ι₂ : Type*} {β₁ : ι₁ → Type*} {β₂ : ι₂ → Type*}
    [∀ i₁, UniformSpace (β₁ i₁)] [∀ i₂, UniformSpace (β₂ i₂)]
    (e : ι₁ ≃ ι₂) (F : ∀ i₁, β₁ i₁ ≃ᵤ β₂ (e i₁)) : (∀ i₁, β₁ i₁) ≃ᵤ ∀ i₂, β₂ i₂ :=
  (UniformEquiv.piCongrRight F).trans (UniformEquiv.piCongrLeft e)

/-- Uniform equivalence between `ULift α` and `α`. -/
def ulift : ULift.{v, u} α ≃ᵤ α :=
  { Equiv.ulift with
    uniformContinuous_toFun := uniformContinuous_comap
    uniformContinuous_invFun := by
      have hf : IsUniformInducing (@Equiv.ulift.{v, u} α).toFun := ⟨rfl⟩
      simp_rw [hf.uniformContinuous_iff]
      exact uniformContinuous_id }

end

/-- If `ι` has a unique element, then `ι → α` is uniformly isomorphic to `α`. -/
@[simps! -fullyApplied]
def funUnique (ι α : Type*) [Unique ι] [UniformSpace α] : (ι → α) ≃ᵤ α where
  toEquiv := Equiv.funUnique ι α
  uniformContinuous_toFun := Pi.uniformContinuous_proj _ _
  uniformContinuous_invFun := uniformContinuous_pi.mpr fun _ => uniformContinuous_id

/-- Uniform isomorphism between dependent functions `Π i : Fin 2, α i` and `α 0 × α 1`. -/
@[simps! -fullyApplied]
def piFinTwo (α : Fin 2 → Type u) [∀ i, UniformSpace (α i)] : (∀ i, α i) ≃ᵤ α 0 × α 1 where
  toEquiv := piFinTwoEquiv α
  uniformContinuous_toFun := (Pi.uniformContinuous_proj _ 0).prodMk (Pi.uniformContinuous_proj _ 1)
  uniformContinuous_invFun :=
    uniformContinuous_pi.mpr <| Fin.forall_fin_two.2 ⟨uniformContinuous_fst, uniformContinuous_snd⟩

/-- Uniform isomorphism between `α² = Fin 2 → α` and `α × α`. -/
@[simps! -fullyApplied]
def finTwoArrow (α : Type*) [UniformSpace α] : (Fin 2 → α) ≃ᵤ α × α :=
  { piFinTwo fun _ => α with toEquiv := finTwoArrowEquiv α }

/-- A subset of a uniform space is uniformly isomorphic to its image under a uniform isomorphism.
-/
def image (e : α ≃ᵤ β) (s : Set α) : s ≃ᵤ e '' s where
  uniformContinuous_toFun := (e.uniformContinuous.comp uniformContinuous_subtype_val).subtype_mk _
  uniformContinuous_invFun :=
    (e.symm.uniformContinuous.comp uniformContinuous_subtype_val).subtype_mk _
  toEquiv := e.toEquiv.image s

/-- A uniform isomorphism `e : α ≃ᵤ β` lifts to subtypes `{ a : α // p a } ≃ᵤ { b : β // q b }`
provided `p = q ∘ e`. -/
@[simps!]
def subtype {p : α → Prop} {q : β → Prop} (e : α ≃ᵤ β) (h : ∀ a, p a ↔ q (e a)) :
    { a : α // p a } ≃ᵤ { b : β // q b } where
  uniformContinuous_toFun := by
    simpa [Equiv.coe_subtypeEquiv_eq_map] using e.uniformContinuous.subtype_map _
  uniformContinuous_invFun := by
    simpa [Equiv.coe_subtypeEquiv_eq_map] using e.symm.uniformContinuous.subtype_map _
  __ := e.subtypeEquiv h

end UniformEquiv

/-- A uniform inducing equiv between uniform spaces is a uniform isomorphism. -/
def Equiv.toUniformEquivOfIsUniformInducing [UniformSpace α] [UniformSpace β] (f : α ≃ β)
    (hf : IsUniformInducing f) : α ≃ᵤ β :=
  { f with
    uniformContinuous_toFun := hf.uniformContinuous
    uniformContinuous_invFun := hf.uniformContinuous_iff.2 <| by simpa using uniformContinuous_id }
