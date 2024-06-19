/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.MeasureTheory.MeasurableSpace.Basic

/-!
# Measurable embeddings and equivalences

A measurable equivalence between measurable spaces is an equivalence
which respects the σ-algebras, that is, for which both directions of
the equivalence are measurable functions.

## Main definitions

* `MeasurableEmbedding`: a map `f : α → β` is called a *measurable embedding* if it is injective,
  measurable, and sends measurable sets to measurable sets.
* `MeasurableEquiv`: an equivalence `α ≃ β` is a *measurable equivalence* if its forward and inverse
  functions are measurable.

We prove a multitude of elementary lemmas about these, and one more substantial theorem:

* `MeasurableEmbedding.schroederBernstein`: the **measurable Schröder-Bernstein Theorem**: given
  measurable embeddings `α → β` and `β → α`, we can find a measurable equivalence `α ≃ᵐ β`.

## Notation

* We write `α ≃ᵐ β` for measurable equivalences between the measurable spaces `α` and `β`.
  This should not be confused with `≃ₘ` which is used for diffeomorphisms between manifolds.

## Tags

measurable equivalence, measurable embedding
-/


open Set Function Equiv MeasureTheory

universe uι

variable {α β γ δ δ' : Type*} {ι : Sort uι} {s t u : Set α}

/-- A map `f : α → β` is called a *measurable embedding* if it is injective, measurable, and sends
measurable sets to measurable sets. The latter assumption can be replaced with “`f` has measurable
inverse `g : Set.range f → α`”, see `MeasurableEmbedding.measurable_rangeSplitting`,
`MeasurableEmbedding.of_measurable_inverse_range`, and
`MeasurableEmbedding.of_measurable_inverse`.

One more interpretation: `f` is a measurable embedding if it defines a measurable equivalence to its
range and the range is a measurable set. One implication is formalized as
`MeasurableEmbedding.equivRange`; the other one follows from
`MeasurableEquiv.measurableEmbedding`, `MeasurableEmbedding.subtype_coe`, and
`MeasurableEmbedding.comp`. -/
structure MeasurableEmbedding [MeasurableSpace α] [MeasurableSpace β] (f : α → β) : Prop where
  /-- A measurable embedding is injective. -/
  protected injective : Injective f
  /-- A measurable embedding is a measurable function. -/
  protected measurable : Measurable f
  /-- The image of a measurable set under a measurable embedding is a measurable set. -/
  protected measurableSet_image' : ∀ ⦃s⦄, MeasurableSet s → MeasurableSet (f '' s)
#align measurable_embedding MeasurableEmbedding

namespace MeasurableEmbedding

variable {mα : MeasurableSpace α} [MeasurableSpace β] [MeasurableSpace γ] {f : α → β} {g : β → γ}

theorem measurableSet_image (hf : MeasurableEmbedding f) :
    MeasurableSet (f '' s) ↔ MeasurableSet s :=
  ⟨fun h => by simpa only [hf.injective.preimage_image] using hf.measurable h, fun h =>
    hf.measurableSet_image' h⟩
#align measurable_embedding.measurable_set_image MeasurableEmbedding.measurableSet_image

theorem id : MeasurableEmbedding (id : α → α) :=
  ⟨injective_id, measurable_id, fun s hs => by rwa [image_id]⟩
#align measurable_embedding.id MeasurableEmbedding.id

theorem comp (hg : MeasurableEmbedding g) (hf : MeasurableEmbedding f) :
    MeasurableEmbedding (g ∘ f) :=
  ⟨hg.injective.comp hf.injective, hg.measurable.comp hf.measurable, fun s hs => by
    rwa [image_comp, hg.measurableSet_image, hf.measurableSet_image]⟩
#align measurable_embedding.comp MeasurableEmbedding.comp

theorem subtype_coe (hs : MeasurableSet s) : MeasurableEmbedding ((↑) : s → α) where
  injective := Subtype.coe_injective
  measurable := measurable_subtype_coe
  measurableSet_image' := fun _ => MeasurableSet.subtype_image hs
#align measurable_embedding.subtype_coe MeasurableEmbedding.subtype_coe

theorem measurableSet_range (hf : MeasurableEmbedding f) : MeasurableSet (range f) := by
  rw [← image_univ]
  exact hf.measurableSet_image' MeasurableSet.univ
#align measurable_embedding.measurable_set_range MeasurableEmbedding.measurableSet_range

theorem measurableSet_preimage (hf : MeasurableEmbedding f) {s : Set β} :
    MeasurableSet (f ⁻¹' s) ↔ MeasurableSet (s ∩ range f) := by
  rw [← image_preimage_eq_inter_range, hf.measurableSet_image]
#align measurable_embedding.measurable_set_preimage MeasurableEmbedding.measurableSet_preimage

theorem measurable_rangeSplitting (hf : MeasurableEmbedding f) :
    Measurable (rangeSplitting f) := fun s hs => by
  rwa [preimage_rangeSplitting hf.injective,
    ← (subtype_coe hf.measurableSet_range).measurableSet_image, ← image_comp,
    coe_comp_rangeFactorization, hf.measurableSet_image]
#align measurable_embedding.measurable_range_splitting MeasurableEmbedding.measurable_rangeSplitting

theorem measurable_extend (hf : MeasurableEmbedding f) {g : α → γ} {g' : β → γ} (hg : Measurable g)
    (hg' : Measurable g') : Measurable (extend f g g') := by
  refine measurable_of_restrict_of_restrict_compl hf.measurableSet_range ?_ ?_
  · rw [restrict_extend_range]
    simpa only [rangeSplitting] using hg.comp hf.measurable_rangeSplitting
  · rw [restrict_extend_compl_range]
    exact hg'.comp measurable_subtype_coe
#align measurable_embedding.measurable_extend MeasurableEmbedding.measurable_extend

theorem exists_measurable_extend (hf : MeasurableEmbedding f) {g : α → γ} (hg : Measurable g)
    (hne : β → Nonempty γ) : ∃ g' : β → γ, Measurable g' ∧ g' ∘ f = g :=
  ⟨extend f g fun x => Classical.choice (hne x),
    hf.measurable_extend hg (measurable_const' fun _ _ => rfl),
    funext fun _ => hf.injective.extend_apply _ _ _⟩
#align measurable_embedding.exists_measurable_extend MeasurableEmbedding.exists_measurable_extend

theorem measurable_comp_iff (hg : MeasurableEmbedding g) : Measurable (g ∘ f) ↔ Measurable f := by
  refine ⟨fun H => ?_, hg.measurable.comp⟩
  suffices Measurable ((rangeSplitting g ∘ rangeFactorization g) ∘ f) by
    rwa [(rightInverse_rangeSplitting hg.injective).comp_eq_id] at this
  exact hg.measurable_rangeSplitting.comp H.subtype_mk
#align measurable_embedding.measurable_comp_iff MeasurableEmbedding.measurable_comp_iff

end MeasurableEmbedding

theorem MeasurableSet.exists_measurable_proj {_ : MeasurableSpace α}
    (hs : MeasurableSet s) (hne : s.Nonempty) : ∃ f : α → s, Measurable f ∧ ∀ x : s, f x = x :=
  let ⟨f, hfm, hf⟩ :=
    (MeasurableEmbedding.subtype_coe hs).exists_measurable_extend measurable_id fun _ =>
      hne.to_subtype
  ⟨f, hfm, congr_fun hf⟩
#align measurable_set.exists_measurable_proj MeasurableSet.exists_measurable_proj

/-- Equivalences between measurable spaces. Main application is the simplification of measurability
statements along measurable equivalences. -/
structure MeasurableEquiv (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] extends α ≃ β where
  /-- The forward function of a measurable equivalence is measurable. -/
  measurable_toFun : Measurable toEquiv
  /-- The inverse function of a measurable equivalence is measurable. -/
  measurable_invFun : Measurable toEquiv.symm
#align measurable_equiv MeasurableEquiv

@[inherit_doc]
infixl:25 " ≃ᵐ " => MeasurableEquiv

namespace MeasurableEquiv

variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]

theorem toEquiv_injective : Injective (toEquiv : α ≃ᵐ β → α ≃ β) := by
  rintro ⟨e₁, _, _⟩ ⟨e₂, _, _⟩ (rfl : e₁ = e₂)
  rfl
#align measurable_equiv.to_equiv_injective MeasurableEquiv.toEquiv_injective

instance instEquivLike : EquivLike (α ≃ᵐ β) α β where
  coe e := e.toEquiv
  inv e := e.toEquiv.symm
  left_inv e := e.toEquiv.left_inv
  right_inv e := e.toEquiv.right_inv
  coe_injective' _ _ he _ := toEquiv_injective <| DFunLike.ext' he

@[simp]
theorem coe_toEquiv (e : α ≃ᵐ β) : (e.toEquiv : α → β) = e :=
  rfl
#align measurable_equiv.coe_to_equiv MeasurableEquiv.coe_toEquiv

@[measurability]
protected theorem measurable (e : α ≃ᵐ β) : Measurable (e : α → β) :=
  e.measurable_toFun
#align measurable_equiv.measurable MeasurableEquiv.measurable

@[simp]
theorem coe_mk (e : α ≃ β) (h1 : Measurable e) (h2 : Measurable e.symm) :
    ((⟨e, h1, h2⟩ : α ≃ᵐ β) : α → β) = e :=
  rfl
#align measurable_equiv.coe_mk MeasurableEquiv.coe_mk

/-- Any measurable space is equivalent to itself. -/
def refl (α : Type*) [MeasurableSpace α] : α ≃ᵐ α where
  toEquiv := Equiv.refl α
  measurable_toFun := measurable_id
  measurable_invFun := measurable_id
#align measurable_equiv.refl MeasurableEquiv.refl

instance instInhabited : Inhabited (α ≃ᵐ α) := ⟨refl α⟩

/-- The composition of equivalences between measurable spaces. -/
def trans (ab : α ≃ᵐ β) (bc : β ≃ᵐ γ) : α ≃ᵐ γ where
  toEquiv := ab.toEquiv.trans bc.toEquiv
  measurable_toFun := bc.measurable_toFun.comp ab.measurable_toFun
  measurable_invFun := ab.measurable_invFun.comp bc.measurable_invFun
#align measurable_equiv.trans MeasurableEquiv.trans

theorem coe_trans (ab : α ≃ᵐ β) (bc : β ≃ᵐ γ) : ⇑(ab.trans bc) = bc ∘ ab := rfl

/-- The inverse of an equivalence between measurable spaces. -/
def symm (ab : α ≃ᵐ β) : β ≃ᵐ α where
  toEquiv := ab.toEquiv.symm
  measurable_toFun := ab.measurable_invFun
  measurable_invFun := ab.measurable_toFun
#align measurable_equiv.symm MeasurableEquiv.symm

@[simp]
theorem coe_toEquiv_symm (e : α ≃ᵐ β) : (e.toEquiv.symm : β → α) = e.symm :=
  rfl
#align measurable_equiv.coe_to_equiv_symm MeasurableEquiv.coe_toEquiv_symm

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def Simps.apply (h : α ≃ᵐ β) : α → β := h
#align measurable_equiv.simps.apply MeasurableEquiv.Simps.apply

/-- See Note [custom simps projection] -/
def Simps.symm_apply (h : α ≃ᵐ β) : β → α := h.symm
#align measurable_equiv.simps.symm_apply MeasurableEquiv.Simps.symm_apply

initialize_simps_projections MeasurableEquiv (toFun → apply, invFun → symm_apply)

@[ext] theorem ext {e₁ e₂ : α ≃ᵐ β} (h : (e₁ : α → β) = e₂) : e₁ = e₂ := DFunLike.ext' h
#align measurable_equiv.ext MeasurableEquiv.ext

@[simp]
theorem symm_mk (e : α ≃ β) (h1 : Measurable e) (h2 : Measurable e.symm) :
    (⟨e, h1, h2⟩ : α ≃ᵐ β).symm = ⟨e.symm, h2, h1⟩ :=
  rfl
#align measurable_equiv.symm_mk MeasurableEquiv.symm_mk

attribute [simps! apply toEquiv] trans refl

@[simp]
theorem symm_symm (e : α ≃ᵐ β) : e.symm.symm = e := rfl

theorem symm_bijective :
    Function.Bijective (MeasurableEquiv.symm : (α ≃ᵐ β) → β ≃ᵐ α) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
theorem symm_refl (α : Type*) [MeasurableSpace α] : (refl α).symm = refl α :=
  rfl
#align measurable_equiv.symm_refl MeasurableEquiv.symm_refl

@[simp]
theorem symm_comp_self (e : α ≃ᵐ β) : e.symm ∘ e = id :=
  funext e.left_inv
#align measurable_equiv.symm_comp_self MeasurableEquiv.symm_comp_self

@[simp]
theorem self_comp_symm (e : α ≃ᵐ β) : e ∘ e.symm = id :=
  funext e.right_inv
#align measurable_equiv.self_comp_symm MeasurableEquiv.self_comp_symm

@[simp]
theorem apply_symm_apply (e : α ≃ᵐ β) (y : β) : e (e.symm y) = y :=
  e.right_inv y
#align measurable_equiv.apply_symm_apply MeasurableEquiv.apply_symm_apply

@[simp]
theorem symm_apply_apply (e : α ≃ᵐ β) (x : α) : e.symm (e x) = x :=
  e.left_inv x
#align measurable_equiv.symm_apply_apply MeasurableEquiv.symm_apply_apply

@[simp]
theorem symm_trans_self (e : α ≃ᵐ β) : e.symm.trans e = refl β :=
  ext e.self_comp_symm
#align measurable_equiv.symm_trans_self MeasurableEquiv.symm_trans_self

@[simp]
theorem self_trans_symm (e : α ≃ᵐ β) : e.trans e.symm = refl α :=
  ext e.symm_comp_self
#align measurable_equiv.self_trans_symm MeasurableEquiv.self_trans_symm

protected theorem surjective (e : α ≃ᵐ β) : Surjective e :=
  e.toEquiv.surjective
#align measurable_equiv.surjective MeasurableEquiv.surjective

protected theorem bijective (e : α ≃ᵐ β) : Bijective e :=
  e.toEquiv.bijective
#align measurable_equiv.bijective MeasurableEquiv.bijective

protected theorem injective (e : α ≃ᵐ β) : Injective e :=
  e.toEquiv.injective
#align measurable_equiv.injective MeasurableEquiv.injective

@[simp]
theorem symm_preimage_preimage (e : α ≃ᵐ β) (s : Set β) : e.symm ⁻¹' (e ⁻¹' s) = s :=
  e.toEquiv.symm_preimage_preimage s
#align measurable_equiv.symm_preimage_preimage MeasurableEquiv.symm_preimage_preimage

theorem image_eq_preimage (e : α ≃ᵐ β) (s : Set α) : e '' s = e.symm ⁻¹' s :=
  e.toEquiv.image_eq_preimage s
#align measurable_equiv.image_eq_preimage MeasurableEquiv.image_eq_preimage

lemma preimage_symm (e : α ≃ᵐ β) (s : Set α) : e.symm ⁻¹' s = e '' s := (image_eq_preimage _ _).symm

lemma image_symm (e : α ≃ᵐ β) (s : Set β) : e.symm '' s = e ⁻¹' s := by
  rw [← symm_symm e, preimage_symm, symm_symm]

lemma eq_image_iff_symm_image_eq (e : α ≃ᵐ β) (s : Set β) (t : Set α) :
    s = e '' t ↔ e.symm '' s = t := by
  rw [← coe_toEquiv, Equiv.eq_image_iff_symm_image_eq, coe_toEquiv_symm]

@[simp]
lemma image_preimage (e : α ≃ᵐ β) (s : Set β) : e '' (e ⁻¹' s) = s := by
  rw [← coe_toEquiv, Equiv.image_preimage]

@[simp]
lemma preimage_image (e : α ≃ᵐ β) (s : Set α) : e ⁻¹' (e '' s) = s := by
  rw [← coe_toEquiv, Equiv.preimage_image]

@[simp]
theorem measurableSet_preimage (e : α ≃ᵐ β) {s : Set β} :
    MeasurableSet (e ⁻¹' s) ↔ MeasurableSet s :=
  ⟨fun h => by simpa only [symm_preimage_preimage] using e.symm.measurable h, fun h =>
    e.measurable h⟩
#align measurable_equiv.measurable_set_preimage MeasurableEquiv.measurableSet_preimage

@[simp]
theorem measurableSet_image (e : α ≃ᵐ β) :
    MeasurableSet (e '' s) ↔ MeasurableSet s := by rw [image_eq_preimage, measurableSet_preimage]
#align measurable_equiv.measurable_set_image MeasurableEquiv.measurableSet_image

@[simp] theorem map_eq (e : α ≃ᵐ β) : MeasurableSpace.map e ‹_› = ‹_› :=
  e.measurable.le_map.antisymm' fun _s ↦ e.measurableSet_preimage.1
#align measurable_equiv.map_eq MeasurableEquiv.map_eq

/-- A measurable equivalence is a measurable embedding. -/
protected theorem measurableEmbedding (e : α ≃ᵐ β) : MeasurableEmbedding e where
  injective := e.injective
  measurable := e.measurable
  measurableSet_image' := fun _ => e.measurableSet_image.2
#align measurable_equiv.measurable_embedding MeasurableEquiv.measurableEmbedding

/-- Equal measurable spaces are equivalent. -/
protected def cast {α β} [i₁ : MeasurableSpace α] [i₂ : MeasurableSpace β] (h : α = β)
    (hi : HEq i₁ i₂) : α ≃ᵐ β where
  toEquiv := Equiv.cast h
  measurable_toFun := by
    subst h
    subst hi
    exact measurable_id
  measurable_invFun := by
    subst h
    subst hi
    exact measurable_id
#align measurable_equiv.cast MeasurableEquiv.cast

/-- Measurable equivalence between `ULift α` and `α`. -/
def ulift.{u, v} {α : Type u} [MeasurableSpace α] : ULift.{v, u} α ≃ᵐ α :=
  ⟨Equiv.ulift, measurable_down, measurable_up⟩

protected theorem measurable_comp_iff {f : β → γ} (e : α ≃ᵐ β) :
    Measurable (f ∘ e) ↔ Measurable f :=
  Iff.intro
    (fun hfe => by
      have : Measurable (f ∘ (e.symm.trans e).toEquiv) := hfe.comp e.symm.measurable
      rwa [coe_toEquiv, symm_trans_self] at this)
    fun h => h.comp e.measurable
#align measurable_equiv.measurable_comp_iff MeasurableEquiv.measurable_comp_iff

/-- Any two types with unique elements are measurably equivalent. -/
def ofUniqueOfUnique (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] [Unique α] [Unique β] :
    α ≃ᵐ β where
  toEquiv := equivOfUnique α β
  measurable_toFun := Subsingleton.measurable
  measurable_invFun := Subsingleton.measurable
#align measurable_equiv.of_unique_of_unique MeasurableEquiv.ofUniqueOfUnique

/-- Products of equivalent measurable spaces are equivalent. -/
def prodCongr (ab : α ≃ᵐ β) (cd : γ ≃ᵐ δ) : α × γ ≃ᵐ β × δ where
  toEquiv := .prodCongr ab.toEquiv cd.toEquiv
  measurable_toFun :=
    (ab.measurable_toFun.comp measurable_id.fst).prod_mk
      (cd.measurable_toFun.comp measurable_id.snd)
  measurable_invFun :=
    (ab.measurable_invFun.comp measurable_id.fst).prod_mk
      (cd.measurable_invFun.comp measurable_id.snd)
#align measurable_equiv.prod_congr MeasurableEquiv.prodCongr

/-- Products of measurable spaces are symmetric. -/
def prodComm : α × β ≃ᵐ β × α where
  toEquiv := .prodComm α β
  measurable_toFun := measurable_id.snd.prod_mk measurable_id.fst
  measurable_invFun := measurable_id.snd.prod_mk measurable_id.fst
#align measurable_equiv.prod_comm MeasurableEquiv.prodComm

/-- Products of measurable spaces are associative. -/
def prodAssoc : (α × β) × γ ≃ᵐ α × β × γ where
  toEquiv := .prodAssoc α β γ
  measurable_toFun := measurable_fst.fst.prod_mk <| measurable_fst.snd.prod_mk measurable_snd
  measurable_invFun := (measurable_fst.prod_mk measurable_snd.fst).prod_mk measurable_snd.snd
#align measurable_equiv.prod_assoc MeasurableEquiv.prodAssoc

/-- Sums of measurable spaces are symmetric. -/
def sumCongr (ab : α ≃ᵐ β) (cd : γ ≃ᵐ δ) : Sum α γ ≃ᵐ Sum β δ where
  toEquiv := .sumCongr ab.toEquiv cd.toEquiv
  measurable_toFun := ab.measurable.sumMap cd.measurable
  measurable_invFun := ab.symm.measurable.sumMap cd.symm.measurable
#align measurable_equiv.sum_congr MeasurableEquiv.sumCongr

/-- `s ×ˢ t ≃ (s × t)` as measurable spaces. -/
def Set.prod (s : Set α) (t : Set β) : ↥(s ×ˢ t) ≃ᵐ s × t where
  toEquiv := Equiv.Set.prod s t
  measurable_toFun :=
    measurable_id.subtype_val.fst.subtype_mk.prod_mk measurable_id.subtype_val.snd.subtype_mk
  measurable_invFun :=
    Measurable.subtype_mk <| measurable_id.fst.subtype_val.prod_mk measurable_id.snd.subtype_val
#align measurable_equiv.set.prod MeasurableEquiv.Set.prod

/-- `univ α ≃ α` as measurable spaces. -/
def Set.univ (α : Type*) [MeasurableSpace α] : (univ : Set α) ≃ᵐ α where
  toEquiv := Equiv.Set.univ α
  measurable_toFun := measurable_id.subtype_val
  measurable_invFun := measurable_id.subtype_mk
#align measurable_equiv.set.univ MeasurableEquiv.Set.univ

/-- `{a} ≃ Unit` as measurable spaces. -/
def Set.singleton (a : α) : ({a} : Set α) ≃ᵐ Unit where
  toEquiv := Equiv.Set.singleton a
  measurable_toFun := measurable_const
  measurable_invFun := measurable_const
#align measurable_equiv.set.singleton MeasurableEquiv.Set.singleton

/-- `α` is equivalent to its image in `α ⊕ β` as measurable spaces. -/
def Set.rangeInl : (range Sum.inl : Set (α ⊕ β)) ≃ᵐ α where
  toEquiv := Equiv.Set.rangeInl α β
  measurable_toFun s (hs : MeasurableSet s) := by
    refine ⟨_, hs.inl_image, Set.ext ?_⟩
    rintro ⟨ab, a, rfl⟩
    simp [Set.range_inl]
  measurable_invFun := Measurable.subtype_mk measurable_inl
#align measurable_equiv.set.range_inl MeasurableEquiv.Set.rangeInl

/-- `β` is equivalent to its image in `α ⊕ β` as measurable spaces. -/
def Set.rangeInr : (range Sum.inr : Set (Sum α β)) ≃ᵐ β where
  toEquiv := Equiv.Set.rangeInr α β
  measurable_toFun s (hs : MeasurableSet s) := by
    refine ⟨_, hs.inr_image, Set.ext ?_⟩
    rintro ⟨ab, b, rfl⟩
    simp [Set.range_inr]
  measurable_invFun := Measurable.subtype_mk measurable_inr
#align measurable_equiv.set.range_inr MeasurableEquiv.Set.rangeInr

/-- Products distribute over sums (on the right) as measurable spaces. -/
def sumProdDistrib (α β γ) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] :
    (α ⊕ β) × γ ≃ᵐ (α × γ) ⊕ (β × γ) where
  toEquiv := .sumProdDistrib α β γ
  measurable_toFun := by
    refine
      measurable_of_measurable_union_cover (range Sum.inl ×ˢ (univ : Set γ))
        (range Sum.inr ×ˢ (univ : Set γ)) (measurableSet_range_inl.prod MeasurableSet.univ)
        (measurableSet_range_inr.prod MeasurableSet.univ)
        (by rintro ⟨a | b, c⟩ <;> simp [Set.prod_eq]) ?_ ?_
    · refine (Set.prod (range Sum.inl) univ).symm.measurable_comp_iff.1 ?_
      refine (prodCongr Set.rangeInl (Set.univ _)).symm.measurable_comp_iff.1 ?_
      exact measurable_inl
    · refine (Set.prod (range Sum.inr) univ).symm.measurable_comp_iff.1 ?_
      refine (prodCongr Set.rangeInr (Set.univ _)).symm.measurable_comp_iff.1 ?_
      exact measurable_inr
  measurable_invFun :=
    measurable_sum ((measurable_inl.comp measurable_fst).prod_mk measurable_snd)
      ((measurable_inr.comp measurable_fst).prod_mk measurable_snd)
#align measurable_equiv.sum_prod_distrib MeasurableEquiv.sumProdDistrib

/-- Products distribute over sums (on the left) as measurable spaces. -/
def prodSumDistrib (α β γ) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] :
    α × (β ⊕ γ) ≃ᵐ (α × β) ⊕ (α × γ) :=
  prodComm.trans <| (sumProdDistrib _ _ _).trans <| sumCongr prodComm prodComm
#align measurable_equiv.prod_sum_distrib MeasurableEquiv.prodSumDistrib

/-- Products distribute over sums as measurable spaces. -/
def sumProdSum (α β γ δ) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] : (α ⊕ β) × (γ ⊕ δ) ≃ᵐ ((α × γ) ⊕ (α × δ)) ⊕ ((β × γ) ⊕ (β × δ)) :=
  (sumProdDistrib _ _ _).trans <| sumCongr (prodSumDistrib _ _ _) (prodSumDistrib _ _ _)
#align measurable_equiv.sum_prod_sum MeasurableEquiv.sumProdSum

variable {π π' : δ' → Type*} [∀ x, MeasurableSpace (π x)] [∀ x, MeasurableSpace (π' x)]

/-- A family of measurable equivalences `Π a, β₁ a ≃ᵐ β₂ a` generates a measurable equivalence
  between `Π a, β₁ a` and `Π a, β₂ a`. -/
def piCongrRight (e : ∀ a, π a ≃ᵐ π' a) : (∀ a, π a) ≃ᵐ ∀ a, π' a where
  toEquiv := .piCongrRight fun a => (e a).toEquiv
  measurable_toFun :=
    measurable_pi_lambda _ fun i => (e i).measurable_toFun.comp (measurable_pi_apply i)
  measurable_invFun :=
    measurable_pi_lambda _ fun i => (e i).measurable_invFun.comp (measurable_pi_apply i)
#align measurable_equiv.Pi_congr_right MeasurableEquiv.piCongrRight

variable (π) in
/-- Moving a dependent type along an equivalence of coordinates, as a measurable equivalence. -/
def piCongrLeft (f : δ ≃ δ') : (∀ b, π (f b)) ≃ᵐ ∀ a, π a where
  __ := Equiv.piCongrLeft π f
  measurable_toFun := measurable_piCongrLeft f
  measurable_invFun := by
    simp only [invFun_as_coe, coe_fn_symm_mk]
    rw [measurable_pi_iff]
    exact fun i => measurable_pi_apply (f i)

theorem coe_piCongrLeft (f : δ ≃ δ') :
    ⇑(MeasurableEquiv.piCongrLeft π f) = f.piCongrLeft π := by rfl

lemma piCongrLeft_apply_apply {ι ι' : Type*} (e : ι ≃ ι') {β : ι' → Type*}
    [∀ i', MeasurableSpace (β i')] (x : (i : ι) → β (e i)) (i : ι) :
    piCongrLeft (fun i' ↦ β i') e x (e i) = x i := by
  rw [piCongrLeft, coe_mk, Equiv.piCongrLeft_apply_apply]

/-- Pi-types are measurably equivalent to iterated products. -/
@[simps! (config := .asFn)]
def piMeasurableEquivTProd [DecidableEq δ'] {l : List δ'} (hnd : l.Nodup) (h : ∀ i, i ∈ l) :
    (∀ i, π i) ≃ᵐ List.TProd π l where
  toEquiv := List.TProd.piEquivTProd hnd h
  measurable_toFun := measurable_tProd_mk l
  measurable_invFun := measurable_tProd_elim' h
#align measurable_equiv.pi_measurable_equiv_tprod MeasurableEquiv.piMeasurableEquivTProd

variable (π) in
/-- The measurable equivalence `(∀ i, π i) ≃ᵐ π ⋆` when the domain of `π` only contains `⋆` -/
@[simps! (config := .asFn)]
def piUnique [Unique δ'] : (∀ i, π i) ≃ᵐ π default where
  toEquiv := Equiv.piUnique π
  measurable_toFun := measurable_pi_apply _
  measurable_invFun := measurable_uniqueElim

/-- If `α` has a unique term, then the type of function `α → β` is measurably equivalent to `β`. -/
@[simps! (config := .asFn)]
def funUnique (α β : Type*) [Unique α] [MeasurableSpace β] : (α → β) ≃ᵐ β :=
  MeasurableEquiv.piUnique _
#align measurable_equiv.fun_unique MeasurableEquiv.funUnique

/-- The space `Π i : Fin 2, α i` is measurably equivalent to `α 0 × α 1`. -/
@[simps! (config := .asFn)]
def piFinTwo (α : Fin 2 → Type*) [∀ i, MeasurableSpace (α i)] : (∀ i, α i) ≃ᵐ α 0 × α 1 where
  toEquiv := piFinTwoEquiv α
  measurable_toFun := Measurable.prod (measurable_pi_apply _) (measurable_pi_apply _)
  measurable_invFun := measurable_pi_iff.2 <| Fin.forall_fin_two.2 ⟨measurable_fst, measurable_snd⟩
#align measurable_equiv.pi_fin_two MeasurableEquiv.piFinTwo

/-- The space `Fin 2 → α` is measurably equivalent to `α × α`. -/
@[simps! (config := .asFn)]
def finTwoArrow : (Fin 2 → α) ≃ᵐ α × α :=
  piFinTwo fun _ => α
#align measurable_equiv.fin_two_arrow MeasurableEquiv.finTwoArrow

/-- Measurable equivalence between `Π j : Fin (n + 1), α j` and
`α i × Π j : Fin n, α (Fin.succAbove i j)`. -/
@[simps! (config := .asFn)]
def piFinSuccAbove {n : ℕ} (α : Fin (n + 1) → Type*) [∀ i, MeasurableSpace (α i)]
    (i : Fin (n + 1)) : (∀ j, α j) ≃ᵐ α i × ∀ j, α (i.succAbove j) where
  toEquiv := .piFinSuccAbove α i
  measurable_toFun := (measurable_pi_apply i).prod_mk <| measurable_pi_iff.2 fun j =>
    measurable_pi_apply _
  measurable_invFun := measurable_pi_iff.2 <| i.forall_iff_succAbove.2
    ⟨by simp only [piFinSuccAbove_symm_apply, Fin.insertNth_apply_same, measurable_fst],
      fun j => by simpa only [piFinSuccAbove_symm_apply, Fin.insertNth_apply_succAbove]
        using (measurable_pi_apply _).comp measurable_snd⟩
#align measurable_equiv.pi_fin_succ_above_equiv MeasurableEquiv.piFinSuccAbove

variable (π)

/-- Measurable equivalence between (dependent) functions on a type and pairs of functions on
`{i // p i}` and `{i // ¬p i}`. See also `Equiv.piEquivPiSubtypeProd`. -/
@[simps! (config := .asFn)]
def piEquivPiSubtypeProd (p : δ' → Prop) [DecidablePred p] :
    (∀ i, π i) ≃ᵐ (∀ i : Subtype p, π i) × ∀ i : { i // ¬p i }, π i where
  toEquiv := .piEquivPiSubtypeProd p π
  measurable_toFun := measurable_piEquivPiSubtypeProd π p
  measurable_invFun := measurable_piEquivPiSubtypeProd_symm π p
#align measurable_equiv.pi_equiv_pi_subtype_prod MeasurableEquiv.piEquivPiSubtypeProd

/-- The measurable equivalence between the pi type over a sum type and a product of pi-types.
This is similar to `MeasurableEquiv.piEquivPiSubtypeProd`. -/
def sumPiEquivProdPi (α : δ ⊕ δ' → Type*) [∀ i, MeasurableSpace (α i)] :
    (∀ i, α i) ≃ᵐ (∀ i, α (.inl i)) × ∀ i', α (.inr i') where
  __ := Equiv.sumPiEquivProdPi α
  measurable_toFun := by
    apply Measurable.prod <;> rw [measurable_pi_iff] <;> rintro i <;> apply measurable_pi_apply
  measurable_invFun := by
    rw [measurable_pi_iff]; rintro (i | i)
    · exact measurable_pi_iff.1 measurable_fst _
    · exact measurable_pi_iff.1 measurable_snd _

theorem coe_sumPiEquivProdPi (α : δ ⊕ δ' → Type*) [∀ i, MeasurableSpace (α i)] :
    ⇑(MeasurableEquiv.sumPiEquivProdPi α) = Equiv.sumPiEquivProdPi α := by rfl

theorem coe_sumPiEquivProdPi_symm (α : δ ⊕ δ' → Type*) [∀ i, MeasurableSpace (α i)] :
    ⇑(MeasurableEquiv.sumPiEquivProdPi α).symm = (Equiv.sumPiEquivProdPi α).symm := by rfl

/-- The measurable equivalence for (dependent) functions on an Option type
  `(∀ i : Option δ, α i) ≃ᵐ (∀ (i : δ), α i) × α none`. -/
def piOptionEquivProd {δ : Type*} (α : Option δ → Type*) [∀ i, MeasurableSpace (α i)] :
    (∀ i, α i) ≃ᵐ (∀ (i : δ), α i) × α none :=
  let e : Option δ ≃ δ ⊕ Unit := Equiv.optionEquivSumPUnit δ
  let em1 : ((i : δ ⊕ Unit) → α (e.symm i)) ≃ᵐ ((a : Option δ) → α a) :=
    MeasurableEquiv.piCongrLeft α e.symm
  let em2 : ((i : δ ⊕ Unit) → α (e.symm i)) ≃ᵐ ((i : δ) → α (e.symm (Sum.inl i)))
      × ((i' : Unit) → α (e.symm (Sum.inr i'))) :=
    MeasurableEquiv.sumPiEquivProdPi (fun i ↦ α (e.symm i))
  let em3 : ((i : δ) → α (e.symm (Sum.inl i))) × ((i' : Unit) → α (e.symm (Sum.inr i')))
      ≃ᵐ ((i : δ) → α (some i)) × α none :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.refl ((i : δ) → α (e.symm (Sum.inl i))))
      (MeasurableEquiv.piUnique fun i ↦ α (e.symm (Sum.inr i)))
  em1.symm.trans <| em2.trans em3

/-- The measurable equivalence `(∀ i : s, π i) × (∀ i : t, π i) ≃ᵐ (∀ i : s ∪ t, π i)`
  for disjoint finsets `s` and `t`. `Equiv.piFinsetUnion` as a measurable equivalence. -/
def piFinsetUnion [DecidableEq δ'] {s t : Finset δ'} (h : Disjoint s t) :
    ((∀ i : s, π i) × ∀ i : t, π i) ≃ᵐ ∀ i : (s ∪ t : Finset δ'), π i :=
  letI e := Finset.union s t h
  MeasurableEquiv.sumPiEquivProdPi (fun b ↦ π (e b)) |>.symm.trans <|
    .piCongrLeft (fun i : ↥(s ∪ t) ↦ π i) e

/-- If `s` is a measurable set in a measurable space, that space is equivalent
to the sum of `s` and `sᶜ`. -/
def sumCompl {s : Set α} [DecidablePred (· ∈ s)] (hs : MeasurableSet s) :
    s ⊕ (sᶜ : Set α) ≃ᵐ α where
  toEquiv := .sumCompl (· ∈ s)
  measurable_toFun := measurable_subtype_coe.sumElim measurable_subtype_coe
  measurable_invFun := Measurable.dite measurable_inl measurable_inr hs
#align measurable_equiv.sum_compl MeasurableEquiv.sumCompl

/-- Convert a measurable involutive function `f` to a measurable permutation with
`toFun = invFun = f`. See also `Function.Involutive.toPerm`. -/
@[simps toEquiv]
def ofInvolutive (f : α → α) (hf : Involutive f) (hf' : Measurable f) : α ≃ᵐ α where
  toEquiv := hf.toPerm
  measurable_toFun := hf'
  measurable_invFun := hf'
#align measurable_equiv.of_involutive MeasurableEquiv.ofInvolutive

@[simp] theorem ofInvolutive_apply (f : α → α) (hf : Involutive f) (hf' : Measurable f) (a : α) :
    ofInvolutive f hf hf' a = f a := rfl
#align measurable_equiv.of_involutive_apply MeasurableEquiv.ofInvolutive_apply

@[simp] theorem ofInvolutive_symm (f : α → α) (hf : Involutive f) (hf' : Measurable f) :
    (ofInvolutive f hf hf').symm = ofInvolutive f hf hf' := rfl
#align measurable_equiv.of_involutive_symm MeasurableEquiv.ofInvolutive_symm

end MeasurableEquiv

namespace MeasurableEmbedding

variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] {f : α → β} {g : β → α}

@[simp] theorem comap_eq (hf : MeasurableEmbedding f) : MeasurableSpace.comap f ‹_› = ‹_› :=
  hf.measurable.comap_le.antisymm fun _s h ↦
    ⟨_, hf.measurableSet_image' h, hf.injective.preimage_image _⟩
#align measurable_embedding.comap_eq MeasurableEmbedding.comap_eq

theorem iff_comap_eq :
    MeasurableEmbedding f ↔
      Injective f ∧ MeasurableSpace.comap f ‹_› = ‹_› ∧ MeasurableSet (range f) :=
  ⟨fun hf ↦ ⟨hf.injective, hf.comap_eq, hf.measurableSet_range⟩, fun hf ↦
    { injective := hf.1
      measurable := by rw [← hf.2.1]; exact comap_measurable f
      measurableSet_image' := by
        rw [← hf.2.1]
        rintro _ ⟨s, hs, rfl⟩
        simpa only [image_preimage_eq_inter_range] using hs.inter hf.2.2 }⟩
#align measurable_embedding.iff_comap_eq MeasurableEmbedding.iff_comap_eq

/-- A set is equivalent to its image under a function `f` as measurable spaces,
  if `f` is a measurable embedding -/
noncomputable def equivImage (s : Set α) (hf : MeasurableEmbedding f) : s ≃ᵐ f '' s where
  toEquiv := Equiv.Set.image f s hf.injective
  measurable_toFun := (hf.measurable.comp measurable_id.subtype_val).subtype_mk
  measurable_invFun := by
    rintro t ⟨u, hu, rfl⟩; simp [preimage_preimage, Set.image_symm_preimage hf.injective]
    exact measurable_subtype_coe (hf.measurableSet_image' hu)
#align measurable_embedding.equiv_image MeasurableEmbedding.equivImage

/-- The domain of `f` is equivalent to its range as measurable spaces,
  if `f` is a measurable embedding -/
noncomputable def equivRange (hf : MeasurableEmbedding f) : α ≃ᵐ range f :=
  (MeasurableEquiv.Set.univ _).symm.trans <|
    (hf.equivImage univ).trans <| MeasurableEquiv.cast (by rw [image_univ]) (by rw [image_univ])
#align measurable_embedding.equiv_range MeasurableEmbedding.equivRange

theorem of_measurable_inverse_on_range {g : range f → α} (hf₁ : Measurable f)
    (hf₂ : MeasurableSet (range f)) (hg : Measurable g) (H : LeftInverse g (rangeFactorization f)) :
    MeasurableEmbedding f := by
  set e : α ≃ᵐ range f :=
    ⟨⟨rangeFactorization f, g, H, H.rightInverse_of_surjective surjective_onto_range⟩,
      hf₁.subtype_mk, hg⟩
  exact (MeasurableEmbedding.subtype_coe hf₂).comp e.measurableEmbedding
#align measurable_embedding.of_measurable_inverse_on_range MeasurableEmbedding.of_measurable_inverse_on_range

theorem of_measurable_inverse (hf₁ : Measurable f) (hf₂ : MeasurableSet (range f))
    (hg : Measurable g) (H : LeftInverse g f) : MeasurableEmbedding f :=
  of_measurable_inverse_on_range hf₁ hf₂ (hg.comp measurable_subtype_coe) H
#align measurable_embedding.of_measurable_inverse MeasurableEmbedding.of_measurable_inverse

open scoped Classical

/-- The **measurable Schröder-Bernstein Theorem**: given measurable embeddings
`α → β` and `β → α`, we can find a measurable equivalence `α ≃ᵐ β`. -/
noncomputable def schroederBernstein {f : α → β} {g : β → α} (hf : MeasurableEmbedding f)
    (hg : MeasurableEmbedding g) : α ≃ᵐ β := by
  let F : Set α → Set α := fun A => (g '' (f '' A)ᶜ)ᶜ
  -- We follow the proof of the usual SB theorem in mathlib,
  -- the crux of which is finding a fixed point of this F.
  -- However, we must find this fixed point manually instead of invoking Knaster-Tarski
  -- in order to make sure it is measurable.
  suffices Σ'A : Set α, MeasurableSet A ∧ F A = A by
    rcases this with ⟨A, Ameas, Afp⟩
    let B := f '' A
    have Bmeas : MeasurableSet B := hf.measurableSet_image' Ameas
    refine (MeasurableEquiv.sumCompl Ameas).symm.trans
      (MeasurableEquiv.trans ?_ (MeasurableEquiv.sumCompl Bmeas))
    apply MeasurableEquiv.sumCongr (hf.equivImage _)
    have : Aᶜ = g '' Bᶜ := by
      apply compl_injective
      rw [← Afp]
      simp
    rw [this]
    exact (hg.equivImage _).symm
  have Fmono : ∀ {A B}, A ⊆ B → F A ⊆ F B := fun h =>
    compl_subset_compl.mpr <| Set.image_subset _ <| compl_subset_compl.mpr <| Set.image_subset _ h
  let X : ℕ → Set α := fun n => F^[n] univ
  refine ⟨iInter X, ?_, ?_⟩
  · apply MeasurableSet.iInter
    intro n
    induction' n with n ih
    · exact MeasurableSet.univ
    rw [Function.iterate_succ', Function.comp_apply]
    exact (hg.measurableSet_image' (hf.measurableSet_image' ih).compl).compl
  apply subset_antisymm
  · apply subset_iInter
    intro n
    cases n
    · exact subset_univ _
    rw [Function.iterate_succ', Function.comp_apply]
    exact Fmono (iInter_subset _ _)
  rintro x hx ⟨y, hy, rfl⟩
  rw [mem_iInter] at hx
  apply hy
  rw [hf.injective.injOn.image_iInter_eq]
  rw [mem_iInter]
  intro n
  specialize hx n.succ
  rw [Function.iterate_succ', Function.comp_apply] at hx
  by_contra h
  apply hx
  exact ⟨y, h, rfl⟩
#align measurable_embedding.schroeder_bernstein MeasurableEmbedding.schroederBernstein

end MeasurableEmbedding

theorem MeasurableSpace.comap_compl {m' : MeasurableSpace β} [BooleanAlgebra β]
    (h : Measurable (compl : β → β)) (f : α → β) :
    MeasurableSpace.comap (fun a => (f a)ᶜ) inferInstance =
      MeasurableSpace.comap f inferInstance := by
  rw [← Function.comp_def, ← MeasurableSpace.comap_comp]
  congr
  exact (MeasurableEquiv.ofInvolutive _ compl_involutive h).measurableEmbedding.comap_eq
#align measurable_space.comap_compl MeasurableSpace.comap_compl

@[simp] theorem MeasurableSpace.comap_not (p : α → Prop) :
    MeasurableSpace.comap (fun a ↦ ¬p a) inferInstance = MeasurableSpace.comap p inferInstance :=
  MeasurableSpace.comap_compl (fun _ _ ↦ measurableSet_top) _
#align measurable_space.comap_not MeasurableSpace.comap_not
