/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Set.Lattice.Image
import Mathlib.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.SetLike

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

@[expose] public section


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

attribute [fun_prop] MeasurableEmbedding.measurable

namespace MeasurableEmbedding

variable {mα : MeasurableSpace α} [MeasurableSpace β] [MeasurableSpace γ] {f : α → β} {g : β → γ}

theorem measurableSet_image (hf : MeasurableEmbedding f) :
    MeasurableSet (f '' s) ↔ MeasurableSet s :=
  ⟨fun h => by simpa only [hf.injective.preimage_image] using hf.measurable h, fun h =>
    hf.measurableSet_image' h⟩

theorem id : MeasurableEmbedding (id : α → α) :=
  ⟨injective_id, measurable_id, fun s hs => by rwa [image_id]⟩

theorem comp (hg : MeasurableEmbedding g) (hf : MeasurableEmbedding f) :
    MeasurableEmbedding (g ∘ f) :=
  ⟨hg.injective.comp hf.injective, hg.measurable.comp hf.measurable, fun s hs => by
    rwa [image_comp, hg.measurableSet_image, hf.measurableSet_image]⟩

theorem subtype_coe (hs : MeasurableSet s) : MeasurableEmbedding ((↑) : s → α) where
  injective := Subtype.coe_injective
  measurable := measurable_subtype_coe
  measurableSet_image' := fun _ => MeasurableSet.subtype_image hs

theorem measurableSet_range (hf : MeasurableEmbedding f) : MeasurableSet (range f) := by
  rw [← image_univ]
  exact hf.measurableSet_image' MeasurableSet.univ

theorem measurableSet_preimage (hf : MeasurableEmbedding f) {s : Set β} :
    MeasurableSet (f ⁻¹' s) ↔ MeasurableSet (s ∩ range f) := by
  rw [← image_preimage_eq_inter_range, hf.measurableSet_image]

theorem measurable_rangeSplitting (hf : MeasurableEmbedding f) :
    Measurable (rangeSplitting f) := fun s hs => by
  rwa [preimage_rangeSplitting hf.injective,
    ← (subtype_coe hf.measurableSet_range).measurableSet_image, ← image_comp,
    coe_comp_rangeFactorization, hf.measurableSet_image]

theorem measurable_extend (hf : MeasurableEmbedding f) {g : α → γ} {g' : β → γ} (hg : Measurable g)
    (hg' : Measurable g') : Measurable (extend f g g') := by
  refine measurable_of_restrict_of_restrict_compl hf.measurableSet_range ?_ ?_
  · rw [restrict_extend_range]
    simpa only [rangeSplitting] using hg.comp hf.measurable_rangeSplitting
  · rw [restrict_extend_compl_range]
    exact hg'.comp measurable_subtype_coe

theorem exists_measurable_extend (hf : MeasurableEmbedding f) {g : α → γ} (hg : Measurable g)
    (hne : β → Nonempty γ) : ∃ g' : β → γ, Measurable g' ∧ g' ∘ f = g :=
  ⟨extend f g fun x => Classical.choice (hne x),
    hf.measurable_extend hg (measurable_const' fun _ _ => rfl),
    funext fun _ => hf.injective.extend_apply _ _ _⟩

theorem measurable_comp_iff (hg : MeasurableEmbedding g) : Measurable (g ∘ f) ↔ Measurable f := by
  refine ⟨fun H => ?_, hg.measurable.comp⟩
  suffices Measurable ((rangeSplitting g ∘ rangeFactorization g) ∘ f) by
    rwa [(rightInverse_rangeSplitting hg.injective).comp_eq_id] at this
  exact hg.measurable_rangeSplitting.comp H.subtype_mk

lemma natCast {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [AddMonoidWithOne α] [CharZero α] :
    MeasurableEmbedding (Nat.cast : ℕ → α) where
  injective := Nat.cast_injective
  measurable := measurable_from_nat
  measurableSet_image' := fun _ _ =>
    ((Set.countable_range (Nat.cast : ℕ → α)).mono
      (Set.image_subset_range _ _)).measurableSet

end MeasurableEmbedding

section gluing
variable {α₁ α₂ α₃ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mα₁ : MeasurableSpace α₁} {mα₂ : MeasurableSpace α₂} {mα₃ : MeasurableSpace α₃}
  {i₁ : α₁ → α} {i₂ : α₂ → α} {i₃ : α₃ → α} {s : Set α} {f : α → β}

lemma MeasurableSet.of_union_range_cover (hi₁ : MeasurableEmbedding i₁)
    (hi₂ : MeasurableEmbedding i₂) (h : univ ⊆ range i₁ ∪ range i₂)
    (hs₁ : MeasurableSet (i₁ ⁻¹' s)) (hs₂ : MeasurableSet (i₂ ⁻¹' s)) : MeasurableSet s := by
  convert (hi₁.measurableSet_image' hs₁).union (hi₂.measurableSet_image' hs₂)
  simp [image_preimage_eq_range_inter, ← union_inter_distrib_right, univ_subset_iff.1 h]

lemma MeasurableSet.of_union₃_range_cover (hi₁ : MeasurableEmbedding i₁)
    (hi₂ : MeasurableEmbedding i₂) (hi₃ : MeasurableEmbedding i₃)
    (h : univ ⊆ range i₁ ∪ range i₂ ∪ range i₃) (hs₁ : MeasurableSet (i₁ ⁻¹' s))
    (hs₂ : MeasurableSet (i₂ ⁻¹' s)) (hs₃ : MeasurableSet (i₃ ⁻¹' s)) : MeasurableSet s := by
  convert (hi₁.measurableSet_image' hs₁).union (hi₂.measurableSet_image' hs₂) |>.union
    (hi₃.measurableSet_image' hs₃)
  simp [image_preimage_eq_range_inter, ← union_inter_distrib_right, univ_subset_iff.1 h]

lemma Measurable.of_union_range_cover (hi₁ : MeasurableEmbedding i₁)
    (hi₂ : MeasurableEmbedding i₂) (h : univ ⊆ range i₁ ∪ range i₂)
    (hf₁ : Measurable (f ∘ i₁)) (hf₂ : Measurable (f ∘ i₂)) : Measurable f :=
  fun _s hs ↦ .of_union_range_cover hi₁ hi₂ h (hf₁ hs) (hf₂ hs)

lemma Measurable.of_union₃_range_cover (hi₁ : MeasurableEmbedding i₁)
    (hi₂ : MeasurableEmbedding i₂) (hi₃ : MeasurableEmbedding i₃)
    (h : univ ⊆ range i₁ ∪ range i₂ ∪ range i₃) (hf₁ : Measurable (f ∘ i₁))
    (hf₂ : Measurable (f ∘ i₂)) (hf₃ : Measurable (f ∘ i₃)) : Measurable f :=
  fun _s hs ↦ .of_union₃_range_cover hi₁ hi₂ hi₃ h (hf₁ hs) (hf₂ hs) (hf₃ hs)

end gluing

theorem MeasurableSet.exists_measurable_proj {_ : MeasurableSpace α}
    (hs : MeasurableSet s) (hne : s.Nonempty) : ∃ f : α → s, Measurable f ∧ ∀ x : s, f x = x :=
  let ⟨f, hfm, hf⟩ :=
    (MeasurableEmbedding.subtype_coe hs).exists_measurable_extend measurable_id fun _ =>
      hne.to_subtype
  ⟨f, hfm, congr_fun hf⟩

/-- Equivalences between measurable spaces. Main application is the simplification of measurability
statements along measurable equivalences. -/
structure MeasurableEquiv (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] extends α ≃ β where
  /-- The forward function of a measurable equivalence is measurable. -/
  measurable_toFun : Measurable toEquiv := by measurability
  /-- The inverse function of a measurable equivalence is measurable. -/
  measurable_invFun : Measurable toEquiv.symm := by measurability

@[inherit_doc]
infixl:25 " ≃ᵐ " => MeasurableEquiv

namespace MeasurableEquiv

variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

theorem toEquiv_injective : Injective (toEquiv : α ≃ᵐ β → α ≃ β) := by
  rintro ⟨e₁, _, _⟩ ⟨e₂, _, _⟩ (rfl : e₁ = e₂)
  rfl

instance instEquivLike : EquivLike (α ≃ᵐ β) α β where
  coe e := e.toEquiv
  inv e := e.toEquiv.symm
  left_inv e := e.toEquiv.left_inv
  right_inv e := e.toEquiv.right_inv
  coe_injective' _ _ he _ := toEquiv_injective <| DFunLike.ext' he

@[simp]
theorem coe_toEquiv (e : α ≃ᵐ β) : (e.toEquiv : α → β) = e :=
  rfl

@[fun_prop]
protected theorem measurable (e : α ≃ᵐ β) : Measurable (e : α → β) :=
  e.measurable_toFun

@[simp]
theorem coe_mk (e : α ≃ β) (h1 : Measurable e) (h2 : Measurable e.symm) :
    ((⟨e, h1, h2⟩ : α ≃ᵐ β) : α → β) = e :=
  rfl

/-- Any measurable space is equivalent to itself. -/
def refl (α : Type*) [MeasurableSpace α] : α ≃ᵐ α where
  toEquiv := Equiv.refl α

instance instInhabited : Inhabited (α ≃ᵐ α) := ⟨refl α⟩

/-- The composition of equivalences between measurable spaces. -/
def trans (ab : α ≃ᵐ β) (bc : β ≃ᵐ γ) : α ≃ᵐ γ where
  toEquiv := ab.toEquiv.trans bc.toEquiv
  measurable_toFun := bc.measurable_toFun.comp ab.measurable_toFun
  measurable_invFun := ab.measurable_invFun.comp bc.measurable_invFun

theorem coe_trans (ab : α ≃ᵐ β) (bc : β ≃ᵐ γ) : ⇑(ab.trans bc) = bc ∘ ab := rfl

/-- The inverse of an equivalence between measurable spaces. -/
def symm (ab : α ≃ᵐ β) : β ≃ᵐ α where
  toEquiv := ab.toEquiv.symm
  measurable_toFun := ab.measurable_invFun

@[simp]
theorem coe_toEquiv_symm (e : α ≃ᵐ β) : (e.toEquiv.symm : β → α) = e.symm :=
  rfl

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def Simps.apply (h : α ≃ᵐ β) : α → β := h

/-- See Note [custom simps projection] -/
def Simps.symm_apply (h : α ≃ᵐ β) : β → α := h.symm

initialize_simps_projections MeasurableEquiv (toFun → apply, invFun → symm_apply)

@[ext] theorem ext {e₁ e₂ : α ≃ᵐ β} (h : (e₁ : α → β) = e₂) : e₁ = e₂ := DFunLike.ext' h

@[simp]
theorem symm_mk (e : α ≃ β) (h1 : Measurable e) (h2 : Measurable e.symm) :
    (⟨e, h1, h2⟩ : α ≃ᵐ β).symm = ⟨e.symm, h2, h1⟩ :=
  rfl

attribute [simps! apply toEquiv] trans refl

@[simp]
theorem symm_symm (e : α ≃ᵐ β) : e.symm.symm = e := rfl

theorem symm_bijective :
    Function.Bijective (MeasurableEquiv.symm : (α ≃ᵐ β) → β ≃ᵐ α) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
theorem symm_refl (α : Type*) [MeasurableSpace α] : (refl α).symm = refl α :=
  rfl

@[simp]
theorem symm_comp_self (e : α ≃ᵐ β) : e.symm ∘ e = id :=
  funext e.left_inv

@[simp]
theorem self_comp_symm (e : α ≃ᵐ β) : e ∘ e.symm = id :=
  funext e.right_inv

@[simp]
theorem apply_symm_apply (e : α ≃ᵐ β) (y : β) : e (e.symm y) = y :=
  e.right_inv y

@[simp]
theorem symm_apply_apply (e : α ≃ᵐ β) (x : α) : e.symm (e x) = x :=
  e.left_inv x

@[simp]
theorem symm_trans_self (e : α ≃ᵐ β) : e.symm.trans e = refl β :=
  ext e.self_comp_symm

@[simp]
theorem self_trans_symm (e : α ≃ᵐ β) : e.trans e.symm = refl α :=
  ext e.symm_comp_self

@[simp]
theorem trans_symm (e₁ : α ≃ᵐ β) (e₂ : β ≃ᵐ γ) : (e₁.trans e₂).symm = e₂.symm.trans (e₁.symm) :=
  rfl

protected theorem surjective (e : α ≃ᵐ β) : Surjective e :=
  e.toEquiv.surjective

protected theorem bijective (e : α ≃ᵐ β) : Bijective e :=
  e.toEquiv.bijective

protected theorem injective (e : α ≃ᵐ β) : Injective e :=
  e.toEquiv.injective

@[simp]
theorem symm_preimage_preimage (e : α ≃ᵐ β) (s : Set β) : e.symm ⁻¹' (e ⁻¹' s) = s :=
  e.toEquiv.symm_preimage_preimage s

theorem image_eq_preimage_symm (e : α ≃ᵐ β) (s : Set α) : e '' s = e.symm ⁻¹' s :=
  e.toEquiv.image_eq_preimage_symm s

lemma preimage_symm (e : α ≃ᵐ β) (s : Set α) : e.symm ⁻¹' s = e '' s :=
  (image_eq_preimage_symm ..).symm

lemma image_symm (e : α ≃ᵐ β) (s : Set β) : e.symm '' s = e ⁻¹' s := image_symm_eq_preimage ..

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

@[simp]
theorem measurableSet_image (e : α ≃ᵐ β) : MeasurableSet (e '' s) ↔ MeasurableSet s := by
  rw [image_eq_preimage_symm, measurableSet_preimage]

@[simp] theorem map_eq (e : α ≃ᵐ β) : MeasurableSpace.map e ‹_› = ‹_› :=
  e.measurable.le_map.antisymm' fun _s ↦ e.measurableSet_preimage.1

/-- A measurable equivalence is a measurable embedding. -/
protected theorem measurableEmbedding (e : α ≃ᵐ β) : MeasurableEmbedding e where
  injective := e.injective
  measurable := e.measurable
  measurableSet_image' := fun _ => e.measurableSet_image.2

/-- Equal measurable spaces are equivalent. -/
protected def cast {α β} [i₁ : MeasurableSpace α] [i₂ : MeasurableSpace β] (h : α = β)
    (hi : i₁ ≍ i₂) : α ≃ᵐ β where
  toEquiv := Equiv.cast h

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

/-- Any two types with unique elements are measurably equivalent. -/
def ofUniqueOfUnique (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] [Unique α] [Unique β] :
    α ≃ᵐ β where
  toEquiv := ofUnique α β

variable [MeasurableSpace δ] in
/-- Products of equivalent measurable spaces are equivalent. -/
def prodCongr (ab : α ≃ᵐ β) (cd : γ ≃ᵐ δ) : α × γ ≃ᵐ β × δ where
  toEquiv := .prodCongr ab.toEquiv cd.toEquiv

/-- Products of measurable spaces are symmetric. -/
def prodComm : α × β ≃ᵐ β × α where
  toEquiv := .prodComm α β

/-- Products of measurable spaces are associative. -/
def prodAssoc : (α × β) × γ ≃ᵐ α × β × γ where
  toEquiv := .prodAssoc α β γ
  measurable_toFun := by eta_expand; dsimp; measurability
  measurable_invFun := by eta_expand; dsimp; measurability

/-- `PUnit` is a left identity for product of measurable spaces up to a measurable equivalence. -/
def punitProd : PUnit × α ≃ᵐ α where
  toEquiv := Equiv.punitProd α
  measurable_toFun := measurable_snd
  measurable_invFun := measurable_prodMk_left

/-- `PUnit` is a right identity for product of measurable spaces up to a measurable equivalence. -/
def prodPUnit : α × PUnit ≃ᵐ α where
  toEquiv := Equiv.prodPUnit α
  measurable_toFun := measurable_fst
  measurable_invFun := measurable_prodMk_right

variable [MeasurableSpace δ] in
/-- Sums of measurable spaces are symmetric. -/
def sumCongr (ab : α ≃ᵐ β) (cd : γ ≃ᵐ δ) : α ⊕ γ ≃ᵐ β ⊕ δ where
  toEquiv := .sumCongr ab.toEquiv cd.toEquiv
  measurable_toFun := ab.measurable.sumMap cd.measurable
  measurable_invFun := ab.symm.measurable.sumMap cd.symm.measurable

/-- `s ×ˢ t ≃ (s × t)` as measurable spaces. -/
def Set.prod (s : Set α) (t : Set β) : ↥(s ×ˢ t) ≃ᵐ s × t where
  toEquiv := Equiv.Set.prod s t
  measurable_toFun := .prodMk (by measurability) (by measurability)
  measurable_invFun := Measurable.subtype_mk <| by fun_prop

/-- `univ α ≃ α` as measurable spaces. -/
def Set.univ (α : Type*) [MeasurableSpace α] : (univ : Set α) ≃ᵐ α where
  toEquiv := Equiv.Set.univ α
  measurable_toFun := measurable_id.subtype_val
  measurable_invFun := measurable_id.subtype_mk

/-- `{a} ≃ Unit` as measurable spaces. -/
def Set.singleton (a : α) : ({a} : Set α) ≃ᵐ Unit where
  toEquiv := Equiv.Set.singleton a

/-- `α` is equivalent to its image in `α ⊕ β` as measurable spaces. -/
def Set.rangeInl : (range Sum.inl : Set (α ⊕ β)) ≃ᵐ α where
  toEquiv := Equiv.Set.rangeInl α β
  measurable_toFun s (hs : MeasurableSet s) := by
    refine ⟨_, hs.inl_image, Set.ext ?_⟩
    simp
  measurable_invFun := Measurable.subtype_mk measurable_inl

/-- `β` is equivalent to its image in `α ⊕ β` as measurable spaces. -/
def Set.rangeInr : (range Sum.inr : Set (α ⊕ β)) ≃ᵐ β where
  toEquiv := Equiv.Set.rangeInr α β
  measurable_toFun s (hs : MeasurableSet s) := by
    refine ⟨_, hs.inr_image, Set.ext ?_⟩
    simp
  measurable_invFun := Measurable.subtype_mk measurable_inr

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
    measurable_fun_sum ((measurable_inl.comp measurable_fst).prodMk measurable_snd)
      ((measurable_inr.comp measurable_fst).prodMk measurable_snd)

/-- Products distribute over sums (on the left) as measurable spaces. -/
def prodSumDistrib (α β γ) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] :
    α × (β ⊕ γ) ≃ᵐ (α × β) ⊕ (α × γ) :=
  prodComm.trans <| (sumProdDistrib _ _ _).trans <| sumCongr prodComm prodComm

/-- Products distribute over sums as measurable spaces. -/
def sumProdSum (α β γ δ) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] : (α ⊕ β) × (γ ⊕ δ) ≃ᵐ ((α × γ) ⊕ (α × δ)) ⊕ ((β × γ) ⊕ (β × δ)) :=
  (sumProdDistrib _ _ _).trans <| sumCongr (prodSumDistrib _ _ _) (prodSumDistrib _ _ _)

variable {π π' : δ' → Type*} [∀ x, MeasurableSpace (π x)] [∀ x, MeasurableSpace (π' x)]

/-- The type of functions `f : ∀ a, β a` such that for all `a` we have `p a (f a)` is measurably
equivalent to the type of functions `∀ a, {b : β a // p a b}`. -/
def subtypePiEquivPi {p : (a : δ') → π a → Prop} :
    { f : (a : δ') → π a // ∀ (a : δ'), p a (f a) } ≃ᵐ ((a : δ') → { b : π a // p a b }) where
  toEquiv := .subtypePiEquivPi
  measurable_toFun := measurable_pi_lambda _ (fun a =>
    ((measurable_pi_apply a).comp measurable_subtype_coe).subtype_mk)
  measurable_invFun := (measurable_pi_lambda _ (fun a =>
    measurable_subtype_coe.comp (measurable_pi_apply a))).subtype_mk

/-- A family of measurable equivalences `Π a, β₁ a ≃ᵐ β₂ a` generates a measurable equivalence
  between `Π a, β₁ a` and `Π a, β₂ a`. -/
def piCongrRight (e : ∀ a, π a ≃ᵐ π' a) : (∀ a, π a) ≃ᵐ ∀ a, π' a where
  toEquiv := .piCongrRight fun a => (e a).toEquiv
  measurable_toFun :=
    measurable_pi_lambda _ fun i => (e i).measurable_toFun.comp (measurable_pi_apply i)
  measurable_invFun :=
    measurable_pi_lambda _ fun i => (e i).measurable_invFun.comp (measurable_pi_apply i)

variable (π) in
/-- Moving a dependent type along an equivalence of coordinates, as a measurable equivalence. -/
def piCongrLeft (f : δ ≃ δ') : (∀ b, π (f b)) ≃ᵐ ∀ a, π a where
  __ := Equiv.piCongrLeft π f
  measurable_invFun := by
    rw [measurable_pi_iff]
    exact fun i => measurable_pi_apply (f i)

theorem coe_piCongrLeft (f : δ ≃ δ') :
    ⇑(MeasurableEquiv.piCongrLeft π f) = f.piCongrLeft π := by rfl

lemma piCongrLeft_apply_apply {ι ι' : Type*} (e : ι ≃ ι') {β : ι' → Type*}
    [∀ i', MeasurableSpace (β i')] (x : (i : ι) → β (e i)) (i : ι) :
    piCongrLeft (fun i' ↦ β i') e x (e i) = x i := by
  rw [piCongrLeft, coe_mk, Equiv.piCongrLeft_apply_apply]

/-- The isomorphism `(γ → α × β) ≃ (γ → α) × (γ → β)` as a measurable equivalence. -/
def arrowProdEquivProdArrow (α β γ : Type*) [MeasurableSpace α] [MeasurableSpace β] :
    (γ → α × β) ≃ᵐ (γ → α) × (γ → β) where
  __ := Equiv.arrowProdEquivProdArrow γ _ _
  measurable_toFun := by
    dsimp [Equiv.arrowProdEquivProdArrow]
    fun_prop
  measurable_invFun := by
    dsimp [Equiv.arrowProdEquivProdArrow]
    fun_prop

/-- The measurable equivalence `(α₁ → β₁) ≃ᵐ (α₂ → β₂)` induced by `α₁ ≃ α₂` and `β₁ ≃ᵐ β₂`. -/
def arrowCongr' {α₁ β₁ α₂ β₂ : Type*} [MeasurableSpace β₁] [MeasurableSpace β₂]
    (hα : α₁ ≃ α₂) (hβ : β₁ ≃ᵐ β₂) :
    (α₁ → β₁) ≃ᵐ (α₂ → β₂) where
  __ := Equiv.arrowCongr' hα hβ
  measurable_toFun _ h := by
    exact MeasurableSet.preimage h <|
      measurable_pi_iff.mpr fun _ ↦ hβ.measurable.comp (measurable_pi_apply _)
  measurable_invFun _ h := by
    exact MeasurableSet.preimage h <|
      measurable_pi_iff.mpr fun _ ↦ hβ.symm.measurable.comp (measurable_pi_apply _)

/-- Pi-types are measurably equivalent to iterated products. -/
@[simps! -fullyApplied]
def piMeasurableEquivTProd [DecidableEq δ'] {l : List δ'} (hnd : l.Nodup) (h : ∀ i, i ∈ l) :
    (∀ i, π i) ≃ᵐ List.TProd π l where
  toEquiv := List.TProd.piEquivTProd hnd h
  measurable_toFun := measurable_tProd_mk l
  measurable_invFun := measurable_tProd_elim' h

variable (π) in
/-- The measurable equivalence `(∀ i, π i) ≃ᵐ π ⋆` when the domain of `π` only contains `⋆` -/
@[simps! -fullyApplied]
def piUnique [Unique δ'] : (∀ i, π i) ≃ᵐ π default where
  toEquiv := Equiv.piUnique π

/-- If `α` has a unique term, then the type of function `α → β` is measurably equivalent to `β`. -/
@[simps! -fullyApplied]
def funUnique (α β : Type*) [Unique α] [MeasurableSpace β] : (α → β) ≃ᵐ β :=
  MeasurableEquiv.piUnique _

/-- The space `Π i : Fin 2, α i` is measurably equivalent to `α 0 × α 1`. -/
@[simps! -fullyApplied]
def piFinTwo (α : Fin 2 → Type*) [∀ i, MeasurableSpace (α i)] : (∀ i, α i) ≃ᵐ α 0 × α 1 where
  toEquiv := piFinTwoEquiv α
  measurable_invFun := measurable_pi_iff.2 <| Fin.forall_fin_two.2 ⟨measurable_fst, measurable_snd⟩

/-- The space `Fin 2 → α` is measurably equivalent to `α × α`. -/
@[simps! -fullyApplied]
def finTwoArrow : (Fin 2 → α) ≃ᵐ α × α :=
  piFinTwo fun _ => α

/-- Measurable equivalence between `Π j : Fin (n + 1), α j` and
`α i × Π j : Fin n, α (Fin.succAbove i j)`.

Measurable version of `Fin.insertNthEquiv`. -/
@[simps! -fullyApplied]
def piFinSuccAbove {n : ℕ} (α : Fin (n + 1) → Type*) [∀ i, MeasurableSpace (α i)]
    (i : Fin (n + 1)) : (∀ j, α j) ≃ᵐ α i × ∀ j, α (i.succAbove j) where
  toEquiv := (Fin.insertNthEquiv α i).symm
  measurable_toFun := (measurable_pi_apply i).prodMk <| measurable_pi_iff.2 fun _ =>
    measurable_pi_apply _
  measurable_invFun := measurable_pi_iff.2 <| i.forall_iff_succAbove.2
    ⟨by simp [measurable_fst], fun j => by simpa using (measurable_pi_apply _).comp measurable_snd⟩

variable (π)

/-- Measurable equivalence between (dependent) functions on a type and pairs of functions on
`{i // p i}` and `{i // ¬p i}`. See also `Equiv.piEquivPiSubtypeProd`. -/
@[simps! -fullyApplied]
def piEquivPiSubtypeProd (p : δ' → Prop) [DecidablePred p] :
    (∀ i, π i) ≃ᵐ (∀ i : Subtype p, π i) × ∀ i : { i // ¬p i }, π i where
  toEquiv := .piEquivPiSubtypeProd p π

/-- The measurable equivalence between the pi type over a sum type and a product of pi-types.
This is similar to `MeasurableEquiv.piEquivPiSubtypeProd`. -/
def sumPiEquivProdPi (α : δ ⊕ δ' → Type*) [∀ i, MeasurableSpace (α i)] :
    (∀ i, α i) ≃ᵐ (∀ i, α (.inl i)) × ∀ i', α (.inr i') where
  __ := Equiv.sumPiEquivProdPi α
  measurable_toFun := by eta_expand; dsimp; measurability
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

/-- Convert a measurable involutive function `f` to a measurable permutation with
`toFun = invFun = f`. See also `Function.Involutive.toPerm`. -/
@[simps toEquiv]
def ofInvolutive (f : α → α) (hf : Involutive f) (hf' : Measurable f) : α ≃ᵐ α where
  toEquiv := hf.toPerm

@[simp] theorem ofInvolutive_apply (f : α → α) (hf : Involutive f) (hf' : Measurable f) (a : α) :
    ofInvolutive f hf hf' a = f a := rfl

@[simp] theorem ofInvolutive_symm (f : α → α) (hf : Involutive f) (hf' : Measurable f) :
    (ofInvolutive f hf hf').symm = ofInvolutive f hf hf' := rfl

/-- `setOf` as a `MeasurableEquiv`. -/
@[simps]
protected def setOf {α : Type*} : (α → Prop) ≃ᵐ Set α where
  toFun p := {a | p a}
  invFun s a := a ∈ s

@[simp, norm_cast] lemma coe_setOf {α : Type*} : ⇑MeasurableEquiv.setOf = setOf (α := α) := rfl

end MeasurableEquiv

namespace MeasurableEmbedding

variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] {f : α → β} {g : β → α}

@[simp] theorem comap_eq (hf : MeasurableEmbedding f) : MeasurableSpace.comap f ‹_› = ‹_› :=
  hf.measurable.comap_le.antisymm fun _s h ↦
    ⟨_, hf.measurableSet_image' h, hf.injective.preimage_image _⟩

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

/-- A set is equivalent to its image under a function `f` as measurable spaces,
  if `f` is a measurable embedding -/
noncomputable def equivImage (s : Set α) (hf : MeasurableEmbedding f) : s ≃ᵐ f '' s where
  toEquiv := Equiv.Set.image f s hf.injective
  measurable_toFun := (hf.measurable.comp measurable_id.subtype_val).subtype_mk
  measurable_invFun := by
    rintro t ⟨u, hu, rfl⟩
    simpa [preimage_preimage, Set.image_symm_preimage hf.injective]
      using measurable_subtype_coe (hf.measurableSet_image' hu)

/-- The domain of `f` is equivalent to its range as measurable spaces,
  if `f` is a measurable embedding -/
noncomputable def equivRange (hf : MeasurableEmbedding f) : α ≃ᵐ range f :=
  (MeasurableEquiv.Set.univ _).symm.trans <|
    (hf.equivImage univ).trans <| MeasurableEquiv.cast (by rw [image_univ]) (by rw [image_univ])

theorem of_measurable_inverse_on_range {g : range f → α} (hf₁ : Measurable f)
    (hf₂ : MeasurableSet (range f)) (hg : Measurable g) (H : LeftInverse g (rangeFactorization f)) :
    MeasurableEmbedding f := by
  set e : α ≃ᵐ range f :=
    ⟨⟨rangeFactorization f, g, H, H.rightInverse_of_surjective rangeFactorization_surjective⟩,
      hf₁.subtype_mk, hg⟩
  exact (MeasurableEmbedding.subtype_coe hf₂).comp e.measurableEmbedding

theorem of_measurable_inverse (hf₁ : Measurable f) (hf₂ : MeasurableSet (range f))
    (hg : Measurable g) (H : LeftInverse g f) : MeasurableEmbedding f :=
  of_measurable_inverse_on_range hf₁ hf₂ (hg.comp measurable_subtype_coe) H

/-- The **measurable Schröder-Bernstein Theorem**: given measurable embeddings
`α → β` and `β → α`, we can find a measurable equivalence `α ≃ᵐ β`. -/
noncomputable def schroederBernstein {f : α → β} {g : β → α} (hf : MeasurableEmbedding f)
    (hg : MeasurableEmbedding g) : α ≃ᵐ β := by
  let F : Set α → Set α := fun A => (g '' (f '' A)ᶜ)ᶜ
  -- We follow the proof of the usual SB theorem in mathlib,
  -- the crux of which is finding a fixed point of this F.
  -- However, we must find this fixed point manually instead of invoking Knaster-Tarski
  -- in order to make sure it is measurable.
  suffices Σ' A : Set α, MeasurableSet A ∧ F A = A by
    classical
    rcases this with ⟨A, Ameas, Afp⟩
    let B := f '' A
    have Bmeas : MeasurableSet B := hf.measurableSet_image' Ameas
    refine (MeasurableEquiv.sumCompl Ameas).symm.trans
      (MeasurableEquiv.trans ?_ (MeasurableEquiv.sumCompl Bmeas))
    apply MeasurableEquiv.sumCongr (hf.equivImage _)
    have : Aᶜ = g '' Bᶜ := by
      apply compl_injective
      rw [← Afp]
      simp [F, B]
    rw [this]
    exact (hg.equivImage _).symm
  have Fmono : ∀ {A B}, A ⊆ B → F A ⊆ F B := fun h =>
    compl_subset_compl.mpr <| Set.image_mono <| compl_subset_compl.mpr <| Set.image_mono h
  let X : ℕ → Set α := fun n => F^[n] univ
  refine ⟨iInter X, ?_, ?_⟩
  · refine MeasurableSet.iInter fun n ↦ ?_
    induction n with
    | zero => exact MeasurableSet.univ
    | succ n ih =>
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

@[simp]
lemma equivRange_apply (hf : MeasurableEmbedding f) (x : α) :
    hf.equivRange x = ⟨f x, mem_range_self x⟩ := by
  simp [MeasurableEmbedding.equivRange, MeasurableEquiv.cast, MeasurableEquiv.Set.univ,
    MeasurableEmbedding.equivImage]

@[simp]
lemma equivRange_symm_apply_mk (hf : MeasurableEmbedding f) (x : α) :
    hf.equivRange.symm ⟨f x, mem_range_self x⟩ = x := by
  nth_rw 3 [← hf.equivRange.symm_apply_apply x]
  rw [hf.equivRange_apply]

/-- The left-inverse of a `MeasurableEmbedding` -/
protected noncomputable
def invFun [Nonempty α] (hf : MeasurableEmbedding f) (x : β) : α :=
  open Classical in
  if hx : x ∈ range f then hf.equivRange.symm ⟨x, hx⟩ else (Nonempty.some inferInstance)

@[fun_prop]
lemma measurable_invFun [Nonempty α] (hf : MeasurableEmbedding f) :
    Measurable (hf.invFun : β → α) :=
  open Classical in
  Measurable.dite (by fun_prop) measurable_const hf.measurableSet_range

lemma leftInverse_invFun [Nonempty α] (hf : MeasurableEmbedding f) : hf.invFun.LeftInverse f := by
  intro x
  simp [MeasurableEmbedding.invFun]

end MeasurableEmbedding

theorem MeasurableSpace.comap_compl {m' : MeasurableSpace β} [BooleanAlgebra β]
    (h : Measurable (compl : β → β)) (f : α → β) :
    MeasurableSpace.comap (fun a => (f a)ᶜ) inferInstance =
      MeasurableSpace.comap f inferInstance := by
  rw [← Function.comp_def, ← MeasurableSpace.comap_comp]
  congr
  exact (MeasurableEquiv.ofInvolutive _ compl_involutive h).measurableEmbedding.comap_eq

@[simp] theorem MeasurableSpace.comap_not (p : α → Prop) :
    MeasurableSpace.comap (fun a ↦ ¬p a) inferInstance = MeasurableSpace.comap p inferInstance :=
  MeasurableSpace.comap_compl (fun _ _ ↦ measurableSet_top) _

section curry

/-! ### Currying as a measurable equivalence -/

namespace MeasurableEquiv

/-- The currying operation `Function.curry` as a measurable equivalence.
See `MeasurableEquiv.curry` for the non-dependent version. -/
@[simps!]
def piCurry {ι : Type*} {κ : ι → Type*} (X : (i : ι) → κ i → Type*)
    [∀ i j, MeasurableSpace (X i j)] :
    ((p : (i : ι) × κ i) → X p.1 p.2) ≃ᵐ ((i : ι) → (j : κ i) → X i j) where
  toEquiv := Equiv.piCurry X

lemma coe_piCurry {ι : Type*} {κ : ι → Type*} (X : (i : ι) → κ i → Type*)
    [∀ i j, MeasurableSpace (X i j)] : ⇑(piCurry X) = Sigma.curry := rfl

lemma coe_piCurry_symm {ι : Type*} {κ : ι → Type*} (X : (i : ι) → κ i → Type*)
    [∀ i j, MeasurableSpace (X i j)] : ⇑(piCurry X).symm = Sigma.uncurry := rfl

/-- The currying operation `Sigma.curry` as a measurable equivalence.
See `MeasurableEquiv.piCurry` for the dependent version. -/
@[simps!]
def curry (ι κ X : Type*) [MeasurableSpace X] : (ι × κ → X) ≃ᵐ (ι → κ → X) where
  toEquiv := Equiv.curry ι κ X

lemma coe_curry (ι κ X : Type*) [MeasurableSpace X] : ⇑(curry ι κ X) = Function.curry := rfl

lemma coe_curry_symm (ι κ X : Type*) [MeasurableSpace X] :
    ⇑(curry ι κ X).symm = Function.uncurry := rfl

end MeasurableEquiv

end curry
