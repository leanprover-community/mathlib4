/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Data.Set.Piecewise
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.Core
import Mathlib.Tactic.Attr.Core

/-!
# Partial equivalences

This files defines equivalences between subsets of given types.
An element `e` of `PartialEquiv α β` is made of two maps `e.toFun` and `e.invFun` respectively
from α to β and from β to α (just like equivs), which are inverse to each other on the subsets
`e.source` and `e.target` of respectively α and β.

They are designed in particular to define charts on manifolds.

The main functionality is `e.trans f`, which composes the two partial equivalences by restricting
the source and target to the maximal set where the composition makes sense.

As for equivs, we register a coercion to functions and use it in our simp normal form: we write
`e x` and `e.symm y` instead of `e.toFun x` and `e.invFun y`.

## Main definitions

* `Equiv.toPartialEquiv`: associating a partial equiv to an equiv, with source = target = univ
* `PartialEquiv.symm`: the inverse of a partial equivalence
* `PartialEquiv.trans`: the composition of two partial equivalences
* `PartialEquiv.refl`: the identity partial equivalence
* `PartialEquiv.ofSet`: the identity on a set `s`
* `EqOnSource`: equivalence relation describing the "right" notion of equality for partial
  equivalences (see below in implementation notes)

## Implementation notes

There are at least three possible implementations of partial equivalences:
* equivs on subtypes
* pairs of functions taking values in `Option α` and `Option β`, equal to none where the partial
  equivalence is not defined
* pairs of functions defined everywhere, keeping the source and target as additional data

Each of these implementations has pros and cons.
* When dealing with subtypes, one still need to define additional API for composition and
  restriction of domains. Checking that one always belongs to the right subtype makes things very
  tedious, and leads quickly to DTT hell (as the subtype `u ∩ v` is not the "same" as `v ∩ u`, for
  instance).
* With option-valued functions, the composition is very neat (it is just the usual composition, and
  the domain is restricted automatically). These are implemented in `PEquiv.lean`. For manifolds,
  where one wants to discuss thoroughly the smoothness of the maps, this creates however a lot of
  overhead as one would need to extend all classes of smoothness to option-valued maps.
* The `PartialEquiv` version as explained above is easier to use for manifolds. The drawback is that
  there is extra useless data (the values of `toFun` and `invFun` outside of `source` and `target`).
  In particular, the equality notion between partial equivs is not "the right one", i.e., coinciding
  source and target and equality there. Moreover, there are no partial equivs in this sense between
  an empty type and a nonempty type. Since empty types are not that useful, and since one almost
  never needs to talk about equal partial equivs, this is not an issue in practice.
  Still, we introduce an equivalence relation `EqOnSource` that captures this right notion of
  equality, and show that many properties are invariant under this equivalence relation.

### Local coding conventions

If a lemma deals with the intersection of a set with either source or target of a `PartialEquiv`,
then it should use `e.source ∩ s` or `e.target ∩ t`, not `s ∩ e.source` or `t ∩ e.target`.

-/
open Lean Meta Elab Tactic

/-! Implementation of the `mfld_set_tac` tactic for working with the domains of partially-defined
functions (`PartialEquiv`, `PartialHomeomorph`, etc).

This is in a separate file from `Mathlib/Logic/Equiv/MfldSimpsAttr.lean` because attributes need a
new file to become functional.
-/

/-- Common `@[simps]` configuration options used for manifold-related declarations. -/
@[deprecated "Use `@[simps (attr := mfld_simps) -fullyApplied]` instead" (since := "2025-09-23")]
def mfld_cfg : Simps.Config where
  fullyApplied := false

namespace Tactic.MfldSetTac

/-- A very basic tactic to show that sets showing up in manifolds coincide or are included
in one another. -/
elab (name := mfldSetTac) "mfld_set_tac" : tactic => withMainContext do
  let g ← getMainGoal
  let goalTy := (← instantiateMVars (← g.getDecl).type).getAppFnArgs
  match goalTy with
  | (``Eq, #[_ty, _e₁, _e₂]) =>
    evalTactic (← `(tactic| (
      apply Set.ext; intro my_y
      constructor <;>
        · intro h_my_y
          try simp only [*, mfld_simps] at h_my_y
          try simp only [*, mfld_simps])))
  | (``Subset, #[_ty, _inst, _e₁, _e₂]) =>
    evalTactic (← `(tactic| (
      intro my_y h_my_y
      try simp only [*, mfld_simps] at h_my_y
      try simp only [*, mfld_simps])))
  | _ => throwError "goal should be an equality or an inclusion"

attribute [mfld_simps] and_true eq_self_iff_true Function.comp_apply

end Tactic.MfldSetTac

open Function Set

variable {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

/-- Local equivalence between subsets `source` and `target` of `α` and `β` respectively. The
(global) maps `toFun : α → β` and `invFun : β → α` map `source` to `target` and conversely, and are
inverse to each other there. The values of `toFun` outside of `source` and of `invFun` outside of
`target` are irrelevant. -/
structure PartialEquiv (α : Type*) (β : Type*) where
  /-- The global function which has a partial inverse. Its value outside of the `source` subset is
  irrelevant. -/
  toFun : α → β
  /-- The partial inverse to `toFun`. Its value outside of the `target` subset is irrelevant. -/
  invFun : β → α
  /-- The domain of the partial equivalence. -/
  source : Set α
  /-- The codomain of the partial equivalence. -/
  target : Set β
  /-- The proposition that elements of `source` are mapped to elements of `target`. -/
  map_source' : ∀ ⦃x⦄, x ∈ source → toFun x ∈ target
  /-- The proposition that elements of `target` are mapped to elements of `source`. -/
  map_target' : ∀ ⦃x⦄, x ∈ target → invFun x ∈ source
  /-- The proposition that `invFun` is a left-inverse of `toFun` on `source`. -/
  left_inv' : ∀ ⦃x⦄, x ∈ source → invFun (toFun x) = x
  /-- The proposition that `invFun` is a right-inverse of `toFun` on `target`. -/
  right_inv' : ∀ ⦃x⦄, x ∈ target → toFun (invFun x) = x

attribute [coe] PartialEquiv.toFun

namespace PartialEquiv

variable (e : PartialEquiv α β) (e' : PartialEquiv β γ)

instance [Inhabited α] [Inhabited β] : Inhabited (PartialEquiv α β) :=
  ⟨⟨const α default, const β default, ∅, ∅, mapsTo_empty _ _, mapsTo_empty _ _, eqOn_empty _ _,
      eqOn_empty _ _⟩⟩

/-- The inverse of a partial equivalence -/
@[symm]
protected def symm : PartialEquiv β α where
  toFun := e.invFun
  invFun := e.toFun
  source := e.target
  target := e.source
  map_source' := e.map_target'
  map_target' := e.map_source'
  left_inv' := e.right_inv'
  right_inv' := e.left_inv'

instance : CoeFun (PartialEquiv α β) fun _ => α → β :=
  ⟨PartialEquiv.toFun⟩

/-- See Note [custom simps projection] -/
def Simps.symm_apply (e : PartialEquiv α β) : β → α :=
  e.symm

initialize_simps_projections PartialEquiv (toFun → apply, invFun → symm_apply)

theorem coe_mk (f : α → β) (g s t ml mr il ir) :
    (PartialEquiv.mk f g s t ml mr il ir : α → β) = f := rfl

@[simp, mfld_simps]
theorem coe_symm_mk (f : α → β) (g s t ml mr il ir) :
    ((PartialEquiv.mk f g s t ml mr il ir).symm : β → α) = g :=
  rfl

@[simp, mfld_simps]
theorem invFun_as_coe : e.invFun = e.symm :=
  rfl

@[simp, mfld_simps]
theorem map_source {x : α} (h : x ∈ e.source) : e x ∈ e.target :=
  e.map_source' h

/-- Variant of `e.map_source` and `map_source'`, stated for images of subsets of `source`. -/
lemma map_source'' : e '' e.source ⊆ e.target :=
  fun _ ⟨_, hx, hex⟩ ↦ mem_of_eq_of_mem (id hex.symm) (e.map_source' hx)

@[simp, mfld_simps]
theorem map_target {x : β} (h : x ∈ e.target) : e.symm x ∈ e.source :=
  e.map_target' h

@[simp, mfld_simps]
theorem left_inv {x : α} (h : x ∈ e.source) : e.symm (e x) = x :=
  e.left_inv' h

@[simp, mfld_simps]
theorem right_inv {x : β} (h : x ∈ e.target) : e (e.symm x) = x :=
  e.right_inv' h

theorem target_subset_range : e.target ⊆ range e :=
  fun x hx ↦ ⟨e.symm x, right_inv e hx⟩

theorem eq_symm_apply {x : α} {y : β} (hx : x ∈ e.source) (hy : y ∈ e.target) :
    x = e.symm y ↔ e x = y :=
  ⟨fun h => by rw [← e.right_inv hy, h], fun h => by rw [← e.left_inv hx, h]⟩

protected theorem mapsTo : MapsTo e e.source e.target := fun _ => e.map_source

theorem symm_mapsTo : MapsTo e.symm e.target e.source :=
  e.symm.mapsTo

protected theorem leftInvOn : LeftInvOn e.symm e e.source := fun _ => e.left_inv

protected theorem rightInvOn : RightInvOn e.symm e e.target := fun _ => e.right_inv

protected theorem invOn : InvOn e.symm e e.source e.target :=
  ⟨e.leftInvOn, e.rightInvOn⟩

protected theorem injOn : InjOn e e.source :=
  e.leftInvOn.injOn

protected theorem bijOn : BijOn e e.source e.target :=
  e.invOn.bijOn e.mapsTo e.symm_mapsTo

protected theorem surjOn : SurjOn e e.source e.target :=
  e.bijOn.surjOn

/-- Interpret an `Equiv` as a `PartialEquiv` by restricting it to `s` in the domain
and to `t` in the codomain. -/
@[simps -fullyApplied]
def _root_.Equiv.toPartialEquivOfImageEq (e : α ≃ β) (s : Set α) (t : Set β) (h : e '' s = t) :
    PartialEquiv α β where
  toFun := e
  invFun := e.symm
  source := s
  target := t
  map_source' _ hx := h ▸ mem_image_of_mem _ hx
  map_target' x hx := by
    subst t
    rcases hx with ⟨x, hx, rfl⟩
    rwa [e.symm_apply_apply]
  left_inv' x _ := e.symm_apply_apply x
  right_inv' x _ := e.apply_symm_apply x

/-- Associate a `PartialEquiv` to an `Equiv`. -/
@[simps! (attr := mfld_simps) -fullyApplied]
def _root_.Equiv.toPartialEquiv (e : α ≃ β) : PartialEquiv α β :=
  e.toPartialEquivOfImageEq univ univ <| by rw [image_univ, e.surjective.range_eq]

instance inhabitedOfEmpty [IsEmpty α] [IsEmpty β] : Inhabited (PartialEquiv α β) :=
  ⟨((Equiv.equivEmpty α).trans (Equiv.equivEmpty β).symm).toPartialEquiv⟩

/-- Create a copy of a `PartialEquiv` providing better definitional equalities. -/
@[simps -fullyApplied]
def copy (e : PartialEquiv α β) (f : α → β) (hf : ⇑e = f) (g : β → α) (hg : ⇑e.symm = g) (s : Set α)
    (hs : e.source = s) (t : Set β) (ht : e.target = t) :
    PartialEquiv α β where
  toFun := f
  invFun := g
  source := s
  target := t
  map_source' _ := ht ▸ hs ▸ hf ▸ e.map_source
  map_target' _ := hs ▸ ht ▸ hg ▸ e.map_target
  left_inv' _ := hs ▸ hf ▸ hg ▸ e.left_inv
  right_inv' _ := ht ▸ hf ▸ hg ▸ e.right_inv

theorem copy_eq (e : PartialEquiv α β) (f : α → β) (hf : ⇑e = f) (g : β → α) (hg : ⇑e.symm = g)
    (s : Set α) (hs : e.source = s) (t : Set β) (ht : e.target = t) :
    e.copy f hf g hg s hs t ht = e := by
  substs f g s t
  cases e
  rfl

/-- Associate to a `PartialEquiv` an `Equiv` between the source and the target. -/
protected def toEquiv : e.source ≃ e.target where
  toFun x := ⟨e x, e.map_source x.mem⟩
  invFun y := ⟨e.symm y, e.map_target y.mem⟩
  left_inv := fun ⟨_, hx⟩ => Subtype.eq <| e.left_inv hx
  right_inv := fun ⟨_, hy⟩ => Subtype.eq <| e.right_inv hy

@[simp, mfld_simps]
theorem symm_source : e.symm.source = e.target :=
  rfl

@[simp, mfld_simps]
theorem symm_target : e.symm.target = e.source :=
  rfl

@[simp, mfld_simps]
theorem symm_symm : e.symm.symm = e := rfl

theorem symm_bijective :
    Function.Bijective (PartialEquiv.symm : PartialEquiv α β → PartialEquiv β α) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

theorem image_source_eq_target : e '' e.source = e.target :=
  e.bijOn.image_eq

theorem forall_mem_target {p : β → Prop} : (∀ y ∈ e.target, p y) ↔ ∀ x ∈ e.source, p (e x) := by
  rw [← image_source_eq_target, forall_mem_image]

theorem exists_mem_target {p : β → Prop} : (∃ y ∈ e.target, p y) ↔ ∃ x ∈ e.source, p (e x) := by
  rw [← image_source_eq_target, exists_mem_image]

/-- We say that `t : Set β` is an image of `s : Set α` under a partial equivalence if
any of the following equivalent conditions hold:

* `e '' (e.source ∩ s) = e.target ∩ t`;
* `e.source ∩ e ⁻¹ t = e.source ∩ s`;
* `∀ x ∈ e.source, e x ∈ t ↔ x ∈ s` (this one is used in the definition).
-/
def IsImage (s : Set α) (t : Set β) : Prop :=
  ∀ ⦃x⦄, x ∈ e.source → (e x ∈ t ↔ x ∈ s)

namespace IsImage

variable {e} {s : Set α} {t : Set β} {x : α}

theorem apply_mem_iff (h : e.IsImage s t) (hx : x ∈ e.source) : e x ∈ t ↔ x ∈ s :=
  h hx

theorem symm_apply_mem_iff (h : e.IsImage s t) : ∀ ⦃y⦄, y ∈ e.target → (e.symm y ∈ s ↔ y ∈ t) :=
  e.forall_mem_target.mpr fun x hx => by rw [e.left_inv hx, h hx]

protected theorem symm (h : e.IsImage s t) : e.symm.IsImage t s :=
  h.symm_apply_mem_iff

@[simp]
theorem symm_iff : e.symm.IsImage t s ↔ e.IsImage s t :=
  ⟨fun h => h.symm, fun h => h.symm⟩

protected theorem mapsTo (h : e.IsImage s t) : MapsTo e (e.source ∩ s) (e.target ∩ t) :=
  fun _ hx => ⟨e.mapsTo hx.1, (h hx.1).2 hx.2⟩

theorem symm_mapsTo (h : e.IsImage s t) : MapsTo e.symm (e.target ∩ t) (e.source ∩ s) :=
  h.symm.mapsTo

/-- Restrict a `PartialEquiv` to a pair of corresponding sets. -/
@[simps -fullyApplied]
def restr (h : e.IsImage s t) : PartialEquiv α β where
  toFun := e
  invFun := e.symm
  source := e.source ∩ s
  target := e.target ∩ t
  map_source' := h.mapsTo
  map_target' := h.symm_mapsTo
  left_inv' := e.leftInvOn.mono inter_subset_left
  right_inv' := e.rightInvOn.mono inter_subset_left

theorem image_eq (h : e.IsImage s t) : e '' (e.source ∩ s) = e.target ∩ t :=
  h.restr.image_source_eq_target

theorem symm_image_eq (h : e.IsImage s t) : e.symm '' (e.target ∩ t) = e.source ∩ s :=
  h.symm.image_eq

theorem iff_preimage_eq : e.IsImage s t ↔ e.source ∩ e ⁻¹' t = e.source ∩ s := by
  simp only [IsImage, Set.ext_iff, mem_inter_iff, mem_preimage, and_congr_right_iff]

alias ⟨preimage_eq, of_preimage_eq⟩ := iff_preimage_eq

theorem iff_symm_preimage_eq : e.IsImage s t ↔ e.target ∩ e.symm ⁻¹' s = e.target ∩ t :=
  symm_iff.symm.trans iff_preimage_eq

alias ⟨symm_preimage_eq, of_symm_preimage_eq⟩ := iff_symm_preimage_eq

theorem of_image_eq (h : e '' (e.source ∩ s) = e.target ∩ t) : e.IsImage s t :=
  of_symm_preimage_eq <| Eq.trans (of_symm_preimage_eq rfl).image_eq.symm h

theorem of_symm_image_eq (h : e.symm '' (e.target ∩ t) = e.source ∩ s) : e.IsImage s t :=
  of_preimage_eq <| Eq.trans (iff_preimage_eq.2 rfl).symm_image_eq.symm h

protected theorem compl (h : e.IsImage s t) : e.IsImage sᶜ tᶜ := fun _ hx => not_congr (h hx)

protected theorem inter {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s ∩ s') (t ∩ t') := fun _ hx => and_congr (h hx) (h' hx)

protected theorem union {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s ∪ s') (t ∪ t') := fun _ hx => or_congr (h hx) (h' hx)

protected theorem diff {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s \ s') (t \ t') :=
  h.inter h'.compl

theorem leftInvOn_piecewise {e' : PartialEquiv α β} [∀ i, Decidable (i ∈ s)]
    [∀ i, Decidable (i ∈ t)] (h : e.IsImage s t) (h' : e'.IsImage s t) :
    LeftInvOn (t.piecewise e.symm e'.symm) (s.piecewise e e') (s.ite e.source e'.source) := by
  rintro x (⟨he, hs⟩ | ⟨he, hs : x ∉ s⟩)
  · rw [piecewise_eq_of_mem _ _ _ hs, piecewise_eq_of_mem _ _ _ ((h he).2 hs), e.left_inv he]
  · rw [piecewise_eq_of_notMem _ _ _ hs, piecewise_eq_of_notMem _ _ _ ((h'.compl he).2 hs),
      e'.left_inv he]

theorem inter_eq_of_inter_eq_of_eqOn {e' : PartialEquiv α β} (h : e.IsImage s t)
    (h' : e'.IsImage s t) (hs : e.source ∩ s = e'.source ∩ s) (heq : EqOn e e' (e.source ∩ s)) :
    e.target ∩ t = e'.target ∩ t := by rw [← h.image_eq, ← h'.image_eq, ← hs, heq.image_eq]

theorem symm_eq_on_of_inter_eq_of_eqOn {e' : PartialEquiv α β} (h : e.IsImage s t)
    (hs : e.source ∩ s = e'.source ∩ s) (heq : EqOn e e' (e.source ∩ s)) :
    EqOn e.symm e'.symm (e.target ∩ t) := by
  rw [← h.image_eq]
  rintro y ⟨x, hx, rfl⟩
  have hx' := hx; rw [hs] at hx'
  rw [e.left_inv hx.1, heq hx, e'.left_inv hx'.1]

end IsImage

theorem isImage_source_target : e.IsImage e.source e.target := fun x hx => by simp [hx]

theorem isImage_source_target_of_disjoint (e' : PartialEquiv α β) (hs : Disjoint e.source e'.source)
    (ht : Disjoint e.target e'.target) : e.IsImage e'.source e'.target :=
  IsImage.of_image_eq <| by rw [hs.inter_eq, ht.inter_eq, image_empty]

theorem image_source_inter_eq' (s : Set α) : e '' (e.source ∩ s) = e.target ∩ e.symm ⁻¹' s := by
  rw [inter_comm, e.leftInvOn.image_inter', image_source_eq_target, inter_comm]

theorem image_source_inter_eq (s : Set α) :
    e '' (e.source ∩ s) = e.target ∩ e.symm ⁻¹' (e.source ∩ s) := by
  rw [inter_comm, e.leftInvOn.image_inter, image_source_eq_target, inter_comm]

theorem image_eq_target_inter_inv_preimage {s : Set α} (h : s ⊆ e.source) :
    e '' s = e.target ∩ e.symm ⁻¹' s := by
  rw [← e.image_source_inter_eq', inter_eq_self_of_subset_right h]

theorem symm_image_eq_source_inter_preimage {s : Set β} (h : s ⊆ e.target) :
    e.symm '' s = e.source ∩ e ⁻¹' s :=
  e.symm.image_eq_target_inter_inv_preimage h

theorem symm_image_target_inter_eq (s : Set β) :
    e.symm '' (e.target ∩ s) = e.source ∩ e ⁻¹' (e.target ∩ s) :=
  e.symm.image_source_inter_eq _

theorem symm_image_target_inter_eq' (s : Set β) : e.symm '' (e.target ∩ s) = e.source ∩ e ⁻¹' s :=
  e.symm.image_source_inter_eq' _

theorem source_inter_preimage_inv_preimage (s : Set α) :
    e.source ∩ e ⁻¹' (e.symm ⁻¹' s) = e.source ∩ s :=
  Set.ext fun x => and_congr_right_iff.2 fun hx =>
    by simp only [mem_preimage, e.left_inv hx]

theorem source_inter_preimage_target_inter (s : Set β) :
    e.source ∩ e ⁻¹' (e.target ∩ s) = e.source ∩ e ⁻¹' s :=
  ext fun _ => ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx => ⟨hx.1, e.map_source hx.1, hx.2⟩⟩

theorem target_inter_inv_preimage_preimage (s : Set β) :
    e.target ∩ e.symm ⁻¹' (e ⁻¹' s) = e.target ∩ s :=
  e.symm.source_inter_preimage_inv_preimage _

theorem symm_image_image_of_subset_source {s : Set α} (h : s ⊆ e.source) : e.symm '' (e '' s) = s :=
  (e.leftInvOn.mono h).image_image

theorem image_symm_image_of_subset_target {s : Set β} (h : s ⊆ e.target) : e '' (e.symm '' s) = s :=
  e.symm.symm_image_image_of_subset_source h

theorem source_subset_preimage_target : e.source ⊆ e ⁻¹' e.target :=
  e.mapsTo

theorem symm_image_target_eq_source : e.symm '' e.target = e.source :=
  e.symm.image_source_eq_target

theorem target_subset_preimage_source : e.target ⊆ e.symm ⁻¹' e.source :=
  e.symm_mapsTo

/-- Two partial equivs that have the same `source`, same `toFun` and same `invFun`, coincide. -/
@[ext]
protected theorem ext {e e' : PartialEquiv α β} (h : ∀ x, e x = e' x)
    (hsymm : ∀ x, e.symm x = e'.symm x) (hs : e.source = e'.source) : e = e' := by
  have A : (e : α → β) = e' := by
    ext x
    exact h x
  have B : (e.symm : β → α) = e'.symm := by
    ext x
    exact hsymm x
  have I : e '' e.source = e.target := e.image_source_eq_target
  have I' : e' '' e'.source = e'.target := e'.image_source_eq_target
  rw [A, hs, I'] at I
  cases e; cases e'
  simp_all

/-- Restricting a partial equivalence to `e.source ∩ s` -/
protected def restr (s : Set α) : PartialEquiv α β :=
  (@IsImage.of_symm_preimage_eq α β e s (e.symm ⁻¹' s) rfl).restr

@[simp, mfld_simps]
theorem restr_coe (s : Set α) : (e.restr s : α → β) = e :=
  rfl

@[simp, mfld_simps]
theorem restr_coe_symm (s : Set α) : ((e.restr s).symm : β → α) = e.symm :=
  rfl

@[simp, mfld_simps]
theorem restr_source (s : Set α) : (e.restr s).source = e.source ∩ s :=
  rfl

theorem source_restr_subset_source (s : Set α) : (e.restr s).source ⊆ e.source := inter_subset_left

@[simp, mfld_simps]
theorem restr_target (s : Set α) : (e.restr s).target = e.target ∩ e.symm ⁻¹' s :=
  rfl

theorem restr_eq_of_source_subset {e : PartialEquiv α β} {s : Set α} (h : e.source ⊆ s) :
    e.restr s = e :=
  PartialEquiv.ext (fun _ => rfl) (fun _ => rfl) (by simp [inter_eq_self_of_subset_left h])

@[simp, mfld_simps]
theorem restr_univ {e : PartialEquiv α β} : e.restr univ = e :=
  restr_eq_of_source_subset (subset_univ _)

/-- The identity partial equiv -/
protected def refl (α : Type*) : PartialEquiv α α :=
  (Equiv.refl α).toPartialEquiv

@[simp, mfld_simps]
theorem refl_source : (PartialEquiv.refl α).source = univ :=
  rfl

@[simp, mfld_simps]
theorem refl_target : (PartialEquiv.refl α).target = univ :=
  rfl

@[simp, mfld_simps]
theorem refl_coe : (PartialEquiv.refl α : α → α) = id :=
  rfl

@[simp, mfld_simps]
theorem refl_symm : (PartialEquiv.refl α).symm = PartialEquiv.refl α :=
  rfl

@[mfld_simps]
theorem refl_restr_source (s : Set α) : ((PartialEquiv.refl α).restr s).source = s := by simp

@[mfld_simps]
theorem refl_restr_target (s : Set α) : ((PartialEquiv.refl α).restr s).target = s := by simp

/-- The identity partial equivalence on a set `s` -/
def ofSet (s : Set α) : PartialEquiv α α where
  toFun := id
  invFun := id
  source := s
  target := s
  map_source' _ hx := hx
  map_target' _ hx := hx
  left_inv' _ _ := rfl
  right_inv' _ _ := rfl

@[simp, mfld_simps]
theorem ofSet_source (s : Set α) : (PartialEquiv.ofSet s).source = s :=
  rfl

@[simp, mfld_simps]
theorem ofSet_target (s : Set α) : (PartialEquiv.ofSet s).target = s :=
  rfl

@[simp, mfld_simps]
theorem ofSet_coe (s : Set α) : (PartialEquiv.ofSet s : α → α) = id :=
  rfl

@[simp, mfld_simps]
theorem ofSet_symm (s : Set α) : (PartialEquiv.ofSet s).symm = PartialEquiv.ofSet s :=
  rfl

/-- `Function.const` as a `PartialEquiv`.
It consists of two constant maps in opposite directions. -/
@[simps]
def single (a : α) (b : β) : PartialEquiv α β where
  toFun := Function.const α b
  invFun := Function.const β a
  source := {a}
  target := {b}
  map_source' _ _ := rfl
  map_target' _ _ := rfl
  left_inv' a' ha' := by rw [eq_of_mem_singleton ha', const_apply]
  right_inv' b' hb' := by rw [eq_of_mem_singleton hb', const_apply]

/-- Composing two partial equivs if the target of the first coincides with the source of the
second. -/
@[simps]
protected def trans' (e' : PartialEquiv β γ) (h : e.target = e'.source) : PartialEquiv α γ where
  toFun := e' ∘ e
  invFun := e.symm ∘ e'.symm
  source := e.source
  target := e'.target
  map_source' x hx := by simp [← h, hx]
  map_target' y hy := by simp [h, hy]
  left_inv' x hx := by simp [hx, ← h]
  right_inv' y hy := by simp [hy, h]

/-- Composing two partial equivs, by restricting to the maximal domain where their composition
is well defined.
Within the `Manifold` namespace, there is the notation `e ≫ f` for this.
-/
@[trans]
protected def trans : PartialEquiv α γ :=
  PartialEquiv.trans' (e.symm.restr e'.source).symm (e'.restr e.target) (inter_comm _ _)

@[simp, mfld_simps]
theorem coe_trans : (e.trans e' : α → γ) = e' ∘ e :=
  rfl

@[simp, mfld_simps]
theorem coe_trans_symm : ((e.trans e').symm : γ → α) = e.symm ∘ e'.symm :=
  rfl

theorem trans_apply {x : α} : (e.trans e') x = e' (e x) :=
  rfl

theorem trans_symm_eq_symm_trans_symm : (e.trans e').symm = e'.symm.trans e.symm := rfl

@[simp, mfld_simps]
theorem trans_source : (e.trans e').source = e.source ∩ e ⁻¹' e'.source :=
  rfl

theorem trans_source' : (e.trans e').source = e.source ∩ e ⁻¹' (e.target ∩ e'.source) := by
  mfld_set_tac

theorem trans_source'' : (e.trans e').source = e.symm '' (e.target ∩ e'.source) := by
  rw [e.trans_source', e.symm_image_target_inter_eq]

theorem image_trans_source : e '' (e.trans e').source = e.target ∩ e'.source :=
  (e.symm.restr e'.source).symm.image_source_eq_target

@[simp, mfld_simps]
theorem trans_target : (e.trans e').target = e'.target ∩ e'.symm ⁻¹' e.target :=
  rfl

theorem trans_target' : (e.trans e').target = e'.target ∩ e'.symm ⁻¹' (e'.source ∩ e.target) :=
  trans_source' e'.symm e.symm

theorem trans_target'' : (e.trans e').target = e' '' (e'.source ∩ e.target) :=
  trans_source'' e'.symm e.symm

theorem inv_image_trans_target : e'.symm '' (e.trans e').target = e'.source ∩ e.target :=
  image_trans_source e'.symm e.symm

theorem trans_assoc (e'' : PartialEquiv γ δ) : (e.trans e').trans e'' = e.trans (e'.trans e'') :=
  PartialEquiv.ext (fun _ => rfl) (fun _ => rfl)
    (by simp [trans_source, @preimage_comp α β γ, inter_assoc])

@[simp, mfld_simps]
theorem trans_refl : e.trans (PartialEquiv.refl β) = e :=
  PartialEquiv.ext (fun _ => rfl) (fun _ => rfl) (by simp [trans_source])

@[simp, mfld_simps]
theorem refl_trans : (PartialEquiv.refl α).trans e = e :=
  PartialEquiv.ext (fun _ => rfl) (fun _ => rfl) (by simp [trans_source, preimage_id])

theorem trans_ofSet (s : Set β) : e.trans (ofSet s) = e.restr (e ⁻¹' s) :=
  PartialEquiv.ext (fun _ => rfl) (fun _ => rfl) rfl

theorem trans_refl_restr (s : Set β) :
    e.trans ((PartialEquiv.refl β).restr s) = e.restr (e ⁻¹' s) :=
  PartialEquiv.ext (fun _ => rfl) (fun _ => rfl) (by simp [trans_source])

theorem trans_refl_restr' (s : Set β) :
    e.trans ((PartialEquiv.refl β).restr s) = e.restr (e.source ∩ e ⁻¹' s) :=
  PartialEquiv.ext (fun _ => rfl) (fun _ => rfl) <| by
    simp only [trans_source, restr_source, refl_source, univ_inter]
    rw [← inter_assoc, inter_self]

theorem restr_trans (s : Set α) : (e.restr s).trans e' = (e.trans e').restr s :=
  PartialEquiv.ext (fun _ => rfl) (fun _ => rfl) <| by
    simp [trans_source, inter_comm, inter_assoc]

/-- A lemma commonly useful when `e` and `e'` are charts of a manifold. -/
theorem mem_symm_trans_source {e' : PartialEquiv α γ} {x : α} (he : x ∈ e.source)
    (he' : x ∈ e'.source) : e x ∈ (e.symm.trans e').source :=
  ⟨e.mapsTo he, by rwa [mem_preimage, PartialEquiv.symm_symm, e.left_inv he]⟩

/-- `EqOnSource e e'` means that `e` and `e'` have the same source, and coincide there. Then `e`
and `e'` should really be considered the same partial equiv. -/
def EqOnSource (e e' : PartialEquiv α β) : Prop :=
  e.source = e'.source ∧ e.source.EqOn e e'

/-- `EqOnSource` is an equivalence relation. This instance provides the `≈` notation between two
`PartialEquiv`s. -/
instance eqOnSourceSetoid : Setoid (PartialEquiv α β) where
  r := EqOnSource
  iseqv := by constructor <;> simp only [EqOnSource, EqOn] <;> aesop

theorem eqOnSource_refl : e ≈ e :=
  Setoid.refl _

/-- Two equivalent partial equivs have the same source. -/
theorem EqOnSource.source_eq {e e' : PartialEquiv α β} (h : e ≈ e') : e.source = e'.source :=
  h.1

/-- Two equivalent partial equivs coincide on the source. -/
theorem EqOnSource.eqOn {e e' : PartialEquiv α β} (h : e ≈ e') : e.source.EqOn e e' :=
  h.2

/-- Two equivalent partial equivs have the same target. -/
theorem EqOnSource.target_eq {e e' : PartialEquiv α β} (h : e ≈ e') : e.target = e'.target := by
  simp only [← image_source_eq_target, ← source_eq h, h.2.image_eq]

/-- If two partial equivs are equivalent, so are their inverses. -/
theorem EqOnSource.symm' {e e' : PartialEquiv α β} (h : e ≈ e') : e.symm ≈ e'.symm := by
  refine ⟨target_eq h, eqOn_of_leftInvOn_of_rightInvOn e.leftInvOn ?_ ?_⟩ <;>
    simp only [symm_source, target_eq h, source_eq h, e'.symm_mapsTo]
  exact e'.rightInvOn.congr_right e'.symm_mapsTo (source_eq h ▸ h.eqOn.symm)

/-- Two equivalent partial equivs have coinciding inverses on the target. -/
theorem EqOnSource.symm_eqOn {e e' : PartialEquiv α β} (h : e ≈ e') :
    EqOn e.symm e'.symm e.target :=
  eqOn h.symm'

/-- Composition of partial equivs respects equivalence. -/
theorem EqOnSource.trans' {e e' : PartialEquiv α β} {f f' : PartialEquiv β γ} (he : e ≈ e')
    (hf : f ≈ f') : e.trans f ≈ e'.trans f' := by
  constructor
  · rw [trans_source'', trans_source'', ← target_eq he, ← hf.1]
    exact (he.symm'.eqOn.mono inter_subset_left).image_eq
  · intro x hx
    rw [trans_source] at hx
    simp [Function.comp_apply, PartialEquiv.coe_trans, (he.2 hx.1).symm, hf.2 hx.2]

/-- Restriction of partial equivs respects equivalence. -/
theorem EqOnSource.restr {e e' : PartialEquiv α β} (he : e ≈ e') (s : Set α) :
    e.restr s ≈ e'.restr s := by
  constructor
  · simp [he.1]
  · intro x hx
    simp only [mem_inter_iff, restr_source] at hx
    exact he.2 hx.1

/-- Preimages are respected by equivalence. -/
theorem EqOnSource.source_inter_preimage_eq {e e' : PartialEquiv α β} (he : e ≈ e') (s : Set β) :
    e.source ∩ e ⁻¹' s = e'.source ∩ e' ⁻¹' s := by rw [he.eqOn.inter_preimage_eq, source_eq he]

/-- Composition of a partial equivalence and its inverse is equivalent to
the restriction of the identity to the source. -/
theorem self_trans_symm : e.trans e.symm ≈ ofSet e.source := by
  have A : (e.trans e.symm).source = e.source := by mfld_set_tac
  refine ⟨by rw [A, ofSet_source], fun x hx => ?_⟩
  rw [A] at hx
  simp only [hx, mfld_simps]

/-- Composition of the inverse of a partial equivalence and this partial equivalence is equivalent
to the restriction of the identity to the target. -/
theorem symm_trans_self : e.symm.trans e ≈ ofSet e.target :=
  self_trans_symm e.symm

/-- Two equivalent partial equivs are equal when the source and target are `univ`. -/
theorem eq_of_eqOnSource_univ (e e' : PartialEquiv α β) (h : e ≈ e') (s : e.source = univ)
    (t : e.target = univ) : e = e' := by
  refine PartialEquiv.ext (fun x => ?_) (fun x => ?_) h.1
  · apply h.2
    rw [s]
    exact mem_univ _
  · apply h.symm'.2
    rw [symm_source, t]
    exact mem_univ _

section Prod

/-- The product of two partial equivalences, as a partial equivalence on the product. -/
def prod (e : PartialEquiv α β) (e' : PartialEquiv γ δ) : PartialEquiv (α × γ) (β × δ) where
  source := e.source ×ˢ e'.source
  target := e.target ×ˢ e'.target
  toFun p := (e p.1, e' p.2)
  invFun p := (e.symm p.1, e'.symm p.2)
  map_source' p hp := by simp_all
  map_target' p hp := by simp_all
  left_inv' p hp   := by simp_all
  right_inv' p hp  := by simp_all

@[simp, mfld_simps]
theorem prod_source (e : PartialEquiv α β) (e' : PartialEquiv γ δ) :
    (e.prod e').source = e.source ×ˢ e'.source :=
  rfl

@[simp, mfld_simps]
theorem prod_target (e : PartialEquiv α β) (e' : PartialEquiv γ δ) :
    (e.prod e').target = e.target ×ˢ e'.target :=
  rfl

@[simp, mfld_simps]
theorem prod_coe (e : PartialEquiv α β) (e' : PartialEquiv γ δ) :
    (e.prod e' : α × γ → β × δ) = fun p => (e p.1, e' p.2) :=
  rfl

theorem prod_coe_symm (e : PartialEquiv α β) (e' : PartialEquiv γ δ) :
    ((e.prod e').symm : β × δ → α × γ) = fun p => (e.symm p.1, e'.symm p.2) :=
  rfl

@[simp, mfld_simps]
theorem prod_symm (e : PartialEquiv α β) (e' : PartialEquiv γ δ) :
    (e.prod e').symm = e.symm.prod e'.symm := by
  ext x <;> simp [prod_coe_symm]

@[simp, mfld_simps]
theorem refl_prod_refl :
    (PartialEquiv.refl α).prod (PartialEquiv.refl β) = PartialEquiv.refl (α × β) := by
  ext ⟨x, y⟩ <;> simp

@[simp, mfld_simps]
theorem prod_trans {η : Type*} {ε : Type*} (e : PartialEquiv α β) (f : PartialEquiv β γ)
    (e' : PartialEquiv δ η) (f' : PartialEquiv η ε) :
    (e.prod e').trans (f.prod f') = (e.trans f).prod (e'.trans f') := by
  ext ⟨x, y⟩ <;> simp; tauto

end Prod

/-- Combine two `PartialEquiv`s using `Set.piecewise`. The source of the new `PartialEquiv` is
`s.ite e.source e'.source = e.source ∩ s ∪ e'.source \ s`, and similarly for target.  The function
sends `e.source ∩ s` to `e.target ∩ t` using `e` and `e'.source \ s` to `e'.target \ t` using `e'`,
and similarly for the inverse function. The definition assumes `e.isImage s t` and
`e'.isImage s t`. -/
@[simps -fullyApplied]
def piecewise (e e' : PartialEquiv α β) (s : Set α) (t : Set β) [∀ x, Decidable (x ∈ s)]
    [∀ y, Decidable (y ∈ t)] (H : e.IsImage s t) (H' : e'.IsImage s t) :
    PartialEquiv α β where
  toFun := s.piecewise e e'
  invFun := t.piecewise e.symm e'.symm
  source := s.ite e.source e'.source
  target := t.ite e.target e'.target
  map_source' := H.mapsTo.piecewise_ite H'.compl.mapsTo
  map_target' := H.symm.mapsTo.piecewise_ite H'.symm.compl.mapsTo
  left_inv' := H.leftInvOn_piecewise H'
  right_inv' := H.symm.leftInvOn_piecewise H'.symm

theorem symm_piecewise (e e' : PartialEquiv α β) {s : Set α} {t : Set β} [∀ x, Decidable (x ∈ s)]
    [∀ y, Decidable (y ∈ t)] (H : e.IsImage s t) (H' : e'.IsImage s t) :
    (e.piecewise e' s t H H').symm = e.symm.piecewise e'.symm t s H.symm H'.symm :=
  rfl

/-- Combine two `PartialEquiv`s with disjoint sources and disjoint targets. We reuse
`PartialEquiv.piecewise`, then override `source` and `target` to ensure better definitional
equalities. -/
@[simps! -fullyApplied]
def disjointUnion (e e' : PartialEquiv α β) (hs : Disjoint e.source e'.source)
    (ht : Disjoint e.target e'.target) [∀ x, Decidable (x ∈ e.source)]
    [∀ y, Decidable (y ∈ e.target)] : PartialEquiv α β :=
  (e.piecewise e' e.source e.target e.isImage_source_target <|
        e'.isImage_source_target_of_disjoint _ hs.symm ht.symm).copy
    _ rfl _ rfl (e.source ∪ e'.source) (ite_left _ _) (e.target ∪ e'.target) (ite_left _ _)

theorem disjointUnion_eq_piecewise (e e' : PartialEquiv α β) (hs : Disjoint e.source e'.source)
    (ht : Disjoint e.target e'.target) [∀ x, Decidable (x ∈ e.source)]
    [∀ y, Decidable (y ∈ e.target)] :
    e.disjointUnion e' hs ht =
      e.piecewise e' e.source e.target e.isImage_source_target
        (e'.isImage_source_target_of_disjoint _ hs.symm ht.symm) :=
  copy_eq ..

section Pi

variable {ι : Type*} {αi βi γi : ι → Type*}

/-- The product of a family of partial equivalences, as a partial equivalence on the pi type. -/
@[simps (attr := mfld_simps) -fullyApplied apply source target]
protected def pi (ei : ∀ i, PartialEquiv (αi i) (βi i)) : PartialEquiv (∀ i, αi i) (∀ i, βi i) where
  toFun := Pi.map fun i ↦ ei i
  invFun := Pi.map fun i ↦ (ei i).symm
  source := pi univ fun i => (ei i).source
  target := pi univ fun i => (ei i).target
  map_source' _ hf i hi := (ei i).map_source (hf i hi)
  map_target' _ hf i hi := (ei i).map_target (hf i hi)
  left_inv' _ hf := funext fun i => (ei i).left_inv (hf i trivial)
  right_inv' _ hf := funext fun i => (ei i).right_inv (hf i trivial)

@[simp, mfld_simps]
theorem pi_symm (ei : ∀ i, PartialEquiv (αi i) (βi i)) :
    (PartialEquiv.pi ei).symm = .pi fun i ↦ (ei i).symm :=
  rfl

theorem pi_symm_apply (ei : ∀ i, PartialEquiv (αi i) (βi i)) :
    ⇑(PartialEquiv.pi ei).symm = fun f i ↦ (ei i).symm (f i) :=
  rfl

@[simp, mfld_simps]
theorem pi_refl : (PartialEquiv.pi fun i ↦ PartialEquiv.refl (αi i)) = .refl (∀ i, αi i) := by
  ext <;> simp

@[simp, mfld_simps]
theorem pi_trans (ei : ∀ i, PartialEquiv (αi i) (βi i)) (ei' : ∀ i, PartialEquiv (βi i) (γi i)) :
    (PartialEquiv.pi ei).trans (PartialEquiv.pi ei') = .pi fun i ↦ (ei i).trans (ei' i) := by
  ext <;> simp [forall_and]

end Pi

lemma surjective_of_target_eq_univ (h : e.target = univ) :
    Surjective e :=
  surjective_iff_surjOn_univ.mpr <| e.surjOn.mono (by simp) (by simp [h])

lemma injective_of_source_eq_univ (h : e.source = univ) :
    Injective e := by
  simpa [injective_iff_injOn_univ, h] using e.injOn

lemma injective_symm_of_target_eq_univ (h : e.target = univ) :
    Injective e.symm :=
  e.symm.injective_of_source_eq_univ h

lemma surjective_symm_of_source_eq_univ (h : e.source = univ) :
    Surjective e.symm :=
  e.symm.surjective_of_target_eq_univ h

end PartialEquiv

namespace Set

-- All arguments are explicit to avoid missing information in the pretty printer output
/-- A bijection between two sets `s : Set α` and `t : Set β` provides a partial equivalence
between `α` and `β`. -/
@[simps -fullyApplied]
noncomputable def BijOn.toPartialEquiv [Nonempty α] (f : α → β) (s : Set α) (t : Set β)
    (hf : BijOn f s t) : PartialEquiv α β where
  toFun := f
  invFun := invFunOn f s
  source := s
  target := t
  map_source' := hf.mapsTo
  map_target' := hf.surjOn.mapsTo_invFunOn
  left_inv' := hf.invOn_invFunOn.1
  right_inv' := hf.invOn_invFunOn.2

/-- A map injective on a subset of its domain provides a partial equivalence. -/
@[simp, mfld_simps]
noncomputable def InjOn.toPartialEquiv [Nonempty α] (f : α → β) (s : Set α) (hf : InjOn f s) :
    PartialEquiv α β :=
  hf.bijOn_image.toPartialEquiv f s (f '' s)

end Set

namespace Equiv

/- `Equiv`s give rise to `PartialEquiv`s. We set up simp lemmas to reduce most properties of the
`PartialEquiv` to that of the `Equiv`. -/
variable (e : α ≃ β) (e' : β ≃ γ)

@[simp, mfld_simps]
theorem refl_toPartialEquiv : (Equiv.refl α).toPartialEquiv = PartialEquiv.refl α :=
  rfl

@[simp, mfld_simps]
theorem symm_toPartialEquiv : e.symm.toPartialEquiv = e.toPartialEquiv.symm :=
  rfl

@[simp, mfld_simps]
theorem trans_toPartialEquiv :
    (e.trans e').toPartialEquiv = e.toPartialEquiv.trans e'.toPartialEquiv :=
  PartialEquiv.ext (fun _ => rfl) (fun _ => rfl)
    (by simp [PartialEquiv.trans_source, Equiv.toPartialEquiv])

/-- Precompose a partial equivalence with an equivalence.
We modify the source and target to have better definitional behavior. -/
@[simps!]
def transPartialEquiv (e : α ≃ β) (f' : PartialEquiv β γ) : PartialEquiv α γ :=
  (e.toPartialEquiv.trans f').copy _ rfl _ rfl (e ⁻¹' f'.source) (univ_inter _) f'.target
    (inter_univ _)

theorem transPartialEquiv_eq_trans (e : α ≃ β) (f' : PartialEquiv β γ) :
    e.transPartialEquiv f' = e.toPartialEquiv.trans f' :=
  PartialEquiv.copy_eq ..

@[simp, mfld_simps]
theorem transPartialEquiv_trans (e : α ≃ β) (f' : PartialEquiv β γ) (f'' : PartialEquiv γ δ) :
    (e.transPartialEquiv f').trans f'' = e.transPartialEquiv (f'.trans f'') := by
  simp only [transPartialEquiv_eq_trans, PartialEquiv.trans_assoc]

@[simp, mfld_simps]
theorem trans_transPartialEquiv (e : α ≃ β) (e' : β ≃ γ) (f'' : PartialEquiv γ δ) :
    (e.trans e').transPartialEquiv f'' = e.transPartialEquiv (e'.transPartialEquiv f'') := by
  simp only [transPartialEquiv_eq_trans, PartialEquiv.trans_assoc, trans_toPartialEquiv]

end Equiv

namespace PartialEquiv

/-- Postcompose a partial equivalence with an equivalence.
We modify the source and target to have better definitional behavior. -/
@[simps!]
def transEquiv (e : PartialEquiv α β) (f' : β ≃ γ) : PartialEquiv α γ :=
  (e.trans f'.toPartialEquiv).copy _ rfl _ rfl e.source (inter_univ _) (f'.symm ⁻¹' e.target)
    (univ_inter _)

theorem transEquiv_eq_trans (e : PartialEquiv α β) (e' : β ≃ γ) :
    e.transEquiv e' = e.trans e'.toPartialEquiv :=
  copy_eq ..

@[simp, mfld_simps]
theorem transEquiv_transEquiv (e : PartialEquiv α β) (f' : β ≃ γ) (f'' : γ ≃ δ) :
    (e.transEquiv f').transEquiv f'' = e.transEquiv (f'.trans f'') := by
  simp only [transEquiv_eq_trans, trans_assoc, Equiv.trans_toPartialEquiv]

@[simp, mfld_simps]
theorem trans_transEquiv (e : PartialEquiv α β) (e' : PartialEquiv β γ) (f'' : γ ≃ δ) :
    (e.trans e').transEquiv f'' = e.trans (e'.transEquiv f'') := by
  simp only [transEquiv_eq_trans, trans_assoc]

end PartialEquiv
