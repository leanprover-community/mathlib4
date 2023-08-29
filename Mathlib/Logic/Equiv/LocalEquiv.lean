/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Data.Set.Function
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.Core

#align_import logic.equiv.local_equiv from "leanprover-community/mathlib"@"48fb5b5280e7c81672afc9524185ae994553ebf4"

/-!
# Local equivalences

This files defines equivalences between subsets of given types.
An element `e` of `LocalEquiv α β` is made of two maps `e.toFun` and `e.invFun` respectively
from α to β and from β to α (just like equivs), which are inverse to each other on the subsets
`e.source` and `e.target` of respectively α and β.

They are designed in particular to define charts on manifolds.

The main functionality is `e.trans f`, which composes the two local equivalences by restricting
the source and target to the maximal set where the composition makes sense.

As for equivs, we register a coercion to functions and use it in our simp normal form: we write
`e x` and `e.symm y` instead of `e.toFun x` and `e.invFun y`.

## Main definitions

`Equiv.toLocalEquiv`: associating a local equiv to an equiv, with source = target = univ
`LocalEquiv.symm`    : the inverse of a local equiv
`LocalEquiv.trans`   : the composition of two local equivs
`LocalEquiv.refl`    : the identity local equiv
`LocalEquiv.ofSet`  : the identity on a set `s`
`EqOnSource`        : equivalence relation describing the "right" notion of equality for local
                        equivs (see below in implementation notes)

## Implementation notes

There are at least three possible implementations of local equivalences:
* equivs on subtypes
* pairs of functions taking values in `Option α` and `Option β`, equal to none where the local
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
* The `LocalEquiv` version as explained above is easier to use for manifolds. The drawback is that
there is extra useless data (the values of `toFun` and `invFun` outside of `source` and `target`).
In particular, the equality notion between local equivs is not "the right one", i.e., coinciding
source and target and equality there. Moreover, there are no local equivs in this sense between
an empty type and a nonempty type. Since empty types are not that useful, and since one almost never
needs to talk about equal local equivs, this is not an issue in practice.
Still, we introduce an equivalence relation `EqOnSource` that captures this right notion of
equality, and show that many properties are invariant under this equivalence relation.

### Local coding conventions

If a lemma deals with the intersection of a set with either source or target of a `LocalEquiv`,
then it should use `e.source ∩ s` or `e.target ∩ t`, not `s ∩ e.source` or `t ∩ e.target`.

-/
open Lean Meta Elab Tactic

/-! Implementation of the `mfld_set_tac` tactic for working with the domains of partially-defined
functions (`LocalEquiv`, `LocalHomeomorph`, etc).

This is in a separate file from `Mathlib.Logic.Equiv.MfldSimpsAttr` because attributes need a new
file to become functional.
-/

/-- Common `@[simps]` configuration options used for manifold-related declarations. -/
def mfld_cfg : Simps.Config where
  attrs := [`mfld_simps]
  fullyApplied := false
#align mfld_cfg mfld_cfg

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
structure LocalEquiv (α : Type*) (β : Type*) where
  /-- The global function which has a local inverse. Its value outside of the `source` subset is
  irrelevant. -/
  toFun : α → β
  /-- The local inverse to `toFun`. Its value outside of the `target` subset is irrelevant. -/
  invFun : β → α
  /-- The domain of the local equivalence. -/
  source : Set α
  /-- The codomain of the local equivalence. -/
  target : Set β
  /-- The proposition that elements of `source` are mapped to elements of `target`. -/
  map_source' : ∀ ⦃x⦄, x ∈ source → toFun x ∈ target
  /-- The proposition that elements of `target` are mapped to elements of `source`. -/
  map_target' : ∀ ⦃x⦄, x ∈ target → invFun x ∈ source
  /-- The proposition that `invFun` is a local left-inverse of `toFun` on `source`. -/
  left_inv' : ∀ ⦃x⦄, x ∈ source → invFun (toFun x) = x
  /-- The proposition that `invFun` is a local right-inverse of `toFun` on `target`. -/
  right_inv' : ∀ ⦃x⦄, x ∈ target → toFun (invFun x) = x
#align local_equiv LocalEquiv

attribute [coe] LocalEquiv.toFun

namespace LocalEquiv

variable (e : LocalEquiv α β) (e' : LocalEquiv β γ)

instance [Inhabited α] [Inhabited β] : Inhabited (LocalEquiv α β) :=
  ⟨⟨const α default, const β default, ∅, ∅, mapsTo_empty _ _, mapsTo_empty _ _, eqOn_empty _ _,
      eqOn_empty _ _⟩⟩

/-- The inverse of a local equiv -/
protected def symm : LocalEquiv β α where
  toFun := e.invFun
  invFun := e.toFun
  source := e.target
  target := e.source
  map_source' := e.map_target'
  map_target' := e.map_source'
  left_inv' := e.right_inv'
  right_inv' := e.left_inv'
#align local_equiv.symm LocalEquiv.symm

instance : CoeFun (LocalEquiv α β) fun _ => α → β :=
  ⟨LocalEquiv.toFun⟩

/-- See Note [custom simps projection] -/
def Simps.symm_apply (e : LocalEquiv α β) : β → α :=
  e.symm
#align local_equiv.simps.symm_apply LocalEquiv.Simps.symm_apply

initialize_simps_projections LocalEquiv (toFun → apply, invFun → symm_apply)

-- Porting note: this can be proven with `dsimp only`
-- @[simp, mfld_simps]
-- theorem coe_mk (f : α → β) (g s t ml mr il ir) : (LocalEquiv.mk f g s t ml mr il ir : α → β) = f
-- := by dsimp only
-- #align local_equiv.coe_mk LocalEquiv.coe_mk
#noalign local_equiv.coe_mk

@[simp, mfld_simps]
theorem coe_symm_mk (f : α → β) (g s t ml mr il ir) :
    ((LocalEquiv.mk f g s t ml mr il ir).symm : β → α) = g :=
  rfl
#align local_equiv.coe_symm_mk LocalEquiv.coe_symm_mk

-- Porting note: this is now a syntactic tautology
-- @[simp, mfld_simps]
-- theorem toFun_as_coe : e.toFun = e := rfl
-- #align local_equiv.to_fun_as_coe LocalEquiv.toFun_as_coe
#noalign local_equiv.to_fun_as_coe

@[simp, mfld_simps]
theorem invFun_as_coe : e.invFun = e.symm :=
  rfl
#align local_equiv.inv_fun_as_coe LocalEquiv.invFun_as_coe

@[simp, mfld_simps]
theorem map_source {x : α} (h : x ∈ e.source) : e x ∈ e.target :=
  e.map_source' h
#align local_equiv.map_source LocalEquiv.map_source

@[simp, mfld_simps]
theorem map_target {x : β} (h : x ∈ e.target) : e.symm x ∈ e.source :=
  e.map_target' h
#align local_equiv.map_target LocalEquiv.map_target

@[simp, mfld_simps]
theorem left_inv {x : α} (h : x ∈ e.source) : e.symm (e x) = x :=
  e.left_inv' h
#align local_equiv.left_inv LocalEquiv.left_inv

@[simp, mfld_simps]
theorem right_inv {x : β} (h : x ∈ e.target) : e (e.symm x) = x :=
  e.right_inv' h
#align local_equiv.right_inv LocalEquiv.right_inv

theorem eq_symm_apply {x : α} {y : β} (hx : x ∈ e.source) (hy : y ∈ e.target) :
    x = e.symm y ↔ e x = y :=
  ⟨fun h => by rw [← e.right_inv hy, h], fun h => by rw [← e.left_inv hx, h]⟩
               -- 🎉 no goals
                                                     -- 🎉 no goals
#align local_equiv.eq_symm_apply LocalEquiv.eq_symm_apply

protected theorem mapsTo : MapsTo e e.source e.target := fun _ => e.map_source
#align local_equiv.maps_to LocalEquiv.mapsTo

theorem symm_mapsTo : MapsTo e.symm e.target e.source :=
  e.symm.mapsTo
#align local_equiv.symm_maps_to LocalEquiv.symm_mapsTo

protected theorem leftInvOn : LeftInvOn e.symm e e.source := fun _ => e.left_inv
#align local_equiv.left_inv_on LocalEquiv.leftInvOn

protected theorem rightInvOn : RightInvOn e.symm e e.target := fun _ => e.right_inv
#align local_equiv.right_inv_on LocalEquiv.rightInvOn

protected theorem invOn : InvOn e.symm e e.source e.target :=
  ⟨e.leftInvOn, e.rightInvOn⟩
#align local_equiv.inv_on LocalEquiv.invOn

protected theorem injOn : InjOn e e.source :=
  e.leftInvOn.injOn
#align local_equiv.inj_on LocalEquiv.injOn

protected theorem bijOn : BijOn e e.source e.target :=
  e.invOn.bijOn e.mapsTo e.symm_mapsTo
#align local_equiv.bij_on LocalEquiv.bijOn

protected theorem surjOn : SurjOn e e.source e.target :=
  e.bijOn.surjOn
#align local_equiv.surj_on LocalEquiv.surjOn

/-- Interpret an `Equiv` as a `LocalEquiv` by restricting it to `s` in the domain
and to `t` in the codomain. -/
@[simps (config := .asFn)]
def _root_.Equiv.toLocalEquivOfImageEq (e : α ≃ β) (s : Set α) (t : Set β) (h : e '' s = t) :
    LocalEquiv α β where
  toFun := e
  invFun := e.symm
  source := s
  target := t
  map_source' x hx := h ▸ mem_image_of_mem _ hx
  map_target' x hx := by
    subst t
    -- ⊢ ↑e.symm x ∈ s
    rcases hx with ⟨x, hx, rfl⟩
    -- ⊢ ↑e.symm (↑e x) ∈ s
    rwa [e.symm_apply_apply]
    -- 🎉 no goals
  left_inv' x _ := e.symm_apply_apply x
  right_inv' x _ := e.apply_symm_apply x

/-- Associate a `LocalEquiv` to an `Equiv`. -/
@[simps! (config := mfld_cfg)]
def _root_.Equiv.toLocalEquiv (e : α ≃ β) : LocalEquiv α β :=
  e.toLocalEquivOfImageEq univ univ <| by rw [image_univ, e.surjective.range_eq]
                                          -- 🎉 no goals
#align equiv.to_local_equiv Equiv.toLocalEquiv
#align equiv.to_local_equiv_symm_apply Equiv.toLocalEquiv_symm_apply
#align equiv.to_local_equiv_target Equiv.toLocalEquiv_target
#align equiv.to_local_equiv_apply Equiv.toLocalEquiv_apply
#align equiv.to_local_equiv_source Equiv.toLocalEquiv_source

instance inhabitedOfEmpty [IsEmpty α] [IsEmpty β] : Inhabited (LocalEquiv α β) :=
  ⟨((Equiv.equivEmpty α).trans (Equiv.equivEmpty β).symm).toLocalEquiv⟩
#align local_equiv.inhabited_of_empty LocalEquiv.inhabitedOfEmpty

/-- Create a copy of a `LocalEquiv` providing better definitional equalities. -/
@[simps (config := { fullyApplied := false })]
def copy (e : LocalEquiv α β) (f : α → β) (hf : ⇑e = f) (g : β → α) (hg : ⇑e.symm = g) (s : Set α)
    (hs : e.source = s) (t : Set β) (ht : e.target = t) :
    LocalEquiv α β where
  toFun := f
  invFun := g
  source := s
  target := t
  map_source' _ := ht ▸ hs ▸ hf ▸ e.map_source
  map_target' _ := hs ▸ ht ▸ hg ▸ e.map_target
  left_inv' _ := hs ▸ hf ▸ hg ▸ e.left_inv
  right_inv' _ := ht ▸ hf ▸ hg ▸ e.right_inv
#align local_equiv.copy LocalEquiv.copy
#align local_equiv.copy_source LocalEquiv.copy_source
#align local_equiv.copy_apply LocalEquiv.copy_apply
#align local_equiv.copy_symm_apply LocalEquiv.copy_symm_apply
#align local_equiv.copy_target LocalEquiv.copy_target

theorem copy_eq (e : LocalEquiv α β) (f : α → β) (hf : ⇑e = f) (g : β → α) (hg : ⇑e.symm = g)
    (s : Set α) (hs : e.source = s) (t : Set β) (ht : e.target = t) :
    e.copy f hf g hg s hs t ht = e := by
  substs f g s t
  -- ⊢ copy e ↑e (_ : ↑e = ↑e) ↑(LocalEquiv.symm e) (_ : ↑(LocalEquiv.symm e) = ↑(L …
  cases e
  -- ⊢ copy { toFun := toFun✝, invFun := invFun✝, source := source✝, target := targ …
  rfl
  -- 🎉 no goals
#align local_equiv.copy_eq LocalEquiv.copy_eq

/-- Associate to a `LocalEquiv` an `Equiv` between the source and the target. -/
protected def toEquiv : e.source ≃ e.target where
  toFun x := ⟨e x, e.map_source x.mem⟩
  invFun y := ⟨e.symm y, e.map_target y.mem⟩
  left_inv := fun ⟨_, hx⟩ => Subtype.eq <| e.left_inv hx
  right_inv := fun ⟨_, hy⟩ => Subtype.eq <| e.right_inv hy
#align local_equiv.to_equiv LocalEquiv.toEquiv

@[simp, mfld_simps]
theorem symm_source : e.symm.source = e.target :=
  rfl
#align local_equiv.symm_source LocalEquiv.symm_source

@[simp, mfld_simps]
theorem symm_target : e.symm.target = e.source :=
  rfl
#align local_equiv.symm_target LocalEquiv.symm_target

@[simp, mfld_simps]
theorem symm_symm : e.symm.symm = e := by
  cases e
  -- ⊢ LocalEquiv.symm (LocalEquiv.symm { toFun := toFun✝, invFun := invFun✝, sourc …
  rfl
  -- 🎉 no goals
#align local_equiv.symm_symm LocalEquiv.symm_symm

theorem image_source_eq_target : e '' e.source = e.target :=
  e.bijOn.image_eq
#align local_equiv.image_source_eq_target LocalEquiv.image_source_eq_target

theorem forall_mem_target {p : β → Prop} : (∀ y ∈ e.target, p y) ↔ ∀ x ∈ e.source, p (e x) := by
  rw [← image_source_eq_target, ball_image_iff]
  -- 🎉 no goals
#align local_equiv.forall_mem_target LocalEquiv.forall_mem_target

theorem exists_mem_target {p : β → Prop} : (∃ y ∈ e.target, p y) ↔ ∃ x ∈ e.source, p (e x) := by
  rw [← image_source_eq_target, bex_image_iff]
  -- 🎉 no goals
#align local_equiv.exists_mem_target LocalEquiv.exists_mem_target

/-- We say that `t : Set β` is an image of `s : Set α` under a local equivalence if
any of the following equivalent conditions hold:

* `e '' (e.source ∩ s) = e.target ∩ t`;
* `e.source ∩ e ⁻¹ t = e.source ∩ s`;
* `∀ x ∈ e.source, e x ∈ t ↔ x ∈ s` (this one is used in the definition).
-/
def IsImage (s : Set α) (t : Set β) : Prop :=
  ∀ ⦃x⦄, x ∈ e.source → (e x ∈ t ↔ x ∈ s)
#align local_equiv.is_image LocalEquiv.IsImage

namespace IsImage

variable {e} {s : Set α} {t : Set β} {x : α} {y : β}

theorem apply_mem_iff (h : e.IsImage s t) (hx : x ∈ e.source) : e x ∈ t ↔ x ∈ s :=
  h hx
#align local_equiv.is_image.apply_mem_iff LocalEquiv.IsImage.apply_mem_iff

theorem symm_apply_mem_iff (h : e.IsImage s t) : ∀ ⦃y⦄, y ∈ e.target → (e.symm y ∈ s ↔ y ∈ t) :=
  e.forall_mem_target.mpr fun x hx => by rw [e.left_inv hx, h hx]
                                         -- 🎉 no goals
#align local_equiv.is_image.symm_apply_mem_iff LocalEquiv.IsImage.symm_apply_mem_iff

protected theorem symm (h : e.IsImage s t) : e.symm.IsImage t s :=
  h.symm_apply_mem_iff
#align local_equiv.is_image.symm LocalEquiv.IsImage.symm

@[simp]
theorem symm_iff : e.symm.IsImage t s ↔ e.IsImage s t :=
  ⟨fun h => h.symm, fun h => h.symm⟩
#align local_equiv.is_image.symm_iff LocalEquiv.IsImage.symm_iff

protected theorem mapsTo (h : e.IsImage s t) : MapsTo e (e.source ∩ s) (e.target ∩ t) :=
  fun _ hx => ⟨e.mapsTo hx.1, (h hx.1).2 hx.2⟩
#align local_equiv.is_image.maps_to LocalEquiv.IsImage.mapsTo

theorem symm_mapsTo (h : e.IsImage s t) : MapsTo e.symm (e.target ∩ t) (e.source ∩ s) :=
  h.symm.mapsTo
#align local_equiv.is_image.symm_maps_to LocalEquiv.IsImage.symm_mapsTo

/-- Restrict a `LocalEquiv` to a pair of corresponding sets. -/
@[simps (config := { fullyApplied := false })]
def restr (h : e.IsImage s t) : LocalEquiv α β where
  toFun := e
  invFun := e.symm
  source := e.source ∩ s
  target := e.target ∩ t
  map_source' := h.mapsTo
  map_target' := h.symm_mapsTo
  left_inv' := e.leftInvOn.mono (inter_subset_left _ _)
  right_inv' := e.rightInvOn.mono (inter_subset_left _ _)
#align local_equiv.is_image.restr LocalEquiv.IsImage.restr
#align local_equiv.is_image.restr_apply LocalEquiv.IsImage.restr_apply
#align local_equiv.is_image.restr_source LocalEquiv.IsImage.restr_source
#align local_equiv.is_image.restr_target LocalEquiv.IsImage.restr_target
#align local_equiv.is_image.restr_symm_apply LocalEquiv.IsImage.restr_symm_apply

theorem image_eq (h : e.IsImage s t) : e '' (e.source ∩ s) = e.target ∩ t :=
  h.restr.image_source_eq_target
#align local_equiv.is_image.image_eq LocalEquiv.IsImage.image_eq

theorem symm_image_eq (h : e.IsImage s t) : e.symm '' (e.target ∩ t) = e.source ∩ s :=
  h.symm.image_eq
#align local_equiv.is_image.symm_image_eq LocalEquiv.IsImage.symm_image_eq

theorem iff_preimage_eq : e.IsImage s t ↔ e.source ∩ e ⁻¹' t = e.source ∩ s := by
  simp only [IsImage, ext_iff, mem_inter_iff, mem_preimage, and_congr_right_iff]
  -- 🎉 no goals
#align local_equiv.is_image.iff_preimage_eq LocalEquiv.IsImage.iff_preimage_eq

alias ⟨preimage_eq, of_preimage_eq⟩ := iff_preimage_eq
#align local_equiv.is_image.of_preimage_eq LocalEquiv.IsImage.of_preimage_eq
#align local_equiv.is_image.preimage_eq LocalEquiv.IsImage.preimage_eq

theorem iff_symm_preimage_eq : e.IsImage s t ↔ e.target ∩ e.symm ⁻¹' s = e.target ∩ t :=
  symm_iff.symm.trans iff_preimage_eq
#align local_equiv.is_image.iff_symm_preimage_eq LocalEquiv.IsImage.iff_symm_preimage_eq

alias ⟨symm_preimage_eq, of_symm_preimage_eq⟩ := iff_symm_preimage_eq
#align local_equiv.is_image.of_symm_preimage_eq LocalEquiv.IsImage.of_symm_preimage_eq
#align local_equiv.is_image.symm_preimage_eq LocalEquiv.IsImage.symm_preimage_eq

theorem of_image_eq (h : e '' (e.source ∩ s) = e.target ∩ t) : e.IsImage s t :=
  of_symm_preimage_eq <| Eq.trans (of_symm_preimage_eq rfl).image_eq.symm h
#align local_equiv.is_image.of_image_eq LocalEquiv.IsImage.of_image_eq

theorem of_symm_image_eq (h : e.symm '' (e.target ∩ t) = e.source ∩ s) : e.IsImage s t :=
  of_preimage_eq <| Eq.trans (iff_preimage_eq.2 rfl).symm_image_eq.symm h
#align local_equiv.is_image.of_symm_image_eq LocalEquiv.IsImage.of_symm_image_eq

protected theorem compl (h : e.IsImage s t) : e.IsImage sᶜ tᶜ := fun _ hx => not_congr (h hx)
#align local_equiv.is_image.compl LocalEquiv.IsImage.compl

protected theorem inter {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s ∩ s') (t ∩ t') := fun _ hx => and_congr (h hx) (h' hx)
#align local_equiv.is_image.inter LocalEquiv.IsImage.inter

protected theorem union {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s ∪ s') (t ∪ t') := fun _ hx => or_congr (h hx) (h' hx)
#align local_equiv.is_image.union LocalEquiv.IsImage.union

protected theorem diff {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s \ s') (t \ t') :=
  h.inter h'.compl
#align local_equiv.is_image.diff LocalEquiv.IsImage.diff

theorem leftInvOn_piecewise {e' : LocalEquiv α β} [∀ i, Decidable (i ∈ s)]
    [∀ i, Decidable (i ∈ t)] (h : e.IsImage s t) (h' : e'.IsImage s t) :
    LeftInvOn (t.piecewise e.symm e'.symm) (s.piecewise e e') (s.ite e.source e'.source) := by
  rintro x (⟨he, hs⟩ | ⟨he, hs : x ∉ s⟩)
  -- ⊢ piecewise t (↑(LocalEquiv.symm e)) (↑(LocalEquiv.symm e')) (piecewise s (↑e) …
  · rw [piecewise_eq_of_mem _ _ _ hs, piecewise_eq_of_mem _ _ _ ((h he).2 hs), e.left_inv he]
    -- 🎉 no goals
  · rw [piecewise_eq_of_not_mem _ _ _ hs, piecewise_eq_of_not_mem _ _ _ ((h'.compl he).2 hs),
      e'.left_inv he]
#align local_equiv.is_image.left_inv_on_piecewise LocalEquiv.IsImage.leftInvOn_piecewise

theorem inter_eq_of_inter_eq_of_eqOn {e' : LocalEquiv α β} (h : e.IsImage s t)
    (h' : e'.IsImage s t) (hs : e.source ∩ s = e'.source ∩ s) (heq : EqOn e e' (e.source ∩ s)) :
    e.target ∩ t = e'.target ∩ t := by rw [← h.image_eq, ← h'.image_eq, ← hs, heq.image_eq]
                                       -- 🎉 no goals
#align local_equiv.is_image.inter_eq_of_inter_eq_of_eq_on LocalEquiv.IsImage.inter_eq_of_inter_eq_of_eqOn

theorem symm_eq_on_of_inter_eq_of_eqOn {e' : LocalEquiv α β} (h : e.IsImage s t)
    (hs : e.source ∩ s = e'.source ∩ s) (heq : EqOn e e' (e.source ∩ s)) :
    EqOn e.symm e'.symm (e.target ∩ t) := by
  rw [← h.image_eq]
  -- ⊢ EqOn (↑(LocalEquiv.symm e)) (↑(LocalEquiv.symm e')) (↑e '' (e.source ∩ s))
  rintro y ⟨x, hx, rfl⟩
  -- ⊢ ↑(LocalEquiv.symm e) (↑e x) = ↑(LocalEquiv.symm e') (↑e x)
  have hx' := hx; rw [hs] at hx'
  -- ⊢ ↑(LocalEquiv.symm e) (↑e x) = ↑(LocalEquiv.symm e') (↑e x)
                  -- ⊢ ↑(LocalEquiv.symm e) (↑e x) = ↑(LocalEquiv.symm e') (↑e x)
  rw [e.left_inv hx.1, heq hx, e'.left_inv hx'.1]
  -- 🎉 no goals
#align local_equiv.is_image.symm_eq_on_of_inter_eq_of_eq_on LocalEquiv.IsImage.symm_eq_on_of_inter_eq_of_eqOn

end IsImage

theorem isImage_source_target : e.IsImage e.source e.target := fun x hx => by simp [hx]
                                                                              -- 🎉 no goals
#align local_equiv.is_image_source_target LocalEquiv.isImage_source_target

theorem isImage_source_target_of_disjoint (e' : LocalEquiv α β) (hs : Disjoint e.source e'.source)
    (ht : Disjoint e.target e'.target) : e.IsImage e'.source e'.target :=
  IsImage.of_image_eq <| by rw [hs.inter_eq, ht.inter_eq, image_empty]
                            -- 🎉 no goals
#align local_equiv.is_image_source_target_of_disjoint LocalEquiv.isImage_source_target_of_disjoint

theorem image_source_inter_eq' (s : Set α) : e '' (e.source ∩ s) = e.target ∩ e.symm ⁻¹' s := by
  rw [inter_comm, e.leftInvOn.image_inter', image_source_eq_target, inter_comm]
  -- 🎉 no goals
#align local_equiv.image_source_inter_eq' LocalEquiv.image_source_inter_eq'

theorem image_source_inter_eq (s : Set α) :
    e '' (e.source ∩ s) = e.target ∩ e.symm ⁻¹' (e.source ∩ s) := by
  rw [inter_comm, e.leftInvOn.image_inter, image_source_eq_target, inter_comm]
  -- 🎉 no goals
#align local_equiv.image_source_inter_eq LocalEquiv.image_source_inter_eq

theorem image_eq_target_inter_inv_preimage {s : Set α} (h : s ⊆ e.source) :
    e '' s = e.target ∩ e.symm ⁻¹' s := by
  rw [← e.image_source_inter_eq', inter_eq_self_of_subset_right h]
  -- 🎉 no goals
#align local_equiv.image_eq_target_inter_inv_preimage LocalEquiv.image_eq_target_inter_inv_preimage

theorem symm_image_eq_source_inter_preimage {s : Set β} (h : s ⊆ e.target) :
    e.symm '' s = e.source ∩ e ⁻¹' s :=
  e.symm.image_eq_target_inter_inv_preimage h
#align local_equiv.symm_image_eq_source_inter_preimage LocalEquiv.symm_image_eq_source_inter_preimage

theorem symm_image_target_inter_eq (s : Set β) :
    e.symm '' (e.target ∩ s) = e.source ∩ e ⁻¹' (e.target ∩ s) :=
  e.symm.image_source_inter_eq _
#align local_equiv.symm_image_target_inter_eq LocalEquiv.symm_image_target_inter_eq

theorem symm_image_target_inter_eq' (s : Set β) : e.symm '' (e.target ∩ s) = e.source ∩ e ⁻¹' s :=
  e.symm.image_source_inter_eq' _
#align local_equiv.symm_image_target_inter_eq' LocalEquiv.symm_image_target_inter_eq'

theorem source_inter_preimage_inv_preimage (s : Set α) :
    e.source ∩ e ⁻¹' (e.symm ⁻¹' s) = e.source ∩ s :=
  Set.ext fun x => and_congr_right_iff.2 fun hx =>
    by simp only [mem_preimage, e.left_inv hx]
       -- 🎉 no goals
#align local_equiv.source_inter_preimage_inv_preimage LocalEquiv.source_inter_preimage_inv_preimage

theorem source_inter_preimage_target_inter (s : Set β) :
    e.source ∩ e ⁻¹' (e.target ∩ s) = e.source ∩ e ⁻¹' s :=
  ext fun _ => ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx => ⟨hx.1, e.map_source hx.1, hx.2⟩⟩
#align local_equiv.source_inter_preimage_target_inter LocalEquiv.source_inter_preimage_target_inter

theorem target_inter_inv_preimage_preimage (s : Set β) :
    e.target ∩ e.symm ⁻¹' (e ⁻¹' s) = e.target ∩ s :=
  e.symm.source_inter_preimage_inv_preimage _
#align local_equiv.target_inter_inv_preimage_preimage LocalEquiv.target_inter_inv_preimage_preimage

theorem symm_image_image_of_subset_source {s : Set α} (h : s ⊆ e.source) : e.symm '' (e '' s) = s :=
  (e.leftInvOn.mono h).image_image
#align local_equiv.symm_image_image_of_subset_source LocalEquiv.symm_image_image_of_subset_source

theorem image_symm_image_of_subset_target {s : Set β} (h : s ⊆ e.target) : e '' (e.symm '' s) = s :=
  e.symm.symm_image_image_of_subset_source h
#align local_equiv.image_symm_image_of_subset_target LocalEquiv.image_symm_image_of_subset_target

theorem source_subset_preimage_target : e.source ⊆ e ⁻¹' e.target :=
  e.mapsTo
#align local_equiv.source_subset_preimage_target LocalEquiv.source_subset_preimage_target

theorem symm_image_target_eq_source : e.symm '' e.target = e.source :=
  e.symm.image_source_eq_target
#align local_equiv.symm_image_target_eq_source LocalEquiv.symm_image_target_eq_source

theorem target_subset_preimage_source : e.target ⊆ e.symm ⁻¹' e.source :=
  e.symm_mapsTo
#align local_equiv.target_subset_preimage_source LocalEquiv.target_subset_preimage_source

/-- Two local equivs that have the same `source`, same `toFun` and same `invFun`, coincide. -/
@[ext]
protected theorem ext {e e' : LocalEquiv α β} (h : ∀ x, e x = e' x)
    (hsymm : ∀ x, e.symm x = e'.symm x) (hs : e.source = e'.source) : e = e' := by
  have A : (e : α → β) = e' := by
    ext x
    exact h x
  have B : (e.symm : β → α) = e'.symm := by
    ext x
    exact hsymm x
  have I : e '' e.source = e.target := e.image_source_eq_target
  -- ⊢ e = e'
  have I' : e' '' e'.source = e'.target := e'.image_source_eq_target
  -- ⊢ e = e'
  rw [A, hs, I'] at I
  -- ⊢ e = e'
  cases e; cases e'
  -- ⊢ { toFun := toFun✝, invFun := invFun✝, source := source✝, target := target✝,  …
           -- ⊢ { toFun := toFun✝¹, invFun := invFun✝¹, source := source✝¹, target := target …
  simp [*] at *
  -- ⊢ toFun✝¹ = toFun✝ ∧ invFun✝¹ = invFun✝ ∧ source✝¹ = source✝ ∧ target✝¹ = targ …
  simp [*]
  -- 🎉 no goals
#align local_equiv.ext LocalEquiv.ext

/-- Restricting a local equivalence to e.source ∩ s -/
protected def restr (s : Set α) : LocalEquiv α β :=
  (@IsImage.of_symm_preimage_eq α β e s (e.symm ⁻¹' s) rfl).restr
#align local_equiv.restr LocalEquiv.restr

@[simp, mfld_simps]
theorem restr_coe (s : Set α) : (e.restr s : α → β) = e :=
  rfl
#align local_equiv.restr_coe LocalEquiv.restr_coe

@[simp, mfld_simps]
theorem restr_coe_symm (s : Set α) : ((e.restr s).symm : β → α) = e.symm :=
  rfl
#align local_equiv.restr_coe_symm LocalEquiv.restr_coe_symm

@[simp, mfld_simps]
theorem restr_source (s : Set α) : (e.restr s).source = e.source ∩ s :=
  rfl
#align local_equiv.restr_source LocalEquiv.restr_source

@[simp, mfld_simps]
theorem restr_target (s : Set α) : (e.restr s).target = e.target ∩ e.symm ⁻¹' s :=
  rfl
#align local_equiv.restr_target LocalEquiv.restr_target

theorem restr_eq_of_source_subset {e : LocalEquiv α β} {s : Set α} (h : e.source ⊆ s) :
    e.restr s = e :=
  LocalEquiv.ext (fun _ => rfl) (fun _ => rfl) (by simp [inter_eq_self_of_subset_left h])
                                                   -- 🎉 no goals
#align local_equiv.restr_eq_of_source_subset LocalEquiv.restr_eq_of_source_subset

@[simp, mfld_simps]
theorem restr_univ {e : LocalEquiv α β} : e.restr univ = e :=
  restr_eq_of_source_subset (subset_univ _)
#align local_equiv.restr_univ LocalEquiv.restr_univ

/-- The identity local equiv -/
protected def refl (α : Type*) : LocalEquiv α α :=
  (Equiv.refl α).toLocalEquiv
#align local_equiv.refl LocalEquiv.refl

@[simp, mfld_simps]
theorem refl_source : (LocalEquiv.refl α).source = univ :=
  rfl
#align local_equiv.refl_source LocalEquiv.refl_source

@[simp, mfld_simps]
theorem refl_target : (LocalEquiv.refl α).target = univ :=
  rfl
#align local_equiv.refl_target LocalEquiv.refl_target

@[simp, mfld_simps]
theorem refl_coe : (LocalEquiv.refl α : α → α) = id :=
  rfl
#align local_equiv.refl_coe LocalEquiv.refl_coe

@[simp, mfld_simps]
theorem refl_symm : (LocalEquiv.refl α).symm = LocalEquiv.refl α :=
  rfl
#align local_equiv.refl_symm LocalEquiv.refl_symm

-- Porting note: removed `simp` because `simp` can prove this
@[mfld_simps]
theorem refl_restr_source (s : Set α) : ((LocalEquiv.refl α).restr s).source = s := by simp
                                                                                       -- 🎉 no goals
#align local_equiv.refl_restr_source LocalEquiv.refl_restr_source

-- Porting note: removed `simp` because `simp` can prove this
@[mfld_simps]
theorem refl_restr_target (s : Set α) : ((LocalEquiv.refl α).restr s).target = s := by
  change univ ∩ id ⁻¹' s = s
  -- ⊢ univ ∩ id ⁻¹' s = s
  simp
  -- 🎉 no goals
#align local_equiv.refl_restr_target LocalEquiv.refl_restr_target

/-- The identity local equiv on a set `s` -/
def ofSet (s : Set α) : LocalEquiv α α where
  toFun := id
  invFun := id
  source := s
  target := s
  map_source' _ hx := hx
  map_target' _ hx := hx
  left_inv' _ _ := rfl
  right_inv' _ _ := rfl
#align local_equiv.of_set LocalEquiv.ofSet

@[simp, mfld_simps]
theorem ofSet_source (s : Set α) : (LocalEquiv.ofSet s).source = s :=
  rfl
#align local_equiv.of_set_source LocalEquiv.ofSet_source

@[simp, mfld_simps]
theorem ofSet_target (s : Set α) : (LocalEquiv.ofSet s).target = s :=
  rfl
#align local_equiv.of_set_target LocalEquiv.ofSet_target

@[simp, mfld_simps]
theorem ofSet_coe (s : Set α) : (LocalEquiv.ofSet s : α → α) = id :=
  rfl
#align local_equiv.of_set_coe LocalEquiv.ofSet_coe

@[simp, mfld_simps]
theorem ofSet_symm (s : Set α) : (LocalEquiv.ofSet s).symm = LocalEquiv.ofSet s :=
  rfl
#align local_equiv.of_set_symm LocalEquiv.ofSet_symm

/-- Composing two local equivs if the target of the first coincides with the source of the
second. -/
@[simps]
protected def trans' (e' : LocalEquiv β γ) (h : e.target = e'.source) : LocalEquiv α γ where
  toFun := e' ∘ e
  invFun := e.symm ∘ e'.symm
  source := e.source
  target := e'.target
  map_source' x hx := by simp [←h, hx]
                         -- 🎉 no goals
  map_target' y hy := by simp [h, hy]
                         -- 🎉 no goals
  left_inv' x hx := by simp [hx, ←h]
                       -- 🎉 no goals
  right_inv' y hy := by simp [hy, h]
                        -- 🎉 no goals
#align local_equiv.trans' LocalEquiv.trans'

/-- Composing two local equivs, by restricting to the maximal domain where their composition
is well defined. -/
protected def trans : LocalEquiv α γ :=
  LocalEquiv.trans' (e.symm.restr e'.source).symm (e'.restr e.target) (inter_comm _ _)
#align local_equiv.trans LocalEquiv.trans

@[simp, mfld_simps]
theorem coe_trans : (e.trans e' : α → γ) = e' ∘ e :=
  rfl
#align local_equiv.coe_trans LocalEquiv.coe_trans

@[simp, mfld_simps]
theorem coe_trans_symm : ((e.trans e').symm : γ → α) = e.symm ∘ e'.symm :=
  rfl
#align local_equiv.coe_trans_symm LocalEquiv.coe_trans_symm

theorem trans_apply {x : α} : (e.trans e') x = e' (e x) :=
  rfl
#align local_equiv.trans_apply LocalEquiv.trans_apply

theorem trans_symm_eq_symm_trans_symm : (e.trans e').symm = e'.symm.trans e.symm := by
  cases e; cases e'; rfl
  -- ⊢ LocalEquiv.symm (LocalEquiv.trans { toFun := toFun✝, invFun := invFun✝, sour …
           -- ⊢ LocalEquiv.symm (LocalEquiv.trans { toFun := toFun✝¹, invFun := invFun✝¹, so …
                     -- 🎉 no goals
#align local_equiv.trans_symm_eq_symm_trans_symm LocalEquiv.trans_symm_eq_symm_trans_symm

@[simp, mfld_simps]
theorem trans_source : (e.trans e').source = e.source ∩ e ⁻¹' e'.source :=
  rfl
#align local_equiv.trans_source LocalEquiv.trans_source

theorem trans_source' : (e.trans e').source = e.source ∩ e ⁻¹' (e.target ∩ e'.source) := by
  mfld_set_tac
  -- 🎉 no goals
#align local_equiv.trans_source' LocalEquiv.trans_source'

theorem trans_source'' : (e.trans e').source = e.symm '' (e.target ∩ e'.source) := by
  rw [e.trans_source', e.symm_image_target_inter_eq]
  -- 🎉 no goals
#align local_equiv.trans_source'' LocalEquiv.trans_source''

theorem image_trans_source : e '' (e.trans e').source = e.target ∩ e'.source :=
  (e.symm.restr e'.source).symm.image_source_eq_target
#align local_equiv.image_trans_source LocalEquiv.image_trans_source

@[simp, mfld_simps]
theorem trans_target : (e.trans e').target = e'.target ∩ e'.symm ⁻¹' e.target :=
  rfl
#align local_equiv.trans_target LocalEquiv.trans_target

theorem trans_target' : (e.trans e').target = e'.target ∩ e'.symm ⁻¹' (e'.source ∩ e.target) :=
  trans_source' e'.symm e.symm
#align local_equiv.trans_target' LocalEquiv.trans_target'

theorem trans_target'' : (e.trans e').target = e' '' (e'.source ∩ e.target) :=
  trans_source'' e'.symm e.symm
#align local_equiv.trans_target'' LocalEquiv.trans_target''

theorem inv_image_trans_target : e'.symm '' (e.trans e').target = e'.source ∩ e.target :=
  image_trans_source e'.symm e.symm
#align local_equiv.inv_image_trans_target LocalEquiv.inv_image_trans_target

theorem trans_assoc (e'' : LocalEquiv γ δ) : (e.trans e').trans e'' = e.trans (e'.trans e'') :=
  LocalEquiv.ext (fun x => rfl) (fun x => rfl)
    (by simp [trans_source, @preimage_comp α β γ, inter_assoc])
        -- 🎉 no goals
#align local_equiv.trans_assoc LocalEquiv.trans_assoc

@[simp, mfld_simps]
theorem trans_refl : e.trans (LocalEquiv.refl β) = e :=
  LocalEquiv.ext (fun x => rfl) (fun x => rfl) (by simp [trans_source])
                                                   -- 🎉 no goals
#align local_equiv.trans_refl LocalEquiv.trans_refl

@[simp, mfld_simps]
theorem refl_trans : (LocalEquiv.refl α).trans e = e :=
  LocalEquiv.ext (fun x => rfl) (fun x => rfl) (by simp [trans_source, preimage_id])
                                                   -- 🎉 no goals
#align local_equiv.refl_trans LocalEquiv.refl_trans

theorem trans_ofSet (s : Set β) : e.trans (ofSet s) = e.restr (e ⁻¹' s) :=
  LocalEquiv.ext (fun _ => rfl) (fun _ => rfl) rfl

theorem trans_refl_restr (s : Set β) : e.trans ((LocalEquiv.refl β).restr s) = e.restr (e ⁻¹' s) :=
  LocalEquiv.ext (fun x => rfl) (fun x => rfl) (by simp [trans_source])
                                                   -- 🎉 no goals
#align local_equiv.trans_refl_restr LocalEquiv.trans_refl_restr

theorem trans_refl_restr' (s : Set β) :
    e.trans ((LocalEquiv.refl β).restr s) = e.restr (e.source ∩ e ⁻¹' s) :=
  LocalEquiv.ext (fun x => rfl) (fun x => rfl) <| by
    simp [trans_source]
    -- ⊢ e.source ∩ ↑e ⁻¹' s = e.source ∩ (e.source ∩ ↑e ⁻¹' s)
    rw [← inter_assoc, inter_self]
    -- 🎉 no goals
#align local_equiv.trans_refl_restr' LocalEquiv.trans_refl_restr'

theorem restr_trans (s : Set α) : (e.restr s).trans e' = (e.trans e').restr s :=
  LocalEquiv.ext (fun x => rfl) (fun x => rfl) <| by
    simp [trans_source, inter_comm, inter_assoc]
    -- 🎉 no goals
#align local_equiv.restr_trans LocalEquiv.restr_trans

/-- A lemma commonly useful when `e` and `e'` are charts of a manifold. -/
theorem mem_symm_trans_source {e' : LocalEquiv α γ} {x : α} (he : x ∈ e.source)
    (he' : x ∈ e'.source) : e x ∈ (e.symm.trans e').source :=
  ⟨e.mapsTo he, by rwa [mem_preimage, LocalEquiv.symm_symm, e.left_inv he]⟩
                   -- 🎉 no goals
#align local_equiv.mem_symm_trans_source LocalEquiv.mem_symm_trans_source

/-- Postcompose a local equivalence with an equivalence.
We modify the source and target to have better definitional behavior. -/
@[simps!]
def transEquiv (e' : β ≃ γ) : LocalEquiv α γ :=
  (e.trans e'.toLocalEquiv).copy _ rfl _ rfl e.source (inter_univ _) (e'.symm ⁻¹' e.target)
    (univ_inter _)
#align local_equiv.trans_equiv LocalEquiv.transEquiv
#align local_equiv.trans_equiv_source LocalEquiv.transEquiv_source
#align local_equiv.trans_equiv_apply LocalEquiv.transEquiv_apply
#align local_equiv.trans_equiv_target LocalEquiv.transEquiv_target
#align local_equiv.trans_equiv_symm_apply LocalEquiv.transEquiv_symm_apply

theorem transEquiv_eq_trans (e' : β ≃ γ) : e.transEquiv e' = e.trans e'.toLocalEquiv :=
  copy_eq ..
#align local_equiv.trans_equiv_eq_trans LocalEquiv.transEquiv_eq_trans

/-- Precompose a local equivalence with an equivalence.
We modify the source and target to have better definitional behavior. -/
@[simps!]
def _root_.Equiv.transLocalEquiv (e : α ≃ β) : LocalEquiv α γ :=
  (e.toLocalEquiv.trans e').copy _ rfl _ rfl (e ⁻¹' e'.source) (univ_inter _) e'.target
    (inter_univ _)
#align equiv.trans_local_equiv Equiv.transLocalEquiv
#align equiv.trans_local_equiv_target Equiv.transLocalEquiv_target
#align equiv.trans_local_equiv_apply Equiv.transLocalEquiv_apply
#align equiv.trans_local_equiv_source Equiv.transLocalEquiv_source
#align equiv.trans_local_equiv_symm_apply Equiv.transLocalEquiv_symm_apply

theorem _root_.Equiv.transLocalEquiv_eq_trans (e : α ≃ β) :
    e.transLocalEquiv e' = e.toLocalEquiv.trans e' :=
  copy_eq ..
#align equiv.trans_local_equiv_eq_trans Equiv.transLocalEquiv_eq_trans

/-- `EqOnSource e e'` means that `e` and `e'` have the same source, and coincide there. Then `e`
and `e'` should really be considered the same local equiv. -/
def EqOnSource (e e' : LocalEquiv α β) : Prop :=
  e.source = e'.source ∧ e.source.EqOn e e'
#align local_equiv.eq_on_source LocalEquiv.EqOnSource

/-- `EqOnSource` is an equivalence relation. This instance provides the `≈` notation between two
`LocalEquiv`s. -/
instance eqOnSourceSetoid : Setoid (LocalEquiv α β) where
  r := EqOnSource
  iseqv := by constructor <;> simp only [Equivalence, EqOnSource, EqOn] <;> aesop
                              -- ⊢ ∀ (x : LocalEquiv α β), True ∧ ∀ ⦃x_1 : α⦄, x_1 ∈ x.source → True
                              -- ⊢ ∀ {x y : LocalEquiv α β}, (x.source = y.source ∧ ∀ ⦃x_1 : α⦄, x_1 ∈ x.source …
                              -- ⊢ ∀ {x y z : LocalEquiv α β}, (x.source = y.source ∧ ∀ ⦃x_1 : α⦄, x_1 ∈ x.sour …
                                                                            -- 🎉 no goals
                                                                            -- 🎉 no goals
                                                                            -- 🎉 no goals
#align local_equiv.eq_on_source_setoid LocalEquiv.eqOnSourceSetoid

theorem eqOnSource_refl : e ≈ e :=
  Setoid.refl _
#align local_equiv.eq_on_source_refl LocalEquiv.eqOnSource_refl

/-- Two equivalent local equivs have the same source -/
theorem EqOnSource.source_eq {e e' : LocalEquiv α β} (h : e ≈ e') : e.source = e'.source :=
  h.1
#align local_equiv.eq_on_source.source_eq LocalEquiv.EqOnSource.source_eq

/-- Two equivalent local equivs coincide on the source -/
theorem EqOnSource.eqOn {e e' : LocalEquiv α β} (h : e ≈ e') : e.source.EqOn e e' :=
  h.2
#align local_equiv.eq_on_source.eq_on LocalEquiv.EqOnSource.eqOn

--Porting note: A lot of dot notation failures here. Maybe we should not use `≈`

/-- Two equivalent local equivs have the same target -/
theorem EqOnSource.target_eq {e e' : LocalEquiv α β} (h : e ≈ e') : e.target = e'.target := by
  simp only [← image_source_eq_target, ← source_eq h, h.2.image_eq]
  -- 🎉 no goals
#align local_equiv.eq_on_source.target_eq LocalEquiv.EqOnSource.target_eq

/-- If two local equivs are equivalent, so are their inverses. -/
theorem EqOnSource.symm' {e e' : LocalEquiv α β} (h : e ≈ e') : e.symm ≈ e'.symm := by
  refine' ⟨target_eq h, eqOn_of_leftInvOn_of_rightInvOn e.leftInvOn _ _⟩ <;>
  -- ⊢ RightInvOn (↑(LocalEquiv.symm e')) (↑e) (LocalEquiv.symm e).source
    simp only [symm_source, target_eq h, source_eq h, e'.symm_mapsTo]
    -- ⊢ RightInvOn (↑(LocalEquiv.symm e')) (↑e) e'.target
    -- 🎉 no goals
  exact e'.rightInvOn.congr_right e'.symm_mapsTo (source_eq h ▸ h.eqOn.symm)
  -- 🎉 no goals
#align local_equiv.eq_on_source.symm' LocalEquiv.EqOnSource.symm'

/-- Two equivalent local equivs have coinciding inverses on the target -/
theorem EqOnSource.symm_eqOn {e e' : LocalEquiv α β} (h : e ≈ e') : EqOn e.symm e'.symm e.target :=
  -- Porting note: `h.symm'` dot notation doesn't work anymore because `h` is not recognised as
  -- `LocalEquiv.EqOnSource` for some reason.
  eqOn (symm' h)
#align local_equiv.eq_on_source.symm_eq_on LocalEquiv.EqOnSource.symm_eqOn

/-- Composition of local equivs respects equivalence -/
theorem EqOnSource.trans' {e e' : LocalEquiv α β} {f f' : LocalEquiv β γ} (he : e ≈ e')
    (hf : f ≈ f') : e.trans f ≈ e'.trans f' := by
  constructor
  -- ⊢ (LocalEquiv.trans e f).source = (LocalEquiv.trans e' f').source
  · rw [trans_source'', trans_source'', ← target_eq he, ← hf.1]
    -- ⊢ ↑(LocalEquiv.symm e) '' (e.target ∩ f.source) = ↑(LocalEquiv.symm e') '' (e. …
    exact (he.symm'.eqOn.mono <| inter_subset_left _ _).image_eq
    -- 🎉 no goals
  · intro x hx
    -- ⊢ ↑(LocalEquiv.trans e f) x = ↑(LocalEquiv.trans e' f') x
    rw [trans_source] at hx
    -- ⊢ ↑(LocalEquiv.trans e f) x = ↑(LocalEquiv.trans e' f') x
    simp [Function.comp_apply, LocalEquiv.coe_trans, (he.2 hx.1).symm, hf.2 hx.2]
    -- 🎉 no goals
#align local_equiv.eq_on_source.trans' LocalEquiv.EqOnSource.trans'

/-- Restriction of local equivs respects equivalence -/
theorem EqOnSource.restr {e e' : LocalEquiv α β} (he : e ≈ e') (s : Set α) :
    e.restr s ≈ e'.restr s := by
  constructor
  -- ⊢ (LocalEquiv.restr e s).source = (LocalEquiv.restr e' s).source
  · simp [he.1]
    -- 🎉 no goals
  · intro x hx
    -- ⊢ ↑(LocalEquiv.restr e s) x = ↑(LocalEquiv.restr e' s) x
    simp only [mem_inter_iff, restr_source] at hx
    -- ⊢ ↑(LocalEquiv.restr e s) x = ↑(LocalEquiv.restr e' s) x
    exact he.2 hx.1
    -- 🎉 no goals
#align local_equiv.eq_on_source.restr LocalEquiv.EqOnSource.restr

/-- Preimages are respected by equivalence -/
theorem EqOnSource.source_inter_preimage_eq {e e' : LocalEquiv α β} (he : e ≈ e') (s : Set β) :
    e.source ∩ e ⁻¹' s = e'.source ∩ e' ⁻¹' s := by rw [he.eqOn.inter_preimage_eq, source_eq he]
                                                    -- 🎉 no goals
#align local_equiv.eq_on_source.source_inter_preimage_eq LocalEquiv.EqOnSource.source_inter_preimage_eq

/-- Composition of a local equiv and its inverse is equivalent to the restriction of the identity
to the source -/
theorem trans_self_symm : e.trans e.symm ≈ ofSet e.source := by
  have A : (e.trans e.symm).source = e.source := by mfld_set_tac
  -- ⊢ LocalEquiv.trans e (LocalEquiv.symm e) ≈ ofSet e.source
  refine' ⟨by rw [A, ofSet_source], fun x hx => _⟩
  -- ⊢ ↑(LocalEquiv.trans e (LocalEquiv.symm e)) x = ↑(ofSet e.source) x
  rw [A] at hx
  -- ⊢ ↑(LocalEquiv.trans e (LocalEquiv.symm e)) x = ↑(ofSet e.source) x
  simp only [hx, mfld_simps]
  -- 🎉 no goals
#align local_equiv.trans_self_symm LocalEquiv.trans_self_symm

/-- Composition of the inverse of a local equiv and this local equiv is equivalent to the
restriction of the identity to the target -/
theorem trans_symm_self : e.symm.trans e ≈ LocalEquiv.ofSet e.target :=
  trans_self_symm e.symm
#align local_equiv.trans_symm_self LocalEquiv.trans_symm_self

/-- Two equivalent local equivs are equal when the source and target are univ -/
theorem eq_of_eq_on_source_univ (e e' : LocalEquiv α β) (h : e ≈ e') (s : e.source = univ)
    (t : e.target = univ) : e = e' := by
  refine LocalEquiv.ext (fun x => ?_) (fun x => ?_) h.1
  -- ⊢ ↑e x = ↑e' x
  · apply h.2
    -- ⊢ x ∈ e.source
    rw [s]
    -- ⊢ x ∈ univ
    exact mem_univ _
    -- 🎉 no goals
  · apply h.symm'.2
    -- ⊢ x ∈ (LocalEquiv.symm e).source
    rw [symm_source, t]
    -- ⊢ x ∈ univ
    exact mem_univ _
    -- 🎉 no goals
#align local_equiv.eq_of_eq_on_source_univ LocalEquiv.eq_of_eq_on_source_univ

section Prod

/-- The product of two local equivs, as a local equiv on the product. -/
def prod (e : LocalEquiv α β) (e' : LocalEquiv γ δ) : LocalEquiv (α × γ) (β × δ) where
  source := e.source ×ˢ e'.source
  target := e.target ×ˢ e'.target
  toFun p := (e p.1, e' p.2)
  invFun p := (e.symm p.1, e'.symm p.2)
  map_source' p hp := by
    simp at hp
    -- ⊢ (fun p => (↑e p.fst, ↑e' p.snd)) p ∈ e.target ×ˢ e'.target
    simp [hp]
    -- 🎉 no goals
  map_target' p hp := by
    simp at hp
    -- ⊢ (fun p => (↑(LocalEquiv.symm e) p.fst, ↑(LocalEquiv.symm e') p.snd)) p ∈ e.s …
    simp [map_target, hp]
    -- 🎉 no goals
  left_inv' p hp := by
    simp at hp
    -- ⊢ (fun p => (↑(LocalEquiv.symm e) p.fst, ↑(LocalEquiv.symm e') p.snd)) ((fun p …
    simp [hp]
    -- 🎉 no goals
  right_inv' p hp := by
    simp at hp
    -- ⊢ (fun p => (↑e p.fst, ↑e' p.snd)) ((fun p => (↑(LocalEquiv.symm e) p.fst, ↑(L …
    simp [hp]
    -- 🎉 no goals
#align local_equiv.prod LocalEquiv.prod

@[simp, mfld_simps]
theorem prod_source (e : LocalEquiv α β) (e' : LocalEquiv γ δ) :
    (e.prod e').source = e.source ×ˢ e'.source :=
  rfl
#align local_equiv.prod_source LocalEquiv.prod_source

@[simp, mfld_simps]
theorem prod_target (e : LocalEquiv α β) (e' : LocalEquiv γ δ) :
    (e.prod e').target = e.target ×ˢ e'.target :=
  rfl
#align local_equiv.prod_target LocalEquiv.prod_target

@[simp, mfld_simps]
theorem prod_coe (e : LocalEquiv α β) (e' : LocalEquiv γ δ) :
    (e.prod e' : α × γ → β × δ) = fun p => (e p.1, e' p.2) :=
  rfl
#align local_equiv.prod_coe LocalEquiv.prod_coe

theorem prod_coe_symm (e : LocalEquiv α β) (e' : LocalEquiv γ δ) :
    ((e.prod e').symm : β × δ → α × γ) = fun p => (e.symm p.1, e'.symm p.2) :=
  rfl
#align local_equiv.prod_coe_symm LocalEquiv.prod_coe_symm

@[simp, mfld_simps]
theorem prod_symm (e : LocalEquiv α β) (e' : LocalEquiv γ δ) :
    (e.prod e').symm = e.symm.prod e'.symm := by
  ext x <;> simp [prod_coe_symm]
            -- 🎉 no goals
            -- 🎉 no goals
            -- 🎉 no goals
            -- 🎉 no goals
            -- 🎉 no goals
#align local_equiv.prod_symm LocalEquiv.prod_symm

@[simp, mfld_simps]
theorem refl_prod_refl :
    (LocalEquiv.refl α).prod (LocalEquiv.refl β) = LocalEquiv.refl (α × β) := by
  -- Porting note: `ext1 ⟨x, y⟩` insufficient number of binders
  ext ⟨x, y⟩ <;> simp
                 -- 🎉 no goals
                 -- 🎉 no goals
                 -- 🎉 no goals
                 -- 🎉 no goals
                 -- 🎉 no goals
#align local_equiv.refl_prod_refl LocalEquiv.refl_prod_refl

@[simp, mfld_simps]
theorem prod_trans {η : Type*} {ε : Type*} (e : LocalEquiv α β) (f : LocalEquiv β γ)
    (e' : LocalEquiv δ η) (f' : LocalEquiv η ε) :
    (e.prod e').trans (f.prod f') = (e.trans f).prod (e'.trans f') := by
  ext ⟨x, y⟩ <;> simp [ext_iff]; tauto
                 -- 🎉 no goals
                 -- 🎉 no goals
                 -- 🎉 no goals
                 -- 🎉 no goals
                 -- ⊢ (x ∈ e.source ∧ y ∈ e'.source) ∧ ↑e x ∈ f.source ∧ ↑e' y ∈ f'.source ↔ (x ∈  …
                                 -- 🎉 no goals
#align local_equiv.prod_trans LocalEquiv.prod_trans

end Prod

/-- Combine two `LocalEquiv`s using `Set.piecewise`. The source of the new `LocalEquiv` is
`s.ite e.source e'.source = e.source ∩ s ∪ e'.source \ s`, and similarly for target.  The function
sends `e.source ∩ s` to `e.target ∩ t` using `e` and `e'.source \ s` to `e'.target \ t` using `e'`,
and similarly for the inverse function. The definition assumes `e.isImage s t` and
`e'.isImage s t`. -/
@[simps (config := { fullyApplied := false })]
def piecewise (e e' : LocalEquiv α β) (s : Set α) (t : Set β) [∀ x, Decidable (x ∈ s)]
    [∀ y, Decidable (y ∈ t)] (H : e.IsImage s t) (H' : e'.IsImage s t) :
    LocalEquiv α β where
  toFun := s.piecewise e e'
  invFun := t.piecewise e.symm e'.symm
  source := s.ite e.source e'.source
  target := t.ite e.target e'.target
  map_source' := H.mapsTo.piecewise_ite H'.compl.mapsTo
  map_target' := H.symm.mapsTo.piecewise_ite H'.symm.compl.mapsTo
  left_inv' := H.leftInvOn_piecewise H'
  right_inv' := H.symm.leftInvOn_piecewise H'.symm
#align local_equiv.piecewise LocalEquiv.piecewise
#align local_equiv.piecewise_source LocalEquiv.piecewise_source
#align local_equiv.piecewise_target LocalEquiv.piecewise_target
#align local_equiv.piecewise_symm_apply LocalEquiv.piecewise_symm_apply
#align local_equiv.piecewise_apply LocalEquiv.piecewise_apply

theorem symm_piecewise (e e' : LocalEquiv α β) {s : Set α} {t : Set β} [∀ x, Decidable (x ∈ s)]
    [∀ y, Decidable (y ∈ t)] (H : e.IsImage s t) (H' : e'.IsImage s t) :
    (e.piecewise e' s t H H').symm = e.symm.piecewise e'.symm t s H.symm H'.symm :=
  rfl
#align local_equiv.symm_piecewise LocalEquiv.symm_piecewise

/-- Combine two `LocalEquiv`s with disjoint sources and disjoint targets. We reuse
`LocalEquiv.piecewise`, then override `source` and `target` to ensure better definitional
equalities. -/
@[simps! (config := { fullyApplied := false })]
def disjointUnion (e e' : LocalEquiv α β) (hs : Disjoint e.source e'.source)
    (ht : Disjoint e.target e'.target) [∀ x, Decidable (x ∈ e.source)]
    [∀ y, Decidable (y ∈ e.target)] : LocalEquiv α β :=
  (e.piecewise e' e.source e.target e.isImage_source_target <|
        e'.isImage_source_target_of_disjoint _ hs.symm ht.symm).copy
    _ rfl _ rfl (e.source ∪ e'.source) (ite_left _ _) (e.target ∪ e'.target) (ite_left _ _)
#align local_equiv.disjoint_union LocalEquiv.disjointUnion
#align local_equiv.disjoint_union_source LocalEquiv.disjointUnion_source
#align local_equiv.disjoint_union_target LocalEquiv.disjointUnion_target
#align local_equiv.disjoint_union_symm_apply LocalEquiv.disjointUnion_symm_apply
#align local_equiv.disjoint_union_apply LocalEquiv.disjointUnion_apply

theorem disjointUnion_eq_piecewise (e e' : LocalEquiv α β) (hs : Disjoint e.source e'.source)
    (ht : Disjoint e.target e'.target) [∀ x, Decidable (x ∈ e.source)]
    [∀ y, Decidable (y ∈ e.target)] :
    e.disjointUnion e' hs ht =
      e.piecewise e' e.source e.target e.isImage_source_target
        (e'.isImage_source_target_of_disjoint _ hs.symm ht.symm) :=
  copy_eq ..
#align local_equiv.disjoint_union_eq_piecewise LocalEquiv.disjointUnion_eq_piecewise

section Pi

variable {ι : Type*} {αi βi γi : ι → Type*}

/-- The product of a family of local equivs, as a local equiv on the pi type. -/
@[simps (config := mfld_cfg) apply source target]
protected def pi (ei : ∀ i, LocalEquiv (αi i) (βi i)) : LocalEquiv (∀ i, αi i) (∀ i, βi i) where
  toFun f i := ei i (f i)
  invFun f i := (ei i).symm (f i)
  source := pi univ fun i => (ei i).source
  target := pi univ fun i => (ei i).target
  map_source' _ hf i hi := (ei i).map_source (hf i hi)
  map_target' _ hf i hi := (ei i).map_target (hf i hi)
  left_inv' _ hf := funext fun i => (ei i).left_inv (hf i trivial)
  right_inv' _ hf := funext fun i => (ei i).right_inv (hf i trivial)
#align local_equiv.pi LocalEquiv.pi
#align local_equiv.pi_source LocalEquiv.pi_source
#align local_equiv.pi_apply LocalEquiv.pi_apply
#align local_equiv.pi_target LocalEquiv.pi_target

@[simp, mfld_simps]
theorem pi_symm (ei : ∀ i, LocalEquiv (αi i) (βi i)) :
    (LocalEquiv.pi ei).symm = .pi fun i ↦ (ei i).symm :=
  rfl

theorem pi_symm_apply (ei : ∀ i, LocalEquiv (αi i) (βi i)) :
    ⇑(LocalEquiv.pi ei).symm = fun f i ↦ (ei i).symm (f i) :=
  rfl
#align local_equiv.pi_symm_apply LocalEquiv.pi_symm_apply

@[simp, mfld_simps]
theorem pi_refl : (LocalEquiv.pi fun i ↦ LocalEquiv.refl (αi i)) = .refl (∀ i, αi i) := by
  ext <;> simp
          -- 🎉 no goals
          -- 🎉 no goals
          -- 🎉 no goals

@[simp, mfld_simps]
theorem pi_trans (ei : ∀ i, LocalEquiv (αi i) (βi i)) (ei' : ∀ i, LocalEquiv (βi i) (γi i)) :
    (LocalEquiv.pi ei).trans (LocalEquiv.pi ei') = .pi fun i ↦ (ei i).trans (ei' i) := by
  ext <;> simp [forall_and]
          -- 🎉 no goals
          -- 🎉 no goals
          -- 🎉 no goals

end Pi

end LocalEquiv

namespace Set

-- All arguments are explicit to avoid missing information in the pretty printer output
/-- A bijection between two sets `s : Set α` and `t : Set β` provides a local equivalence
between `α` and `β`. -/
@[simps (config := { fullyApplied := false })]
noncomputable def BijOn.toLocalEquiv [Nonempty α] (f : α → β) (s : Set α) (t : Set β)
    (hf : BijOn f s t) : LocalEquiv α β where
  toFun := f
  invFun := invFunOn f s
  source := s
  target := t
  map_source' := hf.mapsTo
  map_target' := hf.surjOn.mapsTo_invFunOn
  left_inv' := hf.invOn_invFunOn.1
  right_inv' := hf.invOn_invFunOn.2
#align set.bij_on.to_local_equiv Set.BijOn.toLocalEquiv
#align set.bij_on.to_local_equiv_target Set.BijOn.toLocalEquiv_target
#align set.bij_on.to_local_equiv_symm_apply Set.BijOn.toLocalEquiv_symm_apply
#align set.bij_on.to_local_equiv_apply Set.BijOn.toLocalEquiv_apply
#align set.bij_on.to_local_equiv_source Set.BijOn.toLocalEquiv_source

/-- A map injective on a subset of its domain provides a local equivalence. -/
@[simp, mfld_simps]
noncomputable def InjOn.toLocalEquiv [Nonempty α] (f : α → β) (s : Set α) (hf : InjOn f s) :
    LocalEquiv α β :=
  hf.bijOn_image.toLocalEquiv f s (f '' s)
#align set.inj_on.to_local_equiv Set.InjOn.toLocalEquiv

end Set

namespace Equiv

/- `Equiv`s give rise to `LocalEquiv`s. We set up simp lemmas to reduce most properties of the
`LocalEquiv` to that of the `Equiv`. -/
variable (e : α ≃ β) (e' : β ≃ γ)

@[simp, mfld_simps]
theorem refl_toLocalEquiv : (Equiv.refl α).toLocalEquiv = LocalEquiv.refl α :=
  rfl
#align equiv.refl_to_local_equiv Equiv.refl_toLocalEquiv

@[simp, mfld_simps]
theorem symm_toLocalEquiv : e.symm.toLocalEquiv = e.toLocalEquiv.symm :=
  rfl
#align equiv.symm_to_local_equiv Equiv.symm_toLocalEquiv

@[simp, mfld_simps]
theorem trans_toLocalEquiv : (e.trans e').toLocalEquiv = e.toLocalEquiv.trans e'.toLocalEquiv :=
  LocalEquiv.ext (fun x => rfl) (fun x => rfl)
    (by simp [LocalEquiv.trans_source, Equiv.toLocalEquiv])
        -- 🎉 no goals
#align equiv.trans_to_local_equiv Equiv.trans_toLocalEquiv

end Equiv
