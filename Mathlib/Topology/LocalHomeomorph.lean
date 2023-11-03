/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Logic.Equiv.LocalEquiv
import Mathlib.Topology.Sets.Opens

#align_import topology.local_homeomorph from "leanprover-community/mathlib"@"431589bce478b2229eba14b14a283250428217db"

/-!
# Local homeomorphisms

This file defines homeomorphisms between open subsets of topological spaces. An element `e` of
`LocalHomeomorph α β` is an extension of `LocalEquiv α β`, i.e., it is a pair of functions
`e.toFun` and `e.invFun`, inverse of each other on the sets `e.source` and `e.target`.
Additionally, we require that these sets are open, and that the functions are continuous on them.
Equivalently, they are homeomorphisms there.

As in equivs, we register a coercion to functions, and we use `e x` and `e.symm x` throughout
instead of `e.toFun x` and `e.invFun x`.

## Main definitions

`Homeomorph.toLocalHomeomorph` : associating a local homeomorphism to a homeomorphism, with
                                 `source = target = Set.univ`;
`LocalHomeomorph.symm` : the inverse of a local homeomorphism
`LocalHomeomorph.trans` : the composition of two local homeomorphisms
`LocalHomeomorph.refl` : the identity local homeomorphism
`LocalHomeomorph.ofSet` : the identity on a set `s`
`LocalHomeomorph.EqOnSource` : equivalence relation describing the "right" notion of equality
                               for local homeomorphisms

## Implementation notes

Most statements are copied from their `LocalEquiv` versions, although some care is required
especially when restricting to subsets, as these should be open subsets.

For design notes, see `LocalEquiv.lean`.

### Local coding conventions

If a lemma deals with the intersection of a set with either source or target of a `LocalEquiv`,
then it should use `e.source ∩ s` or `e.target ∩ t`, not `s ∩ e.source` or `t ∩ e.target`.
-/


open Function Set Filter Topology

open TopologicalSpace (SecondCountableTopology)

variable {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} [TopologicalSpace α]
  [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]

/-- local homeomorphisms, defined on open subsets of the space -/
-- porting note: commented @[nolint has_nonempty_instance]
structure LocalHomeomorph (α : Type*) (β : Type*) [TopologicalSpace α]
  [TopologicalSpace β] extends LocalEquiv α β where
  open_source : IsOpen source
  open_target : IsOpen target
  continuous_toFun : ContinuousOn toFun source
  continuous_invFun : ContinuousOn invFun target
#align local_homeomorph LocalHomeomorph

namespace LocalHomeomorph

variable (e : LocalHomeomorph α β) (e' : LocalHomeomorph β γ)

/-- Coercion of a local homeomorphisms to a function. We don't use `e.toFun` because it is actually
`e.toLocalEquiv.toFun`, so `simp` will apply lemmas about `toLocalEquiv`. While we may want to
switch to this behavior later, doing it mid-port will break a lot of proofs.  -/
@[coe] def toFun' : α → β := e.toFun

/-- Coercion of a `LocalHomeomorph` to function. Note that a `LocalHomeomorph` is not `FunLike`. -/
instance : CoeFun (LocalHomeomorph α β) fun _ => α → β :=
  ⟨fun e => e.toFun'⟩

/-- The inverse of a local homeomorphism -/
protected def symm : LocalHomeomorph β α where
  toLocalEquiv := e.toLocalEquiv.symm
  open_source := e.open_target
  open_target := e.open_source
  continuous_toFun := e.continuous_invFun
  continuous_invFun := e.continuous_toFun
#align local_homeomorph.symm LocalHomeomorph.symm

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def Simps.apply (e : LocalHomeomorph α β) : α → β := e
#align local_homeomorph.simps.apply LocalHomeomorph.Simps.apply

/-- See Note [custom simps projection] -/
def Simps.symm_apply (e : LocalHomeomorph α β) : β → α := e.symm
#align local_homeomorph.simps.symm_apply LocalHomeomorph.Simps.symm_apply

initialize_simps_projections LocalHomeomorph (toFun → apply, invFun → symm_apply)

protected theorem continuousOn : ContinuousOn e e.source :=
  e.continuous_toFun
#align local_homeomorph.continuous_on LocalHomeomorph.continuousOn

theorem continuousOn_symm : ContinuousOn e.symm e.target :=
  e.continuous_invFun
#align local_homeomorph.continuous_on_symm LocalHomeomorph.continuousOn_symm

@[simp, mfld_simps]
theorem mk_coe (e : LocalEquiv α β) (a b c d) : (LocalHomeomorph.mk e a b c d : α → β) = e :=
  rfl
#align local_homeomorph.mk_coe LocalHomeomorph.mk_coe

@[simp, mfld_simps]
theorem mk_coe_symm (e : LocalEquiv α β) (a b c d) :
    ((LocalHomeomorph.mk e a b c d).symm : β → α) = e.symm :=
  rfl
#align local_homeomorph.mk_coe_symm LocalHomeomorph.mk_coe_symm

theorem toLocalEquiv_injective : Injective (toLocalEquiv : LocalHomeomorph α β → LocalEquiv α β)
  | ⟨_, _, _, _, _⟩, ⟨_, _, _, _, _⟩, rfl => rfl
#align local_homeomorph.to_local_equiv_injective LocalHomeomorph.toLocalEquiv_injective

/- Register a few simp lemmas to make sure that `simp` puts the application of a local
homeomorphism in its normal form, i.e., in terms of its coercion to a function. -/
@[simp, mfld_simps]
theorem toFun_eq_coe (e : LocalHomeomorph α β) : e.toFun = e :=
  rfl
#align local_homeomorph.to_fun_eq_coe LocalHomeomorph.toFun_eq_coe

@[simp, mfld_simps]
theorem invFun_eq_coe (e : LocalHomeomorph α β) : e.invFun = e.symm :=
  rfl
#align local_homeomorph.inv_fun_eq_coe LocalHomeomorph.invFun_eq_coe

@[simp, mfld_simps]
theorem coe_coe : (e.toLocalEquiv : α → β) = e :=
  rfl
#align local_homeomorph.coe_coe LocalHomeomorph.coe_coe

@[simp, mfld_simps]
theorem coe_coe_symm : (e.toLocalEquiv.symm : β → α) = e.symm :=
  rfl
#align local_homeomorph.coe_coe_symm LocalHomeomorph.coe_coe_symm

@[simp, mfld_simps]
theorem map_source {x : α} (h : x ∈ e.source) : e x ∈ e.target :=
  e.map_source' h
#align local_homeomorph.map_source LocalHomeomorph.map_source

-- like `e.map_source'`, but stated in terms of images
lemma map_source'' : e '' e.source ⊆ e.target :=
  fun _ ⟨_, hx, hex⟩ ↦ mem_of_eq_of_mem (id hex.symm) (e.map_source' hx)

@[simp, mfld_simps]
theorem map_target {x : β} (h : x ∈ e.target) : e.symm x ∈ e.source :=
  e.map_target' h
#align local_homeomorph.map_target LocalHomeomorph.map_target

@[simp, mfld_simps]
theorem left_inv {x : α} (h : x ∈ e.source) : e.symm (e x) = x :=
  e.left_inv' h
#align local_homeomorph.left_inv LocalHomeomorph.left_inv

@[simp, mfld_simps]
theorem right_inv {x : β} (h : x ∈ e.target) : e (e.symm x) = x :=
  e.right_inv' h
#align local_homeomorph.right_inv LocalHomeomorph.right_inv

theorem eq_symm_apply {x : α} {y : β} (hx : x ∈ e.source) (hy : y ∈ e.target) :
    x = e.symm y ↔ e x = y :=
  e.toLocalEquiv.eq_symm_apply hx hy
#align local_homeomorph.eq_symm_apply LocalHomeomorph.eq_symm_apply

protected theorem mapsTo : MapsTo e e.source e.target := fun _ => e.map_source
#align local_homeomorph.maps_to LocalHomeomorph.mapsTo

protected theorem symm_mapsTo : MapsTo e.symm e.target e.source :=
  e.symm.mapsTo
#align local_homeomorph.symm_maps_to LocalHomeomorph.symm_mapsTo

protected theorem leftInvOn : LeftInvOn e.symm e e.source := fun _ => e.left_inv
#align local_homeomorph.left_inv_on LocalHomeomorph.leftInvOn

protected theorem rightInvOn : RightInvOn e.symm e e.target := fun _ => e.right_inv
#align local_homeomorph.right_inv_on LocalHomeomorph.rightInvOn

protected theorem invOn : InvOn e.symm e e.source e.target :=
  ⟨e.leftInvOn, e.rightInvOn⟩
#align local_homeomorph.inv_on LocalHomeomorph.invOn

protected theorem injOn : InjOn e e.source :=
  e.leftInvOn.injOn
#align local_homeomorph.inj_on LocalHomeomorph.injOn

protected theorem bijOn : BijOn e e.source e.target :=
  e.invOn.bijOn e.mapsTo e.symm_mapsTo
#align local_homeomorph.bij_on LocalHomeomorph.bijOn

protected theorem surjOn : SurjOn e e.source e.target :=
  e.bijOn.surjOn
#align local_homeomorph.surj_on LocalHomeomorph.surjOn

/-- Interpret a `Homeomorph` as a `LocalHomeomorph` by restricting it
to an open set `s` in the domain and to `t` in the codomain. -/
@[simps! (config := .asFn) apply symm_apply toLocalEquiv,
  simps! (config := .lemmasOnly) source target]
def _root_.Homeomorph.toLocalHomeomorphOfImageEq (e : α ≃ₜ β) (s : Set α) (hs : IsOpen s)
    (t : Set β) (h : e '' s = t) : LocalHomeomorph α β where
  toLocalEquiv := e.toLocalEquivOfImageEq s t h
  open_source := hs
  open_target := by simpa [← h]
  continuous_toFun := e.continuous.continuousOn
  continuous_invFun := e.symm.continuous.continuousOn

/-- A homeomorphism induces a local homeomorphism on the whole space -/
@[simps! (config := mfld_cfg)]
def _root_.Homeomorph.toLocalHomeomorph (e : α ≃ₜ β) : LocalHomeomorph α β :=
  e.toLocalHomeomorphOfImageEq univ isOpen_univ univ <| by rw [image_univ, e.surjective.range_eq]
#align homeomorph.to_local_homeomorph Homeomorph.toLocalHomeomorph

/-- Replace `toLocalEquiv` field to provide better definitional equalities. -/
def replaceEquiv (e : LocalHomeomorph α β) (e' : LocalEquiv α β) (h : e.toLocalEquiv = e') :
    LocalHomeomorph α β where
  toLocalEquiv := e'
  open_source := h ▸ e.open_source
  open_target := h ▸ e.open_target
  continuous_toFun := h ▸ e.continuous_toFun
  continuous_invFun := h ▸ e.continuous_invFun
#align local_homeomorph.replace_equiv LocalHomeomorph.replaceEquiv

theorem replaceEquiv_eq_self (e : LocalHomeomorph α β) (e' : LocalEquiv α β)
    (h : e.toLocalEquiv = e') : e.replaceEquiv e' h = e := by
  cases e
  subst e'
  rfl
#align local_homeomorph.replace_equiv_eq_self LocalHomeomorph.replaceEquiv_eq_self

theorem source_preimage_target : e.source ⊆ e ⁻¹' e.target :=
  e.mapsTo
#align local_homeomorph.source_preimage_target LocalHomeomorph.source_preimage_target

@[deprecated toLocalEquiv_injective]
theorem eq_of_localEquiv_eq {e e' : LocalHomeomorph α β} (h : e.toLocalEquiv = e'.toLocalEquiv) :
    e = e' := toLocalEquiv_injective h
#align local_homeomorph.eq_of_local_equiv_eq LocalHomeomorph.eq_of_localEquiv_eq

theorem eventually_left_inverse (e : LocalHomeomorph α β) {x} (hx : x ∈ e.source) :
    ∀ᶠ y in 𝓝 x, e.symm (e y) = y :=
  (e.open_source.eventually_mem hx).mono e.left_inv'
#align local_homeomorph.eventually_left_inverse LocalHomeomorph.eventually_left_inverse

theorem eventually_left_inverse' (e : LocalHomeomorph α β) {x} (hx : x ∈ e.target) :
    ∀ᶠ y in 𝓝 (e.symm x), e.symm (e y) = y :=
  e.eventually_left_inverse (e.map_target hx)
#align local_homeomorph.eventually_left_inverse' LocalHomeomorph.eventually_left_inverse'

theorem eventually_right_inverse (e : LocalHomeomorph α β) {x} (hx : x ∈ e.target) :
    ∀ᶠ y in 𝓝 x, e (e.symm y) = y :=
  (e.open_target.eventually_mem hx).mono e.right_inv'
#align local_homeomorph.eventually_right_inverse LocalHomeomorph.eventually_right_inverse

theorem eventually_right_inverse' (e : LocalHomeomorph α β) {x} (hx : x ∈ e.source) :
    ∀ᶠ y in 𝓝 (e x), e (e.symm y) = y :=
  e.eventually_right_inverse (e.map_source hx)
#align local_homeomorph.eventually_right_inverse' LocalHomeomorph.eventually_right_inverse'

theorem eventually_ne_nhdsWithin (e : LocalHomeomorph α β) {x} (hx : x ∈ e.source) :
    ∀ᶠ x' in 𝓝[≠] x, e x' ≠ e x :=
  eventually_nhdsWithin_iff.2 <|
    (e.eventually_left_inverse hx).mono fun x' hx' =>
      mt fun h => by rw [mem_singleton_iff, ← e.left_inv hx, ← h, hx']
#align local_homeomorph.eventually_ne_nhds_within LocalHomeomorph.eventually_ne_nhdsWithin

theorem nhdsWithin_source_inter {x} (hx : x ∈ e.source) (s : Set α) : 𝓝[e.source ∩ s] x = 𝓝[s] x :=
  nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds <| IsOpen.mem_nhds e.open_source hx)
#align local_homeomorph.nhds_within_source_inter LocalHomeomorph.nhdsWithin_source_inter

theorem nhdsWithin_target_inter {x} (hx : x ∈ e.target) (s : Set β) : 𝓝[e.target ∩ s] x = 𝓝[s] x :=
  e.symm.nhdsWithin_source_inter hx s
#align local_homeomorph.nhds_within_target_inter LocalHomeomorph.nhdsWithin_target_inter

theorem image_eq_target_inter_inv_preimage {s : Set α} (h : s ⊆ e.source) :
    e '' s = e.target ∩ e.symm ⁻¹' s :=
  e.toLocalEquiv.image_eq_target_inter_inv_preimage h
#align local_homeomorph.image_eq_target_inter_inv_preimage LocalHomeomorph.image_eq_target_inter_inv_preimage

theorem image_source_inter_eq' (s : Set α) : e '' (e.source ∩ s) = e.target ∩ e.symm ⁻¹' s :=
  e.toLocalEquiv.image_source_inter_eq' s
#align local_homeomorph.image_source_inter_eq' LocalHomeomorph.image_source_inter_eq'

theorem image_source_inter_eq (s : Set α) :
    e '' (e.source ∩ s) = e.target ∩ e.symm ⁻¹' (e.source ∩ s) :=
  e.toLocalEquiv.image_source_inter_eq s
#align local_homeomorph.image_source_inter_eq LocalHomeomorph.image_source_inter_eq

theorem symm_image_eq_source_inter_preimage {s : Set β} (h : s ⊆ e.target) :
    e.symm '' s = e.source ∩ e ⁻¹' s :=
  e.symm.image_eq_target_inter_inv_preimage h
#align local_homeomorph.symm_image_eq_source_inter_preimage LocalHomeomorph.symm_image_eq_source_inter_preimage

theorem symm_image_target_inter_eq (s : Set β) :
    e.symm '' (e.target ∩ s) = e.source ∩ e ⁻¹' (e.target ∩ s) :=
  e.symm.image_source_inter_eq _
#align local_homeomorph.symm_image_target_inter_eq LocalHomeomorph.symm_image_target_inter_eq

theorem source_inter_preimage_inv_preimage (s : Set α) :
    e.source ∩ e ⁻¹' (e.symm ⁻¹' s) = e.source ∩ s :=
  e.toLocalEquiv.source_inter_preimage_inv_preimage s
#align local_homeomorph.source_inter_preimage_inv_preimage LocalHomeomorph.source_inter_preimage_inv_preimage

theorem target_inter_inv_preimage_preimage (s : Set β) :
    e.target ∩ e.symm ⁻¹' (e ⁻¹' s) = e.target ∩ s :=
  e.symm.source_inter_preimage_inv_preimage _
#align local_homeomorph.target_inter_inv_preimage_preimage LocalHomeomorph.target_inter_inv_preimage_preimage

theorem source_inter_preimage_target_inter (s : Set β) :
    e.source ∩ e ⁻¹' (e.target ∩ s) = e.source ∩ e ⁻¹' s :=
  e.toLocalEquiv.source_inter_preimage_target_inter s
#align local_homeomorph.source_inter_preimage_target_inter LocalHomeomorph.source_inter_preimage_target_inter

theorem image_source_eq_target (e : LocalHomeomorph α β) : e '' e.source = e.target :=
  e.toLocalEquiv.image_source_eq_target
#align local_homeomorph.image_source_eq_target LocalHomeomorph.image_source_eq_target

theorem symm_image_target_eq_source (e : LocalHomeomorph α β) : e.symm '' e.target = e.source :=
  e.symm.image_source_eq_target
#align local_homeomorph.symm_image_target_eq_source LocalHomeomorph.symm_image_target_eq_source

/-- Two local homeomorphisms are equal when they have equal `toFun`, `invFun` and `source`.
It is not sufficient to have equal `toFun` and `source`, as this only determines `invFun` on
the target. This would only be true for a weaker notion of equality, arguably the right one,
called `EqOnSource`. -/
@[ext]
protected theorem ext (e' : LocalHomeomorph α β) (h : ∀ x, e x = e' x)
    (hinv : ∀ x, e.symm x = e'.symm x) (hs : e.source = e'.source) : e = e' :=
  toLocalEquiv_injective (LocalEquiv.ext h hinv hs)
#align local_homeomorph.ext LocalHomeomorph.ext

protected theorem ext_iff {e e' : LocalHomeomorph α β} :
    e = e' ↔ (∀ x, e x = e' x) ∧ (∀ x, e.symm x = e'.symm x) ∧ e.source = e'.source :=
  ⟨by
    rintro rfl
    exact ⟨fun x => rfl, fun x => rfl, rfl⟩, fun h => e.ext e' h.1 h.2.1 h.2.2⟩
#align local_homeomorph.ext_iff LocalHomeomorph.ext_iff

@[simp, mfld_simps]
theorem symm_toLocalEquiv : e.symm.toLocalEquiv = e.toLocalEquiv.symm :=
  rfl
#align local_homeomorph.symm_to_local_equiv LocalHomeomorph.symm_toLocalEquiv

-- The following lemmas are already simp via `LocalEquiv`
theorem symm_source : e.symm.source = e.target :=
  rfl
#align local_homeomorph.symm_source LocalHomeomorph.symm_source

theorem symm_target : e.symm.target = e.source :=
  rfl
#align local_homeomorph.symm_target LocalHomeomorph.symm_target

@[simp, mfld_simps] theorem symm_symm : e.symm.symm = e := rfl
#align local_homeomorph.symm_symm LocalHomeomorph.symm_symm

/-- A local homeomorphism is continuous at any point of its source -/
protected theorem continuousAt {x : α} (h : x ∈ e.source) : ContinuousAt e x :=
  (e.continuousOn x h).continuousAt (e.open_source.mem_nhds h)
#align local_homeomorph.continuous_at LocalHomeomorph.continuousAt

/-- A local homeomorphism inverse is continuous at any point of its target -/
theorem continuousAt_symm {x : β} (h : x ∈ e.target) : ContinuousAt e.symm x :=
  e.symm.continuousAt h
#align local_homeomorph.continuous_at_symm LocalHomeomorph.continuousAt_symm

theorem tendsto_symm {x} (hx : x ∈ e.source) : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
  simpa only [ContinuousAt, e.left_inv hx] using e.continuousAt_symm (e.map_source hx)
#align local_homeomorph.tendsto_symm LocalHomeomorph.tendsto_symm

theorem map_nhds_eq {x} (hx : x ∈ e.source) : map e (𝓝 x) = 𝓝 (e x) :=
  le_antisymm (e.continuousAt hx) <|
    le_map_of_right_inverse (e.eventually_right_inverse' hx) (e.tendsto_symm hx)
#align local_homeomorph.map_nhds_eq LocalHomeomorph.map_nhds_eq

theorem symm_map_nhds_eq {x} (hx : x ∈ e.source) : map e.symm (𝓝 (e x)) = 𝓝 x :=
  (e.symm.map_nhds_eq <| e.map_source hx).trans <| by rw [e.left_inv hx]
#align local_homeomorph.symm_map_nhds_eq LocalHomeomorph.symm_map_nhds_eq

theorem image_mem_nhds {x} (hx : x ∈ e.source) {s : Set α} (hs : s ∈ 𝓝 x) : e '' s ∈ 𝓝 (e x) :=
  e.map_nhds_eq hx ▸ Filter.image_mem_map hs
#align local_homeomorph.image_mem_nhds LocalHomeomorph.image_mem_nhds

theorem map_nhdsWithin_eq (e : LocalHomeomorph α β) {x} (hx : x ∈ e.source) (s : Set α) :
    map e (𝓝[s] x) = 𝓝[e '' (e.source ∩ s)] e x :=
  calc
    map e (𝓝[s] x) = map e (𝓝[e.source ∩ s] x) :=
      congr_arg (map e) (e.nhdsWithin_source_inter hx _).symm
    _ = 𝓝[e '' (e.source ∩ s)] e x :=
      (e.leftInvOn.mono <| inter_subset_left _ _).map_nhdsWithin_eq (e.left_inv hx)
        (e.continuousAt_symm (e.map_source hx)).continuousWithinAt
        (e.continuousAt hx).continuousWithinAt
#align local_homeomorph.map_nhds_within_eq LocalHomeomorph.map_nhdsWithin_eq

theorem map_nhdsWithin_preimage_eq (e : LocalHomeomorph α β) {x} (hx : x ∈ e.source) (s : Set β) :
    map e (𝓝[e ⁻¹' s] x) = 𝓝[s] e x := by
  rw [e.map_nhdsWithin_eq hx, e.image_source_inter_eq', e.target_inter_inv_preimage_preimage,
    e.nhdsWithin_target_inter (e.map_source hx)]
#align local_homeomorph.map_nhds_within_preimage_eq LocalHomeomorph.map_nhdsWithin_preimage_eq

theorem eventually_nhds (e : LocalHomeomorph α β) {x : α} (p : β → Prop) (hx : x ∈ e.source) :
    (∀ᶠ y in 𝓝 (e x), p y) ↔ ∀ᶠ x in 𝓝 x, p (e x) :=
  Iff.trans (by rw [e.map_nhds_eq hx]) eventually_map
#align local_homeomorph.eventually_nhds LocalHomeomorph.eventually_nhds

theorem eventually_nhds' (e : LocalHomeomorph α β) {x : α} (p : α → Prop) (hx : x ∈ e.source) :
    (∀ᶠ y in 𝓝 (e x), p (e.symm y)) ↔ ∀ᶠ x in 𝓝 x, p x := by
  rw [e.eventually_nhds _ hx]
  refine' eventually_congr ((e.eventually_left_inverse hx).mono fun y hy => _)
  rw [hy]
#align local_homeomorph.eventually_nhds' LocalHomeomorph.eventually_nhds'

theorem eventually_nhdsWithin (e : LocalHomeomorph α β) {x : α} (p : β → Prop) {s : Set α}
    (hx : x ∈ e.source) : (∀ᶠ y in 𝓝[e.symm ⁻¹' s] e x, p y) ↔ ∀ᶠ x in 𝓝[s] x, p (e x) := by
  refine' Iff.trans _ eventually_map
  rw [e.map_nhdsWithin_eq hx, e.image_source_inter_eq', e.nhdsWithin_target_inter (e.mapsTo hx)]
#align local_homeomorph.eventually_nhds_within LocalHomeomorph.eventually_nhdsWithin

theorem eventually_nhdsWithin' (e : LocalHomeomorph α β) {x : α} (p : α → Prop) {s : Set α}
    (hx : x ∈ e.source) : (∀ᶠ y in 𝓝[e.symm ⁻¹' s] e x, p (e.symm y)) ↔ ∀ᶠ x in 𝓝[s] x, p x := by
  rw [e.eventually_nhdsWithin _ hx]
  refine eventually_congr <|
    (eventually_nhdsWithin_of_eventually_nhds <| e.eventually_left_inverse hx).mono fun y hy => ?_
  rw [hy]
#align local_homeomorph.eventually_nhds_within' LocalHomeomorph.eventually_nhdsWithin'

/-- This lemma is useful in the manifold library in the case that `e` is a chart. It states that
  locally around `e x` the set `e.symm ⁻¹' s` is the same as the set intersected with the target
  of `e` and some other neighborhood of `f x` (which will be the source of a chart on `γ`).  -/
theorem preimage_eventuallyEq_target_inter_preimage_inter {e : LocalHomeomorph α β} {s : Set α}
    {t : Set γ} {x : α} {f : α → γ} (hf : ContinuousWithinAt f s x) (hxe : x ∈ e.source)
    (ht : t ∈ 𝓝 (f x)) :
    e.symm ⁻¹' s =ᶠ[𝓝 (e x)] (e.target ∩ e.symm ⁻¹' (s ∩ f ⁻¹' t) : Set β) := by
  rw [eventuallyEq_set, e.eventually_nhds _ hxe]
  filter_upwards [e.open_source.mem_nhds hxe,
    mem_nhdsWithin_iff_eventually.mp (hf.preimage_mem_nhdsWithin ht)]
  intro y hy hyu
  simp_rw [mem_inter_iff, mem_preimage, mem_inter_iff, e.mapsTo hy, true_and_iff, iff_self_and,
    e.left_inv hy, iff_true_intro hyu]
#align local_homeomorph.preimage_eventually_eq_target_inter_preimage_inter LocalHomeomorph.preimage_eventuallyEq_target_inter_preimage_inter

theorem preimage_open_of_open {s : Set β} (hs : IsOpen s) : IsOpen (e.source ∩ e ⁻¹' s) :=
  e.continuousOn.preimage_open_of_open e.open_source hs
#align local_homeomorph.preimage_open_of_open LocalHomeomorph.preimage_open_of_open

/-- A local homeomorphism is an open map on its source. -/
lemma isOpenMapOn_source {s : Set α} (hs : IsOpen s) (hse : s ⊆ e.source) : IsOpen (e '' s) := by
  rw [(image_eq_target_inter_inv_preimage (e := e) hse)]
  exact e.continuous_invFun.preimage_open_of_open e.open_target hs

/-- The inverse of a local homeomorphism `e` is an open map on `e.target`. -/
lemma isOpenMapOn_target_symm {t : Set β} (ht : IsOpen t) (hte : t ⊆ e.target) :
    IsOpen (e.invFun '' t) := by
  have r : e.invFun '' t = e.source ∩ ↑e ⁻¹' t := symm_image_eq_source_inter_preimage (e := e) hte
  exact r ▸ e.continuous_toFun.preimage_open_of_open e.open_source ht

/-!
### `LocalHomeomorph.IsImage` relation

We say that `t : Set β` is an image of `s : Set α` under a local homeomorphism `e` if any of the
following equivalent conditions hold:

* `e '' (e.source ∩ s) = e.target ∩ t`;
* `e.source ∩ e ⁻¹ t = e.source ∩ s`;
* `∀ x ∈ e.source, e x ∈ t ↔ x ∈ s` (this one is used in the definition).

This definition is a restatement of `LocalEquiv.IsImage` for local homeomorphisms. In this section
we transfer API about `LocalEquiv.IsImage` to local homeomorphisms and add a few
`LocalHomeomorph`-specific lemmas like `LocalHomeomorph.IsImage.closure`.
-/

/-- We say that `t : Set β` is an image of `s : Set α` under a local homeomorphism `e` if any of the
following equivalent conditions hold:

* `e '' (e.source ∩ s) = e.target ∩ t`;
* `e.source ∩ e ⁻¹ t = e.source ∩ s`;
* `∀ x ∈ e.source, e x ∈ t ↔ x ∈ s` (this one is used in the definition).
-/
def IsImage (s : Set α) (t : Set β) : Prop :=
  ∀ ⦃x⦄, x ∈ e.source → (e x ∈ t ↔ x ∈ s)
#align local_homeomorph.is_image LocalHomeomorph.IsImage

namespace IsImage

variable {e} {s : Set α} {t : Set β} {x : α} {y : β}

theorem toLocalEquiv (h : e.IsImage s t) : e.toLocalEquiv.IsImage s t :=
  h
#align local_homeomorph.is_image.to_local_equiv LocalHomeomorph.IsImage.toLocalEquiv

theorem apply_mem_iff (h : e.IsImage s t) (hx : x ∈ e.source) : e x ∈ t ↔ x ∈ s :=
  h hx
#align local_homeomorph.is_image.apply_mem_iff LocalHomeomorph.IsImage.apply_mem_iff

protected theorem symm (h : e.IsImage s t) : e.symm.IsImage t s :=
  h.toLocalEquiv.symm
#align local_homeomorph.is_image.symm LocalHomeomorph.IsImage.symm

theorem symm_apply_mem_iff (h : e.IsImage s t) (hy : y ∈ e.target) : e.symm y ∈ s ↔ y ∈ t :=
  h.symm hy
#align local_homeomorph.is_image.symm_apply_mem_iff LocalHomeomorph.IsImage.symm_apply_mem_iff

@[simp]
theorem symm_iff : e.symm.IsImage t s ↔ e.IsImage s t :=
  ⟨fun h => h.symm, fun h => h.symm⟩
#align local_homeomorph.is_image.symm_iff LocalHomeomorph.IsImage.symm_iff

protected theorem mapsTo (h : e.IsImage s t) : MapsTo e (e.source ∩ s) (e.target ∩ t) :=
  h.toLocalEquiv.mapsTo
#align local_homeomorph.is_image.maps_to LocalHomeomorph.IsImage.mapsTo

theorem symm_mapsTo (h : e.IsImage s t) : MapsTo e.symm (e.target ∩ t) (e.source ∩ s) :=
  h.symm.mapsTo
#align local_homeomorph.is_image.symm_maps_to LocalHomeomorph.IsImage.symm_mapsTo

theorem image_eq (h : e.IsImage s t) : e '' (e.source ∩ s) = e.target ∩ t :=
  h.toLocalEquiv.image_eq
#align local_homeomorph.is_image.image_eq LocalHomeomorph.IsImage.image_eq

theorem symm_image_eq (h : e.IsImage s t) : e.symm '' (e.target ∩ t) = e.source ∩ s :=
  h.symm.image_eq
#align local_homeomorph.is_image.symm_image_eq LocalHomeomorph.IsImage.symm_image_eq

theorem iff_preimage_eq : e.IsImage s t ↔ e.source ∩ e ⁻¹' t = e.source ∩ s :=
  LocalEquiv.IsImage.iff_preimage_eq
#align local_homeomorph.is_image.iff_preimage_eq LocalHomeomorph.IsImage.iff_preimage_eq

alias ⟨preimage_eq, of_preimage_eq⟩ := iff_preimage_eq
#align local_homeomorph.is_image.preimage_eq LocalHomeomorph.IsImage.preimage_eq
#align local_homeomorph.is_image.of_preimage_eq LocalHomeomorph.IsImage.of_preimage_eq

theorem iff_symm_preimage_eq : e.IsImage s t ↔ e.target ∩ e.symm ⁻¹' s = e.target ∩ t :=
  symm_iff.symm.trans iff_preimage_eq
#align local_homeomorph.is_image.iff_symm_preimage_eq LocalHomeomorph.IsImage.iff_symm_preimage_eq

alias ⟨symm_preimage_eq, of_symm_preimage_eq⟩ := iff_symm_preimage_eq
#align local_homeomorph.is_image.symm_preimage_eq LocalHomeomorph.IsImage.symm_preimage_eq
#align local_homeomorph.is_image.of_symm_preimage_eq LocalHomeomorph.IsImage.of_symm_preimage_eq

theorem iff_symm_preimage_eq' :
    e.IsImage s t ↔ e.target ∩ e.symm ⁻¹' (e.source ∩ s) = e.target ∩ t := by
  rw [iff_symm_preimage_eq, ← image_source_inter_eq, ← image_source_inter_eq']
#align local_homeomorph.is_image.iff_symm_preimage_eq' LocalHomeomorph.IsImage.iff_symm_preimage_eq'

alias ⟨symm_preimage_eq', of_symm_preimage_eq'⟩ := iff_symm_preimage_eq'
#align local_homeomorph.is_image.symm_preimage_eq' LocalHomeomorph.IsImage.symm_preimage_eq'
#align local_homeomorph.is_image.of_symm_preimage_eq' LocalHomeomorph.IsImage.of_symm_preimage_eq'

theorem iff_preimage_eq' : e.IsImage s t ↔ e.source ∩ e ⁻¹' (e.target ∩ t) = e.source ∩ s :=
  symm_iff.symm.trans iff_symm_preimage_eq'
#align local_homeomorph.is_image.iff_preimage_eq' LocalHomeomorph.IsImage.iff_preimage_eq'

alias ⟨preimage_eq', of_preimage_eq'⟩ := iff_preimage_eq'
#align local_homeomorph.is_image.preimage_eq' LocalHomeomorph.IsImage.preimage_eq'
#align local_homeomorph.is_image.of_preimage_eq' LocalHomeomorph.IsImage.of_preimage_eq'

theorem of_image_eq (h : e '' (e.source ∩ s) = e.target ∩ t) : e.IsImage s t :=
  LocalEquiv.IsImage.of_image_eq h
#align local_homeomorph.is_image.of_image_eq LocalHomeomorph.IsImage.of_image_eq

theorem of_symm_image_eq (h : e.symm '' (e.target ∩ t) = e.source ∩ s) : e.IsImage s t :=
  LocalEquiv.IsImage.of_symm_image_eq h
#align local_homeomorph.is_image.of_symm_image_eq LocalHomeomorph.IsImage.of_symm_image_eq

protected theorem compl (h : e.IsImage s t) : e.IsImage sᶜ tᶜ := fun _ hx => (h hx).not
#align local_homeomorph.is_image.compl LocalHomeomorph.IsImage.compl

protected theorem inter {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s ∩ s') (t ∩ t') := fun _ hx => (h hx).and (h' hx)
#align local_homeomorph.is_image.inter LocalHomeomorph.IsImage.inter

protected theorem union {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s ∪ s') (t ∪ t') := fun _ hx => (h hx).or (h' hx)
#align local_homeomorph.is_image.union LocalHomeomorph.IsImage.union

protected theorem diff {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s \ s') (t \ t') :=
  h.inter h'.compl
#align local_homeomorph.is_image.diff LocalHomeomorph.IsImage.diff

theorem leftInvOn_piecewise {e' : LocalHomeomorph α β} [∀ i, Decidable (i ∈ s)]
    [∀ i, Decidable (i ∈ t)] (h : e.IsImage s t) (h' : e'.IsImage s t) :
    LeftInvOn (t.piecewise e.symm e'.symm) (s.piecewise e e') (s.ite e.source e'.source) :=
  h.toLocalEquiv.leftInvOn_piecewise h'
#align local_homeomorph.is_image.left_inv_on_piecewise LocalHomeomorph.IsImage.leftInvOn_piecewise

theorem inter_eq_of_inter_eq_of_eqOn {e' : LocalHomeomorph α β} (h : e.IsImage s t)
    (h' : e'.IsImage s t) (hs : e.source ∩ s = e'.source ∩ s) (Heq : EqOn e e' (e.source ∩ s)) :
    e.target ∩ t = e'.target ∩ t :=
  h.toLocalEquiv.inter_eq_of_inter_eq_of_eqOn h' hs Heq
#align local_homeomorph.is_image.inter_eq_of_inter_eq_of_eq_on LocalHomeomorph.IsImage.inter_eq_of_inter_eq_of_eqOn

theorem symm_eqOn_of_inter_eq_of_eqOn {e' : LocalHomeomorph α β} (h : e.IsImage s t)
    (hs : e.source ∩ s = e'.source ∩ s) (Heq : EqOn e e' (e.source ∩ s)) :
    EqOn e.symm e'.symm (e.target ∩ t) :=
  h.toLocalEquiv.symm_eq_on_of_inter_eq_of_eqOn hs Heq
#align local_homeomorph.is_image.symm_eq_on_of_inter_eq_of_eq_on LocalHomeomorph.IsImage.symm_eqOn_of_inter_eq_of_eqOn

theorem map_nhdsWithin_eq (h : e.IsImage s t) (hx : x ∈ e.source) : map e (𝓝[s] x) = 𝓝[t] e x := by
  rw [e.map_nhdsWithin_eq hx, h.image_eq, e.nhdsWithin_target_inter (e.map_source hx)]
#align local_homeomorph.is_image.map_nhds_within_eq LocalHomeomorph.IsImage.map_nhdsWithin_eq

protected theorem closure (h : e.IsImage s t) : e.IsImage (closure s) (closure t) := fun x hx => by
  simp only [mem_closure_iff_nhdsWithin_neBot, ← h.map_nhdsWithin_eq hx, map_neBot_iff]
#align local_homeomorph.is_image.closure LocalHomeomorph.IsImage.closure

protected theorem interior (h : e.IsImage s t) : e.IsImage (interior s) (interior t) := by
  simpa only [closure_compl, compl_compl] using h.compl.closure.compl
#align local_homeomorph.is_image.interior LocalHomeomorph.IsImage.interior

protected theorem frontier (h : e.IsImage s t) : e.IsImage (frontier s) (frontier t) :=
  h.closure.diff h.interior
#align local_homeomorph.is_image.frontier LocalHomeomorph.IsImage.frontier

theorem isOpen_iff (h : e.IsImage s t) : IsOpen (e.source ∩ s) ↔ IsOpen (e.target ∩ t) :=
  ⟨fun hs => h.symm_preimage_eq' ▸ e.symm.preimage_open_of_open hs, fun hs =>
    h.preimage_eq' ▸ e.preimage_open_of_open hs⟩
#align local_homeomorph.is_image.is_open_iff LocalHomeomorph.IsImage.isOpen_iff

/-- Restrict a `LocalHomeomorph` to a pair of corresponding open sets. -/
@[simps toLocalEquiv]
def restr (h : e.IsImage s t) (hs : IsOpen (e.source ∩ s)) : LocalHomeomorph α β where
  toLocalEquiv := h.toLocalEquiv.restr
  open_source := hs
  open_target := h.isOpen_iff.1 hs
  continuous_toFun := e.continuousOn.mono (inter_subset_left _ _)
  continuous_invFun := e.symm.continuousOn.mono (inter_subset_left _ _)
#align local_homeomorph.is_image.restr LocalHomeomorph.IsImage.restr

end IsImage

theorem isImage_source_target : e.IsImage e.source e.target :=
  e.toLocalEquiv.isImage_source_target
#align local_homeomorph.is_image_source_target LocalHomeomorph.isImage_source_target

theorem isImage_source_target_of_disjoint (e' : LocalHomeomorph α β)
    (hs : Disjoint e.source e'.source) (ht : Disjoint e.target e'.target) :
    e.IsImage e'.source e'.target :=
  e.toLocalEquiv.isImage_source_target_of_disjoint e'.toLocalEquiv hs ht
#align local_homeomorph.is_image_source_target_of_disjoint LocalHomeomorph.isImage_source_target_of_disjoint

/-- Preimage of interior or interior of preimage coincide for local homeomorphisms, when restricted
to the source. -/
theorem preimage_interior (s : Set β) :
    e.source ∩ e ⁻¹' interior s = e.source ∩ interior (e ⁻¹' s) :=
  (IsImage.of_preimage_eq rfl).interior.preimage_eq
#align local_homeomorph.preimage_interior LocalHomeomorph.preimage_interior

theorem preimage_closure (s : Set β) : e.source ∩ e ⁻¹' closure s = e.source ∩ closure (e ⁻¹' s) :=
  (IsImage.of_preimage_eq rfl).closure.preimage_eq
#align local_homeomorph.preimage_closure LocalHomeomorph.preimage_closure

theorem preimage_frontier (s : Set β) :
    e.source ∩ e ⁻¹' frontier s = e.source ∩ frontier (e ⁻¹' s) :=
  (IsImage.of_preimage_eq rfl).frontier.preimage_eq
#align local_homeomorph.preimage_frontier LocalHomeomorph.preimage_frontier

theorem preimage_open_of_open_symm {s : Set α} (hs : IsOpen s) : IsOpen (e.target ∩ e.symm ⁻¹' s) :=
  e.symm.continuousOn.preimage_open_of_open e.open_target hs
#align local_homeomorph.preimage_open_of_open_symm LocalHomeomorph.preimage_open_of_open_symm

/-- The image of an open set in the source is open. -/
theorem image_open_of_open {s : Set α} (hs : IsOpen s) (h : s ⊆ e.source) : IsOpen (e '' s) := by
  have : e '' s = e.target ∩ e.symm ⁻¹' s := e.toLocalEquiv.image_eq_target_inter_inv_preimage h
  rw [this]
  exact e.continuousOn_symm.preimage_open_of_open e.open_target hs
#align local_homeomorph.image_open_of_open LocalHomeomorph.image_open_of_open

/-- The image of the restriction of an open set to the source is open. -/
theorem image_open_of_open' {s : Set α} (hs : IsOpen s) : IsOpen (e '' (e.source ∩ s)) :=
  image_open_of_open _ (IsOpen.inter e.open_source hs) (inter_subset_left _ _)
#align local_homeomorph.image_open_of_open' LocalHomeomorph.image_open_of_open'

/-- A `LocalEquiv` with continuous open forward map and an open source is a `LocalHomeomorph`. -/
def ofContinuousOpenRestrict (e : LocalEquiv α β) (hc : ContinuousOn e e.source)
    (ho : IsOpenMap (e.source.restrict e)) (hs : IsOpen e.source) : LocalHomeomorph α β where
  toLocalEquiv := e
  open_source := hs
  open_target := by simpa only [range_restrict, e.image_source_eq_target] using ho.isOpen_range
  continuous_toFun := hc
  continuous_invFun := e.image_source_eq_target ▸ ho.continuousOn_image_of_leftInvOn e.leftInvOn
#align local_homeomorph.of_continuous_open_restrict LocalHomeomorph.ofContinuousOpenRestrict

/-- A `LocalEquiv` with continuous open forward map and an open source is a `LocalHomeomorph`. -/
def ofContinuousOpen (e : LocalEquiv α β) (hc : ContinuousOn e e.source) (ho : IsOpenMap e)
    (hs : IsOpen e.source) : LocalHomeomorph α β :=
  ofContinuousOpenRestrict e hc (ho.restrict hs) hs
#align local_homeomorph.of_continuous_open LocalHomeomorph.ofContinuousOpen

/-- Restricting a local homeomorphism `e` to `e.source ∩ s` when `s` is open. This is sometimes hard
to use because of the openness assumption, but it has the advantage that when it can
be used then its local_equiv is defeq to local_equiv.restr -/
protected def restrOpen (s : Set α) (hs : IsOpen s) : LocalHomeomorph α β :=
  (@IsImage.of_symm_preimage_eq α β _ _ e s (e.symm ⁻¹' s) rfl).restr
    (IsOpen.inter e.open_source hs)
#align local_homeomorph.restr_open LocalHomeomorph.restrOpen

@[simp, mfld_simps]
theorem restrOpen_toLocalEquiv (s : Set α) (hs : IsOpen s) :
    (e.restrOpen s hs).toLocalEquiv = e.toLocalEquiv.restr s :=
  rfl
#align local_homeomorph.restr_open_to_local_equiv LocalHomeomorph.restrOpen_toLocalEquiv

-- Already simp via `LocalEquiv`
theorem restrOpen_source (s : Set α) (hs : IsOpen s) : (e.restrOpen s hs).source = e.source ∩ s :=
  rfl
#align local_homeomorph.restr_open_source LocalHomeomorph.restrOpen_source

/-- Restricting a local homeomorphism `e` to `e.source ∩ interior s`. We use the interior to make
sure that the restriction is well defined whatever the set s, since local homeomorphisms are by
definition defined on open sets. In applications where `s` is open, this coincides with the
restriction of local equivalences -/
@[simps! (config := mfld_cfg) apply symm_apply, simps! (config := .lemmasOnly) source target]
protected def restr (s : Set α) : LocalHomeomorph α β :=
  e.restrOpen (interior s) isOpen_interior
#align local_homeomorph.restr LocalHomeomorph.restr

@[simp, mfld_simps]
theorem restr_toLocalEquiv (s : Set α) :
    (e.restr s).toLocalEquiv = e.toLocalEquiv.restr (interior s) :=
  rfl
#align local_homeomorph.restr_to_local_equiv LocalHomeomorph.restr_toLocalEquiv

theorem restr_source' (s : Set α) (hs : IsOpen s) : (e.restr s).source = e.source ∩ s := by
  rw [e.restr_source, hs.interior_eq]
#align local_homeomorph.restr_source' LocalHomeomorph.restr_source'

theorem restr_toLocalEquiv' (s : Set α) (hs : IsOpen s) :
    (e.restr s).toLocalEquiv = e.toLocalEquiv.restr s := by
  rw [e.restr_toLocalEquiv, hs.interior_eq]
#align local_homeomorph.restr_to_local_equiv' LocalHomeomorph.restr_toLocalEquiv'

theorem restr_eq_of_source_subset {e : LocalHomeomorph α β} {s : Set α} (h : e.source ⊆ s) :
    e.restr s = e :=
  toLocalEquiv_injective <| LocalEquiv.restr_eq_of_source_subset <| interior_maximal h e.open_source
#align local_homeomorph.restr_eq_of_source_subset LocalHomeomorph.restr_eq_of_source_subset

@[simp, mfld_simps]
theorem restr_univ {e : LocalHomeomorph α β} : e.restr univ = e :=
  restr_eq_of_source_subset (subset_univ _)
#align local_homeomorph.restr_univ LocalHomeomorph.restr_univ

theorem restr_source_inter (s : Set α) : e.restr (e.source ∩ s) = e.restr s := by
  refine' LocalHomeomorph.ext _ _ (fun x => rfl) (fun x => rfl) _
  simp [e.open_source.interior_eq, ← inter_assoc]
#align local_homeomorph.restr_source_inter LocalHomeomorph.restr_source_inter

/-- The identity on the whole space as a local homeomorphism. -/
@[simps! (config := mfld_cfg) apply, simps! (config := .lemmasOnly) source target]
protected def refl (α : Type*) [TopologicalSpace α] : LocalHomeomorph α α :=
  (Homeomorph.refl α).toLocalHomeomorph
#align local_homeomorph.refl LocalHomeomorph.refl

@[simp, mfld_simps]
theorem refl_localEquiv : (LocalHomeomorph.refl α).toLocalEquiv = LocalEquiv.refl α :=
  rfl
#align local_homeomorph.refl_local_equiv LocalHomeomorph.refl_localEquiv

@[simp, mfld_simps]
theorem refl_symm : (LocalHomeomorph.refl α).symm = LocalHomeomorph.refl α :=
  rfl
#align local_homeomorph.refl_symm LocalHomeomorph.refl_symm

section

variable {s : Set α} (hs : IsOpen s)

/-- The identity local equiv on a set `s` -/
@[simps! (config := mfld_cfg) apply, simps! (config := .lemmasOnly) source target]
def ofSet (s : Set α) (hs : IsOpen s) : LocalHomeomorph α α where
  toLocalEquiv := LocalEquiv.ofSet s
  open_source := hs
  open_target := hs
  continuous_toFun := continuous_id.continuousOn
  continuous_invFun := continuous_id.continuousOn
#align local_homeomorph.of_set LocalHomeomorph.ofSet

@[simp, mfld_simps]
theorem ofSet_toLocalEquiv : (ofSet s hs).toLocalEquiv = LocalEquiv.ofSet s :=
  rfl
#align local_homeomorph.of_set_to_local_equiv LocalHomeomorph.ofSet_toLocalEquiv

@[simp, mfld_simps]
theorem ofSet_symm : (ofSet s hs).symm = ofSet s hs :=
  rfl
#align local_homeomorph.of_set_symm LocalHomeomorph.ofSet_symm

@[simp, mfld_simps]
theorem ofSet_univ_eq_refl : ofSet univ isOpen_univ = LocalHomeomorph.refl α := by ext <;> simp
#align local_homeomorph.of_set_univ_eq_refl LocalHomeomorph.ofSet_univ_eq_refl

end

/-- Composition of two local homeomorphisms when the target of the first and the source of
the second coincide. -/
@[simps! apply symm_apply toLocalEquiv, simps! (config := .lemmasOnly) source target]
protected def trans' (h : e.target = e'.source) : LocalHomeomorph α γ where
  toLocalEquiv := LocalEquiv.trans' e.toLocalEquiv e'.toLocalEquiv h
  open_source := e.open_source
  open_target := e'.open_target
  continuous_toFun :=  e'.continuousOn.comp e.continuousOn <| h ▸ e.mapsTo
  continuous_invFun := e.continuousOn_symm.comp e'.continuousOn_symm <| h.symm ▸ e'.symm_mapsTo
#align local_homeomorph.trans' LocalHomeomorph.trans'

/-- Composing two local homeomorphisms, by restricting to the maximal domain where their
composition is well defined. -/
protected def trans : LocalHomeomorph α γ :=
  LocalHomeomorph.trans' (e.symm.restrOpen e'.source e'.open_source).symm
    (e'.restrOpen e.target e.open_target) (by simp [inter_comm])
#align local_homeomorph.trans LocalHomeomorph.trans

@[simp, mfld_simps]
theorem trans_toLocalEquiv : (e.trans e').toLocalEquiv = e.toLocalEquiv.trans e'.toLocalEquiv :=
  rfl
#align local_homeomorph.trans_to_local_equiv LocalHomeomorph.trans_toLocalEquiv

@[simp, mfld_simps]
theorem coe_trans : (e.trans e' : α → γ) = e' ∘ e :=
  rfl
#align local_homeomorph.coe_trans LocalHomeomorph.coe_trans

@[simp, mfld_simps]
theorem coe_trans_symm : ((e.trans e').symm : γ → α) = e.symm ∘ e'.symm :=
  rfl
#align local_homeomorph.coe_trans_symm LocalHomeomorph.coe_trans_symm

theorem trans_apply {x : α} : (e.trans e') x = e' (e x) :=
  rfl
#align local_homeomorph.trans_apply LocalHomeomorph.trans_apply

theorem trans_symm_eq_symm_trans_symm : (e.trans e').symm = e'.symm.trans e.symm := rfl
#align local_homeomorph.trans_symm_eq_symm_trans_symm LocalHomeomorph.trans_symm_eq_symm_trans_symm

/- This could be considered as a simp lemma, but there are many situations where it makes something
simple into something more complicated. -/
theorem trans_source : (e.trans e').source = e.source ∩ e ⁻¹' e'.source :=
  LocalEquiv.trans_source e.toLocalEquiv e'.toLocalEquiv
#align local_homeomorph.trans_source LocalHomeomorph.trans_source

theorem trans_source' : (e.trans e').source = e.source ∩ e ⁻¹' (e.target ∩ e'.source) :=
  LocalEquiv.trans_source' e.toLocalEquiv e'.toLocalEquiv
#align local_homeomorph.trans_source' LocalHomeomorph.trans_source'

theorem trans_source'' : (e.trans e').source = e.symm '' (e.target ∩ e'.source) :=
  LocalEquiv.trans_source'' e.toLocalEquiv e'.toLocalEquiv
#align local_homeomorph.trans_source'' LocalHomeomorph.trans_source''

theorem image_trans_source : e '' (e.trans e').source = e.target ∩ e'.source :=
  LocalEquiv.image_trans_source e.toLocalEquiv e'.toLocalEquiv
#align local_homeomorph.image_trans_source LocalHomeomorph.image_trans_source

theorem trans_target : (e.trans e').target = e'.target ∩ e'.symm ⁻¹' e.target :=
  rfl
#align local_homeomorph.trans_target LocalHomeomorph.trans_target

theorem trans_target' : (e.trans e').target = e'.target ∩ e'.symm ⁻¹' (e'.source ∩ e.target) :=
  trans_source' e'.symm e.symm
#align local_homeomorph.trans_target' LocalHomeomorph.trans_target'

theorem trans_target'' : (e.trans e').target = e' '' (e'.source ∩ e.target) :=
  trans_source'' e'.symm e.symm
#align local_homeomorph.trans_target'' LocalHomeomorph.trans_target''

theorem inv_image_trans_target : e'.symm '' (e.trans e').target = e'.source ∩ e.target :=
  image_trans_source e'.symm e.symm
#align local_homeomorph.inv_image_trans_target LocalHomeomorph.inv_image_trans_target

theorem trans_assoc (e'' : LocalHomeomorph γ δ) :
    (e.trans e').trans e'' = e.trans (e'.trans e'') :=
  toLocalEquiv_injective <| e.1.trans_assoc _ _
#align local_homeomorph.trans_assoc LocalHomeomorph.trans_assoc

@[simp, mfld_simps]
theorem trans_refl : e.trans (LocalHomeomorph.refl β) = e :=
  toLocalEquiv_injective e.1.trans_refl
#align local_homeomorph.trans_refl LocalHomeomorph.trans_refl

@[simp, mfld_simps]
theorem refl_trans : (LocalHomeomorph.refl α).trans e = e :=
  toLocalEquiv_injective e.1.refl_trans
#align local_homeomorph.refl_trans LocalHomeomorph.refl_trans

theorem trans_ofSet {s : Set β} (hs : IsOpen s) : e.trans (ofSet s hs) = e.restr (e ⁻¹' s) :=
  LocalHomeomorph.ext _ _ (fun _ => rfl) (fun _ => rfl) <| by
    rw [trans_source, restr_source, ofSet_source, ← preimage_interior, hs.interior_eq]
#align local_homeomorph.trans_of_set LocalHomeomorph.trans_ofSet

theorem trans_of_set' {s : Set β} (hs : IsOpen s) :
    e.trans (ofSet s hs) = e.restr (e.source ∩ e ⁻¹' s) := by rw [trans_ofSet, restr_source_inter]
#align local_homeomorph.trans_of_set' LocalHomeomorph.trans_of_set'

theorem ofSet_trans {s : Set α} (hs : IsOpen s) : (ofSet s hs).trans e = e.restr s :=
  LocalHomeomorph.ext _ _ (fun x => rfl) (fun x => rfl) <| by simp [hs.interior_eq, inter_comm]
#align local_homeomorph.of_set_trans LocalHomeomorph.ofSet_trans

theorem ofSet_trans' {s : Set α} (hs : IsOpen s) : (ofSet s hs).trans e = e.restr (e.source ∩ s) :=
  by rw [ofSet_trans, restr_source_inter]
#align local_homeomorph.of_set_trans' LocalHomeomorph.ofSet_trans'

@[simp, mfld_simps]
theorem ofSet_trans_ofSet {s : Set α} (hs : IsOpen s) {s' : Set α} (hs' : IsOpen s') :
    (ofSet s hs).trans (ofSet s' hs') = ofSet (s ∩ s') (IsOpen.inter hs hs') := by
  rw [(ofSet s hs).trans_ofSet hs']
  ext <;> simp [hs'.interior_eq]
#align local_homeomorph.of_set_trans_of_set LocalHomeomorph.ofSet_trans_ofSet

theorem restr_trans (s : Set α) : (e.restr s).trans e' = (e.trans e').restr s :=
  toLocalEquiv_injective <| LocalEquiv.restr_trans e.toLocalEquiv e'.toLocalEquiv (interior s)
#align local_homeomorph.restr_trans LocalHomeomorph.restr_trans

/-- Postcompose a local homeomorphism with a homeomorphism.
We modify the source and target to have better definitional behavior. -/
@[simps! (config := { fullyApplied := false })]
def transHomeomorph (e' : β ≃ₜ γ) : LocalHomeomorph α γ where
  toLocalEquiv := e.toLocalEquiv.transEquiv e'.toEquiv
  open_source := e.open_source
  open_target := e.open_target.preimage e'.symm.continuous
  continuous_toFun := e'.continuous.comp_continuousOn e.continuousOn
  continuous_invFun := e.symm.continuousOn.comp e'.symm.continuous.continuousOn fun _ => id
#align local_homeomorph.trans_homeomorph LocalHomeomorph.transHomeomorph

theorem transHomeomorph_eq_trans (e' : β ≃ₜ γ) :
    e.transHomeomorph e' = e.trans e'.toLocalHomeomorph :=
  toLocalEquiv_injective <| LocalEquiv.transEquiv_eq_trans _ _
#align local_homeomorph.trans_equiv_eq_trans LocalHomeomorph.transHomeomorph_eq_trans

/-- Precompose a local homeomorphism with a homeomorphism.
We modify the source and target to have better definitional behavior. -/
@[simps! (config := { fullyApplied := false })]
def _root_.Homeomorph.transLocalHomeomorph (e : α ≃ₜ β) : LocalHomeomorph α γ where
  toLocalEquiv := e.toEquiv.transLocalEquiv e'.toLocalEquiv
  open_source := e'.open_source.preimage e.continuous
  open_target := e'.open_target
  continuous_toFun := e'.continuousOn.comp e.continuous.continuousOn fun _ => id
  continuous_invFun := e.symm.continuous.comp_continuousOn e'.symm.continuousOn
#align homeomorph.trans_local_homeomorph Homeomorph.transLocalHomeomorph

theorem _root_.Homeomorph.transLocalHomeomorph_eq_trans (e : α ≃ₜ β) :
    e.transLocalHomeomorph e' = e.toLocalHomeomorph.trans e' :=
  toLocalEquiv_injective <| Equiv.transLocalEquiv_eq_trans _ _
#align homeomorph.trans_local_homeomorph_eq_trans Homeomorph.transLocalHomeomorph_eq_trans

/-- `EqOnSource e e'` means that `e` and `e'` have the same source, and coincide there. They
should really be considered the same local equiv. -/
def EqOnSource (e e' : LocalHomeomorph α β) : Prop :=
  e.source = e'.source ∧ EqOn e e' e.source
#align local_homeomorph.eq_on_source LocalHomeomorph.EqOnSource

theorem eqOnSource_iff (e e' : LocalHomeomorph α β) :
    EqOnSource e e' ↔ LocalEquiv.EqOnSource e.toLocalEquiv e'.toLocalEquiv :=
  Iff.rfl
#align local_homeomorph.eq_on_source_iff LocalHomeomorph.eqOnSource_iff

/-- `EqOnSource` is an equivalence relation. -/
instance eqOnSourceSetoid : Setoid (LocalHomeomorph α β) :=
  { LocalEquiv.eqOnSourceSetoid.comap toLocalEquiv with r := EqOnSource }

theorem eqOnSource_refl : e ≈ e := Setoid.refl _
#align local_homeomorph.eq_on_source_refl LocalHomeomorph.eqOnSource_refl

/-- If two local homeomorphisms are equivalent, so are their inverses. -/
theorem EqOnSource.symm' {e e' : LocalHomeomorph α β} (h : e ≈ e') : e.symm ≈ e'.symm :=
  LocalEquiv.EqOnSource.symm' h
#align local_homeomorph.eq_on_source.symm' LocalHomeomorph.EqOnSource.symm'

/-- Two equivalent local homeomorphisms have the same source. -/
theorem EqOnSource.source_eq {e e' : LocalHomeomorph α β} (h : e ≈ e') : e.source = e'.source :=
  h.1
#align local_homeomorph.eq_on_source.source_eq LocalHomeomorph.EqOnSource.source_eq

/-- Two equivalent local homeomorphisms have the same target. -/
theorem EqOnSource.target_eq {e e' : LocalHomeomorph α β} (h : e ≈ e') : e.target = e'.target :=
  h.symm'.1
#align local_homeomorph.eq_on_source.target_eq LocalHomeomorph.EqOnSource.target_eq

/-- Two equivalent local homeomorphisms have coinciding `toFun` on the source -/
theorem EqOnSource.eqOn {e e' : LocalHomeomorph α β} (h : e ≈ e') : EqOn e e' e.source :=
  h.2
#align local_homeomorph.eq_on_source.eq_on LocalHomeomorph.EqOnSource.eqOn

/-- Two equivalent local homeomorphisms have coinciding `invFun` on the target -/
theorem EqOnSource.symm_eqOn_target {e e' : LocalHomeomorph α β} (h : e ≈ e') :
    EqOn e.symm e'.symm e.target :=
  h.symm'.2
#align local_homeomorph.eq_on_source.symm_eq_on_target LocalHomeomorph.EqOnSource.symm_eqOn_target

/-- Composition of local homeomorphisms respects equivalence -/
theorem EqOnSource.trans' {e e' : LocalHomeomorph α β} {f f' : LocalHomeomorph β γ} (he : e ≈ e')
    (hf : f ≈ f') : e.trans f ≈ e'.trans f' :=
  LocalEquiv.EqOnSource.trans' he hf
#align local_homeomorph.eq_on_source.trans' LocalHomeomorph.EqOnSource.trans'

/-- Restriction of local homeomorphisms respects equivalence -/
theorem EqOnSource.restr {e e' : LocalHomeomorph α β} (he : e ≈ e') (s : Set α) :
    e.restr s ≈ e'.restr s :=
  LocalEquiv.EqOnSource.restr he _
#align local_homeomorph.eq_on_source.restr LocalHomeomorph.EqOnSource.restr

/- Two equivalent local homeomorphisms are equal when the source and target are `univ`. -/
theorem Set.EqOn.restr_eqOn_source {e e' : LocalHomeomorph α β}
    (h : EqOn e e' (e.source ∩ e'.source)) : e.restr e'.source ≈ e'.restr e.source := by
  constructor
  · rw [e'.restr_source' _ e.open_source]
    rw [e.restr_source' _ e'.open_source]
    exact Set.inter_comm _ _
  · rw [e.restr_source' _ e'.open_source]
    refine' (EqOn.trans _ h).trans _ <;> simp only [mfld_simps, eqOn_refl]
#align local_homeomorph.set.eq_on.restr_eq_on_source LocalHomeomorph.Set.EqOn.restr_eqOn_source

/-- Composition of a local homeomorphism and its inverse is equivalent to the restriction of the
identity to the source -/
theorem trans_self_symm : e.trans e.symm ≈ LocalHomeomorph.ofSet e.source e.open_source :=
  LocalEquiv.trans_self_symm _
#align local_homeomorph.trans_self_symm LocalHomeomorph.trans_self_symm

theorem trans_symm_self : e.symm.trans e ≈ LocalHomeomorph.ofSet e.target e.open_target :=
  e.symm.trans_self_symm
#align local_homeomorph.trans_symm_self LocalHomeomorph.trans_symm_self

theorem eq_of_eqOnSource_univ {e e' : LocalHomeomorph α β} (h : e ≈ e') (s : e.source = univ)
    (t : e.target = univ) : e = e' :=
  toLocalEquiv_injective <| LocalEquiv.eq_of_eqOnSource_univ _ _ h s t
#align local_homeomorph.eq_of_eq_on_source_univ LocalHomeomorph.eq_of_eqOnSource_univ

section Prod

/-- The product of two local homeomorphisms, as a local homeomorphism on the product space. -/
@[simps! (config := mfld_cfg) toLocalEquiv apply,
  simps! (config := .lemmasOnly) source target symm_apply]
def prod (e : LocalHomeomorph α β) (e' : LocalHomeomorph γ δ) :
    LocalHomeomorph (α × γ) (β × δ) where
  open_source := e.open_source.prod e'.open_source
  open_target := e.open_target.prod e'.open_target
  continuous_toFun := e.continuousOn.prod_map e'.continuousOn
  continuous_invFun := e.continuousOn_symm.prod_map e'.continuousOn_symm
  toLocalEquiv := e.toLocalEquiv.prod e'.toLocalEquiv
#align local_homeomorph.prod LocalHomeomorph.prod

@[simp, mfld_simps]
theorem prod_symm (e : LocalHomeomorph α β) (e' : LocalHomeomorph γ δ) :
    (e.prod e').symm = e.symm.prod e'.symm :=
  rfl
#align local_homeomorph.prod_symm LocalHomeomorph.prod_symm

@[simp]
theorem refl_prod_refl {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] :
    (LocalHomeomorph.refl α).prod (LocalHomeomorph.refl β) = LocalHomeomorph.refl (α × β) :=
  LocalHomeomorph.ext _ _ (fun _ => rfl) (fun _ => rfl) univ_prod_univ
#align local_homeomorph.refl_prod_refl LocalHomeomorph.refl_prod_refl

@[simp, mfld_simps]
theorem prod_trans {η : Type*} {ε : Type*} [TopologicalSpace η] [TopologicalSpace ε]
    (e : LocalHomeomorph α β) (f : LocalHomeomorph β γ) (e' : LocalHomeomorph δ η)
    (f' : LocalHomeomorph η ε) : (e.prod e').trans (f.prod f') = (e.trans f).prod (e'.trans f') :=
  toLocalEquiv_injective <| e.1.prod_trans ..
#align local_homeomorph.prod_trans LocalHomeomorph.prod_trans

theorem prod_eq_prod_of_nonempty {e₁ e₁' : LocalHomeomorph α β} {e₂ e₂' : LocalHomeomorph γ δ}
    (h : (e₁.prod e₂).source.Nonempty) : e₁.prod e₂ = e₁'.prod e₂' ↔ e₁ = e₁' ∧ e₂ = e₂' := by
  obtain ⟨⟨x, y⟩, -⟩ := id h
  haveI : Nonempty α := ⟨x⟩
  haveI : Nonempty β := ⟨e₁ x⟩
  haveI : Nonempty γ := ⟨y⟩
  haveI : Nonempty δ := ⟨e₂ y⟩
  simp_rw [LocalHomeomorph.ext_iff, prod_apply, prod_symm_apply, prod_source, Prod.ext_iff,
    Set.prod_eq_prod_iff_of_nonempty h, forall_and, Prod.forall, forall_const,
    and_assoc, and_left_comm]
#align local_homeomorph.prod_eq_prod_of_nonempty LocalHomeomorph.prod_eq_prod_of_nonempty

theorem prod_eq_prod_of_nonempty' {e₁ e₁' : LocalHomeomorph α β} {e₂ e₂' : LocalHomeomorph γ δ}
    (h : (e₁'.prod e₂').source.Nonempty) : e₁.prod e₂ = e₁'.prod e₂' ↔ e₁ = e₁' ∧ e₂ = e₂' := by
  rw [eq_comm, prod_eq_prod_of_nonempty h, eq_comm, @eq_comm _ e₂']
#align local_homeomorph.prod_eq_prod_of_nonempty' LocalHomeomorph.prod_eq_prod_of_nonempty'

end Prod

section Piecewise

/-- Combine two `LocalHomeomorph`s using `Set.piecewise`. The source of the new `LocalHomeomorph`
is `s.ite e.source e'.source = e.source ∩ s ∪ e'.source \ s`, and similarly for target.  The
function sends `e.source ∩ s` to `e.target ∩ t` using `e` and `e'.source \ s` to `e'.target \ t`
using `e'`, and similarly for the inverse function. To ensure that the maps `toFun` and `invFun`
are inverse of each other on the new `source` and `target`, the definition assumes that the sets `s`
and `t` are related both by `e.is_image` and `e'.is_image`. To ensure that the new maps are
continuous on `source`/`target`, it also assumes that `e.source` and `e'.source` meet `frontier s`
on the same set and `e x = e' x` on this intersection. -/
@[simps! (config := { fullyApplied := false }) toLocalEquiv apply]
def piecewise (e e' : LocalHomeomorph α β) (s : Set α) (t : Set β) [∀ x, Decidable (x ∈ s)]
    [∀ y, Decidable (y ∈ t)] (H : e.IsImage s t) (H' : e'.IsImage s t)
    (Hs : e.source ∩ frontier s = e'.source ∩ frontier s)
    (Heq : EqOn e e' (e.source ∩ frontier s)) : LocalHomeomorph α β where
  toLocalEquiv := e.toLocalEquiv.piecewise e'.toLocalEquiv s t H H'
  open_source := e.open_source.ite e'.open_source Hs
  open_target :=
    e.open_target.ite e'.open_target <| H.frontier.inter_eq_of_inter_eq_of_eqOn H'.frontier Hs Heq
  continuous_toFun := continuousOn_piecewise_ite e.continuousOn e'.continuousOn Hs Heq
  continuous_invFun :=
    continuousOn_piecewise_ite e.continuousOn_symm e'.continuousOn_symm
      (H.frontier.inter_eq_of_inter_eq_of_eqOn H'.frontier Hs Heq)
      (H.frontier.symm_eqOn_of_inter_eq_of_eqOn Hs Heq)
#align local_homeomorph.piecewise LocalHomeomorph.piecewise

@[simp]
theorem symm_piecewise (e e' : LocalHomeomorph α β) {s : Set α} {t : Set β} [∀ x, Decidable (x ∈ s)]
    [∀ y, Decidable (y ∈ t)] (H : e.IsImage s t) (H' : e'.IsImage s t)
    (Hs : e.source ∩ frontier s = e'.source ∩ frontier s)
    (Heq : EqOn e e' (e.source ∩ frontier s)) :
    (e.piecewise e' s t H H' Hs Heq).symm =
      e.symm.piecewise e'.symm t s H.symm H'.symm
        (H.frontier.inter_eq_of_inter_eq_of_eqOn H'.frontier Hs Heq)
        (H.frontier.symm_eqOn_of_inter_eq_of_eqOn Hs Heq) :=
  rfl
#align local_homeomorph.symm_piecewise LocalHomeomorph.symm_piecewise

/-- Combine two `LocalHomeomorph`s with disjoint sources and disjoint targets. We reuse
`LocalHomeomorph.piecewise` then override `toLocalEquiv` to `LocalEquiv.disjointUnion`.
This way we have better definitional equalities for `source` and `target`. -/
def disjointUnion (e e' : LocalHomeomorph α β) [∀ x, Decidable (x ∈ e.source)]
    [∀ y, Decidable (y ∈ e.target)] (Hs : Disjoint e.source e'.source)
    (Ht : Disjoint e.target e'.target) : LocalHomeomorph α β :=
  (e.piecewise e' e.source e.target e.isImage_source_target
        (e'.isImage_source_target_of_disjoint e Hs.symm Ht.symm)
        (by rw [e.open_source.inter_frontier_eq, (Hs.symm.frontier_right e'.open_source).inter_eq])
        (by
          rw [e.open_source.inter_frontier_eq]
          exact eqOn_empty _ _)).replaceEquiv
    (e.toLocalEquiv.disjointUnion e'.toLocalEquiv Hs Ht)
    (LocalEquiv.disjointUnion_eq_piecewise _ _ _ _).symm
#align local_homeomorph.disjoint_union LocalHomeomorph.disjointUnion

end Piecewise

section Pi

variable {ι : Type*} [Fintype ι] {Xi Yi : ι → Type*} [∀ i, TopologicalSpace (Xi i)]
  [∀ i, TopologicalSpace (Yi i)] (ei : ∀ i, LocalHomeomorph (Xi i) (Yi i))

/-- The product of a finite family of `LocalHomeomorph`s. -/
@[simps toLocalEquiv]
def pi : LocalHomeomorph (∀ i, Xi i) (∀ i, Yi i) where
  toLocalEquiv := LocalEquiv.pi fun i => (ei i).toLocalEquiv
  open_source := isOpen_set_pi finite_univ fun i _ => (ei i).open_source
  open_target := isOpen_set_pi finite_univ fun i _ => (ei i).open_target
  continuous_toFun := continuousOn_pi.2 fun i =>
    (ei i).continuousOn.comp (continuous_apply _).continuousOn fun _f hf => hf i trivial
  continuous_invFun := continuousOn_pi.2 fun i =>
    (ei i).continuousOn_symm.comp (continuous_apply _).continuousOn fun _f hf => hf i trivial
#align local_homeomorph.pi LocalHomeomorph.pi

end Pi

section Continuity

/-- Continuity within a set at a point can be read under right composition with a local
homeomorphism, if the point is in its target -/
theorem continuousWithinAt_iff_continuousWithinAt_comp_right {f : β → γ} {s : Set β} {x : β}
    (h : x ∈ e.target) :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt (f ∘ e) (e ⁻¹' s) (e.symm x) := by
  simp_rw [ContinuousWithinAt, ← @tendsto_map'_iff _ _ _ _ e,
    e.map_nhdsWithin_preimage_eq (e.map_target h), (· ∘ ·), e.right_inv h]
#align local_homeomorph.continuous_within_at_iff_continuous_within_at_comp_right LocalHomeomorph.continuousWithinAt_iff_continuousWithinAt_comp_right

/-- Continuity at a point can be read under right composition with a local homeomorphism, if the
point is in its target -/
theorem continuousAt_iff_continuousAt_comp_right {f : β → γ} {x : β} (h : x ∈ e.target) :
    ContinuousAt f x ↔ ContinuousAt (f ∘ e) (e.symm x) := by
  rw [← continuousWithinAt_univ, e.continuousWithinAt_iff_continuousWithinAt_comp_right h,
    preimage_univ, continuousWithinAt_univ]
#align local_homeomorph.continuous_at_iff_continuous_at_comp_right LocalHomeomorph.continuousAt_iff_continuousAt_comp_right

/-- A function is continuous on a set if and only if its composition with a local homeomorphism
on the right is continuous on the corresponding set. -/
theorem continuousOn_iff_continuousOn_comp_right {f : β → γ} {s : Set β} (h : s ⊆ e.target) :
    ContinuousOn f s ↔ ContinuousOn (f ∘ e) (e.source ∩ e ⁻¹' s) := by
  simp only [← e.symm_image_eq_source_inter_preimage h, ContinuousOn, ball_image_iff]
  refine' forall₂_congr fun x hx => _
  rw [e.continuousWithinAt_iff_continuousWithinAt_comp_right (h hx),
    e.symm_image_eq_source_inter_preimage h, inter_comm, continuousWithinAt_inter]
  exact IsOpen.mem_nhds e.open_source (e.map_target (h hx))
#align local_homeomorph.continuous_on_iff_continuous_on_comp_right LocalHomeomorph.continuousOn_iff_continuousOn_comp_right

/-- Continuity within a set at a point can be read under left composition with a local
homeomorphism if a neighborhood of the initial point is sent to the source of the local
homeomorphism-/
theorem continuousWithinAt_iff_continuousWithinAt_comp_left {f : γ → α} {s : Set γ} {x : γ}
    (hx : f x ∈ e.source) (h : f ⁻¹' e.source ∈ 𝓝[s] x) :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt (e ∘ f) s x := by
  refine' ⟨(e.continuousAt hx).comp_continuousWithinAt, fun fe_cont => _⟩
  rw [← continuousWithinAt_inter' h] at fe_cont ⊢
  have : ContinuousWithinAt (e.symm ∘ e ∘ f) (s ∩ f ⁻¹' e.source) x :=
    haveI : ContinuousWithinAt e.symm univ (e (f x)) :=
      (e.continuousAt_symm (e.map_source hx)).continuousWithinAt
    ContinuousWithinAt.comp this fe_cont (subset_univ _)
  exact this.congr (fun y hy => by simp [e.left_inv hy.2]) (by simp [e.left_inv hx])
#align local_homeomorph.continuous_within_at_iff_continuous_within_at_comp_left LocalHomeomorph.continuousWithinAt_iff_continuousWithinAt_comp_left

/-- Continuity at a point can be read under left composition with a local homeomorphism if a
neighborhood of the initial point is sent to the source of the local homeomorphism-/
theorem continuousAt_iff_continuousAt_comp_left {f : γ → α} {x : γ} (h : f ⁻¹' e.source ∈ 𝓝 x) :
    ContinuousAt f x ↔ ContinuousAt (e ∘ f) x := by
  have hx : f x ∈ e.source := (mem_of_mem_nhds h : _)
  have h' : f ⁻¹' e.source ∈ 𝓝[univ] x := by rwa [nhdsWithin_univ]
  rw [← continuousWithinAt_univ, ← continuousWithinAt_univ,
    e.continuousWithinAt_iff_continuousWithinAt_comp_left hx h']
#align local_homeomorph.continuous_at_iff_continuous_at_comp_left LocalHomeomorph.continuousAt_iff_continuousAt_comp_left

/-- A function is continuous on a set if and only if its composition with a local homeomorphism
on the left is continuous on the corresponding set. -/
theorem continuousOn_iff_continuousOn_comp_left {f : γ → α} {s : Set γ} (h : s ⊆ f ⁻¹' e.source) :
    ContinuousOn f s ↔ ContinuousOn (e ∘ f) s :=
  forall₂_congr fun _x hx =>
    e.continuousWithinAt_iff_continuousWithinAt_comp_left (h hx)
      (mem_of_superset self_mem_nhdsWithin h)
#align local_homeomorph.continuous_on_iff_continuous_on_comp_left LocalHomeomorph.continuousOn_iff_continuousOn_comp_left

/-- A function is continuous if and only if its composition with a local homeomorphism
on the left is continuous and its image is contained in the source. -/
theorem continuous_iff_continuous_comp_left {f : γ → α} (h : f ⁻¹' e.source = univ) :
    Continuous f ↔ Continuous (e ∘ f) := by
  simp only [continuous_iff_continuousOn_univ]
  exact e.continuousOn_iff_continuousOn_comp_left (Eq.symm h).subset
#align local_homeomorph.continuous_iff_continuous_comp_left LocalHomeomorph.continuous_iff_continuous_comp_left

end Continuity

/-- The homeomorphism obtained by restricting a `LocalHomeomorph` to a subset of the source. -/
@[simps]
def homeomorphOfImageSubsetSource {s : Set α} {t : Set β} (hs : s ⊆ e.source) (ht : e '' s = t) :
    s ≃ₜ t :=
  have h₁ : MapsTo e s t := mapsTo'.2 ht.subset
  have h₂ : t ⊆ e.target := ht ▸ e.image_source_eq_target ▸ image_subset e hs
  have h₃ : MapsTo e.symm t s := ht ▸ ball_image_iff.2 <| fun _x hx =>
      (e.left_inv (hs hx)).symm ▸ hx
  { toFun := MapsTo.restrict e s t h₁
    invFun := MapsTo.restrict e.symm t s h₃
    left_inv := fun a => Subtype.ext (e.left_inv (hs a.2))
    right_inv := fun b => Subtype.eq <| e.right_inv (h₂ b.2)
    continuous_toFun := (e.continuousOn.mono hs).restrict_mapsTo h₁
    continuous_invFun := (e.continuousOn_symm.mono h₂).restrict_mapsTo h₃ }
#align local_homeomorph.homeomorph_of_image_subset_source LocalHomeomorph.homeomorphOfImageSubsetSource

/-- A local homeomorphism defines a homeomorphism between its source and target. -/
@[simps!] -- porting note: new `simps`
def toHomeomorphSourceTarget : e.source ≃ₜ e.target :=
  e.homeomorphOfImageSubsetSource subset_rfl e.image_source_eq_target
#align local_homeomorph.to_homeomorph_source_target LocalHomeomorph.toHomeomorphSourceTarget

theorem secondCountableTopology_source [SecondCountableTopology β] (e : LocalHomeomorph α β) :
    SecondCountableTopology e.source :=
  e.toHomeomorphSourceTarget.secondCountableTopology
#align local_homeomorph.second_countable_topology_source LocalHomeomorph.secondCountableTopology_source

theorem nhds_eq_comap_inf_principal {x} (hx : x ∈ e.source) :
    𝓝 x = comap e (𝓝 (e x)) ⊓ 𝓟 e.source := by
  lift x to e.source using hx
  rw [← e.open_source.nhdsWithin_eq x.2, ← map_nhds_subtype_val, ← map_comap_setCoe_val,
    e.toHomeomorphSourceTarget.nhds_eq_comap, nhds_subtype_eq_comap]
  simp only [(· ∘ ·), toHomeomorphSourceTarget_apply_coe, comap_comap]

/-- If a local homeomorphism has source and target equal to univ, then it induces a homeomorphism
between the whole spaces, expressed in this definition. -/
@[simps (config := mfld_cfg) apply symm_apply] -- porting note: todo: add a `LocalEquiv` version
def toHomeomorphOfSourceEqUnivTargetEqUniv (h : e.source = (univ : Set α)) (h' : e.target = univ) :
    α ≃ₜ β where
  toFun := e
  invFun := e.symm
  left_inv x :=
    e.left_inv <| by
      rw [h]
      exact mem_univ _
  right_inv x :=
    e.right_inv <| by
      rw [h']
      exact mem_univ _
  continuous_toFun := by
    simpa only [continuous_iff_continuousOn_univ, h] using e.continuousOn
  continuous_invFun := by
    simpa only [continuous_iff_continuousOn_univ, h'] using e.continuousOn_symm
#align local_homeomorph.to_homeomorph_of_source_eq_univ_target_eq_univ LocalHomeomorph.toHomeomorphOfSourceEqUnivTargetEqUniv

theorem openEmbedding_restrict : OpenEmbedding (e.source.restrict e) := by
  refine openEmbedding_of_continuous_injective_open (e.continuousOn.comp_continuous
    continuous_subtype_val Subtype.prop) e.injOn.injective fun V hV ↦ ?_
  rw [Set.restrict_eq, Set.image_comp]
  exact e.image_open_of_open (e.open_source.isOpenMap_subtype_val V hV) fun _ ⟨x, _, h⟩ ↦ h ▸ x.2

/-- A local homeomorphism whose source is all of `α` defines an open embedding of `α` into `β`.  The
converse is also true; see `OpenEmbedding.toLocalHomeomorph`. -/
theorem to_openEmbedding (h : e.source = Set.univ) : OpenEmbedding e :=
  e.openEmbedding_restrict.comp
    ((Homeomorph.setCongr h).trans <| Homeomorph.Set.univ α).symm.openEmbedding

#align local_homeomorph.to_open_embedding LocalHomeomorph.to_openEmbedding

end LocalHomeomorph

namespace Homeomorph

variable (e : α ≃ₜ β) (e' : β ≃ₜ γ)

/- Register as simp lemmas that the fields of a local homeomorphism built from a homeomorphism
correspond to the fields of the original homeomorphism. -/
@[simp, mfld_simps]
theorem refl_toLocalHomeomorph : (Homeomorph.refl α).toLocalHomeomorph = LocalHomeomorph.refl α :=
  rfl
#align homeomorph.refl_to_local_homeomorph Homeomorph.refl_toLocalHomeomorph

@[simp, mfld_simps]
theorem symm_toLocalHomeomorph : e.symm.toLocalHomeomorph = e.toLocalHomeomorph.symm :=
  rfl
#align homeomorph.symm_to_local_homeomorph Homeomorph.symm_toLocalHomeomorph

@[simp, mfld_simps]
theorem trans_toLocalHomeomorph :
    (e.trans e').toLocalHomeomorph = e.toLocalHomeomorph.trans e'.toLocalHomeomorph :=
  LocalHomeomorph.toLocalEquiv_injective <| Equiv.trans_toLocalEquiv _ _
#align homeomorph.trans_to_local_homeomorph Homeomorph.trans_toLocalHomeomorph

end Homeomorph

namespace OpenEmbedding

variable (f : α → β) (h : OpenEmbedding f)

/-- An open embedding of `α` into `β`, with `α` nonempty, defines a local homeomorphism whose source
is all of `α`.  The converse is also true; see `LocalHomeomorph.to_openEmbedding`. -/
@[simps! (config := mfld_cfg) apply source target]
noncomputable def toLocalHomeomorph [Nonempty α] : LocalHomeomorph α β :=
  LocalHomeomorph.ofContinuousOpen ((h.toEmbedding.inj.injOn univ).toLocalEquiv _ _)
    h.continuous.continuousOn h.isOpenMap isOpen_univ
#align open_embedding.to_local_homeomorph OpenEmbedding.toLocalHomeomorph

theorem continuousAt_iff {f : α → β} {g : β → γ} (hf : OpenEmbedding f) {x : α} :
    ContinuousAt (g ∘ f) x ↔ ContinuousAt g (f x) :=
  hf.tendsto_nhds_iff'
#align open_embedding.continuous_at_iff OpenEmbedding.continuousAt_iff

end OpenEmbedding

namespace TopologicalSpace.Opens

open TopologicalSpace

variable (s : Opens α) [Nonempty s]

/-- The inclusion of an open subset `s` of a space `α` into `α` is a local homeomorphism from the
subtype `s` to `α`. -/
noncomputable def localHomeomorphSubtypeCoe : LocalHomeomorph s α :=
  OpenEmbedding.toLocalHomeomorph _ s.2.openEmbedding_subtype_val
#align topological_space.opens.local_homeomorph_subtype_coe TopologicalSpace.Opens.localHomeomorphSubtypeCoe

@[simp, mfld_simps]
theorem localHomeomorphSubtypeCoe_coe : (s.localHomeomorphSubtypeCoe : s → α) = (↑) :=
  rfl
#align topological_space.opens.local_homeomorph_subtype_coe_coe TopologicalSpace.Opens.localHomeomorphSubtypeCoe_coe

@[simp, mfld_simps]
theorem localHomeomorphSubtypeCoe_source : s.localHomeomorphSubtypeCoe.source = Set.univ :=
  rfl
#align topological_space.opens.local_homeomorph_subtype_coe_source TopologicalSpace.Opens.localHomeomorphSubtypeCoe_source

@[simp, mfld_simps]
theorem localHomeomorphSubtypeCoe_target : s.localHomeomorphSubtypeCoe.target = s := by
  simp only [localHomeomorphSubtypeCoe, Subtype.range_coe_subtype, mfld_simps]
  rfl
#align topological_space.opens.local_homeomorph_subtype_coe_target TopologicalSpace.Opens.localHomeomorphSubtypeCoe_target

end TopologicalSpace.Opens

namespace LocalHomeomorph

open TopologicalSpace

variable (e : LocalHomeomorph α β)

variable (s : Opens α) [Nonempty s]

/-- The restriction of a local homeomorphism `e` to an open subset `s` of the domain type produces a
local homeomorphism whose domain is the subtype `s`.-/
noncomputable def subtypeRestr : LocalHomeomorph s β :=
  s.localHomeomorphSubtypeCoe.trans e
#align local_homeomorph.subtype_restr LocalHomeomorph.subtypeRestr

theorem subtypeRestr_def : e.subtypeRestr s = s.localHomeomorphSubtypeCoe.trans e :=
  rfl
#align local_homeomorph.subtype_restr_def LocalHomeomorph.subtypeRestr_def

@[simp, mfld_simps]
theorem subtypeRestr_coe :
    ((e.subtypeRestr s : LocalHomeomorph s β) : s → β) = Set.restrict ↑s (e : α → β) :=
  rfl
#align local_homeomorph.subtype_restr_coe LocalHomeomorph.subtypeRestr_coe

@[simp, mfld_simps]
theorem subtypeRestr_source : (e.subtypeRestr s).source = (↑) ⁻¹' e.source := by
  simp only [subtypeRestr_def, mfld_simps]
#align local_homeomorph.subtype_restr_source LocalHomeomorph.subtypeRestr_source

variable {s}

theorem map_subtype_source {x : s} (hxe : (x : α) ∈ e.source): e x ∈ (e.subtypeRestr s).target := by
  refine' ⟨e.map_source hxe, _⟩
  rw [s.localHomeomorphSubtypeCoe_target, mem_preimage, e.leftInvOn hxe]
  exact x.prop
#align local_homeomorph.map_subtype_source LocalHomeomorph.map_subtype_source

variable (s)

/- This lemma characterizes the transition functions of an open subset in terms of the transition
functions of the original space. -/
theorem subtypeRestr_symm_trans_subtypeRestr (f f' : LocalHomeomorph α β) :
    (f.subtypeRestr s).symm.trans (f'.subtypeRestr s) ≈
      (f.symm.trans f').restr (f.target ∩ f.symm ⁻¹' s) := by
  simp only [subtypeRestr_def, trans_symm_eq_symm_trans_symm]
  have openness₁ : IsOpen (f.target ∩ f.symm ⁻¹' s) := f.preimage_open_of_open_symm s.2
  rw [← ofSet_trans _ openness₁, ← trans_assoc, ← trans_assoc]
  refine' EqOnSource.trans' _ (eqOnSource_refl _)
  -- f' has been eliminated !!!
  have sets_identity : f.symm.source ∩ (f.target ∩ f.symm ⁻¹' s) = f.symm.source ∩ f.symm ⁻¹' s :=
    by mfld_set_tac
  have openness₂ : IsOpen (s : Set α) := s.2
  rw [ofSet_trans', sets_identity, ← trans_of_set' _ openness₂, trans_assoc]
  refine' EqOnSource.trans' (eqOnSource_refl _) _
  -- f has been eliminated !!!
  refine' Setoid.trans (trans_symm_self s.localHomeomorphSubtypeCoe) _
  simp only [mfld_simps, Setoid.refl]
#align local_homeomorph.subtype_restr_symm_trans_subtype_restr LocalHomeomorph.subtypeRestr_symm_trans_subtypeRestr

theorem subtypeRestr_symm_eqOn_of_le {U V : Opens α} [Nonempty U] [Nonempty V] (hUV : U ≤ V) :
    EqOn (e.subtypeRestr V).symm (Set.inclusion hUV ∘ (e.subtypeRestr U).symm)
      (e.subtypeRestr U).target := by
  set i := Set.inclusion hUV
  intro y hy
  dsimp [LocalHomeomorph.subtypeRestr_def] at hy ⊢
  have hyV : e.symm y ∈ V.localHomeomorphSubtypeCoe.target := by
    rw [Opens.localHomeomorphSubtypeCoe_target] at hy ⊢
    exact hUV hy.2
  refine' V.localHomeomorphSubtypeCoe.injOn _ trivial _
  · rw [← LocalHomeomorph.symm_target]
    apply LocalHomeomorph.map_source
    rw [LocalHomeomorph.symm_source]
    exact hyV
  · rw [V.localHomeomorphSubtypeCoe.right_inv hyV]
    show _ = U.localHomeomorphSubtypeCoe _
    rw [U.localHomeomorphSubtypeCoe.right_inv hy.2]
#align local_homeomorph.subtype_restr_symm_eq_on_of_le LocalHomeomorph.subtypeRestr_symm_eqOn_of_le

end LocalHomeomorph
