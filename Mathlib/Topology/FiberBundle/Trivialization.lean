/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Data.Bundle
public import Mathlib.Data.Set.Image
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
public import Mathlib.Topology.Order.Basic

/-!
# Trivializations

## Main definitions

### Basic definitions

* `Trivialization F p` : structure extending open partial homeomorphisms, defining a local
  trivialization of a topological space `Z` with projection `p` and fiber `F`.

* `Pretrivialization F proj` : trivialization as a partial equivalence, mainly used when the
  topology on the total space has not yet been defined.

### Operations on bundles

We provide the following operations on `Trivialization`s.

* `Trivialization.compHomeomorph`: given a local trivialization `e` of a fiber bundle
  `p : Z → B` and a homeomorphism `h : Z' ≃ₜ Z`, returns a local trivialization of the fiber bundle
  `p ∘ h`.

## Implementation notes

Previously, in mathlib, there was a structure `topological_vector_bundle.trivialization` which
extended another structure `topological_fiber_bundle.trivialization` by a linearity hypothesis. As
of PR https://github.com/leanprover-community/mathlib3/pull/17359, we have changed this to a single structure
`Trivialization` (no namespace), together with a mixin class `Trivialization.IsLinear`.

This permits all the *data* of a vector bundle to be held at the level of fiber bundles, so that the
same trivializations can underlie an object's structure as (say) a vector bundle over `ℂ` and as a
vector bundle over `ℝ`, as well as its structure simply as a fiber bundle.

This might be a little surprising, given the general trend of the library to ever-increased
bundling.  But in this case the typical motivation for more bundling does not apply: there is no
algebraic or order structure on the whole type of linear (say) trivializations of a bundle.
Indeed, since trivializations only have meaning on their base sets (taking junk values outside), the
type of linear trivializations is not even particularly well-behaved.
-/

@[expose] public section

open TopologicalSpace Filter Set Bundle Function
open scoped Topology

variable {B : Type*} (F : Type*) {E : B → Type*}
variable {Z : Type*} [TopologicalSpace B] [TopologicalSpace F] {proj : Z → B}

/-- This structure contains the information left for a local trivialization (which is implemented
below as `Trivialization F proj`) if the total space has not been given a topology, but we
have a topology on both the fiber and the base space. Through the construction
`topological_fiber_prebundle F proj` it will be possible to promote a
`Pretrivialization F proj` to a `Trivialization F proj`. -/
structure Pretrivialization (proj : Z → B) extends PartialEquiv Z (B × F) where
  open_target : IsOpen target -- TODO rename isOpen
  /-- The domain of the local trivialisation (i.e., a subset of the bundle `Z`'s base):
  outside of it, the pretrivialisation returns a junk value -/
  baseSet : Set B
  open_baseSet : IsOpen baseSet -- TODO rename isOpen
  source_eq : source = proj ⁻¹' baseSet
  target_eq : target = baseSet ×ˢ univ
  proj_toFun : ∀ p ∈ source, (toFun p).1 = proj p

namespace Pretrivialization

variable {F}
variable (e : Pretrivialization F proj) {x : Z}

/-- Coercion of a pretrivialization to a function. We don't use `e.toFun` in the `CoeFun` instance
because it is actually `e.toPartialEquiv.toFun`, so `simp` will apply lemmas about
`toPartialEquiv`. While we may want to switch to this behavior later, doing it mid-port will break a
lot of proofs. -/
@[coe] def toFun' : Z → (B × F) := e.toFun

instance : CoeFun (Pretrivialization F proj) fun _ => Z → B × F := ⟨toFun'⟩

@[ext]
lemma ext' (e e' : Pretrivialization F proj) (h₁ : e.toPartialEquiv = e'.toPartialEquiv)
    (h₂ : e.baseSet = e'.baseSet) : e = e' := by
  cases e; cases e'; congr

-- TODO: move `ext` here?
lemma ext {e e' : Pretrivialization F proj} (h₁ : ∀ x, e x = e' x)
    (h₂ : ∀ x, e.toPartialEquiv.symm x = e'.toPartialEquiv.symm x) (h₃ : e.baseSet = e'.baseSet) :
    e = e' := by
  ext1 <;> [ext1; exact h₃]
  · apply h₁
  · apply h₂
  · rw [e.source_eq, e'.source_eq, h₃]

/-- If the fiber is nonempty, then the projection also is. -/
lemma toPartialEquiv_injective [Nonempty F] :
    Injective (toPartialEquiv : Pretrivialization F proj → PartialEquiv Z (B × F)) := by
  refine fun e e' h ↦ ext' _ _ h ?_
  simpa only [fst_image_prod, univ_nonempty, target_eq]
    using congr_arg (Prod.fst '' PartialEquiv.target ·) h

@[simp, mfld_simps]
theorem coe_coe : ⇑e.toPartialEquiv = e :=
  rfl

@[simp, mfld_simps]
theorem coe_fst (ex : x ∈ e.source) : (e x).1 = proj x :=
  e.proj_toFun x ex

theorem mem_source : x ∈ e.source ↔ proj x ∈ e.baseSet := by rw [e.source_eq, mem_preimage]

theorem coe_fst' (ex : proj x ∈ e.baseSet) : (e x).1 = proj x :=
  e.coe_fst (e.mem_source.2 ex)

protected theorem eqOn : EqOn (Prod.fst ∘ e) proj e.source := fun _ hx => e.coe_fst hx

theorem mk_proj_snd (ex : x ∈ e.source) : (proj x, (e x).2) = e x :=
  Prod.ext (e.coe_fst ex).symm rfl

theorem mk_proj_snd' (ex : proj x ∈ e.baseSet) : (proj x, (e x).2) = e x :=
  Prod.ext (e.coe_fst' ex).symm rfl

/-- Composition of inverse and coercion from the subtype of the target. -/
def setSymm : e.target → Z :=
  e.target.restrict e.toPartialEquiv.symm

theorem mem_target {x : B × F} : x ∈ e.target ↔ x.1 ∈ e.baseSet := by
  rw [e.target_eq, prod_univ, mem_preimage]

theorem proj_symm_apply {x : B × F} (hx : x ∈ e.target) : proj (e.toPartialEquiv.symm x) = x.1 := by
  have := (e.coe_fst (e.map_target hx)).symm
  rwa [← e.coe_coe, e.right_inv hx] at this

theorem proj_symm_apply' {b : B} {x : F} (hx : b ∈ e.baseSet) :
    proj (e.toPartialEquiv.symm (b, x)) = b :=
  e.proj_symm_apply (e.mem_target.2 hx)

theorem proj_surjOn_baseSet [Nonempty F] : Set.SurjOn proj e.source e.baseSet := fun b hb =>
  let ⟨y⟩ := ‹Nonempty F›
  ⟨e.toPartialEquiv.symm (b, y), e.toPartialEquiv.map_target <| e.mem_target.2 hb,
    e.proj_symm_apply' hb⟩

theorem apply_symm_apply {x : B × F} (hx : x ∈ e.target) : e (e.toPartialEquiv.symm x) = x :=
  e.toPartialEquiv.right_inv hx

theorem apply_symm_apply' {b : B} {x : F} (hx : b ∈ e.baseSet) :
    e (e.toPartialEquiv.symm (b, x)) = (b, x) :=
  e.apply_symm_apply (e.mem_target.2 hx)

theorem symm_apply_apply {x : Z} (hx : x ∈ e.source) : e.toPartialEquiv.symm (e x) = x :=
  e.toPartialEquiv.left_inv hx

@[simp, mfld_simps]
theorem symm_apply_mk_proj {x : Z} (ex : x ∈ e.source) :
    e.toPartialEquiv.symm (proj x, (e x).2) = x := by
  rw [← e.coe_fst ex, ← e.coe_coe, e.left_inv ex]

@[simp, mfld_simps]
theorem preimage_symm_proj_baseSet :
    e.toPartialEquiv.symm ⁻¹' (proj ⁻¹' e.baseSet) ∩ e.target = e.target := by
  refine inter_eq_right.mpr fun x hx => ?_
  simp only [mem_preimage, e.proj_symm_apply hx]
  exact e.mem_target.mp hx

@[simp, mfld_simps]
theorem preimage_symm_proj_inter (s : Set B) :
    e.toPartialEquiv.symm ⁻¹' (proj ⁻¹' s) ∩ e.baseSet ×ˢ univ = (s ∩ e.baseSet) ×ˢ univ := by
  ext ⟨x, y⟩
  suffices x ∈ e.baseSet → (proj (e.toPartialEquiv.symm (x, y)) ∈ s ↔ x ∈ s) by
    simpa only [prodMk_mem_set_prod_eq, mem_inter_iff, and_true, mem_univ, and_congr_left_iff]
  intro h
  rw [e.proj_symm_apply' h]

theorem target_inter_preimage_symm_source_eq (e f : Pretrivialization F proj) :
    f.target ∩ f.toPartialEquiv.symm ⁻¹' e.source = (e.baseSet ∩ f.baseSet) ×ˢ univ := by
  rw [inter_comm, f.target_eq, e.source_eq, f.preimage_symm_proj_inter]

theorem trans_source (e f : Pretrivialization F proj) :
    (f.toPartialEquiv.symm.trans e.toPartialEquiv).source = (e.baseSet ∩ f.baseSet) ×ˢ univ := by
  rw [PartialEquiv.trans_source, PartialEquiv.symm_source, e.target_inter_preimage_symm_source_eq]

theorem symm_trans_symm (e e' : Pretrivialization F proj) :
    (e.toPartialEquiv.symm.trans e'.toPartialEquiv).symm
      = e'.toPartialEquiv.symm.trans e.toPartialEquiv := by
  rw [PartialEquiv.trans_symm_eq_symm_trans_symm, PartialEquiv.symm_symm]

theorem symm_trans_source_eq (e e' : Pretrivialization F proj) :
    (e.toPartialEquiv.symm.trans e'.toPartialEquiv).source = (e.baseSet ∩ e'.baseSet) ×ˢ univ := by
  rw [PartialEquiv.trans_source, e'.source_eq, PartialEquiv.symm_source, e.target_eq, inter_comm,
    e.preimage_symm_proj_inter, inter_comm]

theorem symm_trans_target_eq (e e' : Pretrivialization F proj) :
    (e.toPartialEquiv.symm.trans e'.toPartialEquiv).target = (e.baseSet ∩ e'.baseSet) ×ˢ univ := by
  rw [← PartialEquiv.symm_source, symm_trans_symm, symm_trans_source_eq, inter_comm]

variable (e' : Pretrivialization F (π F E)) {b : B} {y : E b}

@[simp]
theorem coe_mem_source : ↑y ∈ e'.source ↔ b ∈ e'.baseSet :=
  e'.mem_source

@[mfld_simps]
theorem coe_coe_fst (hb : b ∈ e'.baseSet) : (e' y).1 = b := by
  simp [hb]

theorem mk_mem_target {x : B} {y : F} : (x, y) ∈ e'.target ↔ x ∈ e'.baseSet :=
  e'.mem_target

theorem symm_coe_proj {x : B} {y : F} (e' : Pretrivialization F (π F E)) (h : x ∈ e'.baseSet) :
    (e'.toPartialEquiv.symm (x, y)).1 = x :=
  e'.proj_symm_apply' h

section Zero

variable [∀ x, Zero (E x)]

open Classical in
/-- A fiberwise inverse to `e`. This is the function `F → E b` that induces a local inverse
`B × F → TotalSpace F E` of `e` on `e.baseSet`. It is defined to be `0` outside `e.baseSet`. -/
protected noncomputable def symm (e : Pretrivialization F (π F E)) (b : B) (y : F) : E b :=
  if hb : b ∈ e.baseSet then
    cast (congr_arg E (e.proj_symm_apply' hb)) (e.toPartialEquiv.symm (b, y)).2
  else 0

theorem symm_apply (e : Pretrivialization F (π F E)) {b : B} (hb : b ∈ e.baseSet) (y : F) :
    e.symm b y = cast (congr_arg E (e.symm_coe_proj hb)) (e.toPartialEquiv.symm (b, y)).2 :=
  dif_pos hb

theorem symm_apply_of_notMem (e : Pretrivialization F (π F E)) {b : B} (hb : b ∉ e.baseSet)
    (y : F) : e.symm b y = 0 :=
  dif_neg hb

@[deprecated (since := "2025-05-23")] alias symm_apply_of_not_mem := symm_apply_of_notMem

theorem coe_symm_of_notMem (e : Pretrivialization F (π F E)) {b : B} (hb : b ∉ e.baseSet) :
    (e.symm b : F → E b) = 0 :=
  funext fun _ => dif_neg hb

@[deprecated (since := "2025-05-23")] alias coe_symm_of_not_mem := coe_symm_of_notMem

theorem mk_symm (e : Pretrivialization F (π F E)) {b : B} (hb : b ∈ e.baseSet) (y : F) :
    TotalSpace.mk b (e.symm b y) = e.toPartialEquiv.symm (b, y) := by
  simp only [e.symm_apply hb, TotalSpace.mk_cast (e.proj_symm_apply' hb), TotalSpace.eta]

theorem symm_proj_apply (e : Pretrivialization F (π F E)) (z : TotalSpace F E)
    (hz : z.proj ∈ e.baseSet) : e.symm z.proj (e z).2 = z.2 := by
  rw [e.symm_apply hz, cast_eq_iff_heq, e.mk_proj_snd' hz, e.symm_apply_apply (e.mem_source.mpr hz)]

theorem symm_apply_apply_mk (e : Pretrivialization F (π F E)) {b : B} (hb : b ∈ e.baseSet)
    (y : E b) : e.symm b (e ⟨b, y⟩).2 = y :=
  e.symm_proj_apply ⟨b, y⟩ hb

@[simp]
theorem apply_mk_symm (e : Pretrivialization F (π F E)) {b : B} (hb : b ∈ e.baseSet) (y : F) :
    e ⟨b, e.symm b y⟩ = (b, y) := by
  rw [e.mk_symm hb, e.apply_symm_apply (e.mk_mem_target.mpr hb)]

end Zero

end Pretrivialization

variable [TopologicalSpace Z] [TopologicalSpace (TotalSpace F E)]

/-- A structure extending open partial homeomorphisms, defining a local trivialization of a
projection `proj : Z → B` with fiber `F`, as an open partial homeomorphism between `Z` and `B × F`
defined between two sets of the form `proj ⁻¹' baseSet` and `baseSet × F`, acting trivially on the
first coordinate.
-/
structure Trivialization (proj : Z → B) extends OpenPartialHomeomorph Z (B × F) where
  /-- The domain of the local trivialisation (i.e., a subset of the bundle `Z`'s base):
  outside of it, the pretrivialisation returns a junk value -/
  baseSet : Set B
  open_baseSet : IsOpen baseSet
  source_eq : source = proj ⁻¹' baseSet
  target_eq : target = baseSet ×ˢ univ
  proj_toFun : ∀ p ∈ source, (toOpenPartialHomeomorph p).1 = proj p

namespace Trivialization

variable {F}
variable (e : Trivialization F proj) {x : Z}

@[ext]
lemma ext' (e e' : Trivialization F proj)
    (h₁ : e.toOpenPartialHomeomorph = e'.toOpenPartialHomeomorph) (h₂ : e.baseSet = e'.baseSet) :
    e = e' := by
  cases e; cases e'; congr

/-- Coercion of a trivialization to a function. We don't use `e.toFun` in the `CoeFun` instance
because it is actually `e.toPartialEquiv.toFun`, so `simp` will apply lemmas about
`toPartialEquiv`. While we may want to switch to this behavior later, doing it mid-port will break a
lot of proofs. -/
@[coe] def toFun' : Z → (B × F) := e.toFun

/-- Natural identification as a `Pretrivialization`. -/
def toPretrivialization : Pretrivialization F proj :=
  { e with }

instance : CoeFun (Trivialization F proj) fun _ => Z → B × F := ⟨toFun'⟩

instance : Coe (Trivialization F proj) (Pretrivialization F proj) :=
  ⟨toPretrivialization⟩

/-- See Note [custom simps projection] -/
def Simps.apply (proj : Z → B) (e : Trivialization F proj) : Z → B × F := e

/-- See Note [custom simps projection] -/
noncomputable def Simps.symm_apply (proj : Z → B) (e : Trivialization F proj) : B × F → Z :=
  e.toOpenPartialHomeomorph.symm

initialize_simps_projections Trivialization (toFun → apply, invFun → symm_apply)

theorem toPretrivialization_injective :
    Function.Injective fun e : Trivialization F proj => e.toPretrivialization := fun e e' h => by
  ext1
  exacts [OpenPartialHomeomorph.toPartialEquiv_injective
    (congr_arg Pretrivialization.toPartialEquiv h), congr_arg Pretrivialization.baseSet h]

@[simp, mfld_simps]
theorem coe_coe : ⇑e.toOpenPartialHomeomorph = e :=
  rfl

@[simp, mfld_simps]
theorem coe_fst (ex : x ∈ e.source) : (e x).1 = proj x :=
  e.proj_toFun x ex

protected theorem eqOn : EqOn (Prod.fst ∘ e) proj e.source := fun _x hx => e.coe_fst hx

theorem mem_source : x ∈ e.source ↔ proj x ∈ e.baseSet := by rw [e.source_eq, mem_preimage]

theorem coe_fst' (ex : proj x ∈ e.baseSet) : (e x).1 = proj x :=
  e.coe_fst (e.mem_source.2 ex)

theorem mk_proj_snd (ex : x ∈ e.source) : (proj x, (e x).2) = e x :=
  Prod.ext (e.coe_fst ex).symm rfl

theorem mk_proj_snd' (ex : proj x ∈ e.baseSet) : (proj x, (e x).2) = e x :=
  Prod.ext (e.coe_fst' ex).symm rfl

theorem source_inter_preimage_target_inter (s : Set (B × F)) :
    e.source ∩ e ⁻¹' (e.target ∩ s) = e.source ∩ e ⁻¹' s :=
  e.toOpenPartialHomeomorph.source_inter_preimage_target_inter s

@[simp, mfld_simps]
theorem coe_mk (e : OpenPartialHomeomorph Z (B × F)) (i j k l m) (x : Z) :
    (Trivialization.mk e i j k l m : Trivialization F proj) x = e x :=
  rfl

theorem mem_target {x : B × F} : x ∈ e.target ↔ x.1 ∈ e.baseSet :=
  e.toPretrivialization.mem_target

theorem map_target {x : B × F} (hx : x ∈ e.target) : e.toOpenPartialHomeomorph.symm x ∈ e.source :=
  e.toOpenPartialHomeomorph.map_target hx

theorem proj_symm_apply {x : B × F} (hx : x ∈ e.target) :
    proj (e.toOpenPartialHomeomorph.symm x) = x.1 :=
  e.toPretrivialization.proj_symm_apply hx

theorem proj_symm_apply' {b : B} {x : F} (hx : b ∈ e.baseSet) :
    proj (e.toOpenPartialHomeomorph.symm (b, x)) = b :=
  e.toPretrivialization.proj_symm_apply' hx

theorem proj_surjOn_baseSet [Nonempty F] : Set.SurjOn proj e.source e.baseSet :=
  e.toPretrivialization.proj_surjOn_baseSet

theorem apply_symm_apply {x : B × F} (hx : x ∈ e.target) :
    e (e.toOpenPartialHomeomorph.symm x) = x :=
  e.toOpenPartialHomeomorph.right_inv hx

theorem apply_symm_apply' {b : B} {x : F} (hx : b ∈ e.baseSet) :
    e (e.toOpenPartialHomeomorph.symm (b, x)) = (b, x) :=
  e.toPretrivialization.apply_symm_apply' hx

@[simp, mfld_simps]
theorem symm_apply_mk_proj (ex : x ∈ e.source) :
    e.toOpenPartialHomeomorph.symm (proj x, (e x).2) = x :=
  e.toPretrivialization.symm_apply_mk_proj ex

theorem symm_trans_source_eq (e e' : Trivialization F proj) :
    (e.toPartialEquiv.symm.trans e'.toPartialEquiv).source = (e.baseSet ∩ e'.baseSet) ×ˢ univ :=
  Pretrivialization.symm_trans_source_eq e.toPretrivialization e'

theorem symm_trans_target_eq (e e' : Trivialization F proj) :
    (e.toPartialEquiv.symm.trans e'.toPartialEquiv).target = (e.baseSet ∩ e'.baseSet) ×ˢ univ :=
  Pretrivialization.symm_trans_target_eq e.toPretrivialization e'

theorem coe_fst_eventuallyEq_proj (ex : x ∈ e.source) : Prod.fst ∘ e =ᶠ[𝓝 x] proj :=
  mem_nhds_iff.2 ⟨e.source, fun _y hy => e.coe_fst hy, e.open_source, ex⟩

theorem coe_fst_eventuallyEq_proj' (ex : proj x ∈ e.baseSet) : Prod.fst ∘ e =ᶠ[𝓝 x] proj :=
  e.coe_fst_eventuallyEq_proj (e.mem_source.2 ex)

theorem map_proj_nhds (ex : x ∈ e.source) : map proj (𝓝 x) = 𝓝 (proj x) := by
  rw [← e.coe_fst ex, ← map_congr (e.coe_fst_eventuallyEq_proj ex), ← map_map, ← e.coe_coe,
    e.map_nhds_eq ex, map_fst_nhds]

theorem preimage_subset_source {s : Set B} (hb : s ⊆ e.baseSet) : proj ⁻¹' s ⊆ e.source :=
  fun _p hp => e.mem_source.mpr (hb hp)

theorem image_preimage_eq_prod_univ {s : Set B} (hb : s ⊆ e.baseSet) :
    e '' (proj ⁻¹' s) = s ×ˢ univ :=
  Subset.antisymm
    (image_subset_iff.mpr fun p hp =>
      ⟨(e.proj_toFun p (e.preimage_subset_source hb hp)).symm ▸ hp, trivial⟩)
    fun p hp =>
    let hp' : p ∈ e.target := e.mem_target.mpr (hb hp.1)
    ⟨e.invFun p, mem_preimage.mpr ((e.proj_symm_apply hp').symm ▸ hp.1), e.apply_symm_apply hp'⟩

theorem tendsto_nhds_iff {α : Type*} {l : Filter α} {f : α → Z} {z : Z} (hz : z ∈ e.source) :
    Tendsto f l (𝓝 z) ↔
      Tendsto (proj ∘ f) l (𝓝 (proj z)) ∧ Tendsto (fun x ↦ (e (f x)).2) l (𝓝 (e z).2) := by
  rw [e.nhds_eq_comap_inf_principal hz, tendsto_inf, tendsto_comap_iff, Prod.tendsto_iff, coe_coe,
    tendsto_principal, coe_fst _ hz]
  by_cases hl : ∀ᶠ x in l, f x ∈ e.source
  · simp only [hl, and_true]
    refine (tendsto_congr' ?_).and Iff.rfl
    exact hl.mono fun x ↦ e.coe_fst
  · simp only [hl, and_false, false_iff, not_and]
    rw [e.source_eq] at hl hz
    exact fun h _ ↦ hl <| h <| e.open_baseSet.mem_nhds hz

theorem nhds_eq_inf_comap {z : Z} (hz : z ∈ e.source) :
    𝓝 z = comap proj (𝓝 (proj z)) ⊓ comap (Prod.snd ∘ e) (𝓝 (e z).2) := by
  refine eq_of_forall_le_iff fun l ↦ ?_
  rw [le_inf_iff, ← tendsto_iff_comap, ← tendsto_iff_comap]
  exact e.tendsto_nhds_iff hz

/-- The preimage of a subset of the base set is homeomorphic to the product with the fiber. -/
def preimageHomeomorph {s : Set B} (hb : s ⊆ e.baseSet) : proj ⁻¹' s ≃ₜ s × F :=
  (e.toOpenPartialHomeomorph.homeomorphOfImageSubsetSource (e.preimage_subset_source hb)
        (e.image_preimage_eq_prod_univ hb)).trans
    ((Homeomorph.Set.prod s univ).trans ((Homeomorph.refl s).prodCongr (Homeomorph.Set.univ F)))

@[simp]
theorem preimageHomeomorph_apply {s : Set B} (hb : s ⊆ e.baseSet) (p : proj ⁻¹' s) :
    e.preimageHomeomorph hb p = (⟨proj p, p.2⟩, (e p).2) :=
  Prod.ext (Subtype.ext (e.proj_toFun p (e.mem_source.mpr (hb p.2)))) rfl

/-- Auxiliary definition to avoid looping in `dsimp`
with `Trivialization.preimageHomeomorph_symm_apply`. -/
protected def preimageHomeomorph_symm_apply.aux {s : Set B} (hb : s ⊆ e.baseSet) :=
  (e.preimageHomeomorph hb).symm

@[simp]
theorem preimageHomeomorph_symm_apply {s : Set B} (hb : s ⊆ e.baseSet) (p : s × F) :
    (e.preimageHomeomorph hb).symm p =
      ⟨e.symm (p.1, p.2), ((preimageHomeomorph_symm_apply.aux e hb) p).2⟩ :=
  rfl

/-- The source is homeomorphic to the product of the base set with the fiber. -/
def sourceHomeomorphBaseSetProd : e.source ≃ₜ e.baseSet × F :=
  (Homeomorph.setCongr e.source_eq).trans (e.preimageHomeomorph subset_rfl)

@[simp]
theorem sourceHomeomorphBaseSetProd_apply (p : e.source) :
    e.sourceHomeomorphBaseSetProd p = (⟨proj p, e.mem_source.mp p.2⟩, (e p).2) :=
  e.preimageHomeomorph_apply subset_rfl ⟨p, e.mem_source.mp p.2⟩

/-- Auxiliary definition to avoid looping in `dsimp`
with `Trivialization.sourceHomeomorphBaseSetProd_symm_apply`. -/
protected def sourceHomeomorphBaseSetProd_symm_apply.aux := e.sourceHomeomorphBaseSetProd.symm

@[simp]
theorem sourceHomeomorphBaseSetProd_symm_apply (p : e.baseSet × F) :
    e.sourceHomeomorphBaseSetProd.symm p =
      ⟨e.symm (p.1, p.2), (sourceHomeomorphBaseSetProd_symm_apply.aux e p).2⟩ :=
  rfl

/-- Each fiber of a trivialization is homeomorphic to the specified fiber. -/
def preimageSingletonHomeomorph {b : B} (hb : b ∈ e.baseSet) : proj ⁻¹' {b} ≃ₜ F :=
  .trans (e.preimageHomeomorph (Set.singleton_subset_iff.mpr hb)) <|
    .trans (.prodCongr (Homeomorph.homeomorphOfUnique ({b} : Set B) PUnit.{1}) (Homeomorph.refl F))
      (Homeomorph.punitProd F)

@[simp]
theorem preimageSingletonHomeomorph_apply {b : B} (hb : b ∈ e.baseSet) (p : proj ⁻¹' {b}) :
    e.preimageSingletonHomeomorph hb p = (e p).2 :=
  rfl

@[simp]
theorem preimageSingletonHomeomorph_symm_apply {b : B} (hb : b ∈ e.baseSet) (p : F) :
    (e.preimageSingletonHomeomorph hb).symm p =
      ⟨e.symm (b, p), by rw [mem_preimage, e.proj_symm_apply' hb, mem_singleton_iff]⟩ :=
  rfl

/-- In the domain of a bundle trivialization, the projection is continuous -/
theorem continuousAt_proj (ex : x ∈ e.source) : ContinuousAt proj x :=
  (e.map_proj_nhds ex).le

theorem continuousOn_proj : ContinuousOn proj e.source :=
  continuousOn_of_forall_continuousAt fun _ ↦ e.continuousAt_proj

/-- Composition of a `Trivialization` and a `Homeomorph`. -/
protected def compHomeomorph {Z' : Type*} [TopologicalSpace Z'] (h : Z' ≃ₜ Z) :
    Trivialization F (proj ∘ h) where
  toOpenPartialHomeomorph := h.toOpenPartialHomeomorph.trans e.toOpenPartialHomeomorph
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := by simp [source_eq, preimage_preimage, Function.comp_def]
  target_eq := by simp [target_eq]
  proj_toFun p hp := by
    have hp : h p ∈ e.source := by simpa using hp
    simp [hp]

/-- Read off the continuity of a function `f : Z → X` at `z : Z` by transferring via a
trivialization of `Z` containing `z`. -/
theorem continuousAt_of_comp_right {X : Type*} [TopologicalSpace X] {f : Z → X} {z : Z}
    (e : Trivialization F proj) (he : proj z ∈ e.baseSet)
    (hf : ContinuousAt (f ∘ e.toPartialEquiv.symm) (e z)) : ContinuousAt f z := by
  have hez : z ∈ e.toPartialEquiv.symm.target := by
    rw [PartialEquiv.symm_target, e.mem_source]
    exact he
  rwa [e.toOpenPartialHomeomorph.symm.continuousAt_iff_continuousAt_comp_right hez,
    OpenPartialHomeomorph.symm_symm]

/-- Read off the continuity of a function `f : X → Z` at `x : X` by transferring via a
trivialization of `Z` containing `f x`. -/
theorem continuousAt_of_comp_left {X : Type*} [TopologicalSpace X] {f : X → Z} {x : X}
    (e : Trivialization F proj) (hf_proj : ContinuousAt (proj ∘ f) x) (he : proj (f x) ∈ e.baseSet)
    (hf : ContinuousAt (e ∘ f) x) : ContinuousAt f x := by
  rw [e.continuousAt_iff_continuousAt_comp_left]
  · exact hf
  rw [e.source_eq, ← preimage_comp]
  exact hf_proj.preimage_mem_nhds (e.open_baseSet.mem_nhds he)

variable (e' : Trivialization F (π F E)) {b : B} {y : E b}

protected theorem continuousOn : ContinuousOn e' e'.source :=
  e'.continuousOn_toFun

theorem coe_mem_source : ↑y ∈ e'.source ↔ b ∈ e'.baseSet :=
  e'.mem_source

@[simp, mfld_simps]
theorem coe_coe_fst (hb : b ∈ e'.baseSet) : (e' y).1 = b :=
  e'.coe_fst (e'.mem_source.2 hb)

theorem mk_mem_target {y : F} : (b, y) ∈ e'.target ↔ b ∈ e'.baseSet :=
  e'.toPretrivialization.mem_target

theorem symm_apply_apply {x : TotalSpace F E} (hx : x ∈ e'.source) :
    e'.toOpenPartialHomeomorph.symm (e' x) = x :=
  e'.toPartialEquiv.left_inv hx

@[simp, mfld_simps]
theorem symm_coe_proj {x : B} {y : F} (e : Trivialization F (π F E)) (h : x ∈ e.baseSet) :
    (e.toOpenPartialHomeomorph.symm (x, y)).1 = x :=
  e.proj_symm_apply' h

section Zero

variable [∀ x, Zero (E x)]

/-- A fiberwise inverse to `e'`. The function `F → E x` that induces a local inverse
`B × F → TotalSpace F E` of `e'` on `e'.baseSet`. It is defined to be `0` outside `e'.baseSet`. -/
protected noncomputable def symm (e : Trivialization F (π F E)) (b : B) (y : F) : E b :=
  e.toPretrivialization.symm b y

theorem symm_apply (e : Trivialization F (π F E)) {b : B} (hb : b ∈ e.baseSet) (y : F) :
    e.symm b y =
      cast (congr_arg E (e.symm_coe_proj hb)) (e.toOpenPartialHomeomorph.symm (b, y)).2 :=
  dif_pos hb

theorem symm_apply_of_notMem (e : Trivialization F (π F E)) {b : B} (hb : b ∉ e.baseSet) (y : F) :
    e.symm b y = 0 :=
  dif_neg hb

@[deprecated (since := "2025-05-23")] alias symm_apply_of_not_mem := symm_apply_of_notMem

theorem mk_symm (e : Trivialization F (π F E)) {b : B} (hb : b ∈ e.baseSet) (y : F) :
    TotalSpace.mk b (e.symm b y) = e.toOpenPartialHomeomorph.symm (b, y) :=
  e.toPretrivialization.mk_symm hb y

theorem symm_proj_apply (e : Trivialization F (π F E)) (z : TotalSpace F E)
    (hz : z.proj ∈ e.baseSet) : e.symm z.proj (e z).2 = z.2 :=
  e.toPretrivialization.symm_proj_apply z hz

theorem symm_apply_apply_mk (e : Trivialization F (π F E)) {b : B} (hb : b ∈ e.baseSet) (y : E b) :
    e.symm b (e ⟨b, y⟩).2 = y :=
  e.symm_proj_apply ⟨b, y⟩ hb

@[simp, mfld_simps]
theorem apply_mk_symm (e : Trivialization F (π F E)) {b : B} (hb : b ∈ e.baseSet) (y : F) :
    e ⟨b, e.symm b y⟩ = (b, y) :=
  e.toPretrivialization.apply_mk_symm hb y

theorem continuousOn_symm (e : Trivialization F (π F E)) :
    ContinuousOn (fun z : B × F => TotalSpace.mk' F z.1 (e.symm z.1 z.2)) (e.baseSet ×ˢ univ) := by
  have : ∀ z ∈ e.baseSet ×ˢ (univ : Set F),
      TotalSpace.mk z.1 (e.symm z.1 z.2) = e.toOpenPartialHomeomorph.symm z := by
    rintro x ⟨hx : x.1 ∈ e.baseSet, _⟩
    rw [e.mk_symm hx]
  refine ContinuousOn.congr ?_ this
  rw [← e.target_eq]
  exact e.toOpenPartialHomeomorph.continuousOn_symm

end Zero

/-- If `e` is a `Trivialization` of `proj : Z → B` with fiber `F` and `h` is a homeomorphism
`F ≃ₜ F'`, then `e.trans_fiber_homeomorph h` is the trivialization of `proj` with the fiber `F'`
that sends `p : Z` to `((e p).1, h (e p).2)`. -/
def transFiberHomeomorph {F' : Type*} [TopologicalSpace F'] (e : Trivialization F proj)
    (h : F ≃ₜ F') : Trivialization F' proj where
  toOpenPartialHomeomorph :=
    e.toOpenPartialHomeomorph.transHomeomorph <| (Homeomorph.refl _).prodCongr h
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := e.source_eq
  target_eq := by simp [target_eq, prod_univ, preimage_preimage]
  proj_toFun := e.proj_toFun

@[simp]
theorem transFiberHomeomorph_apply {F' : Type*} [TopologicalSpace F'] (e : Trivialization F proj)
    (h : F ≃ₜ F') (x : Z) : e.transFiberHomeomorph h x = ((e x).1, h (e x).2) :=
  rfl

/-- Coordinate transformation in the fiber induced by a pair of bundle trivializations. See also
`Trivialization.coordChangeHomeomorph` for a version bundled as `F ≃ₜ F`. -/
def coordChange (e₁ e₂ : Trivialization F proj) (b : B) (x : F) : F :=
  (e₂ <| e₁.toOpenPartialHomeomorph.symm (b, x)).2

theorem mk_coordChange (e₁ e₂ : Trivialization F proj) {b : B} (h₁ : b ∈ e₁.baseSet)
    (h₂ : b ∈ e₂.baseSet) (x : F) :
    (b, e₁.coordChange e₂ b x) = e₂ (e₁.toOpenPartialHomeomorph.symm (b, x)) := by
  refine Prod.ext ?_ rfl
  rw [e₂.coe_fst', ← e₁.coe_fst', e₁.apply_symm_apply' h₁]
  · rwa [e₁.proj_symm_apply' h₁]
  · rwa [e₁.proj_symm_apply' h₁]

theorem coordChange_apply_snd (e₁ e₂ : Trivialization F proj) {p : Z} (h : proj p ∈ e₁.baseSet) :
    e₁.coordChange e₂ (proj p) (e₁ p).snd = (e₂ p).snd := by
  rw [coordChange, e₁.symm_apply_mk_proj (e₁.mem_source.2 h)]

theorem coordChange_same_apply (e : Trivialization F proj) {b : B} (h : b ∈ e.baseSet) (x : F) :
    e.coordChange e b x = x := by rw [coordChange, e.apply_symm_apply' h]

theorem coordChange_same (e : Trivialization F proj) {b : B} (h : b ∈ e.baseSet) :
    e.coordChange e b = id :=
  funext <| e.coordChange_same_apply h

theorem coordChange_coordChange (e₁ e₂ e₃ : Trivialization F proj) {b : B} (h₁ : b ∈ e₁.baseSet)
    (h₂ : b ∈ e₂.baseSet) (x : F) :
    e₂.coordChange e₃ b (e₁.coordChange e₂ b x) = e₁.coordChange e₃ b x := by
  rw [coordChange, e₁.mk_coordChange _ h₁ h₂, ← e₂.coe_coe, e₂.left_inv, coordChange]
  rwa [e₂.mem_source, e₁.proj_symm_apply' h₁]

theorem continuous_coordChange (e₁ e₂ : Trivialization F proj) {b : B} (h₁ : b ∈ e₁.baseSet)
    (h₂ : b ∈ e₂.baseSet) : Continuous (e₁.coordChange e₂ b) := by
  refine continuous_snd.comp (e₂.toOpenPartialHomeomorph.continuousOn.comp_continuous
    (e₁.toOpenPartialHomeomorph.continuousOn_symm.comp_continuous ?_ ?_) ?_)
  · fun_prop
  · exact fun x => e₁.mem_target.2 h₁
  · intro x
    rwa [e₂.mem_source, e₁.proj_symm_apply' h₁]

/-- Coordinate transformation in the fiber induced by a pair of bundle trivializations,
as a homeomorphism. -/
protected def coordChangeHomeomorph (e₁ e₂ : Trivialization F proj) {b : B} (h₁ : b ∈ e₁.baseSet)
    (h₂ : b ∈ e₂.baseSet) : F ≃ₜ F where
  toFun := e₁.coordChange e₂ b
  invFun := e₂.coordChange e₁ b
  left_inv x := by simp only [*, coordChange_coordChange, coordChange_same_apply]
  right_inv x := by simp only [*, coordChange_coordChange, coordChange_same_apply]
  continuous_toFun := e₁.continuous_coordChange e₂ h₁ h₂
  continuous_invFun := e₂.continuous_coordChange e₁ h₂ h₁

@[simp]
theorem coordChangeHomeomorph_coe (e₁ e₂ : Trivialization F proj) {b : B} (h₁ : b ∈ e₁.baseSet)
    (h₂ : b ∈ e₂.baseSet) : ⇑(e₁.coordChangeHomeomorph e₂ h₁ h₂) = e₁.coordChange e₂ b :=
  rfl

theorem isImage_preimage_prod (e : Trivialization F proj) (s : Set B) :
    e.toOpenPartialHomeomorph.IsImage (proj ⁻¹' s) (s ×ˢ univ) := fun x hx => by simp [hx]

/-- Restrict a `Trivialization` to an open set in the base. -/
protected def restrOpen (e : Trivialization F proj) (s : Set B) (hs : IsOpen s) :
    Trivialization F proj where
  toOpenPartialHomeomorph :=
    ((e.isImage_preimage_prod s).symm.restr (IsOpen.inter e.open_target (hs.prod isOpen_univ))).symm
  baseSet := e.baseSet ∩ s
  open_baseSet := IsOpen.inter e.open_baseSet hs
  source_eq := by simp [source_eq]
  target_eq := by simp [target_eq, prod_univ]
  proj_toFun p hp := e.proj_toFun p hp.1

section Piecewise

theorem frontier_preimage (e : Trivialization F proj) (s : Set B) :
    e.source ∩ frontier (proj ⁻¹' s) = proj ⁻¹' (e.baseSet ∩ frontier s) := by
  rw [← (e.isImage_preimage_prod s).frontier.preimage_eq, frontier_prod_univ_eq,
    (e.isImage_preimage_prod _).preimage_eq, e.source_eq, preimage_inter]

open Classical in
/-- Given two bundle trivializations `e`, `e'` of `proj : Z → B` and a set `s : Set B` such that
the base sets of `e` and `e'` intersect `frontier s` on the same set and `e p = e' p` whenever
`proj p ∈ e.baseSet ∩ frontier s`, `e.piecewise e' s Hs Heq` is the bundle trivialization over
`Set.ite s e.baseSet e'.baseSet` that is equal to `e` on `proj ⁻¹ s` and is equal to `e'`
otherwise. -/
noncomputable def piecewise (e e' : Trivialization F proj) (s : Set B)
    (Hs : e.baseSet ∩ frontier s = e'.baseSet ∩ frontier s)
    (Heq : EqOn e e' <| proj ⁻¹' (e.baseSet ∩ frontier s)) : Trivialization F proj where
  toOpenPartialHomeomorph :=
    e.toOpenPartialHomeomorph.piecewise e'.toOpenPartialHomeomorph (proj ⁻¹' s) (s ×ˢ univ)
      (e.isImage_preimage_prod s) (e'.isImage_preimage_prod s)
      (by rw [e.frontier_preimage, e'.frontier_preimage, Hs]) (by rwa [e.frontier_preimage])
  baseSet := s.ite e.baseSet e'.baseSet
  open_baseSet := e.open_baseSet.ite e'.open_baseSet Hs
  source_eq := by simp [source_eq]
  target_eq := by simp [target_eq, prod_univ]
  proj_toFun p := by
    rintro (⟨he, hs⟩ | ⟨he, hs⟩) <;> simp [*]

/-- Given two bundle trivializations `e`, `e'` of a topological fiber bundle `proj : Z → B`
over a linearly ordered base `B` and a point `a ∈ e.baseSet ∩ e'.baseSet` such that
`e` equals `e'` on `proj ⁻¹' {a}`, `e.piecewise_le_of_eq e' a He He' Heq` is the bundle
trivialization over `Set.ite (Iic a) e.baseSet e'.baseSet` that is equal to `e` on points `p`
such that `proj p ≤ a` and is equal to `e'` otherwise. -/
noncomputable def piecewiseLeOfEq [LinearOrder B] [OrderTopology B] (e e' : Trivialization F proj)
    (a : B) (He : a ∈ e.baseSet) (He' : a ∈ e'.baseSet) (Heq : ∀ p, proj p = a → e p = e' p) :
    Trivialization F proj :=
  e.piecewise e' (Iic a)
    (Set.ext fun x => and_congr_left_iff.2 fun hx => by
      obtain rfl : x = a := mem_singleton_iff.1 (frontier_Iic_subset _ hx)
      simp [He, He'])
    fun p hp => Heq p <| frontier_Iic_subset _ hp.2

/-- Given two bundle trivializations `e`, `e'` of a topological fiber bundle `proj : Z → B` over a
linearly ordered base `B` and a point `a ∈ e.baseSet ∩ e'.baseSet`, `e.piecewise_le e' a He He'`
is the bundle trivialization over `Set.ite (Iic a) e.baseSet e'.baseSet` that is equal to `e` on
points `p` such that `proj p ≤ a` and is equal to `((e' p).1, h (e' p).2)` otherwise, where
`h = e'.coord_change_homeomorph e _ _` is the homeomorphism of the fiber such that
`h (e' p).2 = (e p).2` whenever `e p = a`. -/
noncomputable def piecewiseLe [LinearOrder B] [OrderTopology B] (e e' : Trivialization F proj)
    (a : B) (He : a ∈ e.baseSet) (He' : a ∈ e'.baseSet) : Trivialization F proj :=
  e.piecewiseLeOfEq (e'.transFiberHomeomorph (e'.coordChangeHomeomorph e He' He)) a He He' <| by
    rintro p rfl
    ext1
    · simp [e.coe_fst', e'.coe_fst', *]
    · simp [coordChange_apply_snd, *]

open Classical in
/-- Given two bundle trivializations `e`, `e'` over disjoint sets, `e.disjoint_union e' H` is the
bundle trivialization over the union of the base sets that agrees with `e` and `e'` over their
base sets. -/
noncomputable def disjointUnion (e e' : Trivialization F proj) (H : Disjoint e.baseSet e'.baseSet) :
    Trivialization F proj where
  toOpenPartialHomeomorph :=
    e.toOpenPartialHomeomorph.disjointUnion e'.toOpenPartialHomeomorph
      (by
        rw [e.source_eq, e'.source_eq]
        exact H.preimage _)
      (by
        rw [e.target_eq, e'.target_eq, disjoint_iff_inf_le]
        intro x hx
        exact H.le_bot ⟨hx.1.1, hx.2.1⟩)
  baseSet := e.baseSet ∪ e'.baseSet
  open_baseSet := IsOpen.union e.open_baseSet e'.open_baseSet
  source_eq := congr_arg₂ (· ∪ ·) e.source_eq e'.source_eq
  target_eq := (congr_arg₂ (· ∪ ·) e.target_eq e'.target_eq).trans union_prod.symm
  proj_toFun := by
    rintro p (hp | hp')
    · change (e.source.piecewise e e' p).1 = proj p
      rw [piecewise_eq_of_mem, e.coe_fst] <;> exact hp
    · change (e.source.piecewise e e' p).1 = proj p
      rw [piecewise_eq_of_notMem, e'.coe_fst hp']
      simp only [source_eq] at hp' ⊢
      exact fun h => H.le_bot ⟨h, hp'⟩

end Piecewise

section Lift

/-- The local lifting through a Trivialization `T` from the base to the leaf containing `z`. -/
def lift (T : Trivialization F proj) (z : Z) (b : B) : Z := T.invFun (b, (T z).2)

variable {T : Trivialization F proj} {z : Z} {b : B}

@[simp]
theorem lift_self (he : proj z ∈ T.baseSet) : T.lift z (proj z) = z :=
  symm_apply_mk_proj _ <| T.mem_source.2 he

theorem proj_lift (hx : b ∈ T.baseSet) : proj (T.lift z b) = b :=
  T.proj_symm_apply <| T.mem_target.2 hx

/-- The restriction of `lift` to the source and base set of `T`, as a bundled continuous map. -/
def liftCM (T : Trivialization F proj) : C(T.source × T.baseSet, T.source) where
  toFun ex := ⟨T.lift ex.1 ex.2, T.map_target (by simp [mem_target])⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    refine T.continuousOn_invFun.comp_continuous ?_ (by simp [mem_target])
    refine .prodMk (by fun_prop) (.snd ?_)
    exact T.continuousOn_toFun.comp_continuous (by fun_prop) (by simp)

variable {ι : Type*} [TopologicalSpace ι] [LocallyCompactPair ι T.baseSet]
  {γ : C(ι, T.baseSet)} {i : ι} {e : T.source}

/-- Extension of `liftCM` to continuous maps taking values in `T.baseSet` (local version of
homotopy lifting) -/
def clift (T : Trivialization F proj) [LocallyCompactPair ι T.baseSet] :
    C(T.source × C(ι, T.baseSet), C(ι, T.source)) := by
  let Ψ : C((T.source × C(ι, T.baseSet)) × ι, C(ι, T.baseSet) × ι) :=
    ⟨fun eγt => (eγt.1.2, eγt.2), by fun_prop⟩
  refine ContinuousMap.curry <| T.liftCM.comp <| ⟨fun eγt => ⟨eγt.1.1, eγt.1.2 eγt.2⟩, ?_⟩
  simpa using ⟨by fun_prop, ContinuousEval.continuous_eval.comp Ψ.continuous⟩

@[simp]
theorem clift_self (h : proj e.1 = γ i) :
    T.clift (e, γ) i = e := by
  have : proj e ∈ T.baseSet := by simp [h]
  simp [clift, liftCM, ← h, lift_self, this]

theorem proj_clift : proj (T.clift (e, γ) i) = γ i := by
  simp [clift, liftCM, proj_lift]

end Lift

end Trivialization
