/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.PartialHomeomorph.Basic
/-!
# Partial homeomorphisms: Images of sets

## Main definitions

* `PartialHomeomorph.IsImage`: predicate for when one set is an image of another
* `PartialHomeomorph.ofSet`: the identity on a set `s`
* `PartialHomeomorph.EqOnSource`: equivalence relation describing the "right" notion of equality
  for partial homeomorphisms

## Implementation notes

Most statements are copied from their `PartialEquiv` versions, although some care is required.

For design notes, see `PartialEquiv.lean`.

### Local coding conventions

If a lemma deals with the intersection of a set with either source or target of a `PartialEquiv`,
then it should use `e.source ∩ s` or `e.target ∩ t`, not `s ∩ e.source` or `t ∩ e.target`.
-/

@[expose] public section

open Function Set Filter Topology

variable {X X' : Type*} {Y Y' : Type*} {Z Z' : Type*}
  [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Y']
  [TopologicalSpace Z] [TopologicalSpace Z']

namespace PartialHomeomorph

variable (e : PartialHomeomorph X Y)

section IsImage

/-!
## `OpenPartialHomeomorph.IsImage` relation

We say that `t : Set Y` is an image of `s : Set X` under an open partial homeomorphism `e` if any of
the following equivalent conditions hold:

* `e '' (e.source ∩ s) = e.target ∩ t`;
* `e.source ∩ e ⁻¹ t = e.source ∩ s`;
* `∀ x ∈ e.source, e x ∈ t ↔ x ∈ s` (this one is used in the definition).

This definition is a restatement of `PartialEquiv.IsImage` for open partial homeomorphisms.
In this section we transfer API about `PartialEquiv.IsImage` to open partial homeomorphisms and
add a few `OpenPartialHomeomorph`-specific lemmas like `OpenPartialHomeomorph.IsImage.closure`.
-/

/-- We say that `t : Set Y` is an image of `s : Set X` under an open partial homeomorphism `e`
if any of the following equivalent conditions hold:

* `e '' (e.source ∩ s) = e.target ∩ t`;
* `e.source ∩ e ⁻¹ t = e.source ∩ s`;
* `∀ x ∈ e.source, e x ∈ t ↔ x ∈ s` (this one is used in the definition).
-/
def IsImage (s : Set X) (t : Set Y) : Prop :=
  ∀ ⦃x⦄, x ∈ e.source → (e x ∈ t ↔ x ∈ s)

namespace IsImage

variable {e} {s : Set X} {t : Set Y} {x : X} {y : Y}

theorem toPartialEquiv (h : e.IsImage s t) : e.toPartialEquiv.IsImage s t :=
  h

theorem apply_mem_iff (h : e.IsImage s t) (hx : x ∈ e.source) : e x ∈ t ↔ x ∈ s :=
  h hx

protected theorem symm (h : e.IsImage s t) : e.symm.IsImage t s :=
  h.toPartialEquiv.symm

theorem symm_apply_mem_iff (h : e.IsImage s t) (hy : y ∈ e.target) : e.symm y ∈ s ↔ y ∈ t :=
  h.symm hy

@[simp]
theorem symm_iff : e.symm.IsImage t s ↔ e.IsImage s t :=
  ⟨fun h => h.symm, fun h => h.symm⟩

protected theorem mapsTo (h : e.IsImage s t) : MapsTo e (e.source ∩ s) (e.target ∩ t) :=
  h.toPartialEquiv.mapsTo

theorem symm_mapsTo (h : e.IsImage s t) : MapsTo e.symm (e.target ∩ t) (e.source ∩ s) :=
  h.symm.mapsTo

theorem image_eq (h : e.IsImage s t) : e '' (e.source ∩ s) = e.target ∩ t :=
  h.toPartialEquiv.image_eq

theorem symm_image_eq (h : e.IsImage s t) : e.symm '' (e.target ∩ t) = e.source ∩ s :=
  h.symm.image_eq

theorem iff_preimage_eq : e.IsImage s t ↔ e.source ∩ e ⁻¹' t = e.source ∩ s :=
  PartialEquiv.IsImage.iff_preimage_eq

alias ⟨preimage_eq, of_preimage_eq⟩ := iff_preimage_eq

theorem iff_symm_preimage_eq : e.IsImage s t ↔ e.target ∩ e.symm ⁻¹' s = e.target ∩ t :=
  symm_iff.symm.trans iff_preimage_eq

alias ⟨symm_preimage_eq, of_symm_preimage_eq⟩ := iff_symm_preimage_eq

theorem iff_symm_preimage_eq' :
    e.IsImage s t ↔ e.target ∩ e.symm ⁻¹' (e.source ∩ s) = e.target ∩ t := by
  rw [iff_symm_preimage_eq, ← image_source_inter_eq, ← image_source_inter_eq']

alias ⟨symm_preimage_eq', of_symm_preimage_eq'⟩ := iff_symm_preimage_eq'

theorem iff_preimage_eq' : e.IsImage s t ↔ e.source ∩ e ⁻¹' (e.target ∩ t) = e.source ∩ s :=
  symm_iff.symm.trans iff_symm_preimage_eq'

alias ⟨preimage_eq', of_preimage_eq'⟩ := iff_preimage_eq'

theorem of_image_eq (h : e '' (e.source ∩ s) = e.target ∩ t) : e.IsImage s t :=
  PartialEquiv.IsImage.of_image_eq h

theorem of_symm_image_eq (h : e.symm '' (e.target ∩ t) = e.source ∩ s) : e.IsImage s t :=
  PartialEquiv.IsImage.of_symm_image_eq h

protected theorem compl (h : e.IsImage s t) : e.IsImage sᶜ tᶜ := fun _ hx => (h hx).not

protected theorem inter {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s ∩ s') (t ∩ t') := fun _ hx => (h hx).and (h' hx)

protected theorem union {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s ∪ s') (t ∪ t') := fun _ hx => (h hx).or (h' hx)

protected theorem diff {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s \ s') (t \ t') :=
  h.inter h'.compl

theorem leftInvOn_piecewise {e' : PartialHomeomorph X Y} [∀ i, Decidable (i ∈ s)]
    [∀ i, Decidable (i ∈ t)] (h : e.IsImage s t) (h' : e'.IsImage s t) :
    LeftInvOn (t.piecewise e.symm e'.symm) (s.piecewise e e') (s.ite e.source e'.source) :=
  h.toPartialEquiv.leftInvOn_piecewise h'

theorem inter_eq_of_inter_eq_of_eqOn {e' : PartialHomeomorph X Y} (h : e.IsImage s t)
    (h' : e'.IsImage s t) (hs : e.source ∩ s = e'.source ∩ s) (Heq : EqOn e e' (e.source ∩ s)) :
    e.target ∩ t = e'.target ∩ t :=
  h.toPartialEquiv.inter_eq_of_inter_eq_of_eqOn h' hs Heq

theorem symm_eqOn_of_inter_eq_of_eqOn {e' : PartialHomeomorph X Y} (h : e.IsImage s t)
    (hs : e.source ∩ s = e'.source ∩ s) (Heq : EqOn e e' (e.source ∩ s)) :
    EqOn e.symm e'.symm (e.target ∩ t) :=
  h.toPartialEquiv.symm_eq_on_of_inter_eq_of_eqOn hs Heq

/-- Restrict an `PartialHomeomorph` to a pair of corresponding open sets. -/
@[simps! -fullyApplied apply symm_apply toPartialEquiv]
def restr (h : e.IsImage s t) : PartialHomeomorph X Y where
  toPartialEquiv := h.toPartialEquiv.restr
  continuousOn_toFun := e.continuousOn.mono inter_subset_left
  continuousOn_invFun := e.symm.continuousOn.mono inter_subset_left

end IsImage

theorem isImage_source_target : e.IsImage e.source e.target :=
  e.toPartialEquiv.isImage_source_target

theorem isImage_source_target_of_disjoint (e' : PartialHomeomorph X Y)
    (hs : Disjoint e.source e'.source) (ht : Disjoint e.target e'.target) :
    e.IsImage e'.source e'.target :=
  e.toPartialEquiv.isImage_source_target_of_disjoint e'.toPartialEquiv hs ht

end IsImage


section restr
/-!
## Restriction
-/

/-- Restricting an open partial homeomorphism `e` to `e.source ∩ s`.
This is sometimes hard to use, but it has the advantage that when it can be used then its
`PartialEquiv` is defeq to `PartialEquiv.restr`. -/
@[simps! (attr := mfld_simps) -fullyApplied apply symm_apply,
  simps! (attr := grind =) -isSimp source target]
protected def restr (s : Set X) : PartialHomeomorph X Y :=
  (@IsImage.of_symm_preimage_eq X Y _ _ e s (e.symm ⁻¹' s) rfl).restr

@[simp]
theorem restr_toPartialEquiv (s : Set X) :
    (e.restr s).toPartialEquiv = e.toPartialEquiv.restr s :=
  rfl

@[simp] theorem coe_restrOpen {s : Set X} : ⇑(e.restr s) = e := rfl

@[simp]
theorem coe_restrOpen_symm {s : Set X} : ⇑(e.restr s).symm = e.symm := rfl

@[simp, grind =]
theorem restr_source_inter (s : Set X) : e.restr (e.source ∩ s) = e.restr s := by
  refine PartialHomeomorph.ext _ _ (fun x => rfl) (fun x => rfl) ?_
  simp [← inter_assoc]

end restr

/-!
## ofSet

The identity on a set `s`
-/
section ofSet

variable {s : Set X} (hs : IsOpen s)

/-- The identity partial equivalence on a set `s` -/
@[simps! -fullyApplied apply, simps! -isSimp source target]
def ofSet (s : Set X) : PartialHomeomorph X X where
  toPartialEquiv := PartialEquiv.ofSet s
  continuousOn_toFun := continuous_id.continuousOn
  continuousOn_invFun := continuous_id.continuousOn

@[simp]
theorem ofSet_toPartialEquiv : (ofSet s).toPartialEquiv = PartialEquiv.ofSet s :=
  rfl

@[simp]
theorem ofSet_symm : (ofSet s).symm = ofSet s :=
  rfl

@[simp]
theorem ofSet_univ_eq_refl : ofSet univ = PartialHomeomorph.refl X := by
  ext <;> simp

end ofSet


/-! `EqOnSource`: equivalence on their source -/
section EqOnSource

/-- `EqOnSource e e'` means that `e` and `e'` have the same source, and coincide there. They
should really be considered the same partial equivalence. -/
def EqOnSource (e e' : PartialHomeomorph X Y) : Prop :=
  e.source = e'.source ∧ EqOn e e' e.source

theorem eqOnSource_iff (e e' : PartialHomeomorph X Y) :
    EqOnSource e e' ↔ PartialEquiv.EqOnSource e.toPartialEquiv e'.toPartialEquiv :=
  Iff.rfl

/-- `EqOnSource` is an equivalence relation. -/
instance eqOnSourceSetoid : Setoid (PartialHomeomorph X Y) :=
  { PartialEquiv.eqOnSourceSetoid.comap toPartialEquiv with r := EqOnSource }

theorem eqOnSource_refl : e ≈ e := Setoid.refl _

/-- If two open partial homeomorphisms are equivalent, so are their inverses. -/
theorem EqOnSource.symm' {e e' : PartialHomeomorph X Y} (h : e ≈ e') : e.symm ≈ e'.symm :=
  PartialEquiv.EqOnSource.symm' h

/-- Two equivalent open partial homeomorphisms have the same source. -/
theorem EqOnSource.source_eq {e e' : PartialHomeomorph X Y} (h : e ≈ e') :
    e.source = e'.source :=
  h.1

/-- Two equivalent open partial homeomorphisms have the same target. -/
theorem EqOnSource.target_eq {e e' : PartialHomeomorph X Y} (h : e ≈ e') :
    e.target = e'.target :=
  h.symm'.1

/-- Two equivalent open partial homeomorphisms have coinciding `toFun` on the source -/
theorem EqOnSource.eqOn {e e' : PartialHomeomorph X Y} (h : e ≈ e') : EqOn e e' e.source :=
  h.2

/-- Two equivalent open partial homeomorphisms have coinciding `invFun` on the target -/
theorem EqOnSource.symm_eqOn_target {e e' : PartialHomeomorph X Y} (h : e ≈ e') :
    EqOn e.symm e'.symm e.target :=
  h.symm'.2

/-- Restriction of open partial homeomorphisms respects equivalence -/
theorem EqOnSource.restr {e e' : PartialHomeomorph X Y} (he : e ≈ e') (s : Set X) :
    e.restr s ≈ e'.restr s :=
  PartialEquiv.EqOnSource.restr he _

/-- Two equivalent open partial homeomorphisms are equal when the source and target are `univ`. -/
theorem Set.EqOn.restr_eqOn_source {e e' : PartialHomeomorph X Y}
    (h : EqOn e e' (e.source ∩ e'.source)) : e.restr e'.source ≈ e'.restr e.source := by
  constructor
  · rw [restr_source, restr_source]
    exact Set.inter_comm _ _
  · rw [restr_source]
    refine (EqOn.trans ?_ h).trans ?_ <;> simp only [coe_restrOpen, eqOn_refl]

theorem eq_of_eqOnSource_univ {e e' : PartialHomeomorph X Y} (h : e ≈ e') (s : e.source = univ)
    (t : e.target = univ) : e = e' :=
  toPartialEquiv_injective <| PartialEquiv.eq_of_eqOnSource_univ _ _ h s t

variable {s : Set X}

lemma restr_eqOnSource_restr {s' : Set X}
    (hss' : e.source ∩ s = e.source ∩ s') :
    e.restr s ≈ e.restr s' := by
  constructor
  · simpa [e.restr_source]
  · simp [Set.eqOn_refl]

lemma restr_inter_source : e.restr (e.source ∩ s) ≈ e.restr s :=
  e.restr_eqOnSource_restr (by simp)

theorem restr_eq_of_source_subset {e : PartialHomeomorph X Y} {s : Set X} (h : e.source ⊆ s) :
    e.restr s = e :=
  toPartialEquiv_injective <| PartialEquiv.restr_eq_of_source_subset h

end EqOnSource

end PartialHomeomorph

namespace Homeomorph

variable (e : X ≃ₜ Y) (e' : Y ≃ₜ Z)

/- Register as simp lemmas that the fields of an open partial homeomorphism built from a
homeomorphism correspond to the fields of the original homeomorphism. -/
@[simp]
theorem refl_toPartialHomeomorph :
    (Homeomorph.refl X).toPartialHomeomorph = PartialHomeomorph.refl X :=
  rfl

@[simp]
theorem symm_toPartialHomeomorph :
    e.symm.toPartialHomeomorph = e.toPartialHomeomorph.symm :=
  rfl

end Homeomorph
