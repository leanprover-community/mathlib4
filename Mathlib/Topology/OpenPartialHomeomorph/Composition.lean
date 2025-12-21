/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.IsImage
/-!
# Partial homeomorphisms: composition

## Main definitions

* `OpenPartialHomeomorph.trans`: the composition of two open partial homeomorphisms
-/

@[expose] public section

open Function Set Filter Topology

variable {X X' : Type*} {Y Y' : Type*} {Z Z' : Type*}
  [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Y']
  [TopologicalSpace Z] [TopologicalSpace Z']

namespace OpenPartialHomeomorph

variable (e : OpenPartialHomeomorph X Y)

/-!
## Composition

`trans`: composition of two open partial homeomorphisms
-/
section trans

variable (e' : OpenPartialHomeomorph Y Z)

/-- Composition of two open partial homeomorphisms when the target of the first and the source of
the second coincide. -/
@[simps! apply symm_apply toPartialEquiv, simps! -isSimp source target]
protected def trans' (h : e.target = e'.source) : OpenPartialHomeomorph X Z where
  toPartialEquiv := PartialEquiv.trans' e.toPartialEquiv e'.toPartialEquiv h
  open_source := e.open_source
  open_target := e'.open_target
  continuousOn_toFun := e'.continuousOn.comp e.continuousOn <| h ▸ e.mapsTo
  continuousOn_invFun := e.continuousOn_symm.comp e'.continuousOn_symm <| h.symm ▸ e'.symm_mapsTo

/-- Composing two open partial homeomorphisms, by restricting to the maximal domain where their
composition is well defined.
Within the `Manifold` namespace, there is the notation `e ≫ₕ f` for this. -/
@[trans]
protected def trans : OpenPartialHomeomorph X Z :=
  OpenPartialHomeomorph.trans' (e.symm.restrOpen e'.source e'.open_source).symm
    (e'.restrOpen e.target e.open_target) (by simp [inter_comm])

@[simp, mfld_simps]
theorem trans_toPartialEquiv :
    (e.trans e').toPartialEquiv = e.toPartialEquiv.trans e'.toPartialEquiv :=
  rfl

@[simp, mfld_simps]
theorem coe_trans : (e.trans e' : X → Z) = e' ∘ e :=
  rfl

@[simp, mfld_simps]
theorem coe_trans_symm : ((e.trans e').symm : Z → X) = e.symm ∘ e'.symm :=
  rfl

theorem trans_apply {x : X} : (e.trans e') x = e' (e x) :=
  rfl

theorem trans_symm_eq_symm_trans_symm : (e.trans e').symm = e'.symm.trans e.symm := rfl

/- This could be considered as a simp lemma, but there are many situations where it makes something
simple into something more complicated. -/
theorem trans_source : (e.trans e').source = e.source ∩ e ⁻¹' e'.source :=
  PartialEquiv.trans_source e.toPartialEquiv e'.toPartialEquiv

theorem trans_source' : (e.trans e').source = e.source ∩ e ⁻¹' (e.target ∩ e'.source) :=
  PartialEquiv.trans_source' e.toPartialEquiv e'.toPartialEquiv

theorem trans_source'' : (e.trans e').source = e.symm '' (e.target ∩ e'.source) :=
  PartialEquiv.trans_source'' e.toPartialEquiv e'.toPartialEquiv

theorem image_trans_source : e '' (e.trans e').source = e.target ∩ e'.source :=
  PartialEquiv.image_trans_source e.toPartialEquiv e'.toPartialEquiv

theorem trans_target : (e.trans e').target = e'.target ∩ e'.symm ⁻¹' e.target :=
  rfl

theorem trans_target' : (e.trans e').target = e'.target ∩ e'.symm ⁻¹' (e'.source ∩ e.target) :=
  trans_source' e'.symm e.symm

theorem trans_target'' : (e.trans e').target = e' '' (e'.source ∩ e.target) :=
  trans_source'' e'.symm e.symm

theorem inv_image_trans_target : e'.symm '' (e.trans e').target = e'.source ∩ e.target :=
  image_trans_source e'.symm e.symm

theorem trans_assoc (e'' : OpenPartialHomeomorph Z Z') :
    (e.trans e').trans e'' = e.trans (e'.trans e'') :=
  toPartialEquiv_injective <| e.1.trans_assoc _ _

@[simp, mfld_simps]
theorem trans_refl : e.trans (OpenPartialHomeomorph.refl Y) = e :=
  toPartialEquiv_injective e.1.trans_refl

@[simp, mfld_simps]
theorem refl_trans : (OpenPartialHomeomorph.refl X).trans e = e :=
  toPartialEquiv_injective e.1.refl_trans

theorem trans_ofSet {s : Set Y} (hs : IsOpen s) : e.trans (ofSet s hs) = e.restr (e ⁻¹' s) :=
  OpenPartialHomeomorph.ext _ _ (fun _ => rfl) (fun _ => rfl) <| by
    rw [trans_source, restr_source, ofSet_source, ← preimage_interior, hs.interior_eq]

theorem trans_of_set' {s : Set Y} (hs : IsOpen s) :
    e.trans (ofSet s hs) = e.restr (e.source ∩ e ⁻¹' s) := by rw [trans_ofSet, restr_source_inter]

theorem ofSet_trans {s : Set X} (hs : IsOpen s) : (ofSet s hs).trans e = e.restr s :=
  OpenPartialHomeomorph.ext _ _ (fun _ => rfl) (fun _ => rfl) <|
    by simp [hs.interior_eq, inter_comm]

theorem ofSet_trans' {s : Set X} (hs : IsOpen s) :
    (ofSet s hs).trans e = e.restr (e.source ∩ s) := by
  rw [ofSet_trans, restr_source_inter]

@[simp, mfld_simps]
theorem ofSet_trans_ofSet {s : Set X} (hs : IsOpen s) {s' : Set X} (hs' : IsOpen s') :
    (ofSet s hs).trans (ofSet s' hs') = ofSet (s ∩ s') (IsOpen.inter hs hs') := by
  rw [(ofSet s hs).trans_ofSet hs']
  ext <;> simp [hs'.interior_eq]

theorem restr_trans (s : Set X) : (e.restr s).trans e' = (e.trans e').restr s :=
  toPartialEquiv_injective <|
    PartialEquiv.restr_trans e.toPartialEquiv e'.toPartialEquiv (interior s)

end trans

/-- Composition of open partial homeomorphisms respects equivalence. -/
theorem EqOnSource.trans' {e e' : OpenPartialHomeomorph X Y} {f f' : OpenPartialHomeomorph Y Z}
    (he : e ≈ e') (hf : f ≈ f') : e.trans f ≈ e'.trans f' :=
  PartialEquiv.EqOnSource.trans' he hf

/-- Composition of an open partial homeomorphism and its inverse is equivalent to the restriction of
the identity to the source -/
theorem self_trans_symm : e.trans e.symm ≈ OpenPartialHomeomorph.ofSet e.source e.open_source :=
  PartialEquiv.self_trans_symm _

theorem symm_trans_self : e.symm.trans e ≈ OpenPartialHomeomorph.ofSet e.target e.open_target :=
  e.symm.self_trans_symm

variable {s : Set X}

theorem restr_symm_trans {e' : OpenPartialHomeomorph X Y}
    (hs : IsOpen s) (hs' : IsOpen (e '' s)) (hs'' : s ⊆ e.source) :
    (e.restr s).symm.trans e' ≈ (e.symm.trans e').restr (e '' s) := by
  refine ⟨?_, ?_⟩
  · simp only [trans_toPartialEquiv, symm_toPartialEquiv, restr_toPartialEquiv,
      PartialEquiv.trans_source, PartialEquiv.symm_source, PartialEquiv.restr_target, coe_coe_symm,
      PartialEquiv.restr_coe_symm, PartialEquiv.restr_source]
    rw [interior_eq_iff_isOpen.mpr hs', interior_eq_iff_isOpen.mpr hs]
    -- Get rid of the middle term, which is merely distracting.
    rw [inter_assoc, inter_assoc, inter_comm _ (e '' s), ← inter_assoc, ← inter_assoc]
    congr 1
    -- Now, just a bunch of rewrites: should this be a separate lemma?
    rw [← image_source_inter_eq', ← image_source_eq_target]
    refine image_inter_on ?_
    intro x hx y hy h
    rw [← left_inv e hy, ← left_inv e (hs'' hx), h]
  · simp_rw [coe_trans, restr_symm_apply, restr_apply, coe_trans]
    intro x hx
    simp

theorem symm_trans_restr (e' : OpenPartialHomeomorph X Y) (hs : IsOpen s) :
    e'.symm.trans (e.restr s) ≈ (e'.symm.trans e).restr (e'.target ∩ e'.symm ⁻¹' s) := by
  have ht : IsOpen (e'.target ∩ e'.symm ⁻¹' s) := by
    rw [← image_source_inter_eq']
    exact isOpen_image_source_inter e' hs
  refine ⟨?_, ?_⟩
  · simp only [trans_toPartialEquiv, symm_toPartialEquiv, restr_toPartialEquiv,
      PartialEquiv.trans_source, PartialEquiv.symm_source, coe_coe_symm, PartialEquiv.restr_source,
      preimage_inter]
    -- Shuffle the intersections, pull e'.target into the interior and use interior_inter.
    rw [interior_eq_iff_isOpen.mpr hs,
      ← inter_assoc, inter_comm e'.target, inter_assoc, inter_assoc]
    congr 1
    nth_rw 2 [← interior_eq_iff_isOpen.mpr e'.open_target]
    rw [← interior_inter, ← inter_assoc, inter_self, interior_eq_iff_isOpen.mpr ht]
  · simp [Set.eqOn_refl]

end OpenPartialHomeomorph

namespace Homeomorph

variable (e : X ≃ₜ Y) (e' : Y ≃ₜ Z)

@[simp, mfld_simps]
theorem trans_toOpenPartialHomeomorph : (e.trans e').toOpenPartialHomeomorph =
    e.toOpenPartialHomeomorph.trans e'.toOpenPartialHomeomorph :=
  OpenPartialHomeomorph.toPartialEquiv_injective <| Equiv.trans_toPartialEquiv _ _

@[deprecated (since := "2025-08-29")] alias
  trans_toPartialHomeomorph := trans_toOpenPartialHomeomorph

/-- Precompose an open partial homeomorphism with a homeomorphism.
We modify the source and target to have better definitional behavior. -/
@[simps! -fullyApplied]
def transOpenPartialHomeomorph (e : X ≃ₜ Y) (f' : OpenPartialHomeomorph Y Z) :
    OpenPartialHomeomorph X Z where
  toPartialEquiv := e.toEquiv.transPartialEquiv f'.toPartialEquiv
  open_source := f'.open_source.preimage e.continuous
  open_target := f'.open_target
  continuousOn_toFun := f'.continuousOn.comp e.continuous.continuousOn fun _ => id
  continuousOn_invFun := e.symm.continuous.comp_continuousOn f'.symm.continuousOn

@[deprecated (since := "2025-08-29")] alias
  transPartialHomeomorph := transOpenPartialHomeomorph

theorem transOpenPartialHomeomorph_eq_trans (e : X ≃ₜ Y) (f' : OpenPartialHomeomorph Y Z) :
    e.transOpenPartialHomeomorph f' = e.toOpenPartialHomeomorph.trans f' :=
  OpenPartialHomeomorph.toPartialEquiv_injective <| Equiv.transPartialEquiv_eq_trans _ _

@[deprecated (since := "2025-08-29")] alias
  transPartialHomeomorph_eq_trans := transOpenPartialHomeomorph_eq_trans

@[simp, mfld_simps]
theorem transOpenPartialHomeomorph_trans (e : X ≃ₜ Y) (f : OpenPartialHomeomorph Y Z)
    (f' : OpenPartialHomeomorph Z Z') :
    (e.transOpenPartialHomeomorph f).trans f' = e.transOpenPartialHomeomorph (f.trans f') := by
  simp only [transOpenPartialHomeomorph_eq_trans, OpenPartialHomeomorph.trans_assoc]

@[deprecated (since := "2025-08-29")] alias
  transPartialHomeomorph_trans := transOpenPartialHomeomorph_trans

@[simp, mfld_simps]
theorem trans_transOpenPartialHomeomorph (e : X ≃ₜ Y) (e' : Y ≃ₜ Z)
    (f'' : OpenPartialHomeomorph Z Z') : (e.trans e').transOpenPartialHomeomorph f'' =
      e.transOpenPartialHomeomorph (e'.transOpenPartialHomeomorph f'') := by
  simp only [transOpenPartialHomeomorph_eq_trans, OpenPartialHomeomorph.trans_assoc,
    trans_toOpenPartialHomeomorph]

@[deprecated (since := "2025-08-29")] alias
  trans_transPartialHomeomorph := trans_transOpenPartialHomeomorph

end Homeomorph
