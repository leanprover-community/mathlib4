/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.PartialHomeomorph.IsImage
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

namespace PartialHomeomorph

variable (e : PartialHomeomorph X Y)

/-!
## Composition

`trans`: composition of two open partial homeomorphisms
-/
section trans

variable (e' : PartialHomeomorph Y Z)

/-- Composition of two open partial homeomorphisms when the target of the first and the source of
the second coincide. -/
@[simps! apply symm_apply toPartialEquiv, simps! -isSimp source target]
protected def trans' (h : e.target = e'.source) : PartialHomeomorph X Z where
  toPartialEquiv := PartialEquiv.trans' e.toPartialEquiv e'.toPartialEquiv h
  continuousOn_toFun := e'.continuousOn.comp e.continuousOn <| h ▸ e.mapsTo
  continuousOn_invFun := e.continuousOn_symm.comp e'.continuousOn_symm <| h.symm ▸ e'.symm_mapsTo

/-- Composing two open partial homeomorphisms, by restricting to the maximal domain where their
composition is well defined.
Within the `Manifold` namespace, there is the notation `e ≫ₕ f` for this. -/
@[trans]
protected def trans : PartialHomeomorph X Z :=
  PartialHomeomorph.trans' (e.symm.restr e'.source).symm (e'.restr e.target) (by simp [inter_comm])

@[simp]
theorem trans_toPartialEquiv :
    (e.trans e').toPartialEquiv = e.toPartialEquiv.trans e'.toPartialEquiv :=
  rfl

@[simp]
theorem coe_trans : (e.trans e' : X → Z) = e' ∘ e :=
  rfl

@[simp]
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

theorem trans_assoc (e'' : PartialHomeomorph Z Z') :
    (e.trans e').trans e'' = e.trans (e'.trans e'') :=
  toPartialEquiv_injective <| e.1.trans_assoc _ _

@[simp]
theorem trans_refl : e.trans (PartialHomeomorph.refl Y) = e :=
  toPartialEquiv_injective e.1.trans_refl

@[simp]
theorem refl_trans : (PartialHomeomorph.refl X).trans e = e :=
  toPartialEquiv_injective e.1.refl_trans

theorem trans_ofSet {s : Set Y} : e.trans (ofSet s) = e.restr (e ⁻¹' s) :=
  PartialHomeomorph.ext _ _ (fun _ => rfl) (fun _ => rfl) <| by
    rw [trans_source, restr_source, ofSet_source]

theorem trans_of_set' {s : Set Y} : e.trans (ofSet s) = e.restr (e.source ∩ e ⁻¹' s) := by
  rw [trans_ofSet, restr_source_inter]

theorem ofSet_trans {s : Set X} : (ofSet s).trans e = e.restr s :=
  PartialHomeomorph.ext _ _ (fun _ => rfl) (fun _ => rfl) <|
    by simp [ inter_comm]

theorem ofSet_trans' {s : Set X} : (ofSet s).trans e = e.restr (e.source ∩ s) := by
  rw [ofSet_trans, restr_source_inter]

@[simp]
theorem ofSet_trans_ofSet {s : Set X} {s' : Set X} :
    (ofSet s).trans (ofSet s') = ofSet (s ∩ s') := by
  rw [(ofSet s).trans_ofSet]
  ext <;> simp

theorem restr_trans (s : Set X) : (e.restr s).trans e' = (e.trans e').restr s :=
  toPartialEquiv_injective <|
    PartialEquiv.restr_trans e.toPartialEquiv e'.toPartialEquiv s

end trans

/-- Composition of open partial homeomorphisms respects equivalence. -/
theorem EqOnSource.trans' {e e' : PartialHomeomorph X Y} {f f' : PartialHomeomorph Y Z}
    (he : e ≈ e') (hf : f ≈ f') : e.trans f ≈ e'.trans f' :=
  PartialEquiv.EqOnSource.trans' he hf

/-- Composition of an open partial homeomorphism and its inverse is equivalent to the restriction of
the identity to the source -/
theorem self_trans_symm : e.trans e.symm ≈ PartialHomeomorph.ofSet e.source :=
  PartialEquiv.self_trans_symm _

theorem symm_trans_self : e.symm.trans e ≈ PartialHomeomorph.ofSet e.target :=
  e.symm.self_trans_symm

variable {s : Set X}

theorem restr_symm_trans {e' : PartialHomeomorph X Y} (hs'' : s ⊆ e.source) :
    (e.restr s).symm.trans e' ≈ (e.symm.trans e').restr (e '' s) := by
  refine ⟨?_, ?_⟩
  · simp only [trans_toPartialEquiv, symm_toPartialEquiv, restr_toPartialEquiv,
      PartialEquiv.trans_source, PartialEquiv.symm_source, PartialEquiv.restr_target, coe_coe_symm,
      PartialEquiv.restr_coe_symm, PartialEquiv.restr_source]
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

theorem symm_trans_restr (e' : PartialHomeomorph X Y) :
    e'.symm.trans (e.restr s) ≈ (e'.symm.trans e).restr (e'.target ∩ e'.symm ⁻¹' s) := by
  refine ⟨?_, ?_⟩
  · simp only [trans_toPartialEquiv, symm_toPartialEquiv, restr_toPartialEquiv,
      PartialEquiv.trans_source, PartialEquiv.symm_source, coe_coe_symm, PartialEquiv.restr_source,
      preimage_inter]
    -- Shuffle the intersections, pull e'.target into the interior and use interior_inter.
    rw [
      ← inter_assoc, inter_comm e'.target, inter_assoc, inter_assoc]
    congr 1
    rw [ ← inter_assoc, inter_self]
  · simp [Set.eqOn_refl]

end PartialHomeomorph

namespace Homeomorph

variable (e : X ≃ₜ Y) (e' : Y ≃ₜ Z)

@[simp]
theorem trans_toPartialHomeomorph : (e.trans e').toPartialHomeomorph =
    e.toPartialHomeomorph.trans e'.toPartialHomeomorph :=
  PartialHomeomorph.toPartialEquiv_injective <| Equiv.trans_toPartialEquiv _ _

/-- Precompose an open partial homeomorphism with a homeomorphism.
We modify the source and target to have better definitional behavior. -/
@[simps! -fullyApplied]
def transPartialHomeomorph (e : X ≃ₜ Y) (f' : PartialHomeomorph Y Z) :
    PartialHomeomorph X Z where
  toPartialEquiv := e.toEquiv.transPartialEquiv f'.toPartialEquiv
  continuousOn_toFun := f'.continuousOn.comp e.continuous.continuousOn fun _ => id
  continuousOn_invFun := e.symm.continuous.comp_continuousOn f'.symm.continuousOn

theorem transPartialHomeomorph_eq_trans (e : X ≃ₜ Y) (f' : PartialHomeomorph Y Z) :
    e.transPartialHomeomorph f' = e.toPartialHomeomorph.trans f' :=
  PartialHomeomorph.toPartialEquiv_injective <| Equiv.transPartialEquiv_eq_trans _ _

@[simp]
theorem transPartialHomeomorph_trans (e : X ≃ₜ Y) (f : PartialHomeomorph Y Z)
    (f' : PartialHomeomorph Z Z') :
    (e.transPartialHomeomorph f).trans f' = e.transPartialHomeomorph (f.trans f') := by
  simp only [transPartialHomeomorph_eq_trans, PartialHomeomorph.trans_assoc]

@[simp]
theorem trans_transPartialHomeomorph (e : X ≃ₜ Y) (e' : Y ≃ₜ Z)
    (f'' : PartialHomeomorph Z Z') : (e.trans e').transPartialHomeomorph f'' =
      e.transPartialHomeomorph (e'.transPartialHomeomorph f'') := by
  simp only [transPartialHomeomorph_eq_trans, PartialHomeomorph.trans_assoc,
    trans_toPartialHomeomorph]

end Homeomorph
