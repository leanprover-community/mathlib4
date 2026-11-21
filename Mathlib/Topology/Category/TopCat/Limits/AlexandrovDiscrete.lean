/-
Copyright (c) 2026 Robert Maxton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Maxton
-/
module

public import Mathlib.CategoryTheory.FinCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.Topology.AlexandrovDiscrete
public import Mathlib.Topology.Category.TopCat.EpiMono
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Specialization

/-!
# Equalizers of Alexandrov-discrete spaces in `TopCat`

TODO(docstring)
-/


@[expose] public section
namespace TopCat
open CategoryTheory
open Topology
open CategoryTheory.Limits
universe w v u
variable {J : Type*}
variable [Category J]
variable [FinCategory J]
variable {F : J ⥤ TopCat}
variable [∀ j, AlexandrovDiscrete (F.obj j)]

open Set in
noncomputable def isEqualizer_of_alexandrovDiscrete' {E Y Z : TopCat}
    [AlexandrovDiscrete E] [AlexandrovDiscrete Y] [AlexandrovDiscrete Z]
    (e : E ⟶ Y) [Mono e] {f g : Y ⟶ Z} (w : e ≫ f = e ≫ g)
    (w' : ∀ y, f y = g y → ∃ x, e x = y) (hspec : ∀ x y, e x ⤳ e y → x ⤳ y) :
    IsLimit (Fork.ofι e w) := by
  have he : IsEmbedding e :=
  { eq_induced := by
      refine le_antisymm (e.hom.continuous.le_induced) ?_
      intro u
      simp_rw [isOpen_induced_iff, isOpen_iff_forall_specializes]
      intro uO
      use { y | ∃ x ∈ u, y ⤳ e x }; split_ands
      · rintro y₁ y₂ hy ⟨a, ha, hy₂⟩
        use a, ha, hy.trans hy₂
      · apply subset_antisymm
        · rintro a ⟨b, hb, h⟩; exact uO _ _ (hspec _ _ h) hb
        · intro a ha; use a
    injective := TopCat.mono_iff_injective e |>.mp ‹_› }
  have he' : range e = { y | f y = g y } := by
    ext y; rw [mem_range]; exact ⟨by rintro ⟨a, rfl⟩; exact (elementwise_of% w) a , fun h ↦ w' _ h⟩
  let η : _ ≃ₜ TopCat.of {y | f y = g y } := he.toHomeomorph.trans <| .setCongr he'
  fapply Fork.IsLimit.mk
  · intro s; --let ι' := s.ι
    haveI hι' := elementwise_of% s.condition
    refine ?_ ≫ (isoOfHomeo η).inv
    exact ofHom <| ⟨_, s.ι.hom.continuous.subtype_coind hι'⟩
  · intro s
    ext p
    obtain ⟨a, ha⟩ : s.ι p ∈ range e := by simp [he', elementwise_of% s.condition]
    suffices e (he.toHomeomorph.symm ⟨(Hom.hom s.ι) p, ⟨a, ha⟩⟩) = (Hom.hom s.ι) p by
      simp [η, Homeomorph.setCongr, this]
    simp_rw [← ha, he.toHomeomorph_symm_apply]
  · intro s m hm
    rw [Iso.eq_comp_inv]
    have : Mono (ofHom <| .subtypeVal { y | f y = g y }) :=
      TopCat.mono_iff_injective _ |>.mpr Subtype.val_injective
    apply this.right_cancellation
    trans s.ι
    · rw [← hm, Category.assoc]; congr
    · ext p; simp

open Set in
noncomputable def isEqualizer_of_alexandrovDiscrete {E Y Z : TopCat}
    [AlexandrovDiscrete E] [AlexandrovDiscrete Y] [AlexandrovDiscrete Z]
    (e : E ⟶ Y) {f g : Y ⟶ Z} (ε : E ≃ { y // f y = g y }) (w : e ≫ f = e ≫ g)
    (hε : ∀ x, e x = ε x) (hspec : ∀ x y, e x ⤳ e y → x ⤳ y) : IsLimit (Fork.ofι e w) :=
  have : Mono e := by
    rw [TopCat.mono_iff_injective]; intro x y hxy; simpa [hε, Subtype.val_inj] using hxy
  isEqualizer_of_alexandrovDiscrete' e w (fun y h ↦ ⟨ε.symm ⟨y, h⟩, by simp [hε]⟩) hspec

end TopCat
end
