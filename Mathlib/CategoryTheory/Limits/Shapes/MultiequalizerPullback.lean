/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

/-!
# Multicoequalizers that are pushouts

In this file, we show that a multicoequalizer for
for `I : MultispanIndex (.ofLinearOrder ι) C` is also
a pushout when `ι` has exactly two elements.

-/

namespace CategoryTheory.Limits.Multicofork.IsColimit

variable {C : Type*} [Category C] {ι : Type*} [LinearOrder ι]
  {I : MultispanIndex (.ofLinearOrder ι) C} (c : Multicofork I)

namespace isPushout

variable {i j : ι} {hij : i < j} (h : {i, j} = Set.univ)
  (s : PushoutCocone (I.fst ⟨⟨i, j⟩, hij⟩) (I.snd ⟨⟨i, j⟩, hij⟩))

open Classical in
/-- Given a type `ι` containing only two elements `i < j`,
`I : MultispanIndex (.ofLinearOrder ι) C`, this is the multicofork
for `I` attached to a pushout cocone for the morphism
`I.fst ⟨⟨i, j⟩, _⟩` and `I.snd ⟨⟨i, j⟩, _⟩`. -/
noncomputable def pushoutCocone : Multicofork I :=
  Multicofork.ofπ _ s.pt (fun k ↦
    if hk : k = i then
      eqToHom (by simp [hk]) ≫ s.inl
    else
      eqToHom (by
        obtain rfl : k = j := by
          have := h.symm.le (Set.mem_univ k)
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
          tauto
        rfl) ≫ s.inr) (by
    rintro ⟨⟨k₁, k₂⟩, hk⟩
    have hk₁ := h.symm.le (Set.mem_univ k₁)
    have hk₂ := h.symm.le (Set.mem_univ k₂)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk₁ hk₂
    obtain rfl : i = k₁ := by
      obtain rfl | rfl := hk₁
      · rfl
      · obtain rfl | rfl := hk₂
        · have := hij.trans hk
          simp at this
        · simp at hk
    obtain rfl : j = k₂ := by
      obtain rfl | rfl := hk₂
      · simp at hk
      · rfl
    dsimp only
    rw [dif_pos (by rfl), dif_neg (by rintro (rfl : j = i); simp at hk),
      eqToHom_refl, eqToHom_refl, Category.id_comp, Category.id_comp]
    apply s.condition)

@[simp]
lemma pushoutCocone_π_eq_inl : (pushoutCocone h s).π i = s.inl := by
  dsimp only [pushoutCocone, ofπ, π]
  rw [dif_pos rfl, eqToHom_refl, Category.id_comp]

@[simp]
lemma pushoutCocone_π_eq_inr : (pushoutCocone h s).π j = s.inr := by
  dsimp only [pushoutCocone, ofπ, π]
  rw [dif_neg (by rintro rfl; simp at hij), eqToHom_refl, Category.id_comp]

end isPushout

/-- A multicoequalizer for `I : MultispanIndex (.ofLinearOrder ι) C` is also
a pushout when `ι` has exactly two elements. -/
lemma isPushout (hc : IsColimit c) {i j : ι} (hij : i < j) (h : {i, j} = Set.univ) :
    IsPushout (I.fst ⟨⟨i, j⟩, hij⟩) (I.snd ⟨⟨i, j⟩, hij⟩) (c.π i) (c.π j) where
  w := c.condition _
  isColimit' := ⟨PushoutCocone.IsColimit.mk _
    (fun s ↦ hc.desc (isPushout.pushoutCocone h s))
    (fun s ↦ by simpa using hc.fac (isPushout.pushoutCocone h s) (.right i))
    (fun s ↦ by simpa using hc.fac (isPushout.pushoutCocone h s) (.right j))
    (fun s m h₁ h₂ ↦ by
      apply Multicofork.IsColimit.hom_ext hc
      intro k
      have := h.symm.le (Set.mem_univ k)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
      obtain rfl | rfl := this
      · simpa [h₁] using (hc.fac (isPushout.pushoutCocone h s) (.right k)).symm
      · simpa [h₂] using (hc.fac (isPushout.pushoutCocone h s) (.right k)).symm)⟩

end CategoryTheory.Limits.Multicofork.IsColimit
