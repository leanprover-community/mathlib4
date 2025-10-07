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
`I : MultispanIndex (.ofLinearOrder ι) C` is also
a pushout when `ι` has exactly two elements.

-/

namespace CategoryTheory.Limits.Multicofork.IsColimit

variable {C : Type*} [Category C] {J : MultispanShape} [Unique J.L]
  {I : MultispanIndex J C} (c : Multicofork I)
  (h : {J.fst default, J.snd default} = Set.univ) (h' : J.fst default ≠ J.snd default)

namespace isPushout

variable (s : PushoutCocone (I.fst default) (I.snd default))

open Classical in
/-- Given a multispan shape `J` which is essentially `.ofLinearOrder ι`
(where `ι` has exactly two elements), this is the multicofork
deduced from a pushout cocone. -/
noncomputable def multicofork : Multicofork I :=
  Multicofork.ofπ _ s.pt
    (fun k ↦
      if hk : k = J.fst default then
        eqToHom (by simp [hk]) ≫ s.inl
      else
        eqToHom (by
          obtain rfl : k = J.snd default := by
            have := h.symm.le (Set.mem_univ k)
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
            tauto
          rfl) ≫ s.inr)
    (by
      rw [Unique.forall_iff]
      simpa [h'.symm] using s.condition)

@[simp]
lemma multicofork_π_eq_inl : (multicofork h h' s).π (J.fst default) = s.inl := by
  dsimp only [multicofork, ofπ, π]
  rw [dif_pos rfl, eqToHom_refl, Category.id_comp]

@[simp]
lemma multicofork_π_eq_inr : (multicofork h h' s).π (J.snd default) = s.inr := by
  dsimp only [multicofork, ofπ, π]
  rw [dif_neg h'.symm, eqToHom_refl, Category.id_comp]

end isPushout

include h h' in
/-- A multicoequalizer for `I : MultispanIndex J C` is also
a pushout when `J` is essentially `.ofLinearOrder ι` where
`ι` contains exactly two elements. -/
lemma isPushout (hc : IsColimit c) :
    IsPushout (I.fst default) (I.snd default) (c.π (J.fst default)) (c.π (J.snd default)) where
  w := c.condition _
  isColimit' := ⟨PushoutCocone.IsColimit.mk _
    (fun s ↦ hc.desc (isPushout.multicofork h h' s))
    (fun s ↦ by simpa using hc.fac (isPushout.multicofork h h' s) (.right (J.fst default)))
    (fun s ↦ by simpa using hc.fac (isPushout.multicofork h h' s) (.right (J.snd default)))
    (fun s m h₁ h₂ ↦ by
      apply Multicofork.IsColimit.hom_ext hc
      intro k
      have := h.symm.le (Set.mem_univ k)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
      obtain rfl | rfl := this
      · simpa [h₁] using (hc.fac (isPushout.multicofork h h' s) (.right (J.fst default))).symm
      · simpa [h₂] using (hc.fac (isPushout.multicofork h h' s) (.right (J.snd default))).symm)⟩

end CategoryTheory.Limits.Multicofork.IsColimit
