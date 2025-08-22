/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.GroupTheory.MonoidLocalization.Basic

/-!
# Archimedean groups as localizations of submonoids of nonnegative elements

An Archimedean group is the localization of its submonoid of nonnegative elements
at any nontrivial submonoid.
-/

namespace Archimedean

variable {G : Type*} [AddCommGroup G]

/- TODO: multiplicativize Nonneg.inhabited, .zero, .add, .nsmul, .addMonoid, .coeAddMonoidHom,
.isOrderedAddMonoid, .isOrderedCancelAddMonoid, etc. -/
theorem isLocalizationMap [PartialOrder G] [AddLeftMono G] [Archimedean G]
    (S : AddSubmonoid {g : G // 0 ≤ g}) (hS : S ≠ ⊥) : S.IsLocalizationMap Subtype.val :=
  S.isLocalizationMap_of_addGroup Subtype.val_injective fun g ↦
    have ⟨p, hpS, hp0⟩ := (S.bot_or_exists_ne_zero).resolve_left hS
    have ⟨n, le⟩ := arch (-g) (p.2.lt_of_ne <| Subtype.coe_ne_coe.mpr hp0.symm)
    ⟨⟨g + n • p, by simpa using add_le_add_left le g⟩, _, nsmul_mem hpS n, by simp⟩

instance isLocalizationMap_top [LinearOrder G] [AddLeftMono G] [Archimedean G] :
    (⊤ : AddSubmonoid {g : G // 0 ≤ g}).IsLocalizationMap Subtype.val := by
  cases subsingleton_or_nontrivial G
  · exact AddSubmonoid.isLocalizationMap_of_addGroup Subtype.val_injective
      fun g ↦ ⟨0, 0, ⟨⟩, Subsingleton.elim ..⟩
  · exact isLocalizationMap ⊤ top_ne_bot

example : (⊤ : AddSubmonoid ℚ≥0).IsLocalizationMap ((↑) : ℚ≥0 → ℚ) := isLocalizationMap_top

end Archimedean
