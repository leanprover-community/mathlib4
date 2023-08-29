/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.Topology.Sheaves.SheafCondition.Sites

#align_import topology.sheaves.punit from "leanprover-community/mathlib"@"d39590fc8728fbf6743249802486f8c91ffe07bc"

/-!
# Presheaves on `PUnit`

Presheaves on `PUnit` satisfy sheaf condition iff its value at empty set is a terminal object.
-/


namespace TopCat.Presheaf

universe u v w

open CategoryTheory CategoryTheory.Limits TopCat Opposite

variable {C : Type u} [Category.{v} C]

theorem isSheaf_of_isTerminal_of_indiscrete {X : TopCat.{w}} (hind : X.str = ⊤) (F : Presheaf C X)
    (it : IsTerminal <| F.obj <| op ⊥) : F.IsSheaf := fun c U s hs => by
  obtain rfl | hne := eq_or_ne U ⊥
  -- ⊢ Presieve.IsSheafFor (F ⋙ coyoneda.obj (op c)) s.arrows
  · intro _ _
    -- ⊢ ∃! t, Presieve.FamilyOfElements.IsAmalgamation x✝ t
    rw [@exists_unique_iff_exists _ ⟨fun _ _ => _⟩]
    -- ⊢ ∃ x, Presieve.FamilyOfElements.IsAmalgamation x✝ x
    · refine' ⟨it.from _, fun U hU hs => IsTerminal.hom_ext _ _ _⟩
      -- ⊢ IsTerminal (F.obj (op U))
      rwa [le_bot_iff.1 hU.le]
      -- 🎉 no goals
    · apply it.hom_ext
      -- 🎉 no goals
  · convert Presieve.isSheafFor_top_sieve (F ⋙ coyoneda.obj (@op C c))
    -- ⊢ s = ⊤
    rw [← Sieve.id_mem_iff_eq_top]
    -- ⊢ s.arrows (𝟙 U)
    have := (U.eq_bot_or_top hind).resolve_left hne
    -- ⊢ s.arrows (𝟙 U)
    subst this
    -- ⊢ s.arrows (𝟙 ⊤)
    obtain he | ⟨⟨x⟩⟩ := isEmpty_or_nonempty X
    -- ⊢ s.arrows (𝟙 ⊤)
    · exact (hne <| SetLike.ext'_iff.2 <| Set.univ_eq_empty_iff.2 he).elim
      -- 🎉 no goals
    obtain ⟨U, f, hf, hm⟩ := hs x _root_.trivial
    -- ⊢ s.arrows (𝟙 ⊤)
    obtain rfl | rfl := U.eq_bot_or_top hind
    -- ⊢ s.arrows (𝟙 ⊤)
    · cases hm
      -- 🎉 no goals
    · convert hf
      -- 🎉 no goals
set_option linter.uppercaseLean3 false
#align Top.presheaf.is_sheaf_of_is_terminal_of_indiscrete TopCat.Presheaf.isSheaf_of_isTerminal_of_indiscrete

theorem isSheaf_iff_isTerminal_of_indiscrete {X : TopCat.{w}} (hind : X.str = ⊤)
    (F : Presheaf C X) : F.IsSheaf ↔ Nonempty (IsTerminal <| F.obj <| op ⊥) :=
  ⟨fun h => ⟨Sheaf.isTerminalOfEmpty ⟨F, h⟩⟩, fun ⟨it⟩ =>
    isSheaf_of_isTerminal_of_indiscrete hind F it⟩
#align Top.presheaf.is_sheaf_iff_is_terminal_of_indiscrete TopCat.Presheaf.isSheaf_iff_isTerminal_of_indiscrete

theorem isSheaf_on_punit_of_isTerminal (F : Presheaf C (TopCat.of PUnit))
    (it : IsTerminal <| F.obj <| op ⊥) : F.IsSheaf :=
  isSheaf_of_isTerminal_of_indiscrete (@Subsingleton.elim (TopologicalSpace PUnit) _ _ _) F it
#align Top.presheaf.is_sheaf_on_punit_of_is_terminal TopCat.Presheaf.isSheaf_on_punit_of_isTerminal

theorem isSheaf_on_punit_iff_isTerminal (F : Presheaf C (TopCat.of PUnit)) :
    F.IsSheaf ↔ Nonempty (IsTerminal <| F.obj <| op ⊥) :=
  ⟨fun h => ⟨Sheaf.isTerminalOfEmpty ⟨F, h⟩⟩, fun ⟨it⟩ => isSheaf_on_punit_of_isTerminal F it⟩
#align Top.presheaf.is_sheaf_on_punit_iff_is_terminal TopCat.Presheaf.isSheaf_on_punit_iff_isTerminal

end TopCat.Presheaf
