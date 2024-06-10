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
  · intro _ _
    rw [@exists_unique_iff_exists _ ⟨fun _ _ => _⟩]
    · refine ⟨it.from _, fun U hU hs => IsTerminal.hom_ext ?_ _ _⟩
      rwa [le_bot_iff.1 hU.le]
    · apply it.hom_ext
  · convert Presieve.isSheafFor_top_sieve (F ⋙ coyoneda.obj (@op C c))
    rw [← Sieve.id_mem_iff_eq_top]
    have := (U.eq_bot_or_top hind).resolve_left hne
    subst this
    obtain he | ⟨⟨x⟩⟩ := isEmpty_or_nonempty X
    · exact (hne <| SetLike.ext'_iff.2 <| Set.univ_eq_empty_iff.2 he).elim
    obtain ⟨U, f, hf, hm⟩ := hs x _root_.trivial
    obtain rfl | rfl := U.eq_bot_or_top hind
    · cases hm
    · convert hf
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
