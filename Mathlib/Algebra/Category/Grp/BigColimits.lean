/-
Copyright (c) 2025 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Module.CharacterModule
import Mathlib.Algebra.Group.Equiv.Basic

/-!
# The category of additive commutative groups has all colimits.

This file constructs colimits in the categpry of additive commutative groups, as
quotients of finitely supported functions.

-/

universe w u v

open CategoryTheory Limits

namespace AddCommGrp

variable {J : Type u} [Category.{v} J] {F : J ⥤ AddCommGrp.{w}} (c : Cocone F)

namespace Colimits

/--
If `c` is a cocone of `F` such that `Quot.desc F c` is bijective, then `c` is a colimit
cocone of `F`.
-/
lemma isColimit_iff_bijective_desc [DecidableEq J] :
     Nonempty (IsColimit c) ↔ Function.Bijective (Quot.desc F c) := by
  constructor
  · refine fun ⟨hc⟩ => ?_
    change Function.Bijective (Quot.desc F c).toIntLinearMap
    rw [← CharacterModule.dual_bijective_iff_bijective]
    constructor
    · intro χ ψ eq
      dsimp at eq
      set A := ULift.{w} (AddCircle (1 : ℚ))
      suffices eq : ofHom (AddEquiv.ulift.symm.toAddMonoidHom.comp χ) =
          ofHom (AddEquiv.ulift.symm.toAddMonoidHom.comp ψ) by
        apply (AddMonoidHom.postcompEquiv (@AddEquiv.ulift (AddCircle (1 : ℚ)) _).symm _).injective
        dsimp at eq ⊢
        ext
        rw [← ofHom_apply, ← ofHom_apply, eq]
      refine hc.hom_ext (fun j ↦ ?_)
      ext x
      change (ofHom (AddEquiv.ulift.symm.toAddMonoidHom.comp χ)) _ =
        (ofHom (AddEquiv.ulift.symm.toAddMonoidHom.comp ψ)) _
      dsimp
      simp only [EmbeddingLike.apply_eq_iff_eq]
      erw [← Quot.ι_desc _ c j x]
      change χ.comp (Quot.desc F c).toIntLinearMap.toAddMonoidHom _ =
        ψ.comp (Quot.desc F c).toIntLinearMap.toAddMonoidHom _
      rw [eq]
    · intro χ
      set c' : Cocone F :=
        { pt := AddCommGrp.of (ULift (AddCircle (1 : ℚ)))
          ι :=
            { app j := AddCommGrp.ofHom (((@AddEquiv.ulift _ _).symm.toAddMonoidHom.comp χ).comp
                         (Quot.ι F j))
              naturality {j j'} u := by
                ext
                change ofHom ((AddEquiv.ulift.symm.toAddMonoidHom.comp χ).comp (Quot.ι F j'))
                  (F.map u _) = _
                dsimp
                rw [Quot.map_ι F (f := u)]
                rfl } }
      use AddEquiv.ulift.toAddMonoidHom.comp (hc.desc c')
      refine Quot.addMonoidHom_ext _ (fun j x ↦ ?_)
      dsimp
      rw [Quot.ι_desc]
      change AddEquiv.ulift ((c.ι.app j ≫ hc.desc c') x) = _
      rw [hc.fac]
      dsimp [c']
      rw [AddEquiv.apply_symm_apply]
  · exact fun h ↦ Nonempty.intro (isColimit_of_bijective_desc F c h)

end Colimits

end AddCommGrp
