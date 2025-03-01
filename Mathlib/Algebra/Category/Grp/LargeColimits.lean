/-
Copyright (c) 2025 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Module.CharacterModule
import Mathlib.Algebra.Group.Equiv.Basic

/-!
# Existence of "big" colimits in the category of additive commutative groups

If `F : J ⥤ AddCommGrp.{w}` is a functor, we show that `F` admits a colimit if and only
if `Colimits.Quot F` (the quotient of the direct sum of the commutative groups `F.obj j`
by the relations given by the morphisms in the diagram) is `w`-small.

-/

universe w u v

open CategoryTheory Limits

namespace AddCommGrp

variable {J : Type u} [Category.{v} J] {F : J ⥤ AddCommGrp.{w}} (c : Cocone F)

open Colimits

/--
If `c` is a cocone of `F` such that `Quot.desc F c` is bijective, then `c` is a colimit
cocone of `F`.
-/
lemma isColimit_iff_bijective_desc [DecidableEq J] :
     Nonempty (IsColimit c) ↔ Function.Bijective (Quot.desc F c) := by
  refine ⟨fun ⟨hc⟩ => ?_, fun h ↦ Nonempty.intro (isColimit_of_bijective_desc F c h)⟩
  change Function.Bijective (Quot.desc F c).toIntLinearMap
  rw [← CharacterModule.dual_bijective_iff_bijective]
  refine ⟨fun χ ψ eq ↦ ?_, fun χ ↦ ?_⟩
  · apply (AddMonoidHom.postcompEquiv (@AddEquiv.ulift (AddCircle (1 : ℚ)) _).symm _).injective
    apply ofHom_injective
    refine hc.hom_ext (fun j ↦ ?_)
    ext x
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ← Quot.ι_desc _ c j x]
    simp only [hom_ofHom, AddMonoidHom.postcompEquiv_apply, AddMonoidHom.comp_apply]
    exact DFunLike.congr_fun eq (Quot.ι F j x)
  · set c' : Cocone F :=
      { pt := AddCommGrp.of (ULift (AddCircle (1 : ℚ)))
        ι :=
          { app j := AddCommGrp.ofHom (((@AddEquiv.ulift _ _).symm.toAddMonoidHom.comp χ).comp
                       (Quot.ι F j))
            naturality {j j'} u := by
              ext
              dsimp
              rw [Quot.map_ι F (f := u)] } }
    use AddEquiv.ulift.toAddMonoidHom.comp (hc.desc c').hom
    refine Quot.addMonoidHom_ext _ (fun j x ↦ ?_)
    dsimp
    rw [Quot.ι_desc]
    change AddEquiv.ulift ((c.ι.app j ≫ hc.desc c') x) = _
    rw [hc.fac]
    dsimp [c']
    rw [AddEquiv.apply_symm_apply]

/--
A functor `F : J ⥤ AddCommGrp.{w}` has a colimit if and only if `Colimits.Quot F` is
`w`-small.
-/
lemma hasColimit_iff_small_quot [DecidableEq J] : HasColimit F ↔ Small.{w} (Quot F) :=
  ⟨fun _ ↦ Small.mk ⟨_, ⟨(Equiv.ofBijective _ ((isColimit_iff_bijective_desc (colimit.cocone F)).mp
    ⟨colimit.isColimit _⟩))⟩⟩, hasColimit_of_small_quot F⟩

end AddCommGrp
