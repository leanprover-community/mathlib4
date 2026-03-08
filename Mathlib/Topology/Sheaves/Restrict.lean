module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

@[expose] public section

universe u

variable {X : TopCat.{u}}

open TopologicalSpace CategoryTheory Topology Opposite

variable (C : Type*) [Category* C] {X : TopCat.{u}} {Y : TopCat.{u}} {f : Y ⟶ X}
  (hf : IsOpenEmbedding f)

namespace TopCat.Sheaf

abbrev restrict : Sheaf C X ⥤ Sheaf C Y := by
  haveI := hf.functor_isContinuous
  exact hf.functor.sheafPushforwardContinuous C ..

abbrev restrictPushforwardAdjunction : restrict C hf ⊣ pushforward C f := by
  haveI := hf.functor_isContinuous
  exact Adjunction.sheafPushforwardContinuous hf.isOpenMap.adjunction ..

variable (F : Sheaf C X) (U V : Opens X)

abbrev toRestrict := (restrictPushforwardAdjunction C U.isOpenEmbedding).unit

lemma toRestrict_obj_obj_obj :
    ((restrict C U.isOpenEmbedding ⋙ pushforward C U.inclusion').obj F).obj.obj (op V) =
    F.obj.obj (op (U.isOpenEmbedding.functor.obj ((Opens.map U.inclusion').obj V))) := rfl

example : U.isOpenEmbedding.functor.obj ((Opens.map U.inclusion').obj V) = U ⊓ V := by aesop

lemma toRestrict_app_hom_app : ((toRestrict C U).app F).hom.app (op V) =
    F.obj.map (U.isOpenEmbedding.isOpenMap.adjunction.counit.app V).op := by simp

end TopCat.Sheaf

namespace AlgebraicGeometry.Scheme.Modules

variable (U X : Scheme.{u}) (f : U ⟶ X) [hf : IsOpenImmersion f] (M : X.Modules)

noncomputable def sheaf : TopCat.Sheaf AddCommGrpCat X := (SheafOfModules.toSheaf _).obj M

#check ((restrictAdjunction f).unit.app M)
#check M.sheaf
#check (SheafOfModules.toSheaf _).obj ((restrictFunctor f ⋙ pushforward f).obj M)
#check hf.base_open
#check M.presheaf
#check (TopCat.Sheaf.restrict _ hf.base_open ⋙ TopCat.Sheaf.pushforward _ f.base).obj M.sheaf

example : ((restrictFunctor f ⋙ pushforward f).obj M).sheaf =
  (TopCat.Sheaf.restrict _ hf.base_open ⋙ TopCat.Sheaf.pushforward _ f.base).obj M.sheaf := rfl

example : (SheafOfModules.toSheaf _).map ((restrictAdjunction f).unit.app M) =
    (TopCat.Sheaf.restrictPushforwardAdjunction _ hf.base_open).unit.app M.sheaf := rfl

end AlgebraicGeometry.Scheme.Modules
