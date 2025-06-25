/-
Copyright (c) 2024 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathlib.CategoryTheory.Grothendieck
import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# (Co)limits on the (strict) Grothendieck Construction

* Shows that if a functor `G : Grothendieck F ⥤ H`, with `F : C ⥤ Cat`, has a colimit, and every
  fiber of `G` has a colimit, then so does the fiberwise colimit functor `C ⥤ H`.
* Vice versa, if a each fiber of `G` has a colimit and the fiberwise colimit functor has a colimit,
  then `G` has a colimit.
* Shows that colimits of functors on the Grothendieck construction are colimits of
  "fibered colimits", i.e. of applying the colimit to each fiber of the functor.
* Derives `HasColimitsOfShape (Grothendieck F) H` with `F : C ⥤ Cat` from the presence of colimits
  on each fiber shape `F.obj X` and on the base category `C`.

-/

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

namespace Limits

variable {C : Type u₁} [Category.{v₁} C]
variable {F : C ⥤ Cat}
variable {H : Type u₂} [Category.{v₂} H]
variable (G : Grothendieck F ⥤ H)


noncomputable section

variable [∀ {X Y : C} (f : X ⟶ Y), HasColimit (F.map f ⋙ Grothendieck.ι F Y ⋙ G)]

@[local instance]
lemma hasColimit_ι_comp : ∀ X, HasColimit (Grothendieck.ι F X ⋙ G) :=
  fun X => hasColimit_of_iso (F := F.map (𝟙 _) ⋙ Grothendieck.ι F X ⋙ G) <|
    (Functor.leftUnitor (Grothendieck.ι F X ⋙ G)).symm ≪≫
    (isoWhiskerRight (eqToIso (F.map_id X).symm) (Grothendieck.ι F X ⋙ G))

/-- A functor taking a colimit on each fiber of a functor `G : Grothendieck F ⥤ H`. -/
@[simps]
def fiberwiseColimit : C ⥤ H where
  obj X := colimit (Grothendieck.ι F X ⋙ G)
  map {X Y} f := colimMap (whiskerRight (Grothendieck.ιNatTrans f) G ≫
    (Functor.associator _ _ _).hom) ≫ colimit.pre (Grothendieck.ι F Y ⋙ G) (F.map f)
  map_id X := by
    ext d
    simp only [Functor.comp_obj, Grothendieck.ιNatTrans, Grothendieck.ι_obj, ι_colimMap_assoc,
      NatTrans.comp_app, whiskerRight_app, Functor.associator_hom_app, Category.comp_id,
      colimit.ι_pre]
    conv_rhs => rw [← colimit.eqToHom_comp_ι (Grothendieck.ι F X ⋙ G)
      (j := (F.map (𝟙 X)).obj d) (by simp)]
    rw [← eqToHom_map G (by simp), Grothendieck.eqToHom_eq]
    rfl
  map_comp {X Y Z} f g := by
    ext d
    simp only [Functor.comp_obj, Grothendieck.ιNatTrans, ι_colimMap_assoc, NatTrans.comp_app,
      whiskerRight_app, Functor.associator_hom_app, Category.comp_id, colimit.ι_pre, Category.assoc,
      colimit.ι_pre_assoc]
    rw [← Category.assoc, ← G.map_comp]
    conv_rhs => rw [← colimit.eqToHom_comp_ι (Grothendieck.ι F Z ⋙ G)
      (j := (F.map (f ≫ g)).obj d) (by simp)]
    rw [← Category.assoc, ← eqToHom_map G (by simp), ← G.map_comp, Grothendieck.eqToHom_eq]
    congr 2
    fapply Grothendieck.ext
    · simp only [Cat.comp_obj, eqToHom_refl, Category.assoc, Grothendieck.comp_base,
        Category.comp_id]
    · simp only [Grothendieck.ι_obj, Cat.comp_obj, eqToHom_refl, Cat.id_obj,
        Grothendieck.comp_base, Category.comp_id, Grothendieck.comp_fiber, Functor.map_id]
      conv_rhs => enter [2, 1]; rw [eqToHom_map (F.map (𝟙 Z))]
      conv_rhs => rw [eqToHom_trans, eqToHom_trans]

variable (H) (F) in
/-- Similar to `colimit` and `colim`, taking fiberwise colimits is a functor
`(Grothendieck F ⥤ H) ⥤ (C ⥤ H)` between functor categories. -/
@[simps]
def fiberwiseColim [∀ c, HasColimitsOfShape (F.obj c) H] : (Grothendieck F ⥤ H) ⥤ (C ⥤ H) where
  obj G := fiberwiseColimit G
  map α :=
    { app := fun c => colim.map (whiskerLeft _ α)
      naturality := fun c₁ c₂ f => by apply colimit.hom_ext; simp }
  map_id G := by ext; simp; apply Functor.map_id colim
  map_comp α β := by ext; simp; apply Functor.map_comp colim

/-- Every functor `G : Grothendieck F ⥤ H` induces a natural transformation from `G` to the
composition of the forgetful functor on `Grothendieck F` with the fiberwise colimit on `G`. -/
@[simps]
def natTransIntoForgetCompFiberwiseColimit :
    G ⟶ Grothendieck.forget F ⋙ fiberwiseColimit G where
  app X := colimit.ι (Grothendieck.ι F X.base ⋙ G) X.fiber
  naturality _ _ f := by
    simp only [Functor.comp_obj, Grothendieck.forget_obj, fiberwiseColimit_obj, Functor.comp_map,
      Grothendieck.forget_map, fiberwiseColimit_map, ι_colimMap_assoc, Grothendieck.ι_obj,
      NatTrans.comp_app, whiskerRight_app, Functor.associator_hom_app, Category.comp_id,
      colimit.ι_pre]
    rw [← colimit.w (Grothendieck.ι F _ ⋙ G) f.fiber]
    simp only [← Category.assoc, Functor.comp_obj, Functor.comp_map, ← G.map_comp]
    congr 2
    apply Grothendieck.ext <;> simp

variable {G} in
/-- A cocone on a functor `G : Grothendieck F ⥤ H` induces a cocone on the fiberwise colimit
on `G`. -/
@[simps]
def coconeFiberwiseColimitOfCocone (c : Cocone G) : Cocone (fiberwiseColimit G) where
  pt := c.pt
  ι := { app := fun X => colimit.desc _ (c.whisker (Grothendieck.ι F X)),
         naturality := fun _ _ f => by dsimp; ext; simp }

variable {G} in
/-- If `c` is a colimit cocone on `G : Grockendieck F ⥤ H`, then the induced cocone on the
fiberwise colimit on `G` is a colimit cocone, too. -/
def isColimitCoconeFiberwiseColimitOfCocone {c : Cocone G} (hc : IsColimit c) :
    IsColimit (coconeFiberwiseColimitOfCocone c) where
  desc s := hc.desc <| Cocone.mk s.pt <| natTransIntoForgetCompFiberwiseColimit G ≫
    whiskerLeft (Grothendieck.forget F) s.ι
  fac s c := by dsimp; ext; simp
  uniq s m hm := hc.hom_ext fun X => by
    have := hm X.base
    simp only [Functor.const_obj_obj, IsColimit.fac, NatTrans.comp_app, Functor.comp_obj,
      Grothendieck.forget_obj, fiberwiseColim_obj, natTransIntoForgetCompFiberwiseColimit_app,
      whiskerLeft_app]
    simp only [fiberwiseColim_obj, coconeFiberwiseColimitOfCocone_pt, Functor.const_obj_obj,
      coconeFiberwiseColimitOfCocone_ι_app] at this
    simp [← this]

lemma hasColimit_fiberwiseColimit [HasColimit G] : HasColimit (fiberwiseColimit G) where
  exists_colimit := ⟨⟨_, isColimitCoconeFiberwiseColimitOfCocone (colimit.isColimit _)⟩⟩

variable {G}

/-- For a functor `G : Grothendieck F ⥤ H`, every cocone over `fiberwiseColimit G` induces a
cocone over `G` itself. -/
@[simps]
def coconeOfCoconeFiberwiseColimit (c : Cocone (fiberwiseColimit G)) : Cocone G where
  pt := c.pt
  ι := { app := fun X => colimit.ι (Grothendieck.ι F X.base ⋙ G) X.fiber ≫ c.ι.app X.base
         naturality := fun {X Y} ⟨f, g⟩ => by
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
          rw [← Category.assoc, ← c.w f, ← Category.assoc]
          simp only [fiberwiseColimit_obj, fiberwiseColimit_map, ι_colimMap_assoc,
            Functor.comp_obj, Grothendieck.ι_obj, NatTrans.comp_app, whiskerRight_app,
            Functor.associator_hom_app, Category.comp_id, colimit.ι_pre]
          rw [← colimit.w _ g, ← Category.assoc, Functor.comp_map, ← G.map_comp]
          congr <;> simp }

/-- If a cocone `c` over a functor `G : Grothendieck F ⥤ H` is a colimit, than the induced cocone
`coconeOfFiberwiseCocone G c` -/
def isColimitCoconeOfFiberwiseCocone {c : Cocone (fiberwiseColimit G)} (hc : IsColimit c) :
    IsColimit (coconeOfCoconeFiberwiseColimit c) where
  desc s := hc.desc <| Cocone.mk s.pt <|
    { app := fun X => colimit.desc (Grothendieck.ι F X ⋙ G) (s.whisker _) }
  uniq s m hm := hc.hom_ext <| fun X => by
    simp only [fiberwiseColimit_obj, Functor.const_obj_obj, fiberwiseColimit_map,
      Functor.const_obj_map, Cocone.whisker_pt, id_eq, Functor.comp_obj, Cocone.whisker_ι,
      whiskerLeft_app, NatTrans.comp_app, whiskerRight_app, Functor.associator_hom_app,
      whiskerLeft_twice, eq_mpr_eq_cast, IsColimit.fac]
    simp only [coconeOfCoconeFiberwiseColimit_pt, Functor.const_obj_obj,
      coconeOfCoconeFiberwiseColimit_ι_app, Category.assoc] at hm
    ext d
    simp [hm ⟨X, d⟩]

variable [HasColimit (fiberwiseColimit G)]

variable (G)

/-- We can infer that a functor `G : Grothendieck F ⥤ H`, with `F : C ⥤ Cat`, has a colimit from
the fact that each of its fibers has a colimit and that these fiberwise colimits, as a functor
`C ⥤ H` have a colimit. -/
@[local instance]
lemma hasColimit_of_hasColimit_fiberwiseColimit_of_hasColimit : HasColimit G where
  exists_colimit := ⟨⟨_, isColimitCoconeOfFiberwiseCocone (colimit.isColimit _)⟩⟩

/-- For every functor `G` on the Grothendieck construction `Grothendieck F`, if `G` has a colimit
and every fiber of `G` has a colimit, then taking this colimit is isomorphic to first taking the
fiberwise colimit and then the colimit of the resulting functor. -/
def colimitFiberwiseColimitIso : colimit (fiberwiseColimit G) ≅ colimit G :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit (fiberwiseColimit G))
    (isColimitCoconeFiberwiseColimitOfCocone (colimit.isColimit _))

@[reassoc (attr := simp)]
lemma ι_colimitFiberwiseColimitIso_hom (X : C) (d : F.obj X) :
    colimit.ι (Grothendieck.ι F X ⋙ G) d ≫ colimit.ι (fiberwiseColimit G) X ≫
      (colimitFiberwiseColimitIso G).hom = colimit.ι G ⟨X, d⟩ := by
  simp [colimitFiberwiseColimitIso]

@[reassoc (attr := simp)]
lemma ι_colimitFiberwiseColimitIso_inv (X : Grothendieck F) :
    colimit.ι G X ≫ (colimitFiberwiseColimitIso G).inv =
    colimit.ι (Grothendieck.ι F X.base ⋙ G) X.fiber ≫
      colimit.ι (fiberwiseColimit G) X.base := by
  rw [Iso.comp_inv_eq]
  simp

end

@[instance]
theorem hasColimitsOfShape_grothendieck [∀ X, HasColimitsOfShape (F.obj X) H]
    [HasColimitsOfShape C H] : HasColimitsOfShape (Grothendieck F) H where
  has_colimit _ := hasColimit_of_hasColimit_fiberwiseColimit_of_hasColimit _

noncomputable section FiberwiseColim

variable [∀ (c : C), HasColimitsOfShape (↑(F.obj c)) H] [HasColimitsOfShape C H]

/-- The isomorphism `colimitFiberwiseColimitIso` induces an isomorphism of functors `(J ⥤ C) ⥤ C`
between `fiberwiseColim F H ⋙ colim` and `colim`. -/
@[simps!]
def fiberwiseColimCompColimIso : fiberwiseColim F H ⋙ colim ≅ colim :=
  NatIso.ofComponents (fun G => colimitFiberwiseColimitIso G)
    fun _ => by (iterate 2 apply colimit.hom_ext; intro); simp

/-- Composing `fiberwiseColim F H` with the evaluation functor `(evaluation C H).obj c` is
naturally isomorphic to precomposing the Grothendieck inclusion `Grothendieck.ι` to `colim`. -/
@[simps!]
def fiberwiseColimCompEvaluationIso (c : C) :
    fiberwiseColim F H ⋙ (evaluation C H).obj c ≅
      (whiskeringLeft _ _ _).obj (Grothendieck.ι F c) ⋙ colim :=
  Iso.refl _

end FiberwiseColim

end Limits

end CategoryTheory
