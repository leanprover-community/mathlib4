/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Products.Bifunctor

/-!
# A Fubini theorem for categorical (co)limits

We prove that $lim_{J × K} G = lim_J (lim_K G(j, -))$ for a functor `G : J × K ⥤ C`,
when all the appropriate limits exist.

We begin working with a functor `F : J ⥤ K ⥤ C`. We'll write `G : J × K ⥤ C` for the associated
"uncurried" functor.

In the first part, given a coherent family `D` of limit cones over the functors `F.obj j`,
and a cone `c` over `G`, we construct a cone over the cone points of `D`.
We then show that if `c` is a limit cone, the constructed cone is also a limit cone.

In the second part, we state the Fubini theorem in the setting where limits are
provided by suitable `HasLimit` classes.

We construct
`limitUncurryIsoLimitCompLim F : limit (uncurry.obj F) ≅ limit (F ⋙ lim)`
and give simp lemmas characterising it.
For convenience, we also provide
`limitIsoLimitCurryCompLim G : limit G ≅ limit ((curry.obj G) ⋙ lim)`
in terms of the uncurried functor.

All statements have their counterpart for colimits.
-/

@[expose] public section


open CategoryTheory Functor

namespace CategoryTheory.Limits

variable {J K : Type*} [Category* J] [Category* K]
variable {C : Type*} [Category* C]
variable (F : J ⥤ K ⥤ C) (G : J × K ⥤ C)

-- We could try introducing a "dependent functor type" to handle this?
/-- A structure carrying a diagram of cones over the functors `F.obj j`.
-/
structure DiagramOfCones where
  /-- For each object, a cone. -/
  obj : ∀ j : J, Cone (F.obj j)
  /-- For each map, a map of cones. -/
  map : ∀ {j j' : J} (f : j ⟶ j'), (Cone.postcompose (F.map f)).obj (obj j) ⟶ obj j'
  id : ∀ j : J, (map (𝟙 j)).hom = 𝟙 _ := by cat_disch
  comp : ∀ {j₁ j₂ j₃ : J} (f : j₁ ⟶ j₂) (g : j₂ ⟶ j₃),
    (map (f ≫ g)).hom = (map f).hom ≫ (map g).hom := by cat_disch

/-- A structure carrying a diagram of cocones under the functors `F.obj j`.
-/
structure DiagramOfCocones where
  /-- For each object, a cocone. -/
  obj : ∀ j : J, Cocone (F.obj j)
  /-- For each map, a map of cocones. -/
  map : ∀ {j j' : J} (f : j ⟶ j'), (obj j) ⟶ (Cocone.precompose (F.map f)).obj (obj j')
  id : ∀ j : J, (map (𝟙 j)).hom = 𝟙 _ := by cat_disch
  comp : ∀ {j₁ j₂ j₃ : J} (f : j₁ ⟶ j₂) (g : j₂ ⟶ j₃),
    (map (f ≫ g)).hom = (map f).hom ≫ (map g).hom := by cat_disch

variable {F}

/-- Extract the functor `J ⥤ C` consisting of the cone points and the maps between them,
from a `DiagramOfCones`.
-/
@[simps]
def DiagramOfCones.conePoints (D : DiagramOfCones F) : J ⥤ C where
  obj j := (D.obj j).pt
  map f := (D.map f).hom
  map_id j := D.id j
  map_comp f g := D.comp f g

/-- Extract the functor `J ⥤ C` consisting of the cocone points and the maps between them,
from a `DiagramOfCocones`.
-/
@[simps]
def DiagramOfCocones.coconePoints (D : DiagramOfCocones F) : J ⥤ C where
  obj j := (D.obj j).pt
  map f := (D.map f).hom
  map_id j := D.id j
  map_comp f g := D.comp f g

set_option backward.isDefEq.respectTransparency false in
/-- Given a diagram `D` of limit cones over the `F.obj j`, and a cone over `uncurry.obj F`,
we can construct a cone over the diagram consisting of the cone points from `D`.
-/
@[simps]
def coneOfConeUncurry {D : DiagramOfCones F} (Q : ∀ j, IsLimit (D.obj j))
    (c : Cone (uncurry.obj F)) : Cone D.conePoints where
  pt := c.pt
  π :=
    { app := fun j =>
        (Q j).lift
          { pt := c.pt
            π :=
              { app := fun k => c.π.app (j, k)
                naturality := fun k k' f => by
                  simpa using @NatTrans.naturality _ _ _ _ _ _ c.π (j, k) (j, k') (𝟙 j, f) } }
      naturality := fun j j' f =>
        (Q j').hom_ext
          (fun k => by simpa using @NatTrans.naturality _ _ _ _ _ _ c.π (j, k) (j', k) (f, 𝟙 k)) }

set_option backward.isDefEq.respectTransparency false in
/-- Given a diagram `D` of limit cones over the `curry.obj G j`, and a cone over `G`,
we can construct a cone over the diagram consisting of the cone points from `D`.
-/
@[simps]
def coneOfConeCurry {D : DiagramOfCones (curry.obj G)} (Q : ∀ j, IsLimit (D.obj j))
    (c : Cone G) : Cone D.conePoints where
  pt := c.pt
  π :=
    { app j := (Q j).lift
        { pt := c.pt
          π := { app k := c.π.app (j, k) } }
      naturality {_ j'} _ := (Q j').hom_ext (by simp) }

set_option backward.isDefEq.respectTransparency false in
open scoped Prod in
/-- Given a diagram `D` of colimit cocones under the `F.obj j`, and a cocone under
`uncurry.obj F`, we can construct a cocone under the diagram consisting of the cocone
points from `D`.
-/
@[simps]
def coconeOfCoconeUncurry {D : DiagramOfCocones F} (Q : ∀ j, IsColimit (D.obj j))
    (c : Cocone (uncurry.obj F)) : Cocone D.coconePoints where
  pt := c.pt
  ι :=
    { app := fun j =>
        (Q j).desc
          { pt := c.pt
            ι :=
              { app := fun k => c.ι.app (j, k)
                naturality := fun k k' f => by
                  dsimp; simp only [Category.comp_id]
                  conv_lhs =>
                    arg 1; equals (F.map (𝟙 _)).app _ ≫ (F.obj j).map f =>
                      simp
                  conv_lhs => arg 1; rw [← uncurry_obj_map F (𝟙 j ×ₘ f)]
                  rw [c.w] } }
      naturality := fun j j' f =>
        (Q j).hom_ext
          (by
            dsimp
            intro k
            simp only [Limits.CoconeMorphism.w_assoc, Limits.Cocone.precompose_obj_ι,
              Limits.IsColimit.fac, NatTrans.comp_app, Category.comp_id,
              Category.assoc]
            have := @NatTrans.naturality _ _ _ _ _ _ c.ι (j, k) (j', k) (f, 𝟙 k)
            dsimp at this
            simp only [Category.comp_id, CategoryTheory.Functor.map_id] at this
            exact this) }

set_option backward.isDefEq.respectTransparency false in
/-- Given a diagram `D` of colimit cocones under the `curry.obj G j`, and a cocone under `G`,
we can construct a cocone under the diagram consisting of the cocone points from `D`.
-/
@[simps]
def coconeOfCoconeCurry {D : DiagramOfCocones (curry.obj G)} (Q : ∀ j, IsColimit (D.obj j))
    (c : Cocone G) : Cocone D.coconePoints where
  pt := c.pt
  ι :=
    { app j := (Q j).desc
        { pt := c.pt
          ι := { app k := c.ι.app (j, k) } }
      naturality {j _} _ := (Q j).hom_ext (by simp) }

set_option backward.isDefEq.respectTransparency false in
/-- `coneOfConeUncurry Q c` is a limit cone when `c` is a limit cone.
-/
def coneOfConeUncurryIsLimit {D : DiagramOfCones F} (Q : ∀ j, IsLimit (D.obj j))
    {c : Cone (uncurry.obj F)} (P : IsLimit c) : IsLimit (coneOfConeUncurry Q c) where
  lift s :=
    P.lift
      { pt := s.pt
        π :=
          { app := fun p => s.π.app p.1 ≫ (D.obj p.1).π.app p.2
            naturality := fun p p' f => by
              dsimp; simp only [Category.id_comp, Category.assoc]
              rcases p with ⟨j, k⟩
              rcases p' with ⟨j', k'⟩
              rcases f with ⟨fj, fk⟩
              dsimp
              slice_rhs 3 4 => rw [← NatTrans.naturality]
              slice_rhs 2 3 => rw [← (D.obj j).π.naturality]
              simp only [Functor.const_obj_map, Category.id_comp, Category.assoc]
              have w := (D.map fj).w k'
              dsimp at w
              rw [← w]
              have n := s.π.naturality fj
              dsimp at n
              simp only [Category.id_comp] at n
              rw [n]
              simp } }
  fac s j := by
    apply (Q j).hom_ext
    intro k
    simp
  uniq s m w := by
    refine P.uniq
      { pt := s.pt
        π := _ } m ?_
    rintro ⟨j, k⟩
    dsimp
    rw [← w j]
    simp

set_option backward.isDefEq.respectTransparency false in
/-- If `coneOfConeUncurry Q c` is a limit cone then `c` is in fact a limit cone.
-/
def IsLimit.ofConeOfConeUncurry {D : DiagramOfCones F} (Q : ∀ j, IsLimit (D.obj j))
    {c : Cone (uncurry.obj F)} (P : IsLimit (coneOfConeUncurry Q c)) : IsLimit c :=
  -- These constructions are used in various fields of the proof so we abstract them here.
  letI E (j : J) : Prod.sectR j K ⋙ uncurry.obj F ≅ F.obj j :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _)
  letI S (s : Cone (uncurry.obj F)) : Cone D.conePoints :=
    { pt := s.pt
      π :=
        { app j := (Q j).lift <|
            (Cone.postcompose (E j).hom).obj <| s.whisker (Prod.sectR j K)
          naturality {j' j} f := (Q j).hom_ext <|
            fun k ↦ by simpa [E] using s.π.naturality ((Prod.sectL J k).map f) } }
  { lift s := P.lift (S s)
    fac s p := by
      have h1 := (Q p.1).fac ((Cone.postcompose (E p.1).hom).obj <|
        s.whisker (Prod.sectR p.1 K)) p.2
      simp only [Functor.comp_obj, Prod.sectR_obj, uncurry_obj_obj,
        Cone.postcompose_obj_pt, Cone.whisker_pt, Cone.postcompose_obj_π,
        Cone.whisker_π, NatTrans.comp_app, Functor.const_obj_obj, whiskerLeft_app,
        NatIso.ofComponents_hom_app, Iso.refl_hom, Category.comp_id, E] at h1
      have h2 := (P.fac (S s) p.1)
      dsimp only [Functor.comp_obj, Prod.sectR_obj, uncurry_obj_obj, NatTrans.id_app,
        Functor.const_obj_obj, DiagramOfCones.conePoints_obj, DiagramOfCones.conePoints_map,
        Functor.const_obj_map, id_eq, Cone.postcompose_obj_pt, Cone.whisker_pt,
        Cone.postcompose_obj_π, Cone.whisker_π, NatTrans.comp_app, whiskerLeft_app,
        NatIso.ofComponents_hom_app, Iso.refl_hom, Prod.sectL_obj, Prod.sectL_map, eq_mp_eq_cast,
        eq_mpr_eq_cast, coneOfConeUncurry_pt, coneOfConeUncurry_π_app, S, E] at h2 ⊢
      simp [← h1, ← h2]
    uniq s f hf := P.uniq (s := S s) _ <|
      fun j ↦ (Q j).hom_ext <| fun k ↦ by simpa [S, E] using hf (j, k) }

set_option backward.isDefEq.respectTransparency false in
/-- `coconeOfCoconeUncurry Q c` is a colimit cocone when `c` is a colimit cocone.
-/
def coconeOfCoconeUncurryIsColimit {D : DiagramOfCocones F} (Q : ∀ j, IsColimit (D.obj j))
    {c : Cocone (uncurry.obj F)} (P : IsColimit c) : IsColimit (coconeOfCoconeUncurry Q c) where
  desc s :=
    P.desc
      { pt := s.pt
        ι :=
          { app := fun p => (D.obj p.1).ι.app p.2 ≫ s.ι.app p.1
            naturality := fun p p' f => by
              dsimp; simp only [Category.assoc]
              rcases p with ⟨j, k⟩
              rcases p' with ⟨j', k'⟩
              rcases f with ⟨fj, fk⟩
              dsimp
              slice_lhs 2 3 => rw [(D.obj j').ι.naturality]
              simp only [Functor.const_obj_map, Category.assoc]
              have w := (D.map fj).w k
              dsimp at w
              slice_lhs 1 2 => rw [← w]
              have n := s.ι.naturality fj
              dsimp at n
              simp only [Category.comp_id] at n
              rw [← n]
              simp } }
  fac s j := by
    apply (Q j).hom_ext
    intro k
    simp
  uniq s m w := by
    refine P.uniq
      { pt := s.pt
        ι := _ } m ?_
    rintro ⟨j, k⟩
    dsimp
    rw [← w j]
    simp

set_option backward.isDefEq.respectTransparency false in
/-- If `coconeOfCoconeUncurry Q c` is a colimit cocone then `c` is in fact a colimit
cocone. -/
def IsColimit.ofCoconeUncurry {D : DiagramOfCocones F}
    (Q : ∀ j, IsColimit (D.obj j)) {c : Cocone (uncurry.obj F)}
    (P : IsColimit (coconeOfCoconeUncurry Q c)) : IsColimit c :=
  -- These constructions are used in various fields of the proof so we abstract them here.
  letI E (j : J) : (Prod.sectR j K ⋙ uncurry.obj F ≅ F.obj j) :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _)
  letI S (s : Cocone (uncurry.obj F)) : Cocone D.coconePoints :=
    { pt := s.pt
      ι :=
        { app j := (Q j).desc <|
            (Cocone.precompose (E j).inv).obj <| s.whisker (Prod.sectR j K)
          naturality {j j'} f := (Q j).hom_ext <|
            fun k ↦ by simpa [E] using s.ι.naturality ((Prod.sectL J k).map f) } }
  { desc s := P.desc (S s)
    fac s p := by
      have h1 := (Q p.1).fac ((Cocone.precompose (E p.1).inv).obj <|
        s.whisker (Prod.sectR p.1 K)) p.2
      simp only [Functor.comp_obj, Prod.sectR_obj, uncurry_obj_obj,
        Cocone.precompose_obj_pt, Cocone.whisker_pt, Functor.const_obj_obj,
        Cocone.precompose_obj_ι, Cocone.whisker_ι, NatTrans.comp_app, NatIso.ofComponents_inv_app,
        Iso.refl_inv, whiskerLeft_app, Category.id_comp, E] at h1
      have h2 := (P.fac (S s) p.1)
      dsimp only [DiagramOfCocones.coconePoints_obj, Functor.comp_obj, Prod.sectR_obj,
        uncurry_obj_obj, NatTrans.id_app, Functor.const_obj_obj, DiagramOfCocones.coconePoints_map,
        Functor.const_obj_map, id_eq, Cocone.precompose_obj_pt, Cocone.whisker_pt,
        Cocone.precompose_obj_ι, Cocone.whisker_ι, NatTrans.comp_app, NatIso.ofComponents_inv_app,
        Iso.refl_inv, whiskerLeft_app, Prod.sectL_obj, Prod.sectL_map, eq_mp_eq_cast,
        eq_mpr_eq_cast, coconeOfCoconeUncurry_pt, coconeOfCoconeUncurry_ι_app, S, E] at h2 ⊢
      simp [← h1, ← h2]
    uniq s f hf := P.uniq (s := S s) _ <|
      fun j ↦ (Q j).hom_ext <| fun k ↦ by simpa [S, E] using hf (j, k) }

section

variable (F)
variable [HasLimitsOfShape K C]

/-- Given a functor `F : J ⥤ K ⥤ C`, with all needed limits,
we can construct a diagram consisting of the limit cone over each functor `F.obj j`,
and the universal cone morphisms between these.
-/
@[simps]
noncomputable def DiagramOfCones.mkOfHasLimits : DiagramOfCones F where
  obj j := limit.cone (F.obj j)
  map f := { hom := lim.map (F.map f) }

-- Satisfying the inhabited linter.
noncomputable instance diagramOfConesInhabited : Inhabited (DiagramOfCones F) :=
  ⟨DiagramOfCones.mkOfHasLimits F⟩

@[simp]
theorem DiagramOfCones.mkOfHasLimits_conePoints :
    (DiagramOfCones.mkOfHasLimits F).conePoints = F ⋙ lim :=
  rfl

section

variable [HasLimit (curry.obj G ⋙ lim)]

set_option backward.isDefEq.respectTransparency false in
/-- Given a functor `G : J × K ⥤ C` such that `(curry.obj G ⋙ lim)` makes sense and has a limit,
we can construct a cone over `G` with `limit (curry.obj G ⋙ lim)` as a cone point -/
noncomputable def coneOfHasLimitCurryCompLim : Cone G :=
  let Q : DiagramOfCones (curry.obj G) := .mkOfHasLimits _
  { pt := limit (curry.obj G ⋙ lim),
    π :=
    { app x := limit.π (curry.obj G ⋙ lim) x.fst ≫ (Q.obj x.fst).π.app x.snd
      naturality {x y} := fun ⟨f₁, f₂⟩ ↦ by
        have := (Q.obj x.1).w f₂
        dsimp [Q] at this ⊢
        rw [← limit.w (F := curry.obj G ⋙ lim) (f := f₁)]
        dsimp
        simp only [Category.assoc, Category.id_comp, Prod.fac (f₁, f₂),
          G.map_comp, limMap_π, curry_obj_map_app, reassoc_of% this] } }

set_option backward.isDefEq.respectTransparency false in
/-- The cone `coneOfHasLimitCurryCompLim` is in fact a limit cone.
-/
noncomputable def isLimitConeOfHasLimitCurryCompLim : IsLimit (coneOfHasLimitCurryCompLim G) :=
  let Q : DiagramOfCones (curry.obj G) := .mkOfHasLimits _
  let Q' : ∀ j, IsLimit (Q.obj j) := fun j => limit.isLimit _
  { lift c' := limit.lift (F := curry.obj G ⋙ lim) (coneOfConeCurry G Q' c')
    fac c' f := by simp [coneOfHasLimitCurryCompLim, Q, Q']
    uniq c' f h := by
      dsimp [coneOfHasLimitCurryCompLim] at f h ⊢
      refine limit.hom_ext (F := curry.obj G ⋙ lim) (fun j ↦ limit.hom_ext (fun k ↦ ?_))
      simp [h ⟨j, k⟩, Q'] }

/-- The functor `G` has a limit if `C` has `K`-shaped limits and `(curry.obj G ⋙ lim)` has a limit.
-/
instance : HasLimit G where
  exists_limit :=
    ⟨ { cone := coneOfHasLimitCurryCompLim G
        isLimit := isLimitConeOfHasLimitCurryCompLim G }⟩

end

variable [HasLimit (uncurry.obj F)] [HasLimit (F ⋙ lim)]

/-- The Fubini theorem for a functor `F : J ⥤ K ⥤ C`,
showing that the limit of `uncurry.obj F` can be computed as
the limit of the limits of the functors `F.obj j`.
-/
noncomputable def limitUncurryIsoLimitCompLim : limit (uncurry.obj F) ≅ limit (F ⋙ lim) := by
  let c := limit.cone (uncurry.obj F)
  let P : IsLimit c := limit.isLimit _
  let G := DiagramOfCones.mkOfHasLimits F
  let Q : ∀ j, IsLimit (G.obj j) := fun j => limit.isLimit _
  have Q' := coneOfConeUncurryIsLimit Q P
  have Q'' := limit.isLimit (F ⋙ lim)
  exact IsLimit.conePointUniqueUpToIso Q' Q''

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
theorem limitUncurryIsoLimitCompLim_hom_π_π {j} {k} :
    (limitUncurryIsoLimitCompLim F).hom ≫ limit.π _ j ≫ limit.π _ k = limit.π _ (j, k) := by
  dsimp [limitUncurryIsoLimitCompLim, IsLimit.conePointUniqueUpToIso, IsLimit.uniqueUpToIso]
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
theorem limitUncurryIsoLimitCompLim_inv_π {j} {k} :
    (limitUncurryIsoLimitCompLim F).inv ≫ limit.π _ (j, k) =
      (limit.π _ j ≫ limit.π _ k) := by
  rw [← cancel_epi (limitUncurryIsoLimitCompLim F).hom]
  simp

end

section

variable (F)
variable [HasColimitsOfShape K C]

/-- Given a functor `F : J ⥤ K ⥤ C`, with all needed colimits,
we can construct a diagram consisting of the colimit cocone under each functor `F.obj j`,
and the universal cocone morphisms between these.
-/
@[simps]
noncomputable def DiagramOfCocones.mkOfHasColimits : DiagramOfCocones F where
  obj j := colimit.cocone (F.obj j)
  map f := { hom := colim.map (F.map f) }

-- Satisfying the inhabited linter.
noncomputable instance diagramOfCoconesInhabited : Inhabited (DiagramOfCocones F) :=
  ⟨DiagramOfCocones.mkOfHasColimits F⟩

@[simp]
theorem DiagramOfCocones.mkOfHasColimits_coconePoints :
    (DiagramOfCocones.mkOfHasColimits F).coconePoints = F ⋙ colim :=
  rfl

section

variable [HasColimit (curry.obj G ⋙ colim)]

set_option backward.isDefEq.respectTransparency false in
/-- Given a functor `G : J × K ⥤ C` such that `(curry.obj G ⋙ colim)` makes sense and has a colimit,
we can construct a cocone under `G` with `colimit (curry.obj G ⋙ colim)` as a cocone point -/
noncomputable def coconeOfHasColimitCurryCompColim : Cocone G :=
  let Q : DiagramOfCocones (curry.obj G) := .mkOfHasColimits _
  { pt := colimit (curry.obj G ⋙ colim),
    ι :=
    { app x := (Q.obj x.fst).ι.app x.snd ≫ colimit.ι (curry.obj G ⋙ colim) x.fst
      naturality {x y} := fun ⟨f₁, f₂⟩ ↦ by
        have := (Q.obj y.1).w f₂
        dsimp [Q] at this ⊢
        rw [← colimit.w (F := curry.obj G ⋙ colim) (f := f₁),
          Category.assoc, Category.comp_id, Prod.fac' (f₁, f₂),
          G.map_comp_assoc, ← curry_obj_map_app, ← curry_obj_obj_map]
        dsimp
        simp [ι_colimMap_assoc, curry_obj_map_app, reassoc_of% this] } }


set_option backward.isDefEq.respectTransparency false in
/-- The cocone `coconeOfHasColimitCurryCompColim` is in fact a colimit cocone.
-/
noncomputable def isColimitCoconeOfHasColimitCurryCompColim :
    IsColimit (coconeOfHasColimitCurryCompColim G) :=
  let Q : DiagramOfCocones (curry.obj G) := .mkOfHasColimits _
  let Q' : ∀ j, IsColimit (Q.obj j) := fun j => colimit.isColimit _
  { desc c' := colimit.desc (F := curry.obj G ⋙ colim) (coconeOfCoconeCurry G Q' c')
    fac c' f := by simp [coconeOfHasColimitCurryCompColim, Q, Q']
    uniq c' f h := by
      dsimp [coconeOfHasColimitCurryCompColim] at f h ⊢
      refine colimit.hom_ext (F := curry.obj G ⋙ colim) (fun j ↦ colimit.hom_ext (fun k ↦ ?_))
      simp [← h ⟨j, k⟩, Q'] }

/-- The functor `G` has a colimit if `C` has `K`-shaped colimits and `(curry.obj G ⋙ colim)` has a
colimit. -/
instance : HasColimit G where
  exists_colimit :=
    ⟨ { cocone := coconeOfHasColimitCurryCompColim G
        isColimit := isColimitCoconeOfHasColimitCurryCompColim G }⟩

end

variable [HasColimit (uncurry.obj F)] [HasColimit (F ⋙ colim)]

/-- The Fubini theorem for a functor `F : J ⥤ K ⥤ C`,
showing that the colimit of `uncurry.obj F` can be computed as
the colimit of the colimits of the functors `F.obj j`.
-/
noncomputable def colimitUncurryIsoColimitCompColim :
    colimit (uncurry.obj F) ≅ colimit (F ⋙ colim) := by
  let c := colimit.cocone (uncurry.obj F)
  let P : IsColimit c := colimit.isColimit _
  let G := DiagramOfCocones.mkOfHasColimits F
  let Q : ∀ j, IsColimit (G.obj j) := fun j => colimit.isColimit _
  have Q' := coconeOfCoconeUncurryIsColimit Q P
  have Q'' := colimit.isColimit (F ⋙ colim)
  exact IsColimit.coconePointUniqueUpToIso Q' Q''

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
theorem colimitUncurryIsoColimitCompColim_ι_ι_inv {j} {k} :
    colimit.ι (F.obj j) k ≫ colimit.ι (F ⋙ colim) j ≫ (colimitUncurryIsoColimitCompColim F).inv =
      colimit.ι (uncurry.obj F) (j, k) := by
  dsimp [colimitUncurryIsoColimitCompColim, IsColimit.coconePointUniqueUpToIso,
    IsColimit.uniqueUpToIso]
  simp

@[simp, reassoc]
theorem colimitUncurryIsoColimitCompColim_ι_hom {j} {k} :
    colimit.ι _ (j, k) ≫ (colimitUncurryIsoColimitCompColim F).hom =
      (colimit.ι _ k ≫ colimit.ι (F ⋙ colim) j : _ ⟶ (colimit (F ⋙ colim))) := by
  rw [← cancel_mono (colimitUncurryIsoColimitCompColim F).inv]
  simp

end

section

variable (F) [HasLimitsOfShape J C] [HasLimitsOfShape K C]

/-- The limit of `F.flip ⋙ lim` is isomorphic to the limit of `F ⋙ lim`. -/
noncomputable def limitFlipCompLimIsoLimitCompLim : limit (F.flip ⋙ lim) ≅ limit (F ⋙ lim) :=
  (limitUncurryIsoLimitCompLim _).symm ≪≫
    HasLimit.isoOfNatIso (uncurryObjFlip _) ≪≫
      HasLimit.isoOfEquivalence (Prod.braiding _ _)
          (NatIso.ofComponents fun _ => by rfl) ≪≫
        limitUncurryIsoLimitCompLim _

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
theorem limitFlipCompLimIsoLimitCompLim_hom_π_π (j) (k) :
    (limitFlipCompLimIsoLimitCompLim F).hom ≫ limit.π _ j ≫ limit.π _ k =
      (limit.π _ k ≫ limit.π _ j) := by
  dsimp [limitFlipCompLimIsoLimitCompLim]
  simp [Equivalence.counit]

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
theorem limitFlipCompLimIsoLimitCompLim_inv_π_π (k) (j) :
    (limitFlipCompLimIsoLimitCompLim F).inv ≫ limit.π _ k ≫ limit.π _ j =
      (limit.π _ j ≫ limit.π _ k) := by
  simp [limitFlipCompLimIsoLimitCompLim]

end

section

variable (F) [HasColimitsOfShape J C] [HasColimitsOfShape K C]

/-- The colimit of `F.flip ⋙ colim` is isomorphic to the colimit of `F ⋙ colim`. -/
noncomputable def colimitFlipCompColimIsoColimitCompColim :
    colimit (F.flip ⋙ colim) ≅ colimit (F ⋙ colim) :=
  (colimitUncurryIsoColimitCompColim _).symm ≪≫
    HasColimit.isoOfNatIso (uncurryObjFlip _) ≪≫
      HasColimit.isoOfEquivalence (Prod.braiding _ _)
          (NatIso.ofComponents fun _ => by rfl) ≪≫
        colimitUncurryIsoColimitCompColim _

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
theorem colimitFlipCompColimIsoColimitCompColim_ι_ι_hom (j) (k) :
    colimit.ι (F.flip.obj k) j ≫ colimit.ι (F.flip ⋙ colim) k ≫
      (colimitFlipCompColimIsoColimitCompColim F).hom =
        (colimit.ι _ k ≫ colimit.ι (F ⋙ colim) j : _ ⟶ colimit (F ⋙ colim)) := by
  dsimp [colimitFlipCompColimIsoColimitCompColim]
  slice_lhs 1 3 => simp only []
  simp [Equivalence.unit]

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
theorem colimitFlipCompColimIsoColimitCompColim_ι_ι_inv (k) (j) :
    colimit.ι (F.obj j) k ≫ colimit.ι (F ⋙ colim) j ≫
      (colimitFlipCompColimIsoColimitCompColim F).inv =
        (colimit.ι _ j ≫ colimit.ι (F.flip ⋙ colim) k : _ ⟶ colimit (F.flip ⋙ colim)) := by
  dsimp [colimitFlipCompColimIsoColimitCompColim]
  slice_lhs 1 3 => simp only []
  simp [Equivalence.counitInv]

end

section

variable [HasLimitsOfShape K C] [HasLimit (curry.obj G ⋙ lim)]

/-- The Fubini theorem for a functor `G : J × K ⥤ C`,
showing that the limit of `G` can be computed as
the limit of the limits of the functors `G.obj (j, _)`.
-/
noncomputable def limitIsoLimitCurryCompLim : limit G ≅ limit (curry.obj G ⋙ lim) := by
  have i : G ≅ uncurry.obj ((@curry J _ K _ C _).obj G) := currying.symm.unitIso.app G
  haveI : Limits.HasLimit (uncurry.obj ((@curry J _ K _ C _).obj G)) := hasLimit_of_iso i
  trans limit (uncurry.obj ((@curry J _ K _ C _).obj G))
  · apply HasLimit.isoOfNatIso i
  · exact limitUncurryIsoLimitCompLim ((@curry J _ K _ C _).obj G)

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
theorem limitIsoLimitCurryCompLim_hom_π_π {j} {k} :
    (limitIsoLimitCurryCompLim G).hom ≫ limit.π _ j ≫ limit.π _ k = limit.π _ (j, k) := by
  simp [limitIsoLimitCurryCompLim, Trans.simple]

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
theorem limitIsoLimitCurryCompLim_inv_π {j} {k} :
    (limitIsoLimitCurryCompLim G).inv ≫ limit.π _ (j, k) =
      (limit.π _ j ≫ limit.π _ k) := by
  rw [← cancel_epi (limitIsoLimitCurryCompLim G).hom]
  simp

end

section

variable [HasColimitsOfShape K C] [HasColimit (curry.obj G ⋙ colim)]

/-- The Fubini theorem for a functor `G : J × K ⥤ C`,
showing that the colimit of `G` can be computed as
the colimit of the colimits of the functors `G.obj (j, _)`.
-/
noncomputable def colimitIsoColimitCurryCompColim : colimit G ≅ colimit (curry.obj G ⋙ colim) := by
  have i : G ≅ uncurry.obj ((@curry J _ K _ C _).obj G) := currying.symm.unitIso.app G
  haveI : Limits.HasColimit (uncurry.obj ((@curry J _ K _ C _).obj G)) := hasColimit_of_iso i.symm
  trans colimit (uncurry.obj ((@curry J _ K _ C _).obj G))
  · apply HasColimit.isoOfNatIso i
  · exact colimitUncurryIsoColimitCompColim ((@curry J _ K _ C _).obj G)

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
theorem colimitIsoColimitCurryCompColim_ι_ι_inv {j} {k} :
    colimit.ι ((curry.obj G).obj j) k ≫ colimit.ι (curry.obj G ⋙ colim) j ≫
      (colimitIsoColimitCurryCompColim G).inv = colimit.ι _ (j, k) := by
  simp [colimitIsoColimitCurryCompColim, Trans.simple, colimitUncurryIsoColimitCompColim]

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
theorem colimitIsoColimitCurryCompColim_ι_hom {j} {k} :
    colimit.ι _ (j, k) ≫ (colimitIsoColimitCurryCompColim G).hom =
      (colimit.ι (_) k ≫ colimit.ι (curry.obj G ⋙ colim) j : _ ⟶ colimit (_ ⋙ colim)) := by
  rw [← cancel_mono (colimitIsoColimitCurryCompColim G).inv]
  simp

end

section

variable [HasLimitsOfShape K C] [HasLimitsOfShape J C] [HasLimit (curry.obj G ⋙ lim)]

open CategoryTheory.prod

/-- A variant of the Fubini theorem for a functor `G : J × K ⥤ C`,
showing that $\lim_k \lim_j G(j,k) ≅ \lim_j \lim_k G(j,k)$.
-/
noncomputable def limitCurrySwapCompLimIsoLimitCurryCompLim :
    limit (curry.obj (Prod.swap K J ⋙ G) ⋙ lim) ≅ limit (curry.obj G ⋙ lim) :=
  calc
    limit (curry.obj (Prod.swap K J ⋙ G) ⋙ lim) ≅ limit (Prod.swap K J ⋙ G) :=
      (limitIsoLimitCurryCompLim _).symm
    _ ≅ limit G := HasLimit.isoOfEquivalence (Prod.braiding K J) (Iso.refl _)
    _ ≅ limit (curry.obj G ⋙ lim) := limitIsoLimitCurryCompLim _

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem limitCurrySwapCompLimIsoLimitCurryCompLim_hom_π_π {j} {k} :
    (limitCurrySwapCompLimIsoLimitCurryCompLim G).hom ≫ limit.π _ j ≫ limit.π _ k =
      (limit.π _ k ≫ limit.π _ j) := by
  dsimp [limitCurrySwapCompLimIsoLimitCurryCompLim, Equivalence.counit]
  rw [Category.assoc, Category.assoc, limitIsoLimitCurryCompLim_hom_π_π,
    HasLimit.isoOfEquivalence_hom_π]
  dsimp [Equivalence.counit]
  rw [← prod_id, G.map_id]
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem limitCurrySwapCompLimIsoLimitCurryCompLim_inv_π_π {j} {k} :
    (limitCurrySwapCompLimIsoLimitCurryCompLim G).inv ≫ limit.π _ k ≫ limit.π _ j =
      (limit.π _ j ≫ limit.π _ k) := by
  simp [limitCurrySwapCompLimIsoLimitCurryCompLim]

end

section

variable [HasColimitsOfShape K C] [HasColimitsOfShape J C] [HasColimit (curry.obj G ⋙ colim)]

open CategoryTheory.prod

/-- A variant of the Fubini theorem for a functor `G : J × K ⥤ C`,
showing that $\colim_k \colim_j G(j,k) ≅ \colim_j \colim_k G(j,k)$.
-/
noncomputable def colimitCurrySwapCompColimIsoColimitCurryCompColim :
    colimit (curry.obj (Prod.swap K J ⋙ G) ⋙ colim) ≅ colimit (curry.obj G ⋙ colim) :=
  calc
    colimit (curry.obj (Prod.swap K J ⋙ G) ⋙ colim) ≅ colimit (Prod.swap K J ⋙ G) :=
      (colimitIsoColimitCurryCompColim _).symm
    _ ≅ colimit G := HasColimit.isoOfEquivalence (Prod.braiding K J) (Iso.refl _)
    _ ≅ colimit (curry.obj G ⋙ colim) := colimitIsoColimitCurryCompColim _

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem colimitCurrySwapCompColimIsoColimitCurryCompColim_ι_ι_hom {j} {k} :
    colimit.ι _ j ≫ colimit.ι (curry.obj (Prod.swap K J ⋙ G) ⋙ colim) k ≫
      (colimitCurrySwapCompColimIsoColimitCurryCompColim G).hom =
        (colimit.ι _ k ≫ colimit.ι (curry.obj G ⋙ colim) j :
          _ ⟶ colimit (curry.obj G ⋙ colim)) := by
  dsimp [colimitCurrySwapCompColimIsoColimitCurryCompColim]
  slice_lhs 1 3 => simp only []
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem colimitCurrySwapCompColimIsoColimitCurryCompColim_ι_ι_inv {j} {k} :
    colimit.ι _ k ≫ colimit.ι (curry.obj G ⋙ colim) j ≫
      (colimitCurrySwapCompColimIsoColimitCurryCompColim G).inv =
        (colimit.ι _ j ≫
          colimit.ι (curry.obj _ ⋙ colim) k :
            _ ⟶ colimit (curry.obj (Prod.swap K J ⋙ G) ⋙ colim)) := by
  dsimp [colimitCurrySwapCompColimIsoColimitCurryCompColim]
  slice_lhs 1 3 => simp only []
  rw [colimitIsoColimitCurryCompColim_ι_ι_inv, HasColimit.isoOfEquivalence_inv_π]
  dsimp [Equivalence.counitInv]
  rw [CategoryTheory.Bifunctor.map_id]
  simp

end

end CategoryTheory.Limits
