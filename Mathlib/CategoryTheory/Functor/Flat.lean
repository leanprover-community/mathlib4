/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module category_theory.functor.flat
! leanprover-community/mathlib commit 14e80e85cbca5872a329fbfd3d1f3fd64e306934
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Bicones
import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
/-!
# Representably flat functors

We define representably flat functors as functors such that the category of structured arrows
over `X` is cofiltered for each `X`. This concept is also known as flat functors as in [Elephant]
Remark C2.3.7, and this name is suggested by Mike Shulman in
https://golem.ph.utexas.edu/category/2011/06/flat_functors_and_morphisms_of.html to avoid
confusion with other notions of flatness.

This definition is equivalent to left exact functors (functors that preserves finite limits) when
`C` has all finite limits.

## Main results

* `flat_of_preserves_finite_limits`: If `F : C ⥤ D` preserves finite limits and `C` has all finite
  limits, then `F` is flat.
* `preserves_finite_limits_of_flat`: If `F : C ⥤ D` is flat, then it preserves all finite limits.
* `preserves_finite_limits_iff_flat`: If `C` has all finite limits,
  then `F` is flat iff `F` is left_exact.
* `Lan_preserves_finite_limits_of_flat`: If `F : C ⥤ D` is a flat functor between small categories,
  then the functor `Lan F.op` between presheaves of sets preserves all finite limits.
* `flat_iff_Lan_flat`: If `C`, `D` are small and `C` has all finite limits, then `F` is flat iff
  `Lan F.op : (Cᵒᵖ ⥤ Type*) ⥤ (Dᵒᵖ ⥤ Type*)` is flat.
* `preserves_finite_limits_iff_Lan_preserves_finite_limits`: If `C`, `D` are small and `C` has all
  finite limits, then `F` preserves finite limits iff `Lan F.op : (Cᵒᵖ ⥤ Type*) ⥤ (Dᵒᵖ ⥤ Type*)`
  does.

-/


universe w v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory

open CategoryTheory.Limits

open Opposite

namespace CategoryTheory

namespace StructuredArrowCone

open StructuredArrow

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₁} D]

variable {J : Type w} [SmallCategory J]

variable {K : J ⥤ C} (F : C ⥤ D) (c : Cone K)

-- **TODO** Scott changed `@[simps]` to `@[simps!]` below and I don't
-- know what this does, but one thing it does is that
-- it stops `toDiagram_obj` being created, and `toDiagram_obj` is
-- used later on so I (kmb) have changed it back

/-- Given a cone `c : cone K` and a map `f : X ⟶ c.X`, we can construct a cone of structured
arrows over `X` with `f` as the cone point. This is the underlying diagram.
-/
@[simps]
def toDiagram : J ⥤ StructuredArrow c.pt K where
  obj j := StructuredArrow.mk (c.π.app j)
  map g := StructuredArrow.homMk g (by simp)
#align category_theory.structured_arrow_cone.to_diagram CategoryTheory.StructuredArrowCone.toDiagram

/-- Given a diagram of `structured_arrow X F`s, we may obtain a cone with cone point `X`. -/
@[simps!]
def diagramToCone {X : D} (G : J ⥤ StructuredArrow X F) : Cone (G ⋙ proj X F ⋙ F) where
  π := { app := fun j => (G.obj j).hom }
#align category_theory.structured_arrow_cone.diagram_to_cone CategoryTheory.StructuredArrowCone.diagramToCone

/-- Given a cone `c : cone K` and a map `f : X ⟶ F.obj c.X`, we can construct a cone of structured
arrows over `X` with `f` as the cone point.
-/
@[simps]
def toCone {X : D} (f : X ⟶ F.obj c.pt) :
    Cone (toDiagram (F.mapCone c) ⋙ map f ⋙ pre _ K F) where
  pt := mk f
  π :=
    { app := fun j => homMk (c.π.app j) rfl
      naturality := fun j k g => by
        ext
        simp }
#align category_theory.structured_arrow_cone.to_cone CategoryTheory.StructuredArrowCone.toCone

end StructuredArrowCone

section RepresentablyFlat

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

variable {E : Type u₃} [Category.{v₃} E]

/-- A functor `F : C ⥤ D` is representably-flat functor if the comma category `(X/F)`
is cofiltered for each `X : C`.
-/
class RepresentablyFlat (F : C ⥤ D) : Prop where
  cofiltered : ∀ X : D, IsCofiltered (StructuredArrow X F)
#align category_theory.representably_flat CategoryTheory.RepresentablyFlat

attribute [instance] RepresentablyFlat.cofiltered

attribute [local instance] IsCofiltered.Nonempty

instance RepresentablyFlat.id : RepresentablyFlat (𝟭 C) := by
  constructor
  intro X
  haveI : Nonempty (StructuredArrow X (𝟭 C)) := ⟨StructuredArrow.mk (𝟙 _)⟩
  suffices : IsCofilteredOrEmpty (StructuredArrow X (𝟭 C))
  · constructor
  constructor
  · intro Y Z
    use StructuredArrow.mk (𝟙 _)
    use StructuredArrow.homMk Y.hom (by erw [Functor.id_map, Category.id_comp])
    use StructuredArrow.homMk Z.hom (by erw [Functor.id_map, Category.id_comp])
    trivial
  · intro Y Z f g
    use StructuredArrow.mk (𝟙 _)
    use StructuredArrow.homMk Y.hom (by erw [Functor.id_map, Category.id_comp])
    ext
    trans Z.hom <;> simp
#align category_theory.representably_flat.id CategoryTheory.RepresentablyFlat.id

instance RepresentablyFlat.comp (F : C ⥤ D) (G : D ⥤ E) [RepresentablyFlat F]
    [RepresentablyFlat G] : RepresentablyFlat (F ⋙ G) := by
  constructor
  intro X
  have : Nonempty (StructuredArrow X (F ⋙ G)) := by
    have f₁ : StructuredArrow X G := Nonempty.some inferInstance
    have f₂ : StructuredArrow f₁.right F := Nonempty.some inferInstance
    exact ⟨StructuredArrow.mk (f₁.hom ≫ G.map f₂.hom)⟩
  suffices : IsCofilteredOrEmpty (StructuredArrow X (F ⋙ G))
  · constructor
  constructor
  · intro Y Z
    let W :=
      @IsCofiltered.min (StructuredArrow X G) _ _ (StructuredArrow.mk Y.hom)
        (StructuredArrow.mk Z.hom)
    let Y' : W ⟶ _ := IsCofiltered.minToLeft _ _
    let Z' : W ⟶ _ := IsCofiltered.minToRight _ _
    let W' :=
      @IsCofiltered.min (StructuredArrow W.right F) _ _ (StructuredArrow.mk Y'.right)
        (StructuredArrow.mk Z'.right)
    let Y'' : W' ⟶ _ := IsCofiltered.minToLeft _ _
    let Z'' : W' ⟶ _ := IsCofiltered.minToRight _ _
    use StructuredArrow.mk (W.hom ≫ G.map W'.hom)
    use StructuredArrow.homMk Y''.right (by simp [← G.map_comp])
    use StructuredArrow.homMk Z''.right (by simp [← G.map_comp])
    trivial
  · intro Y Z f g
    let W :=
      @IsCofiltered.eq (StructuredArrow X G) _ _ (StructuredArrow.mk Y.hom)
        (StructuredArrow.mk Z.hom) (StructuredArrow.homMk (F.map f.right) (StructuredArrow.w f))
        (StructuredArrow.homMk (F.map g.right) (StructuredArrow.w g))
    let h : W ⟶ _ := IsCofiltered.eqHom _ _
    let h_cond : h ≫ _ = h ≫ _ := IsCofiltered.eq_condition _ _
    let W' :=
      @IsCofiltered.eq (StructuredArrow W.right F) _ _ (StructuredArrow.mk h.right)
        (StructuredArrow.mk (h.right ≫ F.map f.right)) (StructuredArrow.homMk f.right rfl)
        (StructuredArrow.homMk g.right (congr_arg CommaMorphism.right h_cond).symm)
    let h' : W' ⟶ _ := IsCofiltered.eqHom _ _
    let h'_cond : h' ≫ _ = h' ≫ _ := IsCofiltered.eq_condition _ _
    use StructuredArrow.mk (W.hom ≫ G.map W'.hom)
    use StructuredArrow.homMk h'.right (by simp [← G.map_comp])
    ext
    exact (congr_arg CommaMorphism.right h'_cond : _)
#align category_theory.representably_flat.comp CategoryTheory.RepresentablyFlat.comp

end RepresentablyFlat

section HasLimit

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₁} D]

attribute [local instance] hasFiniteLimits_of_hasFiniteLimits_of_size

theorem cofiltered_of_hasFiniteLimits [HasFiniteLimits C] : IsCofiltered C :=
  { cone_objs := fun A B => ⟨Limits.prod A B, Limits.prod.fst, Limits.prod.snd, trivial⟩
    cone_maps := fun _ _ f g => ⟨equalizer f g, equalizer.ι f g, equalizer.condition f g⟩
    Nonempty := ⟨⊤_ C⟩ }
#align category_theory.cofiltered_of_has_finite_limits CategoryTheory.cofiltered_of_hasFiniteLimits

theorem flat_of_preservesFiniteLimits [HasFiniteLimits C] (F : C ⥤ D) [PreservesFiniteLimits F] :
    RepresentablyFlat F :=
  ⟨fun X =>
    haveI : HasFiniteLimits (StructuredArrow X F) := by
      apply hasFiniteLimits_of_hasFiniteLimits_of_size.{v₁} (StructuredArrow X F)
      intro J sJ fJ
      constructor
      -- porting note: instance was inferred automatically in Lean 3
      infer_instance
    cofiltered_of_hasFiniteLimits⟩
#align category_theory.flat_of_preserves_finite_limits CategoryTheory.flat_of_preservesFiniteLimits

namespace PreservesFiniteLimitsOfFlat

open StructuredArrow

open StructuredArrowCone

variable {J : Type v₁} [SmallCategory J] [FinCategory J] {K : J ⥤ C}

variable (F : C ⥤ D) [RepresentablyFlat F] {c : Cone K} (hc : IsLimit c) (s : Cone (K ⋙ F))

/-- (Implementation).
Given a limit cone `c : cone K` and a cone `s : cone (K ⋙ F)` with `F` representably flat,
`s` can factor through `F.map_cone c`.
-/
noncomputable def lift : s.pt ⟶ F.obj c.pt :=
  let s' := IsCofiltered.cone (toDiagram s ⋙ StructuredArrow.pre _ K F)
  s'.pt.hom ≫
    (F.map <|
      hc.lift <|
        (Cones.postcompose
              ({  app := fun X => 𝟙 _
                  naturality := by simp } : (toDiagram s ⋙ pre s.pt K F) ⋙ proj s.pt F ⟶ K)).obj <|
          (StructuredArrow.proj s.pt F).mapCone s')
#align category_theory.preserves_finite_limits_of_flat.lift CategoryTheory.PreservesFiniteLimitsOfFlat.lift

theorem fac (x : J) : lift F hc s ≫ (F.mapCone c).π.app x = s.π.app x := by
  simp [lift, ← Functor.map_comp]
#align category_theory.preserves_finite_limits_of_flat.fac CategoryTheory.PreservesFiniteLimitsOfFlat.fac

attribute [local simp] eqToHom_map

--set_option pp.universes true

-- **TODO** unexpander to make Functor.mapCone F -> F.mapCone?
theorem uniq {K : J ⥤ C} {c : Cone K} (hc : IsLimit c) (s : Cone (K ⋙ F))
    (f₁ f₂ : s.pt ⟶ F.obj c.pt) (h₁ : ∀ j : J, f₁ ≫ (F.mapCone c).π.app j = s.π.app j)
    (h₂ : ∀ j : J, f₂ ≫ (F.mapCone c).π.app j = s.π.app j) : f₁ = f₂ := by
  -- We can make two cones over the diagram of `s` via `f₁` and `f₂`.
  let α₁ : toDiagram (F.mapCone c) ⋙ map f₁ ⟶ toDiagram s :=
    { -- porting note: this proof uses `toDiagram_obj` and
      -- breaks if `@[simps]` is changed to `@[simps!]`
      -- in the definition of `toDiagram
      app := fun X => eqToHom (by simp [← h₁])
      naturality := fun j₁ j₂ φ => by
        ext
        -- porting note: Lean 3 proof was `simp` but `Comma.eqToHom_right`
        -- isn't firing for some reason
        -- Asked here https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/simp.20not.20using.20a.20simp.20lemma/near/353943416
        simp
        rw [Comma.eqToHom_right, Comma.eqToHom_right] -- this is a `simp` lemma
        simp }
  let α₂ : toDiagram (F.mapCone c) ⋙ map f₂ ⟶ toDiagram s :=
    { app := fun X => eqToHom (by simp [← h₂])
      naturality := fun _ _ _ => by
        ext
        simp
        rw [Comma.eqToHom_right, Comma.eqToHom_right] -- this is a `simp` lemma
        simp }
  let c₁ : Cone (toDiagram s ⋙ pre s.pt K F) :=
    (Cones.postcompose (whiskerRight α₁ (pre s.pt K F) : _)).obj (toCone F c f₁)
  let c₂ : Cone (toDiagram s ⋙ pre s.pt K F) :=
    (Cones.postcompose (whiskerRight α₂ (pre s.pt K F) : _)).obj (toCone F c f₂)
  -- The two cones can then be combined and we may obtain a cone over the two cones since
  -- `StructuredArrow s.pt F` is cofiltered.
  let c₀ := IsCofiltered.cone (biconeMk _ c₁ c₂)
  let g₁ : c₀.pt ⟶ c₁.pt := c₀.π.app Bicone.left
  let g₂ : c₀.pt ⟶ c₂.pt := c₀.π.app Bicone.right
  -- Then `g₁.right` and `g₂.right` are two maps from the same cone into the `c`.
  have : ∀ j : J, g₁.right ≫ c.π.app j = g₂.right ≫ c.π.app j := by
    intro j
    injection c₀.π.naturality (BiconeHom.left j) with _ e₁
    injection c₀.π.naturality (BiconeHom.right j) with _ e₂
    -- Lean 3 proof now finished with `simpa using e₁.symm.trans e₂`
    have foo := e₁.symm.trans e₂
    -- simp at foo -- deterministic timeout :-(
    -- the below job was done by `simp` in lean 3;
    rw [biconeMk_map, biconeMk_map] at foo
    -- `dsimp only` tames this in Lean 3 but not Lean 4
    change (c₀.π.app Bicone.left).right ≫ (c₁.π.app j).right =
      (c₀.π.app Bicone.right).right ≫ (c₂.π.app j).right at foo
    rw [Cones.postcompose_obj_π, Cones.postcompose_obj_π] at foo
    rw [NatTrans.comp_app, whiskerRight_app,
      eqToHom_map, Comma.comp_right,
      Comma.eqToHom_right, eqToHom_refl, Category.comp_id] at foo
    rw [NatTrans.comp_app, whiskerRight_app,
      eqToHom_map, Comma.comp_right,
      Comma.eqToHom_right, eqToHom_refl, Category.comp_id] at foo
    exact foo
  have : c.extend g₁.right = c.extend g₂.right := by
    unfold Cone.extend
    congr 1
    ext x
    apply this
  -- And thus they are equal as `c` is the limit.
  have : g₁.right = g₂.right
  calc
    g₁.right = hc.lift (c.extend g₁.right) := by
      apply hc.uniq (c.extend _)
      -- Porting note: was `by tidy`
      intro j ; rfl -- was `by tidy` but `aesop` is timing out, possibly
      -- for the same reason `simp at foo` is timing out above.
    _ = hc.lift (c.extend g₂.right) := by
      congr
    _ = g₂.right := by
      symm
      apply hc.uniq (c.extend _)
      -- Porting note: was `by tidy`; `aesop` is timing out
      intro _ ; rfl

  -- Finally, since `fᵢ` factors through `F(gᵢ)`, the result follows.
  calc
    f₁ = 𝟙 _ ≫ f₁ := by simp
    _ = c₀.pt.hom ≫ F.map g₁.right := g₁.w
    _ = c₀.pt.hom ≫ F.map g₂.right := by rw [this]
    _ = 𝟙 _ ≫ f₂ := g₂.w.symm
    _ = f₂ := by simp

#align category_theory.preserves_finite_limits_of_flat.uniq CategoryTheory.PreservesFiniteLimitsOfFlat.uniq

end PreservesFiniteLimitsOfFlat

/-- Representably flat functors preserve finite limits. -/
noncomputable def preservesFiniteLimitsOfFlat (F : C ⥤ D) [RepresentablyFlat F] :
    PreservesFiniteLimits F := by
  apply preservesFiniteLimitsOfPreservesFiniteLimitsOfSize
  intro J _ _; constructor
  intro K; constructor
  intro c hc
  exact
    { lift := PreservesFiniteLimitsOfFlat.lift F hc
      fac := PreservesFiniteLimitsOfFlat.fac F hc
      uniq := fun s m h => by
        apply PreservesFiniteLimitsOfFlat.uniq F hc
        exact h
        exact PreservesFiniteLimitsOfFlat.fac F hc s }
#align category_theory.preserves_finite_limits_of_flat CategoryTheory.preservesFiniteLimitsOfFlat

/-- If `C` is finitely cocomplete, then `F : C ⥤ D` is representably flat iff it preserves
finite limits.
-/
noncomputable def preservesFiniteLimitsIffFlat [HasFiniteLimits C] (F : C ⥤ D) :
    RepresentablyFlat F ≃ PreservesFiniteLimits F where
  toFun _ := preservesFiniteLimitsOfFlat F
  invFun _ := flat_of_preservesFiniteLimits F
  left_inv _ := proof_irrel _ _
  right_inv x := by
    cases' x with x
    unfold preservesFiniteLimitsOfFlat
    dsimp only [preservesFiniteLimitsOfPreservesFiniteLimitsOfSize]
    congr
    -- porting note: this next line wasn't needed in lean 3
    apply Subsingleton.elim

#align category_theory.preserves_finite_limits_iff_flat CategoryTheory.preservesFiniteLimitsIffFlat

end HasLimit

section SmallCategory

variable {C D : Type u₁} [SmallCategory C] [SmallCategory D] (E : Type u₂) [Category.{u₁} E]


-- the below proof is broken because
/-

Lean 4:
CategoryTheory.lan_map_app.{v₁, v₂, v₃, u₁, u₂, u₃}
  {S : Type u₁} {L : Type u₂} {D : Type u₃} [inst✝ : Category S]
  [inst✝¹ : Category L] [inst✝² : Category D] (ι : S ⥤ L)
  [inst✝³ : ∀ (X : L), HasColimitsOfShape (CostructuredArrow ι X) D] {X X' : S ⥤ D} (f : X ⟶ X') (x : L) :
  ((lan ι).map f).app x =
    colimit.desc (Lan.diagram ι X x)
      { pt := colimit (Lan.diagram ι X' x),
        ι :=
          NatTrans.mk fun i ↦
            (f.app i.left ≫ (↑(Lan.equiv ι X' (Lan.loc ι X')) (𝟙 (Lan.loc ι X'))).app i.left) ≫
              colimit.pre (Lan.diagram ι X' x) (CostructuredArrow.map i.hom) }

Lean 3:
category_theory.Lan_map_app :
  ∀ {S L : Type u₁} {D : Type u₂} [_inst_1 : category S]
  [_inst_2 : category L] [_inst_3 : category D] (ι : S ⥤ L)
  [_inst_4 : ∀ (X : L), has_colimits_of_shape (costructured_arrow ι X) D] (X X' : S ⥤ D) (f : X ⟶ X') (x : L),
  ((Lan ι).map f).app x =
    colimit.desc (Lan.diagram ι X x)
      {X := colimit (Lan.diagram ι X' x) _,
        ι :=
          {app := λ (i : costructured_arrow ι x),
            (f.app i.left ≫ colimit.ι (Lan.diagram ι X' (ι.obj i.left)) (costructured_arrow.mk (𝟙 (ι.obj i.left))) ≫ 𝟙 (colimit (Lan.diagram ι X' (ι.obj i.left)))) ≫ colimit.pre (Lan.diagram ι X' x) (costructured_arrow.map i.hom), naturality' := _}}


-/
/-- (Implementation)
The evaluation of `Lan F` at `X` is the colimit over the costructured arrows over `X`.
-/
noncomputable def lanEvaluationIsoColim (F : C ⥤ D) (X : D)
    [∀ X : D, HasColimitsOfShape (CostructuredArrow F X) E] :
    lan F ⋙ (evaluation D E).obj X ≅
      (whiskeringLeft _ _ E).obj (CostructuredArrow.proj F X) ⋙ colim :=
  NatIso.ofComponents (fun G => colim.mapIso (Iso.refl _))
    (by
      intro G H i
      -- porting note: was `ext` in lean 3
      apply colimit.hom_ext
      intro j
      -- **Explanation**
      -- Overview of problem: `simp` has changed behaviour. I've narrowed it down
      -- to a change in the type of `lan_map_app`.
      /-
      Lean 4 : ⊢ colimit.ι (Lan.diagram F G X) j ≫
    (lan F ⋙ (evaluation D E).obj X).map i ≫ ((fun G ↦ Functor.mapIso colim (Iso.refl (Lan.diagram F G X))) H).hom =
  colimit.ι (Lan.diagram F G X) j ≫
    ((fun G ↦ Functor.mapIso colim (Iso.refl (Lan.diagram F G X))) G).hom ≫
      ((whiskeringLeft (CostructuredArrow F X) C E).obj (CostructuredArrow.proj F X) ⋙ colim).map i

      Lean 3 : ⊢ colimit.ι (Lan.diagram F G X) j ≫
    (Lan F ⋙ (evaluation D E).obj X).map i ≫ (colim.map_iso (iso.refl (Lan.diagram F H X))).hom =
  colimit.ι (Lan.diagram F G X) j ≫
    (colim.map_iso (iso.refl (Lan.diagram F G X))).hom ≫
      ((whiskering_left (costructured_arrow F X) C E).obj (costructured_arrow.proj F X) ⋙ colim).map i
      -/
      rw [Functor.comp_map]
      rw [Functor.comp_map]
      dsimp only
      rw [Functor.mapIso_refl]
      rw [Functor.mapIso_refl]
      rw [evaluation_obj_map]
      rw [whiskeringLeft_obj_map]
      rw [lan_map_app]
      rw [colimit.ι_desc_assoc]
      rw [Lan.equiv]
      dsimp only
      /-
      Lean 4 : ⊢ { pt := colimit (Lan.diagram F H X),
            ι :=
              NatTrans.mk fun i_1 ↦
                (i.app i_1.left ≫

                (↑(Lan.equiv F H (Lan.loc F H)) (𝟙 (Lan.loc F H))).app i_1.left) ≫

                  colimit.pre (Lan.diagram F H X) (CostructuredArrow.map i_1.hom) }.ι.app
      j ≫
      (Iso.refl (colim.obj (Lan.diagram F H X))).hom =
      colimit.ι (Lan.diagram F G X) j ≫
      (Iso.refl (colim.obj (Lan.diagram F G X))).hom ≫ colim.map (whiskerLeft (CostructuredArrow.proj F X) i)

      Lean 3 : ⊢ {X := colimit (Lan.diagram F H X) _
          , ι :=
              {app := λ (i_1 : costructured_arrow F X),
                (i.app i_1.left ≫

                colimit.ι (Lan.diagram F H (F.obj i_1.left))
                  (costructured_arrow.mk (𝟙 (F.obj i_1.left))) ≫
                  𝟙 (colimit (Lan.diagram F H (F.obj i_1.left)))) ≫

                  colimit.pre (Lan.diagram F H X) (costructured_arrow.map i_1.hom), naturality' := _}}.ι.app
      j ≫
      (iso.refl (colim.obj (Lan.diagram F H X))).hom =
      colimit.ι (Lan.diagram F G X) j ≫
      (iso.refl (colim.obj (Lan.diagram F G X))).hom ≫ colim.map (whisker_left (costructured_arrow.proj F X) i)

      -/
      simp only [Category.comp_id, Category.assoc]

  --    simp only [Functor.comp_map, colimit.ι_desc_assoc, Functor.mapIso_refl, evaluation_obj_map,
  --      whiskeringLeft_obj_map, Category.comp_id, lan_map_app, Category.assoc]

      erw [show ((Lan.equiv F H (Lan.loc F H)) (𝟙 (Lan.loc F H))).app j.left =
        colimit.ι (Lan.diagram F H (F.obj j.left))
        (CostructuredArrow.mk (𝟙 (F.obj j.left))) by apply Category.comp_id]
      -- **TODO** change in behaviour of `lan_map_app` constructed by `simps`
      -- See https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/change.20in.20behaviour.20with.20.60simps.60/near/354350606
      /-
      Lean 4 : ⊢ i.app j.left ≫

       (↑(Lan.equiv F H (Lan.loc F H)) (𝟙 (Lan.loc F H))).app j.left ≫

      colimit.pre (Lan.diagram F H X) (CostructuredArrow.map j.hom) ≫ (Iso.refl (colim.obj (Lan.diagram F H X))).hom =
       colimit.ι (Lan.diagram F G X) j ≫
      (Iso.refl (colim.obj (Lan.diagram F G X))).hom ≫ colim.map (whiskerLeft (CostructuredArrow.proj F X) i)

      Lean 3 : ⊢ i.app j.left ≫

      colimit.ι (Lan.diagram F H (F.obj j.left))
      (costructured_arrow.mk (𝟙 (F.obj j.left))) ≫

      colimit.pre (Lan.diagram F H X) (costructured_arrow.map j.hom) ≫ (iso.refl (colim.obj (Lan.diagram F H X))).hom =
      colimit.ι (Lan.diagram F G X) j ≫
      (iso.refl (colim.obj (Lan.diagram F G X))).hom ≫ colim.map (whisker_left (costructured_arrow.proj F X) i)

      -/
      erw [colimit.ι_pre_assoc (Lan.diagram F H X) (CostructuredArrow.map j.hom), Category.id_comp,
        Category.comp_id, colimit.ι_map]
      rcases j with ⟨j_left, ⟨⟨⟩⟩, j_hom⟩
      congr
      rw [CostructuredArrow.map_mk, Category.id_comp, CostructuredArrow.mk])
set_option linter.uppercaseLean3 false in
#align category_theory.Lan_evaluation_iso_colim CategoryTheory.lanEvaluationIsoColim

variable [ConcreteCategory.{u₁} E] [HasLimits E] [HasColimits E]

variable [ReflectsLimits (forget E)] [PreservesFilteredColimits (forget E)]

variable [PreservesLimits (forget E)]

/-- If `F : C ⥤ D` is a representably flat functor between small categories, then the functor
`Lan F.op` that takes presheaves over `C` to presheaves over `D` preserves finite limits.
-/
noncomputable instance lanPreservesFiniteLimitsOfFlat (F : C ⥤ D) [RepresentablyFlat F] :
    PreservesFiniteLimits (lan F.op : _ ⥤ Dᵒᵖ ⥤ E) := by
  apply preservesFiniteLimitsOfPreservesFiniteLimitsOfSize.{u₁}
  intro J _ _; skip
  apply preservesLimitsOfShapeOfEvaluation (lan F.op : (Cᵒᵖ ⥤ E) ⥤ Dᵒᵖ ⥤ E) J
  intro K
  haveI : IsFiltered (CostructuredArrow F.op K) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence F (unop K))
  exact preservesLimitsOfShapeOfNatIso (lanEvaluationIsoColim _ _ _).symm
set_option linter.uppercaseLean3 false in
#align category_theory.Lan_preserves_finite_limits_of_flat CategoryTheory.lanPreservesFiniteLimitsOfFlat

instance lan_flat_of_flat (F : C ⥤ D) [RepresentablyFlat F] :
    RepresentablyFlat (lan F.op : _ ⥤ Dᵒᵖ ⥤ E) :=
  flat_of_preservesFiniteLimits _
set_option linter.uppercaseLean3 false in
#align category_theory.Lan_flat_of_flat CategoryTheory.lan_flat_of_flat

variable [HasFiniteLimits C]

noncomputable instance lanPreservesFiniteLimitsOfPreservesFiniteLimits (F : C ⥤ D)
    [PreservesFiniteLimits F] : PreservesFiniteLimits (lan F.op : _ ⥤ Dᵒᵖ ⥤ E) := by
  haveI := flat_of_preservesFiniteLimits F
  infer_instance
set_option linter.uppercaseLean3 false in
#align category_theory.Lan_preserves_finite_limits_of_preserves_finite_limits CategoryTheory.lanPreservesFiniteLimitsOfPreservesFiniteLimits

-- porting note: these were all inferred in mathlib3 because lean 3 typeclass inference could see
-- that `forget (Type u) = 𝟭 (Type u)`
-- see https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/typeclass.20inference.20failure/near/354843721
instance : ReflectsLimits (forget (Type u₁)) := Limits.idReflectsLimits
instance : PreservesColimits (forget (Type u₁)) := Limits.idPreservesColimits
instance : PreservesLimits (forget (Type u₁)) := Limits.idPreservesLimits

theorem flat_iff_lan_flat (F : C ⥤ D) :
    RepresentablyFlat F ↔ RepresentablyFlat (lan F.op : _ ⥤ Dᵒᵖ ⥤ Type u₁) :=
--    ⟨λ H, by exactI category_theory.Lan_flat_of_flat (Type u₁) F, λ H,
  ⟨fun H => inferInstance,
  fun H => by
    skip
    haveI := preservesFiniteLimitsOfFlat (lan F.op : _ ⥤ Dᵒᵖ ⥤ Type u₁)
    haveI : PreservesFiniteLimits F := by
      apply preservesFiniteLimitsOfPreservesFiniteLimitsOfSize.{u₁}
      intros ; skip; apply preservesLimitOfLanPreservesLimit
    apply flat_of_preservesFiniteLimits⟩
set_option linter.uppercaseLean3 false in
#align category_theory.flat_iff_Lan_flat CategoryTheory.flat_iff_lan_flat

/-- If `C` is finitely complete, then `F : C ⥤ D` preserves finite limits iff
`Lan F.op : (Cᵒᵖ ⥤ Type*) ⥤ (Dᵒᵖ ⥤ Type*)` preserves finite limits.
-/
noncomputable def preservesFiniteLimitsIffLanPreservesFiniteLimits (F : C ⥤ D) :
    PreservesFiniteLimits F ≃ PreservesFiniteLimits (lan F.op : _ ⥤ Dᵒᵖ ⥤ Type u₁) where
  toFun _ := inferInstance
  invFun _ := by
    apply preservesFiniteLimitsOfPreservesFiniteLimitsOfSize.{u₁}
    intros
    apply preservesLimitOfLanPreservesLimit
  left_inv x := by
    -- cases x; -- porting note: not necessary in lean 4.
    -- porting note: in mathlib3 we had `unfold preservesFiniteLimitsOfFlat`
    -- but there was no `preservesFiniteLimitsOfFlat` in the goal! Experimentation
    -- indicates that it was doing the same as `dsimp only`
    dsimp only [preservesFiniteLimitsOfPreservesFiniteLimitsOfSize]; congr
    -- porting note: next line wasn't necessary in lean 3
    apply Subsingleton.elim
  right_inv x := by
    -- cases x; -- porting note: not necessary in lean 4
    dsimp only [lanPreservesFiniteLimitsOfPreservesFiniteLimits,
      lanPreservesFiniteLimitsOfFlat,
      preservesFiniteLimitsOfPreservesFiniteLimitsOfSize]
    congr
    -- porting note: next line wasn't necessary in lean 3
    apply Subsingleton.elim
set_option linter.uppercaseLean3 false in
#align category_theory.preserves_finite_limits_iff_Lan_preserves_finite_limits CategoryTheory.preservesFiniteLimitsIffLanPreservesFiniteLimits

end SmallCategory

end CategoryTheory
