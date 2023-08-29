/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.CategoryTheory.Limits.ConeCategory
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Bicones
import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

#align_import category_theory.functor.flat from "leanprover-community/mathlib"@"39478763114722f0ec7613cb2f3f7701f9b86c8d"
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

* `flat_of_preservesFiniteLimits`: If `F : C ⥤ D` preserves finite limits and `C` has all finite
  limits, then `F` is flat.
* `preservesFiniteLimitsOfFlat`: If `F : C ⥤ D` is flat, then it preserves all finite limits.
* `preservesFiniteLimitsIffFlat`: If `C` has all finite limits,
  then `F` is flat iff `F` is left_exact.
* `lanPreservesFiniteLimitsOfFlat`: If `F : C ⥤ D` is a flat functor between small categories,
  then the functor `Lan F.op` between presheaves of sets preserves all finite limits.
* `flat_iff_lan_flat`: If `C`, `D` are small and `C` has all finite limits, then `F` is flat iff
  `Lan F.op : (Cᵒᵖ ⥤ Type*) ⥤ (Dᵒᵖ ⥤ Type*)` is flat.
* `preservesFiniteLimitsIffLanPreservesFiniteLimits`: If `C`, `D` are small and `C` has all
  finite limits, then `F` preserves finite limits iff `Lan F.op : (Cᵒᵖ ⥤ Type*) ⥤ (Dᵒᵖ ⥤ Type*)`
  does.

-/


universe w v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory

open CategoryTheory.Limits

open Opposite

namespace CategoryTheory

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
  -- ⊢ ∀ (X : C), IsCofiltered (StructuredArrow X (𝟭 C))
  intro X
  -- ⊢ IsCofiltered (StructuredArrow X (𝟭 C))
  haveI : Nonempty (StructuredArrow X (𝟭 C)) := ⟨StructuredArrow.mk (𝟙 _)⟩
  -- ⊢ IsCofiltered (StructuredArrow X (𝟭 C))
  suffices : IsCofilteredOrEmpty (StructuredArrow X (𝟭 C))
  -- ⊢ IsCofiltered (StructuredArrow X (𝟭 C))
  · constructor
    -- 🎉 no goals
  constructor
  -- ⊢ ∀ (X_1 Y : StructuredArrow X (𝟭 C)), ∃ W x x, True
  · intro Y Z
    -- ⊢ ∃ W x x, True
    use StructuredArrow.mk (𝟙 _)
    -- ⊢ ∃ x x, True
    use StructuredArrow.homMk Y.hom (by erw [Functor.id_map, Category.id_comp])
    -- ⊢ ∃ x, True
    use StructuredArrow.homMk Z.hom (by erw [Functor.id_map, Category.id_comp])
    -- 🎉 no goals
  · intro Y Z f g
    -- ⊢ ∃ W h, h ≫ f = h ≫ g
    use StructuredArrow.mk (𝟙 _)
    -- ⊢ ∃ h, h ≫ f = h ≫ g
    use StructuredArrow.homMk Y.hom (by erw [Functor.id_map, Category.id_comp])
    -- ⊢ StructuredArrow.homMk Y.hom ≫ f = StructuredArrow.homMk Y.hom ≫ g
    ext
    -- ⊢ (StructuredArrow.homMk Y.hom ≫ f).right = (StructuredArrow.homMk Y.hom ≫ g). …
    trans Z.hom <;> simp
    -- ⊢ (StructuredArrow.homMk Y.hom ≫ f).right = Z.hom
                    -- 🎉 no goals
                    -- 🎉 no goals
#align category_theory.representably_flat.id CategoryTheory.RepresentablyFlat.id

instance RepresentablyFlat.comp (F : C ⥤ D) (G : D ⥤ E) [RepresentablyFlat F]
    [RepresentablyFlat G] : RepresentablyFlat (F ⋙ G) := by
  constructor
  -- ⊢ ∀ (X : E), IsCofiltered (StructuredArrow X (F ⋙ G))
  intro X
  -- ⊢ IsCofiltered (StructuredArrow X (F ⋙ G))
  have : Nonempty (StructuredArrow X (F ⋙ G)) := by
    have f₁ : StructuredArrow X G := Nonempty.some inferInstance
    have f₂ : StructuredArrow f₁.right F := Nonempty.some inferInstance
    exact ⟨StructuredArrow.mk (f₁.hom ≫ G.map f₂.hom)⟩
  suffices : IsCofilteredOrEmpty (StructuredArrow X (F ⋙ G))
  -- ⊢ IsCofiltered (StructuredArrow X (F ⋙ G))
  · constructor
    -- 🎉 no goals
  constructor
  -- ⊢ ∀ (X_1 Y : StructuredArrow X (F ⋙ G)), ∃ W x x, True
  · intro Y Z
    -- ⊢ ∃ W x x, True
    let W :=
      @IsCofiltered.min (StructuredArrow X G) _ _ (StructuredArrow.mk Y.hom)
        (StructuredArrow.mk Z.hom)
    let Y' : W ⟶ _ := IsCofiltered.minToLeft _ _
    -- ⊢ ∃ W x x, True
    let Z' : W ⟶ _ := IsCofiltered.minToRight _ _
    -- ⊢ ∃ W x x, True
    let W' :=
      @IsCofiltered.min (StructuredArrow W.right F) _ _ (StructuredArrow.mk Y'.right)
        (StructuredArrow.mk Z'.right)
    let Y'' : W' ⟶ _ := IsCofiltered.minToLeft _ _
    -- ⊢ ∃ W x x, True
    let Z'' : W' ⟶ _ := IsCofiltered.minToRight _ _
    -- ⊢ ∃ W x x, True
    use StructuredArrow.mk (W.hom ≫ G.map W'.hom)
    -- ⊢ ∃ x x, True
    use StructuredArrow.homMk Y''.right (by simp [← G.map_comp])
    -- ⊢ ∃ x, True
    use StructuredArrow.homMk Z''.right (by simp [← G.map_comp])
    -- 🎉 no goals
  · intro Y Z f g
    -- ⊢ ∃ W h, h ≫ f = h ≫ g
    let W :=
      @IsCofiltered.eq (StructuredArrow X G) _ _ (StructuredArrow.mk Y.hom)
        (StructuredArrow.mk Z.hom) (StructuredArrow.homMk (F.map f.right) (StructuredArrow.w f))
        (StructuredArrow.homMk (F.map g.right) (StructuredArrow.w g))
    let h : W ⟶ _ := IsCofiltered.eqHom _ _
    -- ⊢ ∃ W h, h ≫ f = h ≫ g
    let h_cond : h ≫ _ = h ≫ _ := IsCofiltered.eq_condition _ _
    -- ⊢ ∃ W h, h ≫ f = h ≫ g
    let W' :=
      @IsCofiltered.eq (StructuredArrow W.right F) _ _ (StructuredArrow.mk h.right)
        (StructuredArrow.mk (h.right ≫ F.map f.right)) (StructuredArrow.homMk f.right rfl)
        (StructuredArrow.homMk g.right (congr_arg CommaMorphism.right h_cond).symm)
    let h' : W' ⟶ _ := IsCofiltered.eqHom _ _
    -- ⊢ ∃ W h, h ≫ f = h ≫ g
    let h'_cond : h' ≫ _ = h' ≫ _ := IsCofiltered.eq_condition _ _
    -- ⊢ ∃ W h, h ≫ f = h ≫ g
    use StructuredArrow.mk (W.hom ≫ G.map W'.hom)
    -- ⊢ ∃ h, h ≫ f = h ≫ g
    use StructuredArrow.homMk h'.right (by simp [← G.map_comp])
    -- ⊢ StructuredArrow.homMk h'.right ≫ f = StructuredArrow.homMk h'.right ≫ g
    ext
    -- ⊢ (StructuredArrow.homMk h'.right ≫ f).right = (StructuredArrow.homMk h'.right …
    exact (congr_arg CommaMorphism.right h'_cond : _)
    -- 🎉 no goals
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
      -- ⊢ ∀ (J : Type v₁) {𝒥 : SmallCategory J}, FinCategory J → HasLimitsOfShape J (S …
      intro J sJ fJ
      -- ⊢ HasLimitsOfShape J (StructuredArrow X F)
      constructor
      -- ⊢ autoParam (∀ (F_1 : J ⥤ StructuredArrow X F), HasLimit F_1) _auto✝
      -- porting note: instance was inferred automatically in Lean 3
      infer_instance
      -- 🎉 no goals
    cofiltered_of_hasFiniteLimits⟩
#align category_theory.flat_of_preserves_finite_limits CategoryTheory.flat_of_preservesFiniteLimits

namespace PreservesFiniteLimitsOfFlat

open StructuredArrow

variable {J : Type v₁} [SmallCategory J] [FinCategory J] {K : J ⥤ C}

variable (F : C ⥤ D) [RepresentablyFlat F] {c : Cone K} (hc : IsLimit c) (s : Cone (K ⋙ F))

/-- (Implementation).
Given a limit cone `c : cone K` and a cone `s : cone (K ⋙ F)` with `F` representably flat,
`s` can factor through `F.map_cone c`.
-/
noncomputable def lift : s.pt ⟶ F.obj c.pt :=
  let s' := IsCofiltered.cone (s.toStructuredArrow ⋙ StructuredArrow.pre _ K F)
  s'.pt.hom ≫
    (F.map <|
      hc.lift <|
        (Cones.postcompose
              ({ app := fun X => 𝟙 _ } :
                (s.toStructuredArrow ⋙ pre s.pt K F) ⋙ proj s.pt F ⟶ K)).obj <|
          (StructuredArrow.proj s.pt F).mapCone s')
#align category_theory.preserves_finite_limits_of_flat.lift CategoryTheory.PreservesFiniteLimitsOfFlat.lift

theorem fac (x : J) : lift F hc s ≫ (F.mapCone c).π.app x = s.π.app x := by
  simp [lift, ← Functor.map_comp]
  -- 🎉 no goals
#align category_theory.preserves_finite_limits_of_flat.fac CategoryTheory.PreservesFiniteLimitsOfFlat.fac

attribute [local simp] eqToHom_map

theorem uniq {K : J ⥤ C} {c : Cone K} (hc : IsLimit c) (s : Cone (K ⋙ F))
    (f₁ f₂ : s.pt ⟶ F.obj c.pt) (h₁ : ∀ j : J, f₁ ≫ (F.mapCone c).π.app j = s.π.app j)
    (h₂ : ∀ j : J, f₂ ≫ (F.mapCone c).π.app j = s.π.app j) : f₁ = f₂ := by
  -- We can make two cones over the diagram of `s` via `f₁` and `f₂`.
  let α₁ : (F.mapCone c).toStructuredArrow ⋙ map f₁ ⟶ s.toStructuredArrow :=
    { app := fun X => eqToHom (by simp [← h₁])
      naturality := fun j₁ j₂ φ => by
        ext
        -- porting note: Lean 3 proof was `simp` but `Comma.eqToHom_right`
        -- isn't firing for some reason
        -- Asked here https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/simp.20not.20using.20a.20simp.20lemma/near/353943416
        -- I'm now doing `simp, rw [Comma.eqToHom_right, Comma.eqToHom_right], simp` but
        -- I squeezed the first `simp`.
        simp only [Functor.mapCone_pt, Functor.comp_obj, Cone.toStructuredArrow_obj,
          Functor.mapCone_π_app, map_mk, mk_right, Functor.comp_map, Cone.toStructuredArrow_map,
          comp_right, map_map_right, homMk_right]
        rw [Comma.eqToHom_right, Comma.eqToHom_right] -- this is a `simp` lemma
        simp }
  let α₂ : (F.mapCone c).toStructuredArrow ⋙ map f₂ ⟶ s.toStructuredArrow :=
    { app := fun X => eqToHom (by simp [← h₂])
      naturality := fun _ _ _ => by
        ext
        -- porting note: see comments above. `simp` should close this goal (and did in Lean 3)
        simp only [Functor.mapCone_pt, Functor.comp_obj, Cone.toStructuredArrow_obj,
          Functor.mapCone_π_app, map_mk, mk_right, Functor.comp_map, Cone.toStructuredArrow_map,
          comp_right, map_map_right, homMk_right]
        rw [Comma.eqToHom_right, Comma.eqToHom_right] -- this is a `simp` lemma
        simp }
  let c₁ : Cone (s.toStructuredArrow ⋙ pre s.pt K F) :=
    (Cones.postcompose (whiskerRight α₁ (pre s.pt K F) : _)).obj (c.toStructuredArrowCone F f₁)
  let c₂ : Cone (s.toStructuredArrow ⋙ pre s.pt K F) :=
    (Cones.postcompose (whiskerRight α₂ (pre s.pt K F) : _)).obj (c.toStructuredArrowCone F f₂)
  -- The two cones can then be combined and we may obtain a cone over the two cones since
  -- `StructuredArrow s.pt F` is cofiltered.
  let c₀ := IsCofiltered.cone (biconeMk _ c₁ c₂)
  -- ⊢ f₁ = f₂
  let g₁ : c₀.pt ⟶ c₁.pt := c₀.π.app Bicone.left
  -- ⊢ f₁ = f₂
  let g₂ : c₀.pt ⟶ c₂.pt := c₀.π.app Bicone.right
  -- ⊢ f₁ = f₂
  -- Then `g₁.right` and `g₂.right` are two maps from the same cone into the `c`.
  have : ∀ j : J, g₁.right ≫ c.π.app j = g₂.right ≫ c.π.app j := by
    intro j
    injection c₀.π.naturality (BiconeHom.left j) with _ e₁
    injection c₀.π.naturality (BiconeHom.right j) with _ e₂
    -- porting note: Lean 3 proof now finished with `simpa using e₁.symm.trans e₂`
    -- This doesn't work for two reasons in Lean 4: firstly it seems that Lean 4 `simp`
    -- expands `let` definitions by default, so we have to switch this off with `zeta = false`;
    -- secondly, `simp` is not rewriting `Comma.eqToHom_right` for some reason (just like)
    -- 30 lines above here
    have e₃ := e₁.symm.trans e₂
    simp (config := {zeta := false}) at e₃ -- should turn `e₃` into the goal
    rw [Comma.eqToHom_right, Comma.eqToHom_right] at e₃ -- this is a `simp` lemma
    simpa (config := {zeta := false}) using e₃
  have : c.extend g₁.right = c.extend g₂.right := by
    unfold Cone.extend
    congr 1
    ext x
    apply this
  -- And thus they are equal as `c` is the limit.
  have : g₁.right = g₂.right
  -- ⊢ g₁.right = g₂.right
  calc
    g₁.right = hc.lift (c.extend g₁.right) := by
      apply hc.uniq (c.extend _)
      -- Porting note: was `by tidy`, but `aesop` only works if max heartbeats
      -- is increased, so we replace it by the output of `tidy?`
      intro j; rfl
    _ = hc.lift (c.extend g₂.right) := by
      congr
    _ = g₂.right := by
      symm
      apply hc.uniq (c.extend _)
      -- Porting note: was `by tidy`, but `aesop` only works if max heartbeats
      -- is increased, so we replace it by the output of `tidy?`
      intro _; rfl

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
  -- ⊢ (J : Type ?u.100321) → {𝒥 : SmallCategory J} → FinCategory J → PreservesLimi …
  intro J _ _; constructor
  -- ⊢ PreservesLimitsOfShape J F
               -- ⊢ autoParam ({K : J ⥤ C} → PreservesLimit K F) _auto✝
  intro K; constructor
  -- ⊢ PreservesLimit K F
           -- ⊢ {c : Cone K} → IsLimit c → IsLimit (F.mapCone c)
  intro c hc
  -- ⊢ IsLimit (F.mapCone c)
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
    cases x
    -- ⊢ (fun x => preservesFiniteLimitsOfFlat F) (_ : RepresentablyFlat F) = Preserv …
    unfold preservesFiniteLimitsOfFlat
    -- ⊢ (fun x => preservesFiniteLimitsOfPreservesFiniteLimitsOfSize F fun J {𝒥} x_1 …
    dsimp only [preservesFiniteLimitsOfPreservesFiniteLimitsOfSize]
    -- ⊢ PreservesFiniteLimits.mk = PreservesFiniteLimits.mk
    congr
    -- ⊢ (fun J x x_1 => preservesLimitsOfShapeOfEquiv (Equivalence.symm (ULiftHomULi …
    -- porting note: this next line wasn't needed in lean 3
    apply Subsingleton.elim
    -- 🎉 no goals

#align category_theory.preserves_finite_limits_iff_flat CategoryTheory.preservesFiniteLimitsIffFlat

end HasLimit

section SmallCategory

variable {C D : Type u₁} [SmallCategory C] [SmallCategory D] (E : Type u₂) [Category.{u₁} E]


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
      -- ⊢ (lan F ⋙ (evaluation D E).obj X).map i ≫ ((fun G => colim.mapIso (Iso.refl ( …
      -- porting note: was `ext` in lean 3
      -- Now `ext` can't see that `lan` is a colimit.
      -- Uncertain whether it makes sense to add another `@[ext]` lemma.
      -- See https://github.com/leanprover-community/mathlib4/issues/5229
      apply colimit.hom_ext
      -- ⊢ ∀ (j : CostructuredArrow F X), colimit.ι (Lan.diagram F G X) j ≫ (lan F ⋙ (e …
      intro j
      -- ⊢ colimit.ι (Lan.diagram F G X) j ≫ (lan F ⋙ (evaluation D E).obj X).map i ≫ ( …
      simp only [Functor.comp_map, Functor.mapIso_refl, evaluation_obj_map, whiskeringLeft_obj_map,
        lan_map_app, colimit.ι_desc_assoc, Category.comp_id, Category.assoc]
      -- porting note: this deals with the fact that the type of `lan_map_app` has changed
      -- See https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/change.20in.20behaviour.20with.20.60simps.60/near/354350606
      erw [show ((Lan.equiv F H (Lan.loc F H)) (𝟙 (Lan.loc F H))).app j.left =
        colimit.ι (Lan.diagram F H (F.obj j.left))
        (CostructuredArrow.mk (𝟙 (F.obj j.left))) by apply Category.comp_id]
      erw [colimit.ι_pre_assoc (Lan.diagram F H X) (CostructuredArrow.map j.hom), Category.id_comp,
        Category.comp_id, colimit.ι_map]
      rcases j with ⟨j_left, ⟨⟨⟩⟩, j_hom⟩
      -- ⊢ NatTrans.app i { left := j_left, right := { as := PUnit.unit }, hom := j_hom …
      congr
      -- ⊢ (CostructuredArrow.map { left := j_left, right := { as := PUnit.unit }, hom  …
      rw [CostructuredArrow.map_mk, Category.id_comp, CostructuredArrow.mk])
      -- 🎉 no goals
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
  -- ⊢ (J : Type u₁) → {𝒥 : SmallCategory J} → FinCategory J → PreservesLimitsOfSha …
  intro J _ _; skip
  -- ⊢ PreservesLimitsOfShape J (lan F.op)
               -- ⊢ PreservesLimitsOfShape J (lan F.op)
  apply preservesLimitsOfShapeOfEvaluation (lan F.op : (Cᵒᵖ ⥤ E) ⥤ Dᵒᵖ ⥤ E) J
  -- ⊢ (k : Dᵒᵖ) → PreservesLimitsOfShape J (lan F.op ⋙ (evaluation Dᵒᵖ E).obj k)
  intro K
  -- ⊢ PreservesLimitsOfShape J (lan F.op ⋙ (evaluation Dᵒᵖ E).obj K)
  haveI : IsFiltered (CostructuredArrow F.op K) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence F (unop K))
  exact preservesLimitsOfShapeOfNatIso (lanEvaluationIsoColim _ _ _).symm
  -- 🎉 no goals
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
  -- ⊢ PreservesFiniteLimits (lan F.op)
  infer_instance
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.Lan_preserves_finite_limits_of_preserves_finite_limits CategoryTheory.lanPreservesFiniteLimitsOfPreservesFiniteLimits

theorem flat_iff_lan_flat (F : C ⥤ D) :
    RepresentablyFlat F ↔ RepresentablyFlat (lan F.op : _ ⥤ Dᵒᵖ ⥤ Type u₁) :=
  ⟨fun H => inferInstance, fun H => by
    skip
    -- ⊢ RepresentablyFlat F
    haveI := preservesFiniteLimitsOfFlat (lan F.op : _ ⥤ Dᵒᵖ ⥤ Type u₁)
    -- ⊢ RepresentablyFlat F
    haveI : PreservesFiniteLimits F := by
      apply preservesFiniteLimitsOfPreservesFiniteLimitsOfSize.{u₁}
      intros; skip; apply preservesLimitOfLanPreservesLimit
    apply flat_of_preservesFiniteLimits⟩
    -- 🎉 no goals
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
    -- ⊢ (J : Type u₁) → {𝒥 : SmallCategory J} → FinCategory J → PreservesLimitsOfSha …
    intros; apply preservesLimitOfLanPreservesLimit
    -- ⊢ PreservesLimitsOfShape J✝ F
            -- 🎉 no goals
  left_inv x := by
    -- porting note: `cases x` and an `unfold` not necessary in lean 4.
    -- Remark : in mathlib3 we had `unfold preservesFiniteLimitsOfFlat`
    -- but there was no `preservesFiniteLimitsOfFlat` in the goal! Experimentation
    -- indicates that it was doing the same as `dsimp only`
    dsimp only [preservesFiniteLimitsOfPreservesFiniteLimitsOfSize]; congr
    -- ⊢ PreservesFiniteLimits.mk = x
                                                                     -- ⊢ (fun J x_1 x_2 => preservesLimitsOfShapeOfEquiv (Equivalence.symm (ULiftHomU …
    -- porting note: next line wasn't necessary in lean 3
    apply Subsingleton.elim
    -- 🎉 no goals
  right_inv x := by
    -- cases x; -- porting note: not necessary in lean 4
    dsimp only [lanPreservesFiniteLimitsOfPreservesFiniteLimits,
      lanPreservesFiniteLimitsOfFlat,
      preservesFiniteLimitsOfPreservesFiniteLimitsOfSize]
    congr
    -- ⊢ (fun J x_1 x_2 => preservesLimitsOfShapeOfEquiv (Equivalence.symm (ULiftHomU …
    -- porting note: next line wasn't necessary in lean 3
    apply Subsingleton.elim
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.preserves_finite_limits_iff_Lan_preserves_finite_limits CategoryTheory.preservesFiniteLimitsIffLanPreservesFiniteLimits

end SmallCategory

end CategoryTheory
