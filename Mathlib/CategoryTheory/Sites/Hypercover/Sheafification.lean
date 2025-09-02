/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Sites.OneHypercover
import Mathlib.CategoryTheory.Sites.IsSheafOneHypercover
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory

universe w' w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] {A : Type*} [Category A]
variable (P : Cᵒᵖ ⥤ A) (J : GrothendieckTopology C)
variable {S : C}

namespace GrothendieckTopology

namespace OneHypercover

@[simps! id_s₀ id_s₁ id_h₀ id_h₁ comp_s₀ comp_s₁ comp_h₀ comp_h₁]
instance : Category (J.OneHypercover S) where
  Hom := Hom
  id E := PreOneHypercover.Hom.id E.toPreOneHypercover
  comp f g := f.comp g

variable {J} in
@[simps]
def isoMk {E F : J.OneHypercover S} (f : E.toPreOneHypercover ≅ F.toPreOneHypercover) :
    E ≅ F where
  __ := f

@[simps]
noncomputable
def pullback [HasPullbacks C] {T : C} (f : S ⟶ T) : J.OneHypercover T ⥤ J.OneHypercover S where
  obj E := E.pullback₁ f
  map g := g.pullback₁ f
  map_id _ := PreOneHypercover.Hom.pullback₁_id f
  map_comp _ _ := PreOneHypercover.Hom.pullback₁_comp f _ _

@[simps!]
noncomputable
def pullbackId [HasPullbacks C] (S : C) : pullback J (𝟙 S) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun E ↦ isoMk E.pullback₁Id) fun {X Y} f ↦
    PreOneHypercover.Hom.ext'' (by rfl) (by simp) (by simp) (by simp)

@[simps!]
noncomputable
def pullbackComp [HasPullbacks C] {S T W : C} (f : S ⟶ T) (g : T ⟶ W) :
    pullback J (f ≫ g) ≅ pullback J g ⋙ pullback J f :=
  NatIso.ofComponents (fun E ↦ isoMk (E.pullback₁Comp f g)) fun {X Y} f ↦ by
    apply PreOneHypercover.Hom.ext'' (by rfl)
    · intros
      apply pullback.hom_ext
      · simp
      · apply pullback.hom_ext <;> simp
    · intros
      apply pullback.hom_ext
      · simp
      · apply pullback.hom_ext <;> simp
    · simp

end OneHypercover

variable [∀ (X : C) (E : GrothendieckTopology.OneHypercover.{w} J X),
  HasMultiequalizer (E.multicospanIndex P)]

@[simps -isSimp]
noncomputable
def diagram (X : C) : (J.OneHypercover X)ᵒᵖ ⥤ A where
  obj E := multiequalizer (E.unop.multicospanIndex P)
  map f := f.unop.mapMultifork P
  map_id _ := PreOneHypercover.Hom.mapMultifork_id _
  map_comp _ _ := PreOneHypercover.Hom.mapMultifork_comp _ _ _

open Opposite

@[simps -isSimp]
noncomputable
def diagramNatTrans {P Q : Cᵒᵖ ⥤ A}
    [∀ (X : C) (E : J.OneHypercover X), HasMultiequalizer (E.multicospanIndex P)]
    [∀ (X : C) (E : J.OneHypercover X), HasMultiequalizer (E.multicospanIndex Q)]
    (f : P ⟶ Q) (X : C) :
    diagram P J X ⟶ diagram Q J X where
  app E :=
    Multiequalizer.lift _ _ (fun i ↦ Multiequalizer.ι _ i ≫ f.app _) <| by
      intro k
      dsimp
      rw [Category.assoc, ← f.naturality]
      erw [Multiequalizer.condition_assoc]
      simp
  naturality := sorry

@[simps -isSimp]
noncomputable
def diagramMap [HasPullbacks C] {X Y : C} (f : X ⟶ Y) :
    J.diagram P Y ⟶ (OneHypercover.pullback J f).op ⋙ J.diagram P X where
  app E := Multiequalizer.lift _ _
    (fun (i : E.unop.I₀) ↦
      Multiequalizer.ι (E.unop.multicospanIndex P) i ≫ P.map (pullback.snd _ _).op) <| fun i ↦ by
    simp only [Functor.op_obj, OneHypercover.pullback_obj,
      OneHypercover.pullback₁_toPreOneHypercover, PreOneHypercover.multicospanIndex_right,
      PreOneHypercover.pullback₁_toPreZeroHypercover, PreZeroHypercover.pullback₁_I₀,
      PreOneHypercover.pullback₁_I₁, PreOneHypercover.pullback₁_Y,
      PreOneHypercover.multicospanShape_fst, PreOneHypercover.multicospanIndex_left,
      PreZeroHypercover.pullback₁_X, PreOneHypercover.multicospanIndex_fst,
      PreOneHypercover.pullback₁_p₁, Category.assoc, PreOneHypercover.multicospanShape_snd,
      PreOneHypercover.multicospanIndex_snd, PreOneHypercover.pullback₁_p₂]
    rw [← P.map_comp, ← op_comp, Limits.pullback.lift_snd]
    rw [← P.map_comp, ← op_comp, Limits.pullback.lift_snd]
    simp_rw [op_comp, Functor.map_comp, ← Category.assoc]
    congr 1
    apply Multiequalizer.condition
  naturality E F f := by
    apply Multiequalizer.hom_ext
    intro i
    simp only [diagram, Functor.op_obj, OneHypercover.pullback_obj,
      OneHypercover.pullback₁_toPreOneHypercover, PreOneHypercover.multicospanIndex_left,
      PreOneHypercover.pullback₁_toPreZeroHypercover, PreZeroHypercover.pullback₁_X,
      Functor.comp_obj, Category.assoc, limit.lift_π, Multifork.ofι_pt, Multifork.ofι_π_app,
      PreOneHypercover.Hom.mapMultifork_ι_assoc, Functor.comp_map, Functor.op_map,
      OneHypercover.pullback_map, Quiver.Hom.unop_op, PreOneHypercover.Hom.mapMultifork_ι,
      PreOneHypercover.Hom.pullback₁_toHom, PreZeroHypercover.pullback₁_I₀, limit.lift_π_assoc,
      MulticospanIndex.multicospan_obj, PreOneHypercover.multicospanShape_L,
      PreOneHypercover.multicospanShape_R, PreOneHypercover.multicospanIndex_right,
      PreOneHypercover.pullback₁_I₁, PreOneHypercover.pullback₁_Y]
    rw [← P.map_comp, ← op_comp]
    rw [← P.map_comp, ← op_comp, Limits.pullback.lift_snd]

@[simp]
lemma diagramMap_id [HasPullbacks C] (X : C) :
    diagramMap.{w} P J (𝟙 X : X ⟶ X) =
      (Functor.leftUnitor _).inv ≫
        Functor.whiskerRight ((Functor.opId _).inv ≫
          NatTrans.op (OneHypercover.pullbackId.{_, _, w} J X).hom) _ := by
  ext E
  apply Multiequalizer.hom_ext
  simp [diagram_map, diagramMap_app]

@[simp]
lemma diagramMap_comp [HasPullbacks C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    diagramMap.{w} P J (f ≫ g) = diagramMap.{w} P J g ≫
      (OneHypercover.pullback J g).op.whiskerLeft (diagramMap.{w} P J f) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight ((Functor.opComp _ _).inv ≫
        NatTrans.op (OneHypercover.pullbackComp J f g).hom)
        (diagram P J X) := by
  ext E
  apply Multiequalizer.hom_ext
  simp [diagram_map, ← Functor.map_comp, ← op_comp, diagramMap_app]

@[reassoc]
lemma diagramMap_app_app [HasPullbacks C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (E : (J.OneHypercover Z)ᵒᵖ) :
    (diagramMap P J g).app E ≫ (diagramMap P J f).app _ =
    (diagramMap.{w} P J (f ≫ g)).app E ≫
      (diagram P J X).map ((OneHypercover.pullbackComp J f g).app _).inv.op := by
  simp only [Functor.op_obj, OneHypercover.pullback_obj, Functor.comp_obj, diagramMap_comp,
    Functor.whiskerRight_comp, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Functor.opComp_inv_app, Functor.map_id,
    NatTrans.op_app, Category.id_comp, Iso.app_inv, Category.assoc]
  rw [← (diagram P J X).map_comp]
  simp [← op_comp]

variable [∀ X, HasColimitsOfShape (J.OneHypercover X)ᵒᵖ A]

@[simps -isSimp]
noncomputable
def sheafification [HasPullbacks C] : Cᵒᵖ ⥤ A where
  obj X := colimit (J.diagram P X.unop)
  map {X Y} f := colimMap (diagramMap P J f.unop) ≫ colimit.pre _ _

noncomputable
def toSheafification [HasPullbacks C] : P ⟶ sheafification P J where
  app X := by
    dsimp [sheafification_obj]
    refine ?_ ≫ colimit.ι _ ?_
    · dsimp [diagram_obj]
      sorry
    · constructor
      sorry
  naturality := sorry

variable [HasPullbacks C]
variable [∀ (X : C) (E : GrothendieckTopology.OneHypercover.{w} J X),
  HasMultiequalizer (E.multicospanIndex (sheafification P J))]
variable [∀ (X : C) (E : PreOneHypercover.{w} X),
  HasMultiequalizer (E.multicospanIndex P)]

local notation3 "H⁰(" E ", " P ")" =>
  multiequalizer (PreOneHypercover.multicospanIndex (OneHypercover.toPreOneHypercover E) P)

section

variable {J}

variable {E : OneHypercover.{w} J S}

noncomputable
def OneHypercover.Refinement.map (R : E.Refinement) :
    H⁰(R.bind, P) ⟶ H⁰(E, sheafification P J) := by
  refine Multiequalizer.lift _ _
    (fun i : E.I₀ ↦ (diagramMap P J (E.f i)).app ⟨R.bind⟩ ≫
      (diagram P J (E.X i)).map (R.homPullback₁ i).op ≫
      colimit.ι (diagram P J (E.X i)) ⟨R.cover₁ i⟩) <| by
    intro b
    simp [sheafification_map]
    erw [diagramMap_app_app_assoc]
    simp
    -- this all follows from E.w but it is annoying to prove
    sorry

lemma OneHypercover.Refinement.map_comp (R : E.Refinement) :
    R.map P = colimit.ι (diagram P J _) ⟨R.bind⟩ ≫ E.toMultiequalizer (sheafification P J) := by
  apply Multiequalizer.hom_ext
  intro i
  simp [map, PreOneHypercover.toMultiequalizer, PreOneHypercover.multifork, sheafification_map]

end

--lemma foo {S : C} (E F : OneHypercover.{w} J S) (f : E ⟶ F) :
--    colimit.ι _ ⟨F⟩ ≫ F.toMultiequalizer (sheafification P J) =
--      (diagram P J S).map f.op ≫ sorry :=
--  sorry

variable {FA : A → A → Type*} {CA : A → Type*} [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]
variable [ConcreteCategory A FA]
variable [(forget A).ReflectsIsomorphisms]

section

end

variable {J}

@[ext]
structure OneHypercover.Meq {X : C} (P : Cᵒᵖ ⥤ A) (E : J.OneHypercover X) where
  obj (i : E.I₀) : CA (P.obj (op (E.X i)))
  compatible {i j : E.I₀} (k : E.I₁ i j) : P.map (E.p₁ k).op (obj i) = P.map (E.p₂ k).op (obj j)

noncomputable
def OneHypercover.equivMeq {X : C} (P : Cᵒᵖ ⥤ A) (E : J.OneHypercover X)
    [HasMultiequalizer (E.multicospanIndex P)]
    [PreservesLimit (E.multicospanIndex P).multicospan (forget A)] :
    CA (H⁰(E, P)) ≃ E.Meq P :=
  (Concrete.multiequalizerEquiv _).trans
    { toFun x := ⟨x.1, fun {i j} k ↦ x.2 ⟨⟨i, j⟩, k⟩⟩
      invFun x := ⟨x.1, fun i ↦ x.compatible _⟩ }

variable [∀ (X : C) (E : OneHypercover.{w} J X),
  PreservesLimit (E.multicospanIndex P).multicospan (forget A)]
variable [∀ (X : C) (E : OneHypercover.{w} J X),
  PreservesLimit (E.multicospanIndex <| sheafification P J).multicospan (forget A)]
variable [∀ (X : C), PreservesColimit (diagram P J X) (forget A)]

variable (E : OneHypercover.{w} J S)

lemma foobar (x : E.Meq (sheafification P J)) :
    ∃ (y : CA ((sheafification P J).obj (op S))),
      E.toMultiequalizer (sheafification P J) y = (E.equivMeq _).symm x := by
  have (i : E.I₀) : ∃ (W : OneHypercover.{w} J (E.X i)) (w : W.Meq P),
      x.obj i = colimit.ι (diagram P J (E.X i)) ⟨W⟩ ((W.equivMeq P).symm w) := by
    obtain ⟨W, w, hw⟩ := Concrete.colimit_exists_rep _ (x.obj i)
    use W.1, W.1.equivMeq P w
    simp [← hw]
  choose W w hw using this
  let B : OneHypercover.{w} J S := sorry
  let b : B.Meq P := sorry
  use colimit.ι (diagram P J S) ⟨B⟩ ((B.equivMeq P).symm b)
  apply (E.equivMeq _).injective
  ext i
  simp only [Equiv.apply_symm_apply]
  sorry

lemma bazarfaasdf' (x : E.Meq (sheafification P J)) :
    ∃ (R : E.Refinement) (y : R.bind.Meq P),
      R.map P ((R.bind.equivMeq _).symm y) = (E.equivMeq _).symm x := by
  have (i : E.I₀) : ∃ (W : OneHypercover.{w} J (E.X i)) (w : W.Meq P),
      x.obj i = colimit.ι (diagram P J (E.X i)) ⟨W⟩ ((W.equivMeq P).symm w) := by
    obtain ⟨W, w, hw⟩ := Concrete.colimit_exists_rep _ (x.obj i)
    use W.1, W.1.equivMeq P w
    simp [← hw]
  choose W w hw using this
  have (i j : E.I₀) (k : E.I₁ i j) :
      ∃ (V : OneHypercover.{w} J (E.Y k))
        (v₁ : V ⟶ (W i).pullback₁ (E.p₁ k))
        (v₂ : V ⟶ (W j).pullback₁ (E.p₂ k)),
        (diagram P J (E.Y k)).map v₁.op
            ((diagramMap P J (E.p₁ k)).app (op (W i)) (((W i).equivMeq P).symm (w i))) =
          (diagram P J (E.Y k)).map v₂.op
            ((diagramMap P J (E.p₂ k)).app (op (W j)) (((W j).equivMeq P).symm (w j))) := by
    have := x.compatible k
    simp_rw [hw] at this
    simp [sheafification_map] at this
    rw [← ConcreteCategory.comp_apply] at this
    rw [← ConcreteCategory.comp_apply] at this
    erw [← ConcreteCategory.comp_apply] at this
    erw [← ConcreteCategory.comp_apply] at this
    simp at this
    -- this is false but we can fix it
    have _ : IsFiltered (J.OneHypercover (E.Y k))ᵒᵖ := sorry
    obtain ⟨⟨V⟩, v₁, v₂, hv⟩ := Concrete.colimit_exists_of_rep_eq _ _ _ this
    use V, v₁.unop, v₂.unop, hv
  choose V v₁ v₂ hv using this
  let R : E.Refinement := {
    cover i := (W i).toPreZeroHypercover
    I {i j} k a b := (V i j k).I₀
    Z {i j} k a b l := (V i j k).X l
    p {i j} k a b l := (V i j k).f l
    q₁ {i j} k a b l := (v₁ i j k).h₀ _ --exact pullback.snd _ _
    q₂ {i j} k a b l := sorry
    w := sorry
    w_self := sorry
    w₁ := sorry
    w₂ := sorry
    mem₀ := sorry
    mem₁ := sorry
  }
  refine ⟨R, ⟨fun ⟨i, a⟩ ↦ (w i).obj a, ?_⟩, ?_⟩
  · simp [R]
    sorry
  · sorry


lemma bazarfaasdf (x : CA H⁰(E, sheafification P J)) :
    ∃ (R : E.Refinement) (y : CA H⁰(R.bind, P)), R.map P y = x := by
  sorry

lemma isSheaf_sheafification [(forget A).ReflectsIsomorphisms] [HasPullbacks C]
    [∀ (X : C) (E : OneHypercover.{w} J X),
      HasMultiequalizer (E.multicospanIndex (sheafification P J))]
    [IsGeneratedByOneHypercovers.{w} J] :
    Presheaf.IsSheaf J (sheafification.{w} P J) := by
  rw [CategoryTheory.Presheaf.isSheaf_iff_of_isGeneratedByOneHypercovers]
  intro X E
  rw [PreOneHypercover.nonempty_isLimit_multifork_iff_isIso]
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨?_, ?_⟩
  · sorry
  · intro t
    sorry
  --refine Multifork.IsLimit.mk _ ?_ ?_ ?_
  --· intro K
  --  dsimp [PreOneHypercover.multifork, sheafification_obj]
  --  refine ?_ ≫ colimit.ι (diagram P J X) ⟨E⟩
  --  simp [diagram_obj]
  --  refine Multiequalizer.lift _ _ ?_ ?_
  --  · intro (i : E.I₀)
  --    refine K.ι i ≫ ?_
  --    dsimp
  --    simp [sheafification]
  --    let c : Cocone (diagram P J (E.X i)) := {
  --      pt := P.obj ⟨E.X i⟩
  --      ι.app F := by
  --        simp [diagram_obj]
  --        refine Multiequalizer.ι _ ?_ ≫ ?_
  --        · simp
  --          sorry
  --        · sorry
  --      ι.naturality := sorry
  --    }
  --    apply colimit.desc _ c
  --  · sorry
  --· sorry
  --· sorry

end GrothendieckTopology

end CategoryTheory
