/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Sites.OneHypercover
import Mathlib.CategoryTheory.Sites.IsSheafOneHypercover
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc

universe w' w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] {A : Type*} [Category A]
variable (P : Cᵒᵖ ⥤ A) (J : GrothendieckTopology C)
variable {S : C}

namespace PreZeroHypercover

@[simps]
noncomputable
def interOver {X Y S : C} (E : PreZeroHypercover.{w} X) (F : PreZeroHypercover.{w'} Y)
    (f : X ⟶ S) (g : Y ⟶ S) [Limits.HasPullbacks C] :
    PreZeroHypercover (pullback f g) where
  I₀ := E.I₀ × F.I₀
  X ij := pullback (E.f ij.1 ≫ f) (F.f ij.2 ≫ g)
  f ij := pullback.map _ _ _ _ (E.f _) (F.f _) (𝟙 _) (by simp) (by simp)

end PreZeroHypercover

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

@[reassoc (attr := simp)]
lemma diagram_map_ι {X : C} (E F : (J.OneHypercover X)ᵒᵖ) (f : E ⟶ F) (i : F.1.I₀) :
    (diagram P J X).map f ≫ Multiequalizer.ι _ i =
      Multiequalizer.ι (E.1.multicospanIndex P) (f.unop.s₀ i) ≫ P.map (f.unop.h₀ i).op := by
  simp [diagram_map]

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

@[reassoc (attr := simp)]
lemma diagramMap_app_ι [HasPullbacks C] {X Y : C} (f : X ⟶ Y) (E : OneHypercover.{w} J Y)
    (k : E.I₀) :
    (diagramMap.{w} P J f).app (op E) ≫ Multiequalizer.ι _ k =
      Multiequalizer.ι _ _ ≫ P.map (pullback.snd _ _).op := by
  simp [diagramMap_app]

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

include P in
lemma diagramMap_diagram_fst [HasPullbacks C] {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S)
    (E F : OneHypercover.{w} J S) (u : E ⟶ F) :--
    True := by
    --(diagramMap P J f).app (op E) ≫ (diagram P J _).map (by dsimp) = _ :=
  have := (diagramMap P J f).naturality u.op
  dsimp at this
  sorry

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

@[simp]
lemma OneHypercover.ι_equivMeq_symm {X : C} (P : Cᵒᵖ ⥤ A) (E : J.OneHypercover X)
    [HasMultiequalizer (E.multicospanIndex P)]
    [PreservesLimit (E.multicospanIndex P).multicospan (forget A)] (x : E.Meq P) (i : E.I₀) :
    Multiequalizer.ι (E.multicospanIndex P) i ((E.equivMeq _).symm x) = x.obj i := by
  simp [equivMeq]
  erw [← Concrete.multiequalizerEquiv_apply]
  sorry

variable [∀ (X : C) (E : OneHypercover.{w} J X),
  PreservesLimit (E.multicospanIndex P).multicospan (forget A)]
variable [∀ (X : C) (E : OneHypercover.{w} J X),
  PreservesLimit (E.multicospanIndex <| sheafification P J).multicospan (forget A)]
variable [∀ (X : C), PreservesColimit (diagram P J X) (forget A)]

variable (E : OneHypercover.{w} J S)

@[reassoc]
lemma _root_.CategoryTheory.PreOneHypercover.multiequalizer_condition
    (E : PreOneHypercover.{w} S) {i j : E.I₀} (k : E.I₁ i j) :
    Multiequalizer.ι (E.multicospanIndex P) i ≫ P.map (E.p₁ k).op =
      Multiequalizer.ι (E.multicospanIndex P) j ≫ P.map (E.p₂ k).op :=
  Multiequalizer.condition (E.multicospanIndex P) ⟨(i, j), k⟩

lemma something₀' (E F G : OneHypercover.{w} J S) (f : G ⟶ E) (g : G ⟶ F)
    (x : CA H⁰(E, P)) (y : CA H⁰(F, P))
    (h : (diagram P J S).map f.op x = (diagram P J S).map g.op y)
    {i : E.I₀} {j : F.I₀} :
    ∃ (W : PreZeroHypercover.{w} (Limits.pullback (E.f i) (F.f j))),
      ∀ (l : W.I₀),
        P.map (W.f l ≫ pullback.fst _ _).op 
          (Multiequalizer.ι (E.multicospanIndex P) i x) =
        P.map (W.f l ≫ pullback.snd _ _).op
          (Multiequalizer.ι (F.multicospanIndex P) j y) := by
  let W := G.toPreZeroHypercover.pullback₁ (pullback.fst (E.f i) (F.f j) ≫ E.f i)
  let E' (k : G.I₀) : PreZeroHypercover (Limits.pullback (E.f i) (G.f k)) :=
    ((E.cover₀ i (f.s₀ k)).pullback₁ (pullback.fst (pullback.snd _ _) (f.h₀ k))).pushforwardIso
      (pullbackLeftPullbackSndIso _ _ _ ≪≫ pullback.congrHom rfl (by simp))
  let F' (k : G.I₀) : PreZeroHypercover (Limits.pullback (F.f j) (G.f k)) :=
    ((F.cover₀ j (g.s₀ k)).pullback₁ (pullback.fst (pullback.snd _ _) (g.h₀ k))).pushforwardIso
      (pullbackLeftPullbackSndIso _ _ _ ≪≫ pullback.congrHom rfl (by simp))
  let A (k : G.I₀) : PreZeroHypercover (W.X k) :=
    ((E' k).interOver (F' k) (pullback.snd _ _) (pullback.snd _ _)).pushforwardIso <|
      pullbackLeftPullbackSndIso _ _ _ ≪≫
        pullback.congrHom rfl pullback.condition.symm ≪≫
        (pullbackAssoc _ _ _ _).symm ≪≫
        pullback.congrHom pullback.condition.symm rfl
  let W' : PreZeroHypercover.{w} (Limits.pullback (E.f i) (F.f j)) := W.bind A
  refine ⟨W', fun l ↦ ?_⟩
  let pW' : W'.X l ⟶ Limits.pullback (pullback.fst (E.f i) (F.f j) ≫ E.f i) (G.f l.fst) :=
    pullback.lift
      (pullback.lift
        (pullback.fst _ _ ≫ pullback.fst _ _ ≫ pullback.fst _ _ ≫ pullback.fst _ _)
        (pullback.snd _ _ ≫ pullback.fst _ _ ≫ pullback.fst _ _ ≫ pullback.fst _ _)
        ?_)
      (pullback.fst _ _ ≫ pullback.fst _ _ ≫ pullback.snd _ _)
      ?_
  calc
    _ = ((diagramMap P J (pullback.fst (E.f i) (F.f j) ≫ E.f i)).app (op G) ≫
          Multiequalizer.ι _ l.1 ≫ P.map pW'.op) ((diagram P J S).map f.op x) := ?_
    _ = ((diagramMap P J (pullback.fst (E.f i) (F.f j) ≫ E.f i)).app (op G) ≫
          Multiequalizer.ι _ l.1 ≫ P.map pW'.op) ((diagram P J S).map g.op y) := by rw [h]
  · rw [diagramMap_app_ι_assoc]
    rw [← ConcreteCategory.comp_apply]
    erw [← ConcreteCategory.comp_apply]
    rw [diagram_map_ι_assoc]
    dsimp only
    rw [← Functor.map_comp, ← op_comp]
    rw [← Functor.map_comp, ← op_comp]
    congr 2
    have hl : W'.f l ≫ pullback.fst (E.f i) (F.f j) =
        pullback.fst _ _ ≫ pullback.snd _ _ ≫ E.p₁ l.2.1 := by
      obtain ⟨a, b⟩ := l
      simp only [PreZeroHypercover.pullback₁_X, PreZeroHypercover.pullback₁_I₀,
        PreZeroHypercover.pushforwardIso_I₀, PreZeroHypercover.interOver_I₀,
        PreZeroHypercover.bind_X, PreZeroHypercover.pushforwardIso_X, PreZeroHypercover.interOver_X,
        PreZeroHypercover.bind_f, PreZeroHypercover.pushforwardIso_f, PreZeroHypercover.interOver_f,
        Iso.trans_hom, pullback.congrHom_hom, Iso.symm_hom, PreZeroHypercover.pullback₁_f,
        Category.assoc, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app, Category.comp_id,
        pullbackAssoc_inv_fst_fst, pullbackLeftPullbackSndIso_hom_fst, limit.lift_π_assoc,
        cospan_left, PreOneHypercover.cover₀_f, W', W, A]
      congr 1
      simp only [PreZeroHypercover.pushforwardIso_I₀, PreZeroHypercover.pullback₁_I₀,
        PreOneHypercover.cover₀_I₀, PreZeroHypercover.pushforwardIso_X,
        PreZeroHypercover.pullback₁_X, PreOneHypercover.cover₀_X, PreOneHypercover.cover₀_f,
        PreZeroHypercover.pushforwardIso_f, PreZeroHypercover.pullback₁_f, Iso.trans_hom,
        pullback.congrHom_hom, Category.assoc, limit.lift_π, PullbackCone.mk_pt,
        PullbackCone.mk_π_app, Category.comp_id, pullbackLeftPullbackSndIso_hom_fst, E']
      rw [pullback.condition_assoc]
      simp
    have hr : pW' ≫ pullback.snd (pullback.fst (E.f i) (F.f j) ≫ E.f i) (G.f l.fst) ≫
        f.op.unop.h₀ l.fst = pullback.fst _ _ ≫ pullback.snd _ _ ≫ E.p₂ l.2.1 := by
      simp only [Quiver.Hom.unop_op, PreOneHypercover.cover₀_X, PreOneHypercover.cover₀_f,
        limit.lift_π_assoc, PullbackCone.mk_pt, cospan_right, PullbackCone.mk_π_app, Category.assoc,
        pW']
      congr 1
      rw [← pullback.condition]
      rw [pullback.condition_assoc]
      simp
    simp_rw [Category.assoc, hl, hr, op_comp, Functor.map_comp, Category.assoc]
    rw [PreOneHypercover.multiequalizer_condition_assoc]
    dsimp
  · rw [diagramMap_app_ι_assoc]
    rw [← ConcreteCategory.comp_apply]
    erw [← ConcreteCategory.comp_apply]
    rw [diagram_map_ι_assoc]
    dsimp only
    rw [← Functor.map_comp, ← op_comp]
    rw [← Functor.map_comp, ← op_comp]
    congr 2
    have hl : W'.f l ≫ pullback.snd (E.f i) (F.f j) =
        pullback.snd _ _ ≫ pullback.snd _ _ ≫ F.p₁ l.2.2 := by
      obtain ⟨a, b⟩ := l
      simp only [PreZeroHypercover.pullback₁_X, PreZeroHypercover.pullback₁_I₀,
        PreZeroHypercover.pushforwardIso_I₀, PreZeroHypercover.interOver_I₀,
        PreZeroHypercover.bind_X, PreZeroHypercover.pushforwardIso_X, PreZeroHypercover.interOver_X,
        PreZeroHypercover.bind_f, PreZeroHypercover.pushforwardIso_f, PreZeroHypercover.interOver_f,
        Iso.trans_hom, pullback.congrHom_hom, Iso.symm_hom, PreZeroHypercover.pullback₁_f,
        Category.assoc, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app, Category.comp_id,
        pullbackAssoc_inv_fst_snd, limit.lift_π_assoc, cospan_right,
        pullbackLeftPullbackSndIso_hom_snd_assoc, PreOneHypercover.cover₀_f, W', W, A]
      congr 1
      simp only [PreZeroHypercover.pushforwardIso_I₀, PreZeroHypercover.pullback₁_I₀,
        PreOneHypercover.cover₀_I₀, PreZeroHypercover.pushforwardIso_X,
        PreZeroHypercover.pullback₁_X, PreOneHypercover.cover₀_X, PreOneHypercover.cover₀_f,
        PreZeroHypercover.pushforwardIso_f, PreZeroHypercover.pullback₁_f, Iso.trans_hom,
        pullback.congrHom_hom, Category.assoc, limit.lift_π, PullbackCone.mk_pt,
        PullbackCone.mk_π_app, Category.comp_id, pullbackLeftPullbackSndIso_hom_fst, F']
      rw [pullback.condition_assoc]
      congr 1
      simp
    have hr :
        pW' ≫ pullback.snd (pullback.fst (E.f i) (F.f j) ≫ E.f i) (G.f l.fst) ≫ g.op.unop.h₀ l.fst =
          pullback.snd _ _ ≫ pullback.snd _ _ ≫ F.p₂ l.2.2 := by
      simp [pW']
      have : ((E' l.fst).f l.snd.1 ≫ pullback.snd (E.f i) (G.f l.fst)) =
          pullback.fst (pullback.fst (pullback.snd (E.f i) (E.f (f.s₀ l.fst))) (f.h₀ l.fst))
            (E.toPullback l.snd.1) ≫
            pullback.snd (pullback.snd (E.f i) (E.f (f.s₀ l.fst))) (f.h₀ l.fst) := by
        simp [E']
      rw [← reassoc_of% this]
      nth_rw 2 [← Category.assoc]
      rw [pullback.condition_assoc]
      congr 1
      simp only [PreZeroHypercover.pushforwardIso_I₀, PreZeroHypercover.pullback₁_I₀,
        PreOneHypercover.cover₀_I₀, PreZeroHypercover.pushforwardIso_X,
        PreZeroHypercover.pullback₁_X, PreOneHypercover.cover₀_X, PreOneHypercover.cover₀_f,
        PreZeroHypercover.pushforwardIso_f, PreZeroHypercover.pullback₁_f, Iso.trans_hom,
        pullback.congrHom_hom, Category.assoc, limit.lift_π, PullbackCone.mk_pt,
        PullbackCone.mk_π_app, Category.comp_id, pullbackLeftPullbackSndIso_hom_snd, F']
      rw [← pullback.condition]
      rw [pullback.condition_assoc]
      simp
    simp_rw [Category.assoc, hl, hr, op_comp, Functor.map_comp, Category.assoc]
    rw [PreOneHypercover.multiequalizer_condition_assoc]
    dsimp
  · simp only [PreOneHypercover.cover₀_X, PreOneHypercover.cover₀_f, Category.assoc]
    rw [pullback.condition]
    have : (E' l.fst).f l.snd.1 ≫ pullback.snd (E.f i) (G.f l.fst) =
        pullback.fst (pullback.fst (pullback.snd (E.f i) (E.f (f.s₀ l.fst))) (f.h₀ l.fst))
          (E.toPullback l.snd.1) ≫
        pullback.snd (pullback.snd (E.f i) (E.f (f.s₀ l.fst))) (f.h₀ l.fst) := by
      simp [E']
    nth_rw 2 [pullback.condition_assoc]
    rw [← reassoc_of% this]
    nth_rw 2 [← Category.assoc]
    rw [pullback.condition_assoc]
    congr 1
    simp [F']
    congr 1
    rw [pullback.condition, pullback.condition_assoc]
    simp
  · simp only [PreOneHypercover.cover₀_X, PreOneHypercover.cover₀_f, limit.lift_π_assoc,
      PullbackCone.mk_pt, cospan_left, PullbackCone.mk_π_app, Category.assoc]
    congr 2
    rw [pullback.condition, pullback.condition_assoc]
    simp

#exit

lemma something₀ (E F G : OneHypercover.{w} J S) (f : G ⟶ E) (g : G ⟶ F)
    (x : CA H⁰(E, P)) (y : CA H⁰(F, P))
    (h : (diagram P J S).map f.op x = (diagram P J S).map g.op y)
    {i j : E.I₀} (k : E.I₁ i j) {i' j' : F.I₀} (k' : F.I₁ i' j') :
    ∃ (W : OneHypercover.{w} J (Limits.pullback (E.p₁ k ≫ E.f i) (F.p₁ k' ≫ F.f i'))),
      ∀ (l : W.I₀),
        P.map (W.f l ≫ pullback.fst _ _ ≫ E.p₁ k).op 
          (Multiequalizer.ι (E.multicospanIndex P) i x) =
        P.map (W.f l ≫ pullback.snd _ _ ≫ F.p₁ k').op
          (Multiequalizer.ι (F.multicospanIndex P) i' y) := by
        --P.map (W.f k ≫ pullback.fst (E.f i) (F.f j)).op
        --  (Multiequalizer.ι (E.multicospanIndex P) i x) =
        --P.map (W.f k ≫ pullback.snd (E.f i) (F.f j)).op
        --  (Multiequalizer.ι (F.multicospanIndex P) j y) := by
  let W := G.pullback₁ (pullback.fst (E.p₁ k ≫ E.f i) (F.p₁ k' ≫ F.f i') ≫ E.p₁ k ≫ E.f i)
  refine ⟨W, fun l ↦ ?_⟩
  calc
    _ = ((diagramMap P J
          (pullback.fst (E.p₁ k ≫ E.f i) (F.p₁ k' ≫ F.f i') ≫ E.p₁ k ≫ E.f i)).app (op G) ≫
          Multiequalizer.ι _ l) ((diagram P J S).map f.op x) := ?_
    _ = ((diagramMap P J
          (pullback.fst (E.p₁ k ≫ E.f i) (F.p₁ k' ≫ F.f i') ≫ E.p₁ k ≫ E.f i)).app (op G) ≫
          Multiequalizer.ι _ l) ((diagram P J S).map g.op y) := by rw [h]
    _ = _ := ?_
  · rw [diagramMap_app_ι]
    rw [← ConcreteCategory.comp_apply]
    rw [diagram_map_ι_assoc]
    erw [← ConcreteCategory.comp_apply]
    congr 2
    dsimp only
    rw [← Functor.map_comp, ← op_comp]
    --have : pullback.snd
    --    (pullback.fst (E.p₁ k ≫ E.f i) (F.p₁ k' ≫ F.f i') ≫ E.p₁ k ≫ E.f i) (G.f l) ≫
    --    f.op.unop.h₀ l = _ ≫ E.p₁ _ :=
    --  sorry
    sorry
  · sorry
#exit
  --let W := G.pullback₁ (pullback.fst (E.f i) (F.f j) ≫ E.f i)
  --refine ⟨W, fun k ↦ ?_⟩
  --calc
  --  _ = ((diagramMap P J (pullback.fst (E.f i) (F.f j) ≫ E.f i)).app (op G) ≫ Multiequalizer.ι _ k)
  --        ((diagram P J S).map f.op x) := ?_
  --  _ = ((diagramMap P J (pullback.fst (E.f i) (F.f j) ≫ E.f i)).app (op G) ≫ Multiequalizer.ι _ k)
  --        ((diagram P J S).map g.op y) := by rw [h]
  --  _ = _ := ?_
  --· rw [diagramMap_app_ι]
  --  rw [← ConcreteCategory.comp_apply]
  --  rw [diagram_map_ι_assoc]
  --  erw [← ConcreteCategory.comp_apply]
  --  congr 2
  --  dsimp only
  --  rw [← Functor.map_comp, ← op_comp]
  --  sorry
  --· sorry

lemma something (E F : OneHypercover.{w} J S) (x : E.Meq P) (y : F.Meq P)
    (heq : colimit.ι (diagram P J _) _ ((E.equivMeq _).symm x) =
      colimit.ι (diagram P J _) _ ((F.equivMeq _).symm y))
    (i : E.I₀) (j : F.I₀) :
    ∃ (W : OneHypercover.{w} J (Limits.pullback (E.f i) (F.f j))), ∀ (k : W.I₀),
      P.map (W.f k ≫ pullback.fst (E.f i) (F.f j)).op (x.obj i) =
        P.map (W.f k ≫ pullback.snd (E.f i) (F.f j)).op (y.obj j) := by
  -- this is false but we can fix it
  have _ : IsFiltered (J.OneHypercover S)ᵒᵖ := sorry
  obtain ⟨⟨V⟩, ⟨v₁ : V ⟶ E⟩, ⟨v₂ : V ⟶ F⟩, hv⟩ := Concrete.colimit_exists_of_rep_eq _ _ _ heq
  -- have := congr((V.equivMeq _) $hv)
  -- rw [OneHypercover.Meq.ext_iff, funext_iff] at this
  refine ⟨V.pullback₁ (pullback.fst _ _ ≫ E.f i), fun k ↦ ?_⟩
  --convert this k
  simp
  let t := ConcreteCategory.hom <|
    ((diagramMap P J (pullback.fst (E.f i) (F.f j) ≫ E.f i)).app (op V) ≫ Multiequalizer.ι _ k)
  dsimp at t
  have := congr(t $hv)
  --rw [OneHypercover.Meq.ext_iff, funext_iff] at this
  --convert this k
  --simp [t]
  simp only [t] at this
  erw [← ConcreteCategory.comp_apply] at this
  erw [← ConcreteCategory.comp_apply] at this
  rw [diagramMap_app_ι] at this
  rw [diagram_map_ι_assoc] at this
  rw [diagram_map_ι_assoc] at this
  simp at this
  erw [OneHypercover.ι_equivMeq_symm] at this
  erw [OneHypercover.ι_equivMeq_symm] at this
  erw [← ConcreteCategory.comp_apply] at this
  erw [← ConcreteCategory.comp_apply] at this
  rw [← P.map_comp, ← op_comp] at this
  rw [← P.map_comp, ← op_comp] at this
  rw [← v₁.w₀]
  rw [pullback.condition] at this
  -- rw [← v₁.w₀] at this
  --rw [diagramMap_comp] at this
  --simp at this
  --erw [← ConcreteCategory.comp_apply] at this
  --erw [← ConcreteCategory.comp_apply] at this
  --erw [← ConcreteCategory.comp_apply] at this
  --erw [← ConcreteCategory.comp_apply] at this
  --erw [← ConcreteCategory.comp_apply] at this
  --erw [← ConcreteCategory.comp_apply] at this
  sorry

#exit
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

lemma bazarfaasdf'' (x : E.Meq (sheafification P J)) :
    ∃ (R : OneHypercover.{w} J S) (y : R.Meq P),
      E.toMultiequalizer (sheafification P J) (colimit.ι (diagram P J S) ⟨R⟩ ((R.equivMeq _).symm y)) =
        (E.equivMeq _).symm x := by
  have (i : E.I₀) : ∃ (W : OneHypercover.{w} J (E.X i)) (w : W.Meq P),
      x.obj i = colimit.ι (diagram P J (E.X i)) ⟨W⟩ ((W.equivMeq P).symm w) := by
    obtain ⟨W, w, hw⟩ := Concrete.colimit_exists_rep _ (x.obj i)
    use W.1, W.1.equivMeq P w
    simp [← hw]
  choose W w hw using this
  classical
  --have (i j : E.I₀) (a : (W i).I₀) (b : (W j).I₀) (k : E.I₁ i j) :
  --  ∃ (V : OneHypercover.{w} J
  let R₀ : PreZeroHypercover.{w} S :=
    E.toPreZeroHypercover.bind (fun i ↦ (W i).toPreZeroHypercover)
  have (i j : E.I₀) (k : E.I₁ i j) :
      ∃ (V : OneHypercover.{w} J (E.Y k))
        (v₁ : V ⟶ (W i).pullback₁ (E.p₁ k))
        (v₂ : V ⟶ (W j).pullback₁ (E.p₂ k))
        (s₁ : (W i).I₀ → V.I₀)
        (s₂ : (W j).I₀ → V.I₀),
        v₁.s₀ ∘ s₁ = id ∧
        v₂.s₀ ∘ s₂ = id ∧
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
    sorry
    --use V, v₁.unop, v₂.unop, hv
  choose V v₁ v₂ s₁ s₂ hv₁ hv₂ hv using this
  have (i j : R₀.I₀) :
      ∃ (V : OneHypercover.{w} J (Limits.pullback (R₀.f i) (R₀.f j))),
        ∀ (k : V.I₀), P.map (V.f k ≫ pullback.fst _ _).op ((w i.1).obj i.2) =
          P.map (V.f k ≫ pullback.snd _ _).op ((w j.1).obj j.2) := by
    sorry
  let E' : OneHypercover.{w} J S := {
    __ := E.bind₁ (fun {i j} k ↦ (V i j k).1.1)
    mem₀ := sorry
    mem₁ := sorry
  }
  let proj (i j : R₀.I₀) (k : E'.I₁ i.1 j.1) :
      Limits.pullback (R₀.f i) (R₀.f j) ⟶ Limits.pullback (E.f i.1) (E.f j.1) :=
    pullback.lift (pullback.fst _ _ ≫ (W i.1).f i.2) (pullback.snd _ _ ≫ (W j.1).f j.2)
      (by simpa using pullback.condition)
  let 𝒰 : OneHypercover.{w} J S := {
    __ := E'.toPreZeroHypercover.bind (fun i ↦ (W i).toPreZeroHypercover)
    I₁ i j := E'.I₁ i.1 j.1
    Y i j k := Limits.pullback (proj i j k) (E'.toPullback k)
    p₁ {i j} k := pullback.fst _ _ ≫ pullback.fst _ _
    p₂ {i j} k := pullback.fst _ _ ≫ pullback.snd _ _
    w := sorry
    mem₀ := sorry
    mem₁ := sorry
  }
  refine ⟨𝒰, ⟨fun i ↦ (w i.1).obj i.2, ?_⟩, ?_⟩
  · intro i j k
    sorry
  · sorry

#exit

lemma bazarfaasdf' (x : E.Meq (sheafification P J)) :
    ∃ (R : E.Refinement) (y : R.bind.Meq P),
      R.map P ((R.bind.equivMeq _).symm y) = (E.equivMeq _).symm x := by
  have (i : E.I₀) : ∃ (W : OneHypercover.{w} J (E.X i)) (w : W.Meq P),
      x.obj i = colimit.ι (diagram P J (E.X i)) ⟨W⟩ ((W.equivMeq P).symm w) := by
    obtain ⟨W, w, hw⟩ := Concrete.colimit_exists_rep _ (x.obj i)
    use W.1, W.1.equivMeq P w
    simp [← hw]
  choose W w hw using this
  classical
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
  have (i j : E.I₀) (k : E.I₁ i j) : True := by
    have := hv i j k
    erw [← ConcreteCategory.comp_apply] at this
    erw [← ConcreteCategory.comp_apply] at this
    rw [diagramMap_app, diagram_map, PreOneHypercover.Hom.mapMultifork,
      PreOneHypercover.Hom.mapMultiforkOfIsLimit] at this
    sorry
    --erw [← (diagramMap P J (E.p₁ k)).naturality] at this
    --erw [← NatTrans.naturality] at this
  --simp [diagram_map, diagramMap_app] at hv
  let E' : OneHypercover.{w} J S := {
    __ := E.bind₁ (fun {i j} k ↦ (V i j k).1.1)
    mem₀ := sorry
    mem₁ := sorry
  }
  let R₀ : PreZeroHypercover.{w} S :=
    E.toPreZeroHypercover.bind (fun i ↦ (W i).toPreZeroHypercover)
  let 𝒰 : OneHypercover.{w} J S := {
    __ := E.toPreZeroHypercover.bind (fun i ↦ (W i).toPreZeroHypercover)
    I₁ i j := E'.I₁ i.1 j.1
    Y i j k := Limits.pullback (pullback.fst (R₀.f i) (R₀.f j) ≫ R₀.f i) (E'.p₁ k ≫ E'.f _)
    p₁ {i j} k := pullback.fst _ _ ≫ pullback.fst _ _
    p₂ {i j} k := pullback.fst _ _ ≫ pullback.snd _ _
    w := sorry
    mem₀ := sorry
    mem₁ := sorry
  }
  let R : E.Refinement := {
    cover i := (W i).toPreZeroHypercover
    I {i j} k a b := (V i j k).I₀
    Z {i j} k a b l := Limits.pullback
      ((V i j k).f l ≫ E.p₁ _)
      (pullback.fst ((W i).f a ≫ E.f i) ((W j).f b ≫ E.f j) ≫ (W i).f a)
    p {i j} k a b l := pullback.fst _ _ ≫ (V i j k).f l
    q₁ {i j} k a b l := pullback.snd _ _ ≫ pullback.fst _ _
    q₂ {i j} k a b l := pullback.snd _ _ ≫ pullback.snd _ _
    w := sorry
    w_self := sorry
    w₁ := sorry
    w₂ := sorry
    mem₀ := sorry
    mem₁ := sorry
  }
  refine ⟨R, ⟨fun ⟨i, a⟩ ↦ (w i).obj a, ?_⟩, ?_⟩
  · simp
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
