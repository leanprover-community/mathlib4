/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Sites.OneHypercover
import Mathlib.CategoryTheory.Sites.Hypercover.Refinement
import Mathlib.CategoryTheory.Sites.IsSheafOneHypercover
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc

/-!

-/

universe w' w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] {A : Type*} [Category A]
variable (P : Cᵒᵖ ⥤ A) (J : GrothendieckTopology C)
variable {S : C}

namespace PreOneHypercover

@[reassoc (attr := simp)]
lemma toMultiequalizer_ι (E : PreOneHypercover.{w} S) [HasMultiequalizer (E.multicospanIndex P)]
    (i : E.I₀) :
    E.toMultiequalizer P ≫ Multiequalizer.ι _ i = P.map (E.f i).op := by
  simp [toMultiequalizer, multifork]

end PreOneHypercover

namespace GrothendieckTopology

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

@[simp]
lemma diagramMap_ι_apply {X Y : C} (f : X ⟶ Y) (E : OneHypercover.{w} J Y)
    (k : E.I₀) (x : CA H⁰(E, P)) :
    Multiequalizer.ι ((E.pullback₁ f).multicospanIndex P) k
      ((diagramMap P J f).app ⟨E⟩ x) =
      P.map (pullback.snd _ _).op (Multiequalizer.ι (E.multicospanIndex P) _ x) := by
  erw [← ConcreteCategory.comp_apply, diagramMap_app_ι]
  simp
  rfl

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

lemma OneHypercover.exists_zeroHypercover_of_ι_eq (E F : OneHypercover.{w} J S)
    (x : CA H⁰(E, P)) (y : CA H⁰(F, P))
    (heq : colimit.ι (diagram P J _) _ x = colimit.ι (diagram P J _) _ y)
    (i : E.I₀) (j : F.I₀) :
    ∃ (W : Precoverage.ZeroHypercover.{w} J.toPrecoverage
        (Limits.pullback (E.f i) (F.f j))), ∀ (k : W.I₀),
      P.map (W.f k ≫ pullback.fst (E.f i) (F.f j)).op
          (Multiequalizer.ι (E.multicospanIndex P) i x) =
        P.map (W.f k ≫ pullback.snd (E.f i) (F.f j)).op
          (Multiequalizer.ι (F.multicospanIndex P) j y) := by
  -- this is false but we can fix it
  have _ : IsFiltered (J.OneHypercover S)ᵒᵖ := sorry
  obtain ⟨⟨V⟩, ⟨v₁ : V ⟶ E⟩, ⟨v₂ : V ⟶ F⟩, hv⟩ := Concrete.colimit_exists_of_rep_eq _ _ _ heq
  exact OneHypercover.exists_zeroHypercover_of_mapMultifork_eq
    P J E F V v₁ v₂ x y hv (i := i) (j := j)

lemma OneHypercover.exists_zeroHypercover_of_ι_eq' (E F : OneHypercover.{w} J S) (x : E.Meq P)
    (y : F.Meq P)
    (heq : colimit.ι (diagram P J _) _ ((E.equivMeq _).symm x) =
      colimit.ι (diagram P J _) _ ((F.equivMeq _).symm y))
    (i : E.I₀) (j : F.I₀) :
    ∃ (W : Precoverage.ZeroHypercover.{w} J.toPrecoverage
        (Limits.pullback (E.f i) (F.f j))), ∀ (k : W.I₀),
      P.map (W.f k ≫ pullback.fst (E.f i) (F.f j)).op (x.obj i) =
        P.map (W.f k ≫ pullback.snd (E.f i) (F.f j)).op (y.obj j) := by
  -- this is false but we can fix it
  have _ : IsFiltered (J.OneHypercover S)ᵒᵖ := sorry
  obtain ⟨⟨V⟩, ⟨v₁ : V ⟶ E⟩, ⟨v₂ : V ⟶ F⟩, hv⟩ := Concrete.colimit_exists_of_rep_eq _ _ _ heq
  obtain ⟨W, hW⟩ := OneHypercover.exists_zeroHypercover_of_mapMultifork_eq
    P J E F V v₁ v₂ ((E.equivMeq _).symm x) ((F.equivMeq _).symm y) hv (i := i) (j := j)
  refine ⟨W, ?_⟩
  intro k
  rw [OneHypercover.ι_equivMeq_symm] at hW
  rw [OneHypercover.ι_equivMeq_symm] at hW
  exact hW k

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

variable {E P} in
structure Repr (x : CA H⁰(E, sheafification P J)) where
  W (i : E.I₀) : OneHypercover.{w} J (E.X i)
  w (i : E.I₀) : CA H⁰(W i, P)
  hw (i : E.I₀) :
    Multiequalizer.ι (E.multicospanIndex (sheafification P J)) i x =
      colimit.ι (diagram P J (E.X i)) ⟨W i⟩ (w i)

variable {E P} in
lemma Repr.ι_diagramMap {x : CA H⁰(E, sheafification P J)} (R : Repr x) {i j : E.I₀}
    (k : E.I₁ i j) :
    colimit.ι (diagram P J _) ⟨(R.W i).pullback₁ (E.p₁ k)⟩
        ((diagramMap P J (E.p₁ k)).app (op (R.W i)) (R.w i)) =
    colimit.ι (diagram P J _) ⟨(R.W j).pullback₁ (E.p₂ k)⟩
      ((diagramMap P J (E.p₂ k)).app (op (R.W j)) (R.w j)) :=
  sorry

variable {E P} in
noncomputable
def Repr.coverInter {x : CA H⁰(E, sheafification P J)} (R : Repr x)
    {i j : E.I₀} (k : E.I₁ i j) (a : (R.W i).I₀) (b : (R.W j).I₀) :
    J.toPrecoverage.ZeroHypercover
      (Limits.pullback
        (pullback.fst (E.p₁ k) ((R.W i).f a))
        (pullback.fst (E.p₂ k) ((R.W j).f b))) :=
  (OneHypercover.exists_zeroHypercover_of_ι_eq P _ _ _ _ (R.ι_diagramMap k) a b).choose

variable {E P} in
lemma Repr.coverInter_eq {x : CA H⁰(E, sheafification P J)} (R : Repr x)
    (i j : E.I₀) (k : E.I₁ i j) (a : (R.W i).I₀) (b : (R.W j).I₀)
    (l : (R.coverInter k a b).I₀) :
    P.map ((R.coverInter k a b).f l).op
      ((P.map (pullback.fst
          (pullback.fst (E.p₁ k) ((R.W i).f a)) (pullback.fst (E.p₂ k) ((R.W j).f b))).op)
        (P.map (pullback.snd (E.p₁ k) ((R.W i).f a)).op
          (((Multiequalizer.ι ((R.W i).multicospanIndex P) a)) (R.w i)))) =
    P.map ((R.coverInter k a b).f l).op
      ((P.map (pullback.snd
          (pullback.fst (E.p₁ k) ((R.W i).f a)) (pullback.fst (E.p₂ k) ((R.W j).f b))).op)
        (P.map (pullback.snd (E.p₂ k) ((R.W j).f b)).op
          (((Multiequalizer.ι ((R.W j).multicospanIndex P) b)) (R.w j)))) := by
  have :=
    (OneHypercover.exists_zeroHypercover_of_ι_eq P _ _ _ _ (R.ι_diagramMap k) a b).choose_spec l
  sorry

variable {E P} in
lemma Repr.eq_of_hom {x : CA H⁰(E, sheafification P J)}
    (R : Repr x)
    (V : OneHypercover.{w} J S) (y : CA H⁰(V, P))
    (f : ∀ i, R.W i ⟶ V.pullback₁ (E.f i))
    (hf : ∀ i, (diagram P J (E.X i)).map (f i).op ((diagramMap P J (E.f i)).app ⟨V⟩ y) = R.w i) :
    E.toMultiequalizer (sheafification P J) (colimit.ι (diagram P J S) ⟨V⟩ y) = x := by
  apply Concrete.multiequalizer_ext
  intro (i : E.I₀)
  rw [← ConcreteCategory.comp_apply]
  erw [← ConcreteCategory.comp_apply]
  rw [PreOneHypercover.toMultiequalizer_ι]
  dsimp only [sheafification_map]
  simp
  erw [R.hw i]
  rw [← colimit.w (diagram P J (E.X i)) (f i).op]
  simp only [ConcreteCategory.comp_apply]
  erw [hf i]
  rfl

lemma bazarfaasdf'' (x : CA H⁰(E, sheafification P J)) :
    ∃ (R : OneHypercover.{w} J S) (y : CA H⁰(R, P)),
      E.toMultiequalizer (sheafification P J) (colimit.ι (diagram P J S) ⟨R⟩ y) = x := by
  have (i : E.I₀) : ∃ (W : OneHypercover.{w} J (E.X i)) (w : CA H⁰(W, P)),
      Multiequalizer.ι (E.multicospanIndex (sheafification P J)) i x =
        colimit.ι (diagram P J (E.X i)) ⟨W⟩ w := by
    obtain ⟨W, w, hw⟩ := Concrete.colimit_exists_rep _
      (Multiequalizer.ι (E.multicospanIndex (sheafification P J)) i x)
    use W.1, w
    exact hw.symm
  choose W w hw using this
  let R : Repr x := ⟨W, w, hw⟩
  classical
  let V : OneHypercover.{w} J S := {
    __ := E.toPreZeroHypercover.bind (fun i ↦ (W i).toPreZeroHypercover)
    I₁ a b := Σ (k : E.I₁ a.1 b.1), (R.coverInter k a.2 b.2).I₀
    Y {a b} l := (R.coverInter _ _ _).X l.2
    p₁ {a b} l := (R.coverInter _ _ _).f l.2 ≫ pullback.fst _ _ ≫ pullback.snd _ _
    p₂ {a b} l := (R.coverInter _ _ _).f l.2 ≫ pullback.snd _ _ ≫ pullback.snd _ _
    w := sorry
    mem₀ := sorry
    mem₁ := sorry
  }
  refine ⟨V, (V.equivMeq _).symm
      ⟨fun a ↦ Multiequalizer.ι ((W a.1).multicospanIndex P) a.2 (w a.1), ?_⟩, ?_⟩
  · intro a b c
    simp [V]
    apply Repr.coverInter_eq
  · fapply R.eq_of_hom
    · intro i
      exact {
        s₀ a := ⟨i, a⟩
        h₀ a := pullback.lift ((R.W i).f a) (𝟙 _)
        s₁ {a b} l := sorry
        h₁ := sorry
        w₀ := sorry
        w₁₁ := sorry
        w₁₂ := sorry
      }
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
