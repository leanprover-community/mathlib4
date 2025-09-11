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

variable {FA : A → A → Type*} {CA : A → Type*} [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]
variable [ConcreteCategory A FA]
variable [(forget A).ReflectsIsomorphisms]

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

@[reassoc]
lemma PreOneHypercover.multiequalizer_condition
    (E : PreOneHypercover.{w} S) [HasMultiequalizer (E.multicospanIndex P)]
    {i j : E.I₀} (k : E.I₁ i j) :
    Multiequalizer.ι (E.multicospanIndex P) i ≫ P.map (E.p₁ k).op =
      Multiequalizer.ι (E.multicospanIndex P) j ≫ P.map (E.p₂ k).op :=
  Multiequalizer.condition (E.multicospanIndex P) ⟨(i, j), k⟩

namespace GrothendieckTopology.OneHypercover

local notation3 "H⁰(" E ", " P ")" =>
  multiequalizer (PreOneHypercover.multicospanIndex (OneHypercover.toPreOneHypercover E) P)

noncomputable
def pullbackMultiequalizer [HasPullbacks C] {X Y : C} (f : X ⟶ Y) (E : OneHypercover.{w} J Y)
    [HasMultiequalizer (E.multicospanIndex P)]
    [HasMultiequalizer ((pullback₁ f E).multicospanIndex P)] :
    H⁰(E, P) ⟶ H⁰(E.pullback₁ f, P) :=
  Multiequalizer.lift _ _ (fun (i : E.I₀) ↦
      Multiequalizer.ι (E.multicospanIndex P) i ≫ P.map (pullback.snd _ _).op) <| fun i ↦ by
    simp only [pullback₁_toPreOneHypercover, PreOneHypercover.multicospanIndex_right,
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

@[reassoc (attr := simp)]
lemma pullbackMultiequalizer_ι [HasPullbacks C] {X Y : C} (f : X ⟶ Y) (E : OneHypercover.{w} J Y)
    [HasMultiequalizer (E.multicospanIndex P)]
    [HasMultiequalizer ((pullback₁ f E).multicospanIndex P)] (i) :
    pullbackMultiequalizer P J f E ≫ Multiequalizer.ι _ i =
      Multiequalizer.ι (E.multicospanIndex P) i ≫ P.map (pullback.snd _ _).op := by
  simp [pullbackMultiequalizer]

variable [∀ (S : C) (E : OneHypercover.{w} J S), HasMultiequalizer (E.multicospanIndex P)]

lemma exists_zeroHypercover_of_mapMultifork_eq [HasPullbacks C] (E F G : OneHypercover.{w} J S)
    [HasMultiequalizer (E.multicospanIndex P)]
    [HasMultiequalizer (F.multicospanIndex P)]
    [HasMultiequalizer (G.multicospanIndex P)]
    (f : G ⟶ E) (g : G ⟶ F)
    (x : CA H⁰(E, P)) (y : CA H⁰(F, P))
    (h : f.mapMultifork P x = g.mapMultifork P y)
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
    _ = (pullbackMultiequalizer P J (pullback.fst (E.f i) (F.f j) ≫ E.f i) G ≫
          Multiequalizer.ι _ l.1 ≫ P.map pW'.op) (f.mapMultifork P x) := ?_
    _ = (pullbackMultiequalizer P J (pullback.fst (E.f i) (F.f j) ≫ E.f i) G ≫
          Multiequalizer.ι _ l.1 ≫ P.map pW'.op) (g.mapMultifork P y) := by rw [h]
  · rw [pullbackMultiequalizer_ι_assoc]
    rw [← ConcreteCategory.comp_apply]
    erw [← ConcreteCategory.comp_apply]
    rw [PreOneHypercover.Hom.mapMultifork_ι_assoc]
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
        f.h₀ l.fst = pullback.fst _ _ ≫ pullback.snd _ _ ≫ E.p₂ l.2.1 := by
      simp only [PreOneHypercover.cover₀_X, PreOneHypercover.cover₀_f,
        limit.lift_π_assoc, PullbackCone.mk_pt, cospan_right, PullbackCone.mk_π_app, Category.assoc,
        pW']
      congr 1
      rw [← pullback.condition]
      rw [pullback.condition_assoc]
      simp
    simp_rw [Category.assoc, hl, hr, op_comp, Functor.map_comp, Category.assoc]
    rw [PreOneHypercover.multiequalizer_condition_assoc]
  · rw [pullbackMultiequalizer_ι_assoc]
    rw [← ConcreteCategory.comp_apply]
    erw [← ConcreteCategory.comp_apply]
    rw [PreOneHypercover.Hom.mapMultifork_ι_assoc]
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
        pW' ≫ pullback.snd (pullback.fst (E.f i) (F.f j) ≫ E.f i) (G.f l.fst) ≫ g.h₀ l.fst =
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

end CategoryTheory.GrothendieckTopology.OneHypercover
