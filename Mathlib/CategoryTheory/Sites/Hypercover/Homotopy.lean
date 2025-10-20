/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Quotient
import Mathlib.CategoryTheory.Sites.Hypercover.One
import Mathlib.CategoryTheory.Filtered.Basic

/-!
# The category of `1`-hypercovers up to homotopy

In this file we define the category of `1`-hypercovers up to homotopy. This is the category of
`1`-hypercovers, but where morphisms are considered up to existence of a homotopy.

## Main definitions

- `CategoryTheory.PreOneHypercover.Homotopy`: A homotopy of refinements `E ⟶ F` is a family of
  morphisms `Xᵢ ⟶ Yₐ` where `Yₐ` is a component of the cover of `X_{f(i)} ×[S] X_{g(i)}`.
- `CategoryTheory.GrothendieckTopology.HOneHypercover`: The category of `1`-hypercovers
  with respect to a Grothendieck topology and morphisms up to homotopy.

## Main results

- `CategoryTheory.GrothendieckTopology.HOneHypercover.isCofiltered_of_hasPullbacks`: The
  category of `1`-hypercovers up to homotopy is cofiltered if `C` has pullbacks.
-/

universe w'' w' w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

namespace PreOneHypercover

variable {S : C} {E : PreOneHypercover.{w} S} {F : PreOneHypercover.{w'} S}

/-- A homotopy of refinements `E ⟶ F` is a family of morphisms `Xᵢ ⟶ Yₐ` where
`Yₐ` is a component of the cover of `X_{f(i)} ×[S] X_{g(i)}`. -/
structure Homotopy (f g : E.Hom F) where
  /-- The index map sending `i : E.I₀` to `a` above `(f(i), g(i))`. -/
  H (i : E.I₀) : F.I₁ (f.s₀ i) (g.s₀ i)
  /-- The morphism `Xᵢ ⟶ Yₐ`. -/
  a (i : E.I₀) : E.X i ⟶ F.Y (H i)
  wl (i : E.I₀) : a i ≫ F.p₁ (H i) = f.h₀ i
  wr (i : E.I₀) : a i ≫ F.p₂ (H i) = g.h₀ i

attribute [reassoc (attr := simp)] Homotopy.wl Homotopy.wr

/-- Homotopic refinements induce the same map on multiequalizers. -/
lemma Homotopy.mapMultiforkOfIsLimit_eq {A : Type*} [Category A]
    {E F : PreOneHypercover.{w} S} {f g : E.Hom F} (H : Homotopy f g)
    (P : Cᵒᵖ ⥤ A) {c : Multifork (E.multicospanIndex P)} (hc : IsLimit c)
    (d : Multifork (F.multicospanIndex P)) :
    f.mapMultiforkOfIsLimit P hc d = g.mapMultiforkOfIsLimit P hc d := by
  refine Multifork.IsLimit.hom_ext hc fun a ↦ ?_
  have heq := d.condition ⟨⟨(f.s₀ a), (g.s₀ a)⟩, H.H a⟩
  simp only [multicospanIndex_right, multicospanShape_fst, multicospanIndex_left,
    multicospanIndex_fst, multicospanShape_snd, multicospanIndex_snd] at heq
  simp [-Homotopy.wl, -Homotopy.wr, ← H.wl, ← H.wr, reassoc_of% heq]

variable [Limits.HasPullbacks C] (f g : E.Hom F)

/-- (Implementation): The covering object of `cylinder f g`. -/
noncomputable
abbrev cylinderX {i : E.I₀} (k : F.I₁ (f.s₀ i) (g.s₀ i)) : C :=
  pullback (pullback.lift (f.h₀ i) (g.h₀ i) (by simp)) (F.toPullback k)

/-- (Implementation): The structure morphisms of the covering objects of `cylinder f g`. -/
noncomputable
abbrev cylinderf {i : E.I₀} (k : F.I₁ (f.s₀ i) (g.s₀ i)) : cylinderX f g k ⟶ S :=
  pullback.fst _ _ ≫ E.f _

/-- Given two refinement morphisms `f, g : E ⟶ F`, this is a (pre-)`1`-hypercover `W` that
admits a morphism `h : W ⟶ E` such that `h ≫ f` and `h ≫ g` are homotopic. Hence
they become equal after quotienting out by homotopy.
This is a `1`-hypercover, if `E` and `F` are (see `OneHypercover.cylinder`). -/
@[simps]
noncomputable def cylinder (f g : E.Hom F) : PreOneHypercover.{max w w'} S where
  I₀ := Σ (i : E.I₀), F.I₁ (f.s₀ i) (g.s₀ i)
  X p := cylinderX f g p.2
  f p := cylinderf f g p.2
  I₁ p q := ULift.{max w w'} (E.I₁ p.1 q.1)
  Y {p q} k :=
    pullback
      (pullback.map (cylinderf f g p.2)
        (cylinderf f g q.2) _ _ (pullback.fst _ _) (pullback.fst _ _) (𝟙 S) (by simp)
        (by simp))
      (pullback.lift _ _ (E.w k.down))
  p₁ {p q} k := pullback.fst _ _ ≫ pullback.fst _ _
  p₂ {p q} k := pullback.fst _ _ ≫ pullback.snd _ _
  w {_ _} k := by simp [pullback.condition]

lemma toPullback_cylinder {i j : (cylinder f g).I₀} (k : (cylinder f g).I₁ i j) :
    (cylinder f g).toPullback k = pullback.fst _ _ := by
  apply pullback.hom_ext <;> simp [toPullback]

lemma sieve₀_cylinder :
    (cylinder f g).sieve₀ =
      Sieve.generate
        (Presieve.bindOfArrows _ E.f <| fun i ↦
          (Sieve.pullback (pullback.lift (f.h₀ _) (g.h₀ _) (by simp))
            (F.sieve₁' _ _)).arrows) := by
  refine le_antisymm ?_ ?_
  · rw [PreZeroHypercover.sieve₀, Sieve.generate_le_iff]
    rintro - - ⟨i⟩
    refine ⟨_, 𝟙 _, (cylinder f g).f _, ⟨_, _, ?_⟩, by simp⟩
    simp only [Sieve.pullback_apply, pullback.condition]
    exact Sieve.downward_closed _ (Sieve.ofArrows_mk _ _ _) _
  · rw [Sieve.generate_le_iff, PreZeroHypercover.sieve₀]
    rintro Z u ⟨i, v, ⟨W, o, o', ⟨j⟩, hoo'⟩⟩
    exact ⟨_, pullback.lift v o hoo'.symm, (cylinder f g).f ⟨i, j⟩, Presieve.ofArrows.mk _,
      by simp⟩

lemma sieve₁'_cylinder (i j : Σ (i : E.I₀), F.I₁ (f.s₀ i) (g.s₀ i)) :
    (cylinder f g).sieve₁' i j =
      Sieve.pullback
        (pullback.map _ _ _ _ (pullback.fst _ _) (pullback.fst _ _) (𝟙 S) (by simp) (by simp))
        (E.sieve₁' i.1 j.1) := by
  refine le_antisymm ?_ ?_
  · rw [sieve₁', Sieve.ofArrows, Sieve.generate_le_iff]
    rintro - - ⟨k⟩
    refine ⟨E.Y k.down, pullback.snd _ _, E.toPullback k.down, Presieve.ofArrows.mk k.down, ?_⟩
    simp only [cylinder_Y, cylinder_f, toPullback_cylinder, pullback.condition]
  · rw [sieve₁', Sieve.ofArrows, ← Sieve.pullbackArrows_comm, Sieve.generate_le_iff]
    rintro Z u ⟨W, v, ⟨k⟩⟩
    simp_rw [← pullbackSymmetry_inv_comp_fst]
    apply (((cylinder f g).sieve₁' i j)).downward_closed
    rw [sieve₁']
    convert Sieve.ofArrows_mk _ _ (ULift.up k)
    simp [toPullback_cylinder f g ⟨k⟩]

/-- (Implementation): The refinement morphism `cylinder f g ⟶ E`. -/
@[simps]
noncomputable def cylinderHom : (cylinder f g).Hom E where
  s₀ p := p.1
  s₁ k := k.down
  h₀ p := pullback.fst _ _
  h₁ {p q} k := pullback.snd _ _
  w₁₁ k := by
    have : E.p₁ k.down = pullback.lift _ _ (E.w k.down) ≫ pullback.fst _ _ := by simp
    nth_rw 2 [this]
    rw [← pullback.condition_assoc]
    simp
  w₁₂ {p q} k := by
    have : E.p₂ k.down = pullback.lift _ _ (E.w k.down) ≫ pullback.snd _ _ := by simp
    nth_rw 2 [this]
    rw [← pullback.condition_assoc]
    simp
  w₀ := by simp

/-- (Implementation): The homotopy of the morphisms `cylinder f g ⟶ E ⟶ F`. -/
noncomputable def cylinderHomotopy :
    Homotopy ((cylinderHom f g).comp f) ((cylinderHom f g).comp g) where
  H p := p.2
  a p := pullback.snd _ _
  wl p := by
    have : F.p₁ p.snd = pullback.lift _ _ (F.w p.2) ≫ pullback.fst _ _ := by simp
    nth_rw 1 [this]
    rw [← pullback.condition_assoc]
    simp
  wr p := by
    have : g.h₀ p.fst = pullback.lift (f.h₀ p.fst) (g.h₀ p.fst) (by simp) ≫
        pullback.snd (F.f _) (F.f _) := by simp
    dsimp only [cylinder_X, Hom.comp_s₀, cylinder_I₀, Function.comp_apply, cylinderHom_s₀,
      Hom.comp_h₀, cylinderHom_h₀]
    nth_rw 3 [this]
    rw [pullback.condition_assoc]
    simp

/-- Up to homotopy, the category of (pre-)`1`-hypercovers is cofiltered. -/
lemma exists_nonempty_homotopy (f g : E.Hom F) :
    ∃ (W : PreOneHypercover.{max w w'} S) (h : W.Hom E),
      Nonempty (Homotopy (h.comp f) (h.comp g)) :=
  ⟨cylinder f g, PreOneHypercover.cylinderHom f g, ⟨cylinderHomotopy f g⟩⟩

end PreOneHypercover

namespace GrothendieckTopology

open PreOneHypercover OneHypercover

variable {J : GrothendieckTopology C}

namespace OneHypercover

variable {S : C} {E : OneHypercover.{w} J S} {F : OneHypercover.{w'} J S}
variable [HasPullbacks C]

/-- Given two refinement morphism `f, g : E ⟶ F`, this is a `1`-hypercover `W` that
admits a morphism `h : W ⟶ E` such that `h ≫ f` and `h ≫ g` are homotopic. Hence
they become equal after quotienting out by homotopy. -/
@[simps! toPreOneHypercover]
noncomputable def cylinder (f g : E.Hom F) : J.OneHypercover S :=
  mk' (PreOneHypercover.cylinder f g)
    (by
      rw [PreOneHypercover.sieve₀_cylinder]
      refine J.bindOfArrows E.mem₀ fun i ↦ ?_
      rw [Sieve.generate_sieve]
      exact J.pullback_stable _ (mem_sieve₁' F _ _))
    (fun i j ↦ by
      rw [PreOneHypercover.sieve₁'_cylinder]
      exact J.pullback_stable _ (mem_sieve₁' E _ _))

/-- Up to homotopy, the category of `1`-hypercovers is cofiltered. -/
lemma exists_nonempty_homotopy (f g : E.Hom F) :
    ∃ (W : OneHypercover.{max w w'} J S) (h : W.Hom E),
      Nonempty (PreOneHypercover.Homotopy (h.comp f) (h.comp g)) :=
  ⟨cylinder f g, PreOneHypercover.cylinderHom f g, ⟨PreOneHypercover.cylinderHomotopy f g⟩⟩

end OneHypercover

variable (J S)

/--
Two refinement morphisms of `1`-hypercovers are homotopic if there exists a homotopy between
them.
Note: This is not an equivalence relation, it is not even reflexive!
-/
def OneHypercover.homotopicRel : HomRel (J.OneHypercover S) :=
  fun _ _ f g ↦ Nonempty (PreOneHypercover.Homotopy f g)

/-- The category of `1`-hypercovers with refinement morphisms up to homotopy. -/
abbrev HOneHypercover (S : C) := Quotient (OneHypercover.homotopicRel J S)

/-- The canonical projection from `1`-hypercovers to `1`-hypercovers up to homotopy. -/
abbrev OneHypercover.toHOneHypercover (S : C) : J.OneHypercover S ⥤ J.HOneHypercover S :=
  Quotient.functor _

lemma _root_.CategoryTheory.PreOneHypercover.Homotopy.map_eq_map {S : C} {E F : J.OneHypercover S}
    {f g : E ⟶ F} (H : Homotopy f g) :
    (toHOneHypercover J S).map f = (toHOneHypercover J S).map g :=
  Quotient.sound _ ⟨H⟩

namespace HOneHypercover

variable {S : C}

instance : Nonempty (J.HOneHypercover S) := ⟨⟨Nonempty.some inferInstance⟩⟩

/-- If `C` has pullbacks, the category of `1`-hypercovers up to homotopy is cofiltered. -/
instance isCofiltered_of_hasPullbacks [HasPullbacks C] : IsCofiltered (J.HOneHypercover S) where
  cone_objs {E F} :=
    ⟨⟨E.1.inter F.1⟩, Quot.mk _ (PreOneHypercover.interFst _ _),
      Quot.mk _ (PreOneHypercover.interSnd _ _), ⟨⟩⟩
  cone_maps {X Y} f g := by
    obtain ⟨(f : X.1 ⟶ Y.1), rfl⟩ := (toHOneHypercover J S).map_surjective f
    obtain ⟨(g : X.1 ⟶ Y.1), rfl⟩ := (toHOneHypercover J S).map_surjective g
    obtain ⟨W, h, ⟨H⟩⟩ := OneHypercover.exists_nonempty_homotopy f g
    use (toHOneHypercover J S).obj W, (toHOneHypercover J S).map h
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact H.map_eq_map

end HOneHypercover

end GrothendieckTopology

end CategoryTheory
