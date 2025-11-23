/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Sites.OneHypercover
import Mathlib.CategoryTheory.Quotient

/-!

-/

universe w'' w' w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] {A : Type*} [Category A]

@[simp]
lemma Sieve.ofArrows_pUnit {X Y : C} (f : X ⟶ Y) :
    Sieve.ofArrows _ (fun _ : PUnit ↦ f) = Sieve.generate (Presieve.singleton f) := by
  rw [Sieve.ofArrows, Presieve.ofArrows_pUnit]

namespace PreZeroHypercover

variable {S : C} (E : PreZeroHypercover.{w} S) (F : PreZeroHypercover.{w'} S)
  [∀ (i : E.I₀) (j : F.I₀), HasPullback (E.f i) (F.f j)]

/-- First projection from the intersection of two pre-`0`-hypercovers. -/
@[simps]
noncomputable
def interFst : Hom (inter E F) E where
  s₀ i := i.1
  h₀ _ := pullback.fst _ _

/-- Second projection from the intersection of two pre-`0`-hypercovers. -/
@[simps]
noncomputable
def interSnd : Hom (inter E F) F where
  s₀ i := i.2
  h₀ _ := pullback.snd _ _
  w₀ i := by simp [← pullback.condition]

variable {E F} in
/-- Universal property of the intersection of two pre-`0`-hypercovers. -/
@[simps]
noncomputable
def interLift {G : PreZeroHypercover.{w''} S} (f : G.Hom E) (g : G.Hom F) :
    G.Hom (E.inter F) where
  s₀ i := ⟨f.s₀ i, g.s₀ i⟩
  h₀ i := pullback.lift (f.h₀ i) (g.h₀ i) (by simp)

end PreZeroHypercover

namespace PreOneHypercover

variable {S : C}

attribute [local grind =] Category.assoc Category.id_comp

variable {S : C} {E F G : PreOneHypercover S}

section

/-- Intersection of two pre-`1`-hypercovers. -/
@[simps toPreZeroHypercover I₁ Y p₁ p₂]
noncomputable
def inter (E F : PreOneHypercover S) [∀ i j, HasPullback (E.f i) (F.f j)]
    [∀ (i j : E.I₀) (k : E.I₁ i j) (a b : F.I₀) (l : F.I₁ a b),
      HasPullback (E.p₁ k ≫ E.f i) (F.p₁ l ≫ F.f a)] :
    PreOneHypercover S where
  __ := E.toPreZeroHypercover.inter F.toPreZeroHypercover
  I₁ i j := E.I₁ i.1 j.1 × F.I₁ i.2 j.2
  Y i j k := pullback (E.p₁ k.1 ≫ E.f _) (F.p₁ k.2 ≫ F.f _)
  p₁ i j k := pullback.map _ _ _ _ (E.p₁ _) (F.p₁ _) (𝟙 S) (by simp) (by simp)
  p₂ i j k := pullback.map _ _ _ _ (E.p₂ _) (F.p₂ _) (𝟙 S) (by simp [E.w]) (by simp [F.w])
  w := by simp [E.w]

variable (E F : PreOneHypercover S) [∀ i j, HasPullback (E.f i) (F.f j)]
  [∀ (i j : E.I₀) (k : E.I₁ i j) (a b : F.I₀) (l : F.I₁ a b),
    HasPullback (E.p₁ k ≫ E.f i) (F.p₁ l ≫ F.f a)]

lemma sieve₁_inter [HasPullbacks C] {i j : E.I₀ × F.I₀} {W : C}
    (p₁ : W ⟶ pullback (E.f i.1) (F.f i.2))
    (p₂ : W ⟶ pullback (E.f j.1) (F.f j.2))
    (w : p₁ ≫ pullback.fst _ _ ≫ E.f _ = p₂ ≫ pullback.fst _ _ ≫ E.f _) :
    (inter E F).sieve₁ p₁ p₂ = Sieve.bind
      (E.sieve₁ (p₁ ≫ pullback.fst _ _) (p₂ ≫ pullback.fst _ _))
      (fun _ f _ ↦ (F.sieve₁ (p₁ ≫ pullback.snd _ _) (p₂ ≫ pullback.snd _ _)).pullback f) := by
  ext Y f
  let p : W ⟶ pullback ((inter E F).f i) ((inter E F).f j) :=
    pullback.lift p₁ p₂ w
  refine ⟨fun ⟨k, a, h₁, h₂⟩ ↦ ?_, fun ⟨Z, a, b, ⟨k, e, h₁, h₂⟩, ⟨l, u, u₁, u₂⟩, hab⟩ ↦ ?_⟩
  · refine ⟨pullback p ((E.inter F).toPullback k), pullback.lift f a ?_,
        pullback.fst _ _, ?_, ?_, ?_⟩
    · apply pullback.hom_ext
      · apply pullback.hom_ext <;> simp [p, h₁, toPullback]
      · apply pullback.hom_ext <;> simp [p, h₂, toPullback]
    · refine ⟨k.1, pullback.snd _ _ ≫ pullback.fst _ _, ?_, ?_⟩
      · have : p₁ ≫ pullback.fst (E.f i.1) (F.f i.2) = p ≫ pullback.fst _ _ ≫ pullback.fst _ _ := by
          simp [p]
        simp [this, pullback.condition_assoc, toPullback]
      · have : p₂ ≫ pullback.fst (E.f j.1) (F.f j.2) = p ≫ pullback.snd _ _ ≫ pullback.fst _ _ := by
          simp [p]
        simp [this, pullback.condition_assoc, toPullback]
    · exact ⟨k.2, a ≫ pullback.snd _ _, by simp [reassoc_of% h₁], by simp [reassoc_of% h₂]⟩
    · simp
  · subst hab
    refine ⟨(k, l), pullback.lift (a ≫ e) u ?_, ?_, ?_⟩
    · simp only [Category.assoc] at u₁
      simp [← reassoc_of% h₁, w, ← reassoc_of% u₁, ← pullback.condition]
    · apply pullback.hom_ext
      · simp [h₁]
      · simpa using u₁
    · apply pullback.hom_ext
      · simp [h₂]
      · simpa using u₂

/-- First projection from the intersection of two pre-`1`-hypercovers. -/
@[simps toHom s₁]
noncomputable
def interFst : (E.inter F).Hom E where
  __ := E.toPreZeroHypercover.interFst F.toPreZeroHypercover
  s₁ {i j} k := k.1
  h₁ _ := pullback.fst _ _

/-- Second projection from the intersection of two pre-`1`-hypercovers. -/
@[simps toHom s₁]
noncomputable
def interSnd : (E.inter F).Hom F where
  __ := E.toPreZeroHypercover.interSnd F.toPreZeroHypercover
  s₁ {i j} k := k.2
  h₁ _ := pullback.snd _ _

/-- Universal property of the intersection of two pre-`1`-hypercovers. -/
noncomputable
def interLift {G : PreOneHypercover.{w''} S} (f : G.Hom E) (g : G.Hom F) :
    G.Hom (E.inter F) where
  __ := PreZeroHypercover.interLift f.toHom g.toHom
  s₁ {i j} k := ⟨f.s₁ k, g.s₁ k⟩
  h₁ k := pullback.lift (f.h₁ k) (g.h₁ k) <| by
    rw [f.w₁₁_assoc k, g.w₁₁_assoc k]
    simp
  w₀ := by simp
  w₁₁ k := by
    apply pullback.hom_ext
    · simpa using f.w₁₁ k
    · simpa using g.w₁₁ k
  w₁₂ k := by
    apply pullback.hom_ext
    · simpa using f.w₁₂ k
    · simpa using g.w₁₂ k

end

/-- If `g` and `g'` are homotopic, also `f ≫ g` and `f ≫ g'` are homotopic. -/
@[simps]
def Homotopy.whiskerLeft (f : E.Hom F) (g g' : F.Hom G) (h : Homotopy g g') :
    Homotopy (f.comp g) (f.comp g') where
  H i := h.H (f.s₀ i)
  a i := f.h₀ i ≫ h.a (f.s₀ i)
  wl i := by simp
  wr i := by simp

/-- If `f` and `f'` are homotopic, also `f ≫ g` and `f' ≫ g` are homotopic. -/
def Homotopy.whiskerRight (f f' : E.Hom F) (g : F.Hom G) (h : Homotopy f f') :
    Homotopy (f.comp g) (f'.comp g) where
  H i := g.s₁ (h.H i)
  a i := h.a i ≫ g.h₁ _
  wl i := by simp [Hom.w₁₁]
  wr i := by simp [Hom.w₁₂]

/-- The trivial pre-`1`-hypercover of `S` where a single component `S`. -/
@[simps toPreZeroHypercover I₁ Y p₁ p₂]
def trivial (S : C) : PreOneHypercover.{w} S where
  __ := PreZeroHypercover.singleton (𝟙 S)
  I₁ _ _ := PUnit
  Y _ _ _ := S
  p₁ _ _ _ := 𝟙 _
  p₂ _ _ _ := 𝟙 _
  w _ _ _ := by simp

lemma sieve₀_trivial (S : C) : (trivial S).sieve₀ = ⊤ := by
  rw [PreZeroHypercover.sieve₀, Sieve.ofArrows, ← PreZeroHypercover.presieve₀]
  simp

@[simp]
lemma sieve₁_trivial {S : C} {W : C} {p : W ⟶ S} :
    (trivial S).sieve₁ (i₁ := ⟨⟩) (i₂ := ⟨⟩) p p = ⊤ := by ext; simp

instance : Nonempty (PreOneHypercover.{w} S) := ⟨trivial S⟩

end PreOneHypercover

namespace GrothendieckTopology

open Limits
variable (J : GrothendieckTopology C)

namespace OneHypercover

variable {S : C}

/-- The trivial `1`-hypercover of `S` where a single component `S`. -/
@[simps toPreOneHypercover]
def trivial (S : C) : OneHypercover.{w} J S where
  __ := PreOneHypercover.trivial S
  mem₀ := by simp only [PreOneHypercover.sieve₀_trivial, J.top_mem]
  mem₁ _ _ _ _ _ h := by
    simp only [PreOneHypercover.trivial_toPreZeroHypercover, PreZeroHypercover.singleton_X,
      PreZeroHypercover.singleton_f, Category.comp_id] at h
    subst h
    simp

instance : Nonempty (J.OneHypercover S) := ⟨trivial J S⟩

/-- Forget the `1`-components of a `OneHypercover`. -/
@[simps toPreZeroHypercover]
def toZeroHypercover (E : OneHypercover.{w} J S) : J.toPrecoverage.ZeroHypercover S where
  __ := E.toPreZeroHypercover
  mem₀ := E.mem₀

variable {J} in
/-- Intersection of two `1`-hypercovers. -/
@[simps toPreOneHypercover]
noncomputable
def inter [HasPullbacks C] (E F : J.OneHypercover S)
    [∀ (i : E.I₀) (j : F.I₀), HasPullback (E.f i) (F.f j)]
    [∀ (i j : E.I₀) (k : E.I₁ i j) (a b : F.I₀) (l : F.I₁ a b),
      HasPullback (E.p₁ k ≫ E.f i) (F.p₁ l ≫ F.f a)] : J.OneHypercover S where
  __ := E.toPreOneHypercover.inter F.toPreOneHypercover
  mem₀ := (E.toZeroHypercover.inter F.toZeroHypercover).mem₀
  mem₁ i₁ i₂ W p₁ p₂ h := by
    rw [PreOneHypercover.sieve₁_inter _ _ _ _ h]
    refine J.bind_covering (E.mem₁ _ _ _ _ (by simpa using h)) fun _ _ _ ↦ ?_
    exact J.pullback_stable _
      (F.mem₁ _ _ _ _ (by simpa [Category.assoc, ← pullback.condition]))

variable (S) in
/--
Two refinement morphisms of `1`-hypercovers are homotopic if there exists a homotopy between
them.
Note: This is not an equivalence relation, it is not even reflexive!
-/
def homotopicRel : HomRel (J.OneHypercover S) :=
  fun _ _ f g ↦ Nonempty (PreOneHypercover.Homotopy f g)

end OneHypercover

open PreOneHypercover OneHypercover

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
instance [HasPullbacks C] : IsCofiltered (J.HOneHypercover S) where
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
