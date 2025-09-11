/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Sites.OneHypercover

universe w' w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] {A : Type*} [Category A]

@[simp]
lemma Sieve.ofArrows_pUnit {X Y : C} (f : X ⟶ Y) :
    Sieve.ofArrows _ (fun _ : PUnit ↦ f) = Sieve.generate (Presieve.singleton f) := by
  rw [Sieve.ofArrows, Presieve.ofArrows_pUnit]

namespace PreOneHypercover

variable {S : C}

/-- A refinement data of a pre-`1`-hypercover `{Uᵢ} is a pre-`0`-hypercover for every `Uᵢ`
and coverings of the intersections. -/
structure Refinement (E : PreOneHypercover.{w} S) where
  cover (i : E.I₀) : PreZeroHypercover.{w} (E.X i)
  J {i j : E.I₀} (a : (cover i).I₀) (b : (cover j).I₀) : Type w
  Z {i j : E.I₀} (k : E.I₁ i j) {a : (cover i).I₀} {b : (cover j).I₀} (l : J a b) : C
  p {i j : E.I₀} (k : E.I₁ i j) {a : (cover i).I₀} {b : (cover j).I₀} (l : J a b) :
    Z k l ⟶ E.Y k
  q₁ {i j : E.I₀} (k : E.I₁ i j) {a : (cover i).I₀} {b : (cover j).I₀} (l : J a b) :
    Z k l ⟶ (cover i).X a
  q₂ {i j : E.I₀} (k : E.I₁ i j) {a : (cover i).I₀} {b : (cover j).I₀} (l : J a b) :
    Z k l ⟶ (cover j).X b
  w {i j : E.I₀} (k : E.I₁ i j) {a : (cover i).I₀} {b : (cover j).I₀} (l : J a b) :
    q₁ k l ≫ (cover _).f _ ≫ E.f _ = q₂ k l ≫ (cover _).f _ ≫ E.f _
  w_self {i : E.I₀} (k : E.I₁ i i) {a : (cover i).I₀} {b : (cover i).I₀} (l : J a b) :
    q₁ k l ≫ (cover _).f _ = q₂ k l ≫ (cover _).f _
  w₁ {i j : E.I₀} (k : E.I₁ i j) {a : (cover i).I₀} {b : (cover j).I₀} (l : J a b) :
    p k l ≫ E.p₁ k = q₁ k l ≫ (cover i).f a
  w₂ {i j : E.I₀} (k : E.I₁ i j) {a : (cover i).I₀} {b : (cover j).I₀} (l : J a b) :
    p k l ≫ E.p₂ k = q₂ k l ≫ (cover j).f b

attribute [reassoc (attr := grind _=_)] Refinement.w Refinement.w_self Refinement.w₁ Refinement.w₂

variable {E : PreOneHypercover.{w} S}

@[simps! toPreZeroHypercover I₁ Y p₁ p₂]
def Refinement.cover₁ (R : E.Refinement) (i : E.I₀) : PreOneHypercover.{w} (E.X i) where
  __ := R.cover i
  I₁ a b := E.I₁ i i × R.J a b
  Y _ _ p := R.Z p.1 p.2
  p₁ _ _ _ := R.q₁ _ _
  p₂ _ _ _ := R.q₂ _ _
  w _ _ _ := R.w_self _ _

@[simps!]
def Refinement.bind (R : E.Refinement) : PreOneHypercover.{w} S where
  __ := E.toPreZeroHypercover.bind
    fun i ↦ (R.cover i)
  I₁ i j := E.I₁ i.1 j.1 × R.J i.2 j.2
  Y _ _ p := R.Z p.1 p.2
  p₁ _ _ p := R.q₁ p.1 p.2
  p₂ _ _ p := R.q₂ p.1 p.2
  w _ _ p := R.w p.1 p.2

@[simps]
def Refinement.toBase (R : E.Refinement) : R.bind ⟶ E where
  s₀ i := i.1
  h₀ i := (R.cover i.1).f i.2
  s₁ p := p.1
  h₁ p := R.p p.1 p.2
  w₀ _ := rfl
  w₁₁ _ := R.w₁ _ _
  w₁₂ _ := R.w₂ _ _

attribute [local grind =] Category.assoc Category.id_comp

@[simps]
noncomputable
def Refinement.homPullback₁ [HasPullbacks C] (R : E.Refinement) (i : E.I₀) :
    R.cover₁ i ⟶ R.bind.pullback₁ (E.f i) where
  s₀ a := ⟨i, a⟩
  h₀ a := pullback.lift ((R.cover i).f a) (𝟙 _)
  s₁ := id
  h₁ {a b} p := pullback.lift (R.p _ _ ≫ E.p₁ _) (𝟙 _) <| by simp [w_self_assoc, w₁_assoc]
  w₁₁ {a b} p := by apply pullback.hom_ext <;> simp [w₁, w_self]
  w₁₂ {a b} p := by apply pullback.hom_ext <;> simp [w₁, w_self]

variable {S : C} {E F G : PreOneHypercover S}

section

@[simps]
noncomputable
def cone (E F : PreOneHypercover S) [∀ i j, HasPullback (E.f i) (F.f j)]
    [∀ (i j : E.I₀) (k : E.I₁ i j) (a b : F.I₀) (l : F.I₁ a b),
      HasPullback (E.p₁ k ≫ E.f i) (F.p₁ l ≫ F.f a)] :
    PreOneHypercover S where
  I₀ := E.I₀ × F.I₀
  X i := pullback (E.f i.1) (F.f i.2)
  f i := pullback.fst _ _ ≫ E.f _
  I₁ i j := E.I₁ i.1 j.1 × F.I₁ i.2 j.2
  Y i j k := pullback (E.p₁ k.1 ≫ E.f _) (F.p₁ k.2 ≫ F.f _)
  p₁ i j k := pullback.map _ _ _ _ (E.p₁ _) (F.p₁ _) (𝟙 S) (by simp) (by simp)
  p₂ i j k := pullback.map _ _ _ _ (E.p₂ _) (F.p₂ _) (𝟙 S) (by simp [E.w]) (by simp [F.w])
  w := by simp [E.w]

variable (E F : PreOneHypercover S) [∀ i j, HasPullback (E.f i) (F.f j)]
  [∀ (i j : E.I₀) (k : E.I₁ i j) (a b : F.I₀) (l : F.I₁ a b),
    HasPullback (E.p₁ k ≫ E.f i) (F.p₁ l ≫ F.f a)]

lemma sieve₀_cone :
    (cone E F).sieve₀ = Sieve.bind E.sieve₀ (fun _ f _ ↦ F.sieve₀.pullback f) := by
  ext Z f
  refine ⟨fun ⟨W, a, b, hb, hab⟩ ↦ ?_,
      fun ⟨W, a, b, ⟨U, u, v, hv, huv⟩, ⟨V, c, d, hd, hcd⟩, hab⟩ ↦ ?_⟩
  · obtain ⟨i⟩ := hb
    simp only [Sieve.generate_apply, Sieve.bind_apply]
    refine ⟨(E.cone F).X i, a, (E.cone F).f i, ?_, ?_, hab⟩
    · apply E.sieve₀.downward_closed
      exact Sieve.ofArrows_mk E.X E.f i.1
    · dsimp
      refine ⟨F.X i.2, a ≫ pullback.snd _ _, F.f i.2, ⟨i.2⟩, ?_⟩
      simp [pullback.condition]
  · subst huv
    obtain ⟨i⟩ := hv
    obtain ⟨j⟩ := hd
    exact ⟨(cone E F).X (i, j),
      pullback.lift (a ≫ u) c (by simp [hcd]), (cone E F).f (i, j), ⟨(i, j)⟩, by simpa⟩

lemma sieve₁_cone [HasPullbacks C] {i j : E.I₀ × F.I₀} {W : C}
    (p₁ : W ⟶ pullback (E.f i.1) (F.f i.2))
    (p₂ : W ⟶ pullback (E.f j.1) (F.f j.2))
    (w : p₁ ≫ pullback.fst _ _ ≫ E.f _ = p₂ ≫ pullback.fst _ _ ≫ E.f _) :
    (cone E F).sieve₁ p₁ p₂ = Sieve.bind
      (E.sieve₁ (p₁ ≫ pullback.fst _ _) (p₂ ≫ pullback.fst _ _))
      (fun _ f _ ↦ (F.sieve₁ (p₁ ≫ pullback.snd _ _) (p₂ ≫ pullback.snd _ _)).pullback f) := by
  ext Y f
  let p : W ⟶ pullback ((cone E F).f i) ((cone E F).f j) :=
    pullback.lift p₁ p₂ w
  refine ⟨fun ⟨k, a, h₁, h₂⟩ ↦ ?_, fun ⟨Z, a, b, ⟨k, e, h₁, h₂⟩, ⟨l, u, u₁, u₂⟩, hab⟩ ↦ ?_⟩
  · refine ⟨pullback p ((cone E F).toPullback k), ?_, ?_, ?_, ?_, ?_⟩
    · refine pullback.lift f a ?_
      apply pullback.hom_ext
      · apply pullback.hom_ext <;> simp [p, h₁, toPullback]
      · apply pullback.hom_ext <;> simp [p, h₂, toPullback]
    · exact pullback.fst _ _
    · refine ⟨k.1, pullback.snd _ _ ≫ pullback.fst _ _, ?_, ?_⟩
      · have : p₁ ≫ pullback.fst (E.f i.1) (F.f i.2) = p ≫ pullback.fst _ _ ≫ pullback.fst _ _ := by
          simp [p]
        simp [this, pullback.condition_assoc, toPullback]
      · have : p₂ ≫ pullback.fst (E.f j.1) (F.f j.2) = p ≫ pullback.snd _ _ ≫ pullback.fst _ _ := by
          simp [p]
        simp [this, pullback.condition_assoc, toPullback]
    · refine ⟨k.2, a ≫ pullback.snd _ _, ?_, ?_⟩
      · simp [reassoc_of% h₁]
      · simp [reassoc_of% h₂]
    · simp
  · refine ⟨(k, l), ?_, ?_, ?_⟩
    · apply pullback.lift (a ≫ e) u _
      simp at u₁
      simp [← reassoc_of% h₁, w, ← reassoc_of% u₁]
      congr 2
      sorry
    · sorry
    · sorry

@[simps]
noncomputable
def coneHomLeft : Hom (cone E F) E where
  s₀ i := i.1
  s₁ {i j} k := k.1
  h₀ _ := pullback.fst _ _
  h₁ _ := pullback.fst _ _

@[simps]
noncomputable
def coneHomRight : Hom (cone E F) F where
  s₀ i := i.2
  s₁ {i j} k := k.2
  h₀ _ := pullback.snd _ _
  h₁ _ := pullback.snd _ _
  w₀ i := by simp [← pullback.condition]

end

def Hom.homotopic (f g : E.Hom F) : Prop := Nonempty (Homotopy f g)

@[simps]
def Homotopy.whiskerLeft (f : E.Hom F) (g g' : F.Hom G) (h : Homotopy g g') :
    Homotopy (f.comp g) (f.comp g') where
  H i := h.H (f.s₀ i)
  a i := f.h₀ i ≫ h.a (f.s₀ i)
  wl i := by simp
  wr i := by simp

def Homotopy.whiskerRight (f f' : E.Hom F) (g : F.Hom G) (h : Homotopy f f') :
    Homotopy (f.comp g) (f'.comp g) where
  H i := g.s₁ (h.H i)
  a i := h.a i ≫ g.h₁ _
  wl i := by simp [Hom.w₁₁]
  wr i := by simp [Hom.w₁₂]

end PreOneHypercover

namespace GrothendieckTopology

open Limits
variable (J : GrothendieckTopology C)

structure HOneHypercover (S : C) where
  oneHypercover : J.OneHypercover S

namespace OneHypercover

variable {S : C}

abbrev Hom.homotopic {E F : J.OneHypercover S} (f g : E.Hom F) : Prop :=
  PreOneHypercover.Hom.homotopic f g

instance : Category (J.OneHypercover S) where
  Hom := Hom
  id E := PreOneHypercover.Hom.id E.toPreOneHypercover
  comp f g := f.comp g

instance : Nonempty (J.OneHypercover S) :=
  ⟨{ I₀ := PUnit,
     X _ := S,
     f _ := 𝟙 S,
     I₁ _ _ := PUnit,
     Y _ _ _ := S
     p₁ _ _ _ := 𝟙 S
     p₂ _ _ _ := 𝟙 S
     w _ _ _ := rfl
     mem₀ := by simp [PreZeroHypercover.sieve₀]
     mem₁ _ _ _ _ := by
      simp only [Category.comp_id, PreOneHypercover.sieve₁, exists_eq_left', exists_const,
        forall_eq']
      exact J.top_mem' _
  }⟩

noncomputable
def cone (E F : J.OneHypercover S) [∀ (i : E.I₀) (j : F.I₀), HasPullback (E.f i) (F.f j)]
    [∀ (i j : E.I₀) (k : E.I₁ i j) (a b : F.I₀) (l : F.I₁ a b),
      HasPullback (E.p₁ k ≫ E.f i) (F.p₁ l ≫ F.f a)] : J.OneHypercover S where
  __ := E.toPreOneHypercover.cone F.toPreOneHypercover
  mem₀ := sorry
  mem₁ := sorry

end OneHypercover

namespace HOneHypercover

variable {S : C}

variable (S) in
def Hom (E F : J.HOneHypercover S) : Type _ :=
  Quot (OneHypercover.Hom.homotopic (E := E.oneHypercover) (F := F.oneHypercover))

instance : Category (J.HOneHypercover S) where
  Hom := Hom J S
  id E := Quot.mk _ (𝟙 E.oneHypercover)
  comp {E F G} :=
    Quot.lift₂ (fun f g ↦ Quot.mk _ (f ≫ g : E.oneHypercover ⟶ G.oneHypercover))
      (fun f g g' hgg' ↦ by
        obtain ⟨H⟩ := hgg'
        dsimp
        apply Quot.sound
        constructor
        exact H.whiskerLeft _ _ _)
      (fun f f' g hff' ↦ by
        obtain ⟨H⟩ := hff'
        dsimp
        apply Quot.sound
        constructor
        exact H.whiskerRight _ _ _)
  id_comp f := by
    obtain ⟨f, rfl⟩ := Quot.exists_rep f
    simp
  comp_id f := by
    obtain ⟨f, rfl⟩ := Quot.exists_rep f
    simp
  assoc f g h := by
    obtain ⟨f, rfl⟩ := Quot.exists_rep f
    obtain ⟨g, rfl⟩ := Quot.exists_rep g
    obtain ⟨h, rfl⟩ := Quot.exists_rep h
    simp

instance : Nonempty (J.HOneHypercover S) := ⟨⟨Nonempty.some inferInstance⟩⟩

variable (S) in
def _root_.CategoryTheory.GrothendieckTopology.OneHypercover.toHOneHypercover :
    J.OneHypercover S ⥤ J.HOneHypercover S where
  obj E := ⟨E⟩
  map f := Quot.mk _ f

open OneHypercover

instance : (toHOneHypercover J S).Full where
  map_surjective := Quot.exists_rep

instance [HasPullbacks C] : IsCofiltered (J.HOneHypercover S) where
  cone_objs {E F} :=
    sorry
  cone_maps {X Y} f g := by
    obtain ⟨(f : X.1 ⟶ Y.1), rfl⟩ := (toHOneHypercover J S).map_surjective f
    obtain ⟨(g : X.1 ⟶ Y.1), rfl⟩ := (toHOneHypercover J S).map_surjective g
    obtain ⟨W, h, ⟨H⟩⟩ := OneHypercover.exists_nonempty_homotopy f g
    use (toHOneHypercover J S).obj W, (toHOneHypercover J S).map h
    exact Quot.sound ⟨H⟩

section Sheafification

variable [HasPullbacks C]

noncomputable
def foo (E : J.HOneHypercover S) : HOneHypercover.mk (E.1.pullback₁ (𝟙 S)) ≅ E where
  hom := Quot.mk _ {
    s₀ := id
    h₀ i := pullback.snd _ _
    s₁ := id
    h₁ {i j} k := pullback.snd _ _
    w₀ := by simp [← pullback.condition]
  }
  inv := Quot.mk _ {
    s₀ := id
    h₀ i := pullback.lift (E.1.f i) (𝟙 _)
    s₁ := id
    h₁ {i j} k := pullback.lift (E.1.p₁ k ≫ E.1.f _) (𝟙 _)
    w₁₂ k := by apply pullback.hom_ext <;> simp [E.1.w]
  }
  hom_inv_id := by
    apply Quot.sound
    constructor
    refine ⟨fun (i : E.1.I₀) ↦ ?_, ?_, ?_, ?_⟩
    · simp
      change E.1.I₁ i i
      sorry
    · sorry
    · sorry
    · sorry
  inv_hom_id := sorry

noncomputable
def pullback {T : C} (f : S ⟶ T) : J.HOneHypercover T ⥤ J.HOneHypercover S where
  obj E := ⟨E.1.pullback₁ f⟩
  map {E F} := Quot.map (fun g ↦ g.pullback₁ f) fun u v ⟨H⟩ ↦ ⟨H.pullback₁ f⟩
  map_id E := by
    apply Quot.sound
    simp
    constructor
    refine ⟨fun (i : E.1.I₀) ↦ ?_, ?_, ?_, ?_⟩
    · simp
      change E.1.I₁ i i
      sorry
    · sorry
    · sorry
    · sorry
  map_comp := sorry

end Sheafification

end HOneHypercover

end GrothendieckTopology

end CategoryTheory
