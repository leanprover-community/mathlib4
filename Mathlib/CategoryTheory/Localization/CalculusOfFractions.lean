/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.Opposite

/-!
# Calculus of fractions

Following the definitions by [Gabriel and Zisman][gabriel-zisman-1967],
given a morphism property `W : MorphismProperty C` on a category `C`,
we introduce the class `W.HasLeftCalculusOfFractions`. The main
result (TODO) is that if `L : C ⥤ D` is a localization functor for `W`,
then for any morphism `L.obj X ⟶ L.obj Y` in `D`, there exists an auxiliary
object `Y' : C` and morphisms `g : X ⟶ Y'` and `s : Y ⟶ Y'`, with `W s`, such
that the given morphism is a sort of fraction `g / s`, or more precisely of
the form `L.map g ≫ (Localization.isoOfHom L W s hs).inv`.

## References

* [P. Gabriel, M. Zisman, *Calculus of fractions and homotopy theory*][gabriel-zisman-1967]

-/

namespace CategoryTheory

open Category

namespace MorphismProperty

variable {C D : Type _} [Category C] [Category D]

/-- A left fraction from `X : C` to `Y : C` for `W : MorphismProperty C` consists of the
datum of an object `Y' : C` and maps `f : X ⟶ Y'` and `s : Y ⟶ Y'` such that `W s`. -/
structure LeftFraction (W : MorphismProperty C) (X Y : C) where
  /-- the auxiliary object of a left fraction -/
  {Y' : C}
  /-- the numerator of a left fraction -/
  f : X ⟶ Y'
  /-- the denominator of a left fraction -/
  s : Y ⟶ Y'
  /-- the condition that the denominator belongs to the given morphism property -/
  hs : W s

namespace LeftFraction

variable (W : MorphismProperty C) {X Y : C}

/-- The left fraction from `X` to `Y` given by a morphism `f : X ⟶ Y`. -/
@[simps]
def ofHom (f : X ⟶ Y) [W.ContainsIdentities] :
    W.LeftFraction X Y := mk f (𝟙 Y) (W.id_mem Y)

variable {W}

/-- The left fraction from `X` to `Y` given by a morphism `s : Y ⟶ X` such that `W s`. -/
@[simps]
def ofInv (s : Y ⟶ X) (hs : W s) :
    W.LeftFraction X Y := mk (𝟙 X) s hs

/-- If `φ : W.LeftFraction X Y` and `L` is a functor which inverts `W`, this is the
induced morphism `L.obj X ⟶ L.obj Y`  -/
noncomputable def map (φ : W.LeftFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) :
    L.obj X ⟶ L.obj Y :=
  have := hL _ φ.hs
  L.map φ.f ≫ inv (L.map φ.s)

@[reassoc (attr := simp)]
lemma map_comp_map_s (φ : W.LeftFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) :
    φ.map L hL ≫ L.map φ.s = L.map φ.f := by
  letI := hL _ φ.hs
  simp [map]

variable (W)

lemma map_ofHom (f : X ⟶ Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) [W.ContainsIdentities] :
    (ofHom W f).map L hL = L.map f := by
  simp [map]

@[reassoc (attr := simp)]
lemma map_ofInv_hom_id (s : Y ⟶ X) (hs : W s) (L : C ⥤ D) (hL : W.IsInvertedBy L) :
    (ofInv s hs).map L hL ≫ L.map s = 𝟙 _ := by
  letI := hL _ hs
  simp [map]

@[reassoc (attr := simp)]
lemma map_hom_ofInv_id (s : Y ⟶ X) (hs : W s) (L : C ⥤ D) (hL : W.IsInvertedBy L) :
    L.map s ≫ (ofInv s hs).map L hL = 𝟙 _ := by
  letI := hL _ hs
  simp [map]

variable {W}

lemma cases (α : W.LeftFraction X Y) :
    ∃ (Y' : C) (f : X ⟶ Y') (s : Y ⟶ Y') (hs : W s), α = LeftFraction.mk f s hs :=
  ⟨_, _, _, _, rfl⟩

end LeftFraction

/-- A right fraction from `X : C` to `Y : C` for `W : MorphismProperty C` consists of the
datum of an object `X' : C` and maps `s : X' ⟶ X` and `f : X' ⟶ Y` such that `W s`. -/
structure RightFraction (W : MorphismProperty C) (X Y : C) where
  /-- the auxiliary object of a right fraction -/
  {X' : C}
  /-- the denominator of a right fraction -/
  s : X' ⟶ X
  /-- the condition that the denominator belongs to the given morphism property -/
  hs : W s
  /-- the numerator of a right fraction -/
  f : X' ⟶ Y

namespace RightFraction

variable (W : MorphismProperty C)

variable {X Y : C}

/-- The right fraction from `X` to `Y` given by a morphism `f : X ⟶ Y`. -/
@[simps]
def ofHom (f : X ⟶ Y) [W.ContainsIdentities] :
    W.RightFraction X Y := mk (𝟙 X) (W.id_mem X) f

variable {W}

/-- The right fraction from `X` to `Y` given by a morphism `s : Y ⟶ X` such that `W s`. -/
@[simps]
def ofInv (s : Y ⟶ X) (hs : W s) :
    W.RightFraction X Y := mk s hs (𝟙 Y)

/-- If `φ : W.RightFraction X Y` and `L` is a functor which inverts `W`, this is the
induced morphism `L.obj X ⟶ L.obj Y`  -/
noncomputable def map (φ : W.RightFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) :
    L.obj X ⟶ L.obj Y :=
  have := hL _ φ.hs
  inv (L.map φ.s) ≫ L.map φ.f

@[reassoc (attr := simp)]
lemma map_s_comp_map (φ : W.RightFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) :
    L.map φ.s ≫ φ.map L hL = L.map φ.f := by
  letI := hL _ φ.hs
  simp [map]

variable (W)

@[simp]
lemma map_ofHom (f : X ⟶ Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) [W.ContainsIdentities] :
    (ofHom W f).map L hL = L.map f := by
  simp [map]

@[reassoc (attr := simp)]
lemma map_ofInv_hom_id (s : Y ⟶ X) (hs : W s) (L : C ⥤ D) (hL : W.IsInvertedBy L) :
    (ofInv s hs).map L hL ≫ L.map s = 𝟙 _ := by
  letI := hL _ hs
  simp [map]

@[reassoc (attr := simp)]
lemma map_hom_ofInv_id (s : Y ⟶ X) (hs : W s) (L : C ⥤ D) (hL : W.IsInvertedBy L) :
    L.map s ≫ (ofInv s hs).map L hL = 𝟙 _ := by
  letI := hL _ hs
  simp [map]

variable {W}

lemma cases (α : W.RightFraction X Y) :
    ∃ (X' : C) (s : X' ⟶ X) (hs : W s) (f : X' ⟶ Y) , α = RightFraction.mk s hs f :=
  ⟨_, _, _, _, rfl⟩

end RightFraction

variable (W : MorphismProperty C)

/-- A multiplicative morphism property `W` has left calculus of fractions if
any right fraction can be turned into a left fraction and that two morphisms
that can be equalized by precomposition with a morphism in `W` can also
be equalized by postcomposition with a morphism in `W`. -/
class HasLeftCalculusOfFractions extends W.IsMultiplicative : Prop where
  exists_leftFraction ⦃X Y : C⦄ (φ : W.RightFraction X Y) :
    ∃ (ψ : W.LeftFraction X Y), φ.f ≫ ψ.s = φ.s ≫ ψ.f
  ext : ∀ ⦃X' X Y : C⦄ (f₁ f₂ : X ⟶ Y) (s : X' ⟶ X) (_ : W s)
    (_ : s ≫ f₁ = s ≫ f₂), ∃ (Y' : C) (t : Y ⟶ Y') (_ : W t), f₁ ≫ t = f₂ ≫ t

/-- A multiplicative morphism property `W` has right calculus of fractions if
any left fraction can be turned into a right fraction and that two morphisms
that can be equalized by postcomposition with a morphism in `W` can also
be equalized by precomposition with a morphism in `W`. -/
class HasRightCalculusOfFractions extends W.IsMultiplicative : Prop where
  exists_rightFraction ⦃X Y : C⦄ (φ : W.LeftFraction X Y) :
    ∃ (ψ : W.RightFraction X Y), ψ.s ≫ φ.f = ψ.f ≫ φ.s
  ext : ∀ ⦃X Y Y' : C⦄ (f₁ f₂ : X ⟶ Y) (s : Y ⟶ Y') (_ : W s)
    (_ : f₁ ≫ s = f₂ ≫ s), ∃ (X' : C) (t : X' ⟶ X) (_ : W t), t ≫ f₁ = t ≫ f₂

variable {W}

lemma RightFraction.exists_leftFraction [W.HasLeftCalculusOfFractions] {X Y : C}
    (φ : W.RightFraction X Y) : ∃ (ψ : W.LeftFraction X Y), φ.f ≫ ψ.s = φ.s ≫ ψ.f :=
  HasLeftCalculusOfFractions.exists_leftFraction φ

/-- A choice of a left fraction deduced from a right fraction for a morphism property `W`
when `W` has left calculus of fractions. -/
noncomputable def RightFraction.leftFraction [W.HasLeftCalculusOfFractions] {X Y : C}
    (φ : W.RightFraction X Y) : W.LeftFraction X Y :=
  φ.exists_leftFraction.choose

@[reassoc]
lemma RightFraction.leftFraction_fac [W.HasLeftCalculusOfFractions] {X Y : C}
    (φ : W.RightFraction X Y) : φ.f ≫ φ.leftFraction.s = φ.s ≫ φ.leftFraction.f :=
  φ.exists_leftFraction.choose_spec

lemma LeftFraction.exists_rightFraction [W.HasRightCalculusOfFractions] {X Y : C}
    (φ : W.LeftFraction X Y) : ∃ (ψ : W.RightFraction X Y), ψ.s ≫ φ.f = ψ.f ≫ φ.s :=
  HasRightCalculusOfFractions.exists_rightFraction φ

/-- A choice of a right fraction deduced from a left fraction for a morphism property `W`
when `W` has right calculus of fractions. -/
noncomputable def LeftFraction.rightFraction [W.HasRightCalculusOfFractions] {X Y : C}
    (φ : W.LeftFraction X Y) : W.RightFraction X Y :=
  φ.exists_rightFraction.choose

@[reassoc]
lemma LeftFraction.rightFraction_fac [W.HasRightCalculusOfFractions] {X Y : C}
    (φ : W.LeftFraction X Y) : φ.rightFraction.s ≫ φ.f = φ.rightFraction.f ≫ φ.s :=
  φ.exists_rightFraction.choose_spec

/-- The equivalence relation on left fractions for a morphism property `W`. -/
def LeftFractionRel {X Y : C} (z₁ z₂ : W.LeftFraction X Y) : Prop :=
  ∃ (Z : C)  (t₁ : z₁.Y' ⟶ Z) (t₂ : z₂.Y' ⟶ Z) (_ : z₁.s ≫ t₁ = z₂.s ≫ t₂)
    (_ : z₁.f ≫ t₁ = z₂.f ≫ t₂), W (z₁.s ≫ t₁)

namespace LeftFractionRel

lemma refl {X Y : C} (z : W.LeftFraction X Y) : LeftFractionRel z z :=
  ⟨z.Y', 𝟙 _, 𝟙 _, rfl, rfl, by simpa only [Category.comp_id] using z.hs⟩

lemma symm {X Y : C} {z₁ z₂ : W.LeftFraction X Y} (h : LeftFractionRel z₁ z₂) :
    LeftFractionRel z₂ z₁ := by
  obtain ⟨Z, t₁, t₂, hst, hft, ht⟩ := h
  exact ⟨Z, t₂, t₁, hst.symm, hft.symm, by simpa only [← hst] using ht⟩

lemma trans {X Y : C} {z₁ z₂ z₃ : W.LeftFraction X Y}
    [HasLeftCalculusOfFractions W]
    (h₁₂ : LeftFractionRel z₁ z₂) (h₂₃ : LeftFractionRel z₂ z₃) :
    LeftFractionRel z₁ z₃ := by
  obtain ⟨Z₄, t₁, t₂, hst, hft, ht⟩ := h₁₂
  obtain ⟨Z₅, u₂, u₃, hsu, hfu, hu⟩ := h₂₃
  obtain ⟨⟨v₄, v₅, hv₅⟩, fac⟩ := HasLeftCalculusOfFractions.exists_leftFraction
    (RightFraction.mk (z₁.s ≫ t₁) ht (z₃.s ≫ u₃))
  simp only [Category.assoc] at fac
  have eq : z₂.s ≫ u₂ ≫ v₅  = z₂.s ≫ t₂ ≫ v₄ := by
    simpa only [← reassoc_of% hsu, reassoc_of% hst] using fac
  obtain ⟨Z₇, w, hw, fac'⟩ := HasLeftCalculusOfFractions.ext _ _ _ z₂.hs eq
  simp only [Category.assoc] at fac'
  refine' ⟨Z₇, t₁ ≫ v₄ ≫ w, u₃ ≫ v₅ ≫ w, _, _, _⟩
  · rw [reassoc_of% fac]
  · rw [reassoc_of% hft, ← fac', reassoc_of% hfu]
  · rw [← reassoc_of% fac, ← reassoc_of% hsu, ← Category.assoc]
    exact W.comp_mem _ _ hu (W.comp_mem _ _ hv₅ hw)

end LeftFractionRel

section

variable [W.HasLeftCalculusOfFractions] (W)

lemma equivalenceLeftFractionRel (X Y : C) :
    @_root_.Equivalence (W.LeftFraction X Y) LeftFractionRel where
  refl := LeftFractionRel.refl
  symm := LeftFractionRel.symm
  trans := LeftFractionRel.trans

variable {W}

namespace LeftFraction

open HasLeftCalculusOfFractions

/-- Auxiliary definition for the composition of left fractions. -/
@[simp]
def comp₀ {X Y Z : C} (z₁ : W.LeftFraction X Y) (z₂ : W.LeftFraction Y Z)
    (z₃ : W.LeftFraction z₁.Y' z₂.Y') :
    W.LeftFraction X Z :=
  mk (z₁.f ≫ z₃.f) (z₂.s ≫ z₃.s) (W.comp_mem _ _ z₂.hs z₃.hs)

/-- The equivalence class of `z₁.comp₀ z₂ z₃` does not depend on the choice of `z₃` provided
they satisfy the compatibility `z₂.f ≫ z₃.s = z₁.s ≫ z₃.f`. -/
lemma comp₀_rel {X Y Z : C} (z₁ : W.LeftFraction X Y) (z₂ : W.LeftFraction Y Z)
    (z₃ z₃' : W.LeftFraction z₁.Y' z₂.Y') (h₃ : z₂.f ≫ z₃.s = z₁.s ≫ z₃.f)
    (h₃' : z₂.f ≫ z₃'.s = z₁.s ≫ z₃'.f) :
    LeftFractionRel (z₁.comp₀ z₂ z₃) (z₁.comp₀ z₂ z₃') := by
  obtain ⟨z₄, fac⟩ := exists_leftFraction (RightFraction.mk z₃.s z₃.hs z₃'.s)
  dsimp at fac
  have eq : z₁.s ≫ z₃.f ≫ z₄.f = z₁.s ≫ z₃'.f ≫ z₄.s := by
    rw [← reassoc_of% h₃, ← reassoc_of% h₃', fac]
  obtain ⟨Y, t, ht, fac'⟩ := ext _ _ _ z₁.hs eq
  simp only [assoc] at fac'
  refine' ⟨Y, z₄.f ≫ t, z₄.s ≫ t, _, _, _⟩
  · simp only [comp₀, assoc, reassoc_of% fac]
  · simp only [comp₀, assoc, fac']
  · simp only [comp₀, assoc, ← reassoc_of% fac]
    exact W.comp_mem _ _ z₂.hs (W.comp_mem _ _ z₃'.hs (W.comp_mem _ _ z₄.hs ht))

variable (W)

/-- The morphisms in the constructed localized category for a morphism property `W`
that has left calculus of fractions are equivalence classes of left fractions. -/
def Localization.Hom (X Y : C) :=
  Quot (LeftFractionRel : W.LeftFraction X Y → W.LeftFraction X Y → Prop)

variable {W}

/-- The morphism in the constructed localized category that is induced by a left fraction. -/
def Localization.Hom.mk {X Y : C} (z : W.LeftFraction X Y) : Localization.Hom W X Y :=
  Quot.mk _ z

lemma Localization.Hom.mk_surjective {X Y : C} (f : Localization.Hom W X Y) :
    ∃ (z : W.LeftFraction X Y), f = mk z := by
  obtain ⟨z⟩ := f
  exact ⟨z, rfl⟩

/-- Auxiliary definition towards the definition of the composition of morphisms
in the constructed localized category for a morphism property that has
left calculus of fractions. -/
noncomputable def comp {X Y Z : C} (z₁ : W.LeftFraction X Y) (z₂ : W.LeftFraction Y Z) :
    Localization.Hom W X Z :=
  Localization.Hom.mk (z₁.comp₀ z₂ (RightFraction.mk z₁.s z₁.hs z₂.f).leftFraction)

lemma comp_eq {X Y Z : C} (z₁ : W.LeftFraction X Y) (z₂ : W.LeftFraction Y Z)
    (z₃ : W.LeftFraction z₁.Y' z₂.Y') (h₃ : z₂.f ≫ z₃.s = z₁.s ≫ z₃.f) :
    z₁.comp z₂ = Localization.Hom.mk (z₁.comp₀ z₂ z₃) :=
  Quot.sound (LeftFraction.comp₀_rel _ _ _ _
    (RightFraction.leftFraction_fac (RightFraction.mk z₁.s z₁.hs z₂.f)) h₃)

namespace Localization

/-- Composition of morphisms in the constructed localized category
for a morphism property that has left calculus of fractions. -/
noncomputable def Hom.comp {X Y Z : C} (z₁ : Hom W X Y) (z₂ : Hom W Y Z) : Hom W X Z := by
  refine' Quot.lift₂ (fun a b => a.comp b) _ _ z₁ z₂
  · rintro a b₁ b₂ ⟨U, t₁, t₂, hst, hft, ht⟩
    obtain ⟨z₁, fac₁⟩ := exists_leftFraction (RightFraction.mk a.s a.hs b₁.f)
    obtain ⟨z₂, fac₂⟩ := exists_leftFraction (RightFraction.mk a.s a.hs b₂.f)
    obtain ⟨w₁, fac₁'⟩ := exists_leftFraction (RightFraction.mk z₁.s z₁.hs t₁)
    obtain ⟨w₂, fac₂'⟩ := exists_leftFraction (RightFraction.mk z₂.s z₂.hs t₂)
    obtain ⟨u, fac₃⟩ := exists_leftFraction (RightFraction.mk w₁.s w₁.hs w₂.s)
    dsimp at fac₁ fac₂ fac₁' fac₂' fac₃ ⊢
    have eq : a.s ≫ z₁.f ≫ w₁.f ≫ u.f = a.s ≫ z₂.f ≫ w₂.f ≫ u.s := by
      rw [← reassoc_of% fac₁, ← reassoc_of% fac₂, ← reassoc_of% fac₁', ← reassoc_of% fac₂',
        reassoc_of% hft, fac₃]
    obtain ⟨Z, p, hp, fac₄⟩ := ext _ _ _ a.hs eq
    simp only [assoc] at fac₄
    rw [comp_eq _ _ z₁ fac₁, comp_eq _ _ z₂ fac₂]
    apply Quot.sound
    refine' ⟨Z, w₁.f ≫ u.f ≫ p, w₂.f ≫ u.s ≫ p, _, _, _⟩
    · dsimp
      simp only [assoc, ← reassoc_of% fac₁', ← reassoc_of% fac₂',
        reassoc_of% hst, reassoc_of% fac₃]
    · dsimp
      simp only [assoc, fac₄]
    · dsimp
      simp only [assoc]
      rw [← reassoc_of% fac₁', ← reassoc_of% fac₃, ← assoc]
      exact W.comp_mem _ _ ht (W.comp_mem _ _ w₂.hs (W.comp_mem _ _ u.hs hp))
  · rintro a₁ a₂ b ⟨U, t₁, t₂, hst, hft, ht⟩
    obtain ⟨z₁, fac₁⟩ := exists_leftFraction (RightFraction.mk a₁.s a₁.hs b.f)
    obtain ⟨z₂, fac₂⟩ := exists_leftFraction (RightFraction.mk a₂.s a₂.hs b.f)
    obtain ⟨w₁, fac₁'⟩ := exists_leftFraction (RightFraction.mk (a₁.s ≫ t₁) ht (b.f ≫ z₁.s))
    obtain ⟨w₂, fac₂'⟩ := exists_leftFraction (RightFraction.mk (a₂.s ≫ t₂)
      (show W _ by rw [← hst]; exact ht) (b.f ≫ z₂.s))
    let p₁ : W.LeftFraction X Z := LeftFraction.mk (a₁.f ≫ t₁ ≫ w₁.f) (b.s ≫ z₁.s ≫ w₁.s)
      (W.comp_mem _ _ b.hs (W.comp_mem _ _ z₁.hs w₁.hs))
    let p₂ : W.LeftFraction X Z := LeftFraction.mk (a₂.f ≫ t₂ ≫ w₂.f) (b.s ≫ z₂.s ≫ w₂.s)
      (W.comp_mem _ _ b.hs (W.comp_mem _ _ z₂.hs w₂.hs))
    dsimp at fac₁ fac₂ fac₁' fac₂' ⊢
    simp only [assoc] at fac₁' fac₂'
    rw [comp_eq _ _ z₁ fac₁, comp_eq _ _ z₂ fac₂]
    apply Quot.sound
    refine' LeftFractionRel.trans _ ((_ : LeftFractionRel p₁ p₂).trans _)
    · have eq : a₁.s ≫ z₁.f ≫ w₁.s = a₁.s ≫ t₁ ≫ w₁.f := by rw [← fac₁', reassoc_of% fac₁]
      obtain ⟨Z, u, hu, fac₃⟩ := ext _ _ _ a₁.hs eq
      simp only [assoc] at fac₃
      refine' ⟨Z, w₁.s ≫ u, u, _, _, _⟩
      · dsimp
        simp only [assoc]
      · dsimp
        simp only [assoc, fac₃]
      · dsimp
        simp only [assoc]
        exact W.comp_mem _ _ b.hs (W.comp_mem _ _ z₁.hs (W.comp_mem _ _ w₁.hs hu))
    · obtain ⟨q, fac₃⟩ := exists_leftFraction (RightFraction.mk (z₁.s ≫ w₁.s)
        (W.comp_mem _ _ z₁.hs w₁.hs) (z₂.s ≫ w₂.s))
      dsimp at fac₃
      simp only [assoc] at fac₃
      have eq : a₁.s ≫ t₁ ≫ w₁.f ≫ q.f = a₁.s ≫ t₁ ≫ w₂.f ≫ q.s := by
        rw [← reassoc_of% fac₁', ← fac₃, reassoc_of% hst, reassoc_of% fac₂']
      obtain ⟨Z, u, hu, fac₄⟩ := ext _ _ _ a₁.hs eq
      simp only [assoc] at fac₄
      refine' ⟨Z, q.f ≫ u, q.s ≫ u, _, _, _⟩
      · simp only [assoc, reassoc_of% fac₃]
      · rw [assoc, assoc, assoc, assoc, fac₄, reassoc_of% hft]
      · simp only [assoc, ← reassoc_of% fac₃]
        exact W.comp_mem _ _ b.hs (W.comp_mem _ _ z₂.hs
          (W.comp_mem _ _ w₂.hs (W.comp_mem _ _ q.hs hu)))
    · have eq : a₂.s ≫ z₂.f ≫ w₂.s = a₂.s ≫ t₂ ≫ w₂.f := by
        rw [← fac₂', reassoc_of% fac₂]
      obtain ⟨Z, u, hu, fac₄⟩ := ext _ _ _ a₂.hs eq
      simp only [assoc] at fac₄
      refine' ⟨Z, u, w₂.s ≫ u, _, _, _⟩
      · dsimp
        simp only [assoc]
      · dsimp
        simp only [assoc, fac₄]
      · dsimp
        simp only [assoc]
        exact W.comp_mem _ _ b.hs (W.comp_mem _ _ z₂.hs (W.comp_mem _ _ w₂.hs hu))

lemma Hom.comp_eq {X Y Z : C} (z₁ : W.LeftFraction X Y) (z₂ : W.LeftFraction Y Z) :
    Hom.comp (mk z₁) (mk z₂) = z₁.comp z₂ := rfl

end Localization

/-- The constructed localized category for a morphism property
that has left calculus of fractions. -/
@[nolint unusedArguments]
def Localization (_ : MorphismProperty C) := C

namespace Localization

noncomputable instance : Category (Localization W) where
  Hom X Y := Localization.Hom W X Y
  id X := Localization.Hom.mk (ofHom W (𝟙 _))
  comp f g := f.comp g
  comp_id := by
    rintro (X Y : C) f
    obtain ⟨z, rfl⟩ := Hom.mk_surjective f
    change (Hom.mk z).comp (Hom.mk (ofHom W (𝟙 Y))) = Hom.mk z
    rw [Hom.comp_eq, comp_eq z (ofHom W (𝟙 Y)) (ofInv z.s z.hs) (by simp)]
    dsimp [comp₀]
    simp only [comp_id, id_comp]
  id_comp := by
    rintro (X Y : C) f
    obtain ⟨z, rfl⟩ := Hom.mk_surjective f
    change (Hom.mk (ofHom W (𝟙 X))).comp (Hom.mk z) = Hom.mk z
    rw [Hom.comp_eq, comp_eq (ofHom W (𝟙 X)) z (ofHom W z.f) (by simp)]
    dsimp
    simp only [comp₀, id_comp, comp_id]
  assoc := by
    rintro (X₁ X₂ X₃ X₄ : C) f₁ f₂ f₃
    obtain ⟨z₁, rfl⟩ := Hom.mk_surjective f₁
    obtain ⟨z₂, rfl⟩ := Hom.mk_surjective f₂
    obtain ⟨z₃, rfl⟩ := Hom.mk_surjective f₃
    change ((Hom.mk z₁).comp (Hom.mk z₂)).comp (Hom.mk z₃) =
      (Hom.mk z₁).comp ((Hom.mk z₂).comp (Hom.mk z₃))
    rw [Hom.comp_eq z₁ z₂, Hom.comp_eq z₂ z₃]
    obtain ⟨z₁₂, fac₁₂⟩ := exists_leftFraction (RightFraction.mk z₁.s z₁.hs z₂.f)
    obtain ⟨z₂₃, fac₂₃⟩ := exists_leftFraction (RightFraction.mk z₂.s z₂.hs z₃.f)
    obtain ⟨z', fac⟩ := exists_leftFraction (RightFraction.mk z₁₂.s z₁₂.hs z₂₃.f)
    dsimp at fac₁₂ fac₂₃ fac
    rw [comp_eq z₁ z₂ z₁₂ fac₁₂, comp_eq z₂ z₃ z₂₃ fac₂₃, comp₀, comp₀,
      Hom.comp_eq, Hom.comp_eq,
      comp_eq _ z₃ (mk z'.f (z₂₃.s ≫ z'.s) (W.comp_mem _ _ z₂₃.hs z'.hs))
        (by dsimp; rw [assoc, reassoc_of% fac₂₃, fac]),
      comp_eq z₁ _ (mk (z₁₂.f ≫ z'.f) z'.s z'.hs)
        (by dsimp; rw [assoc, ← reassoc_of% fac₁₂, fac])]
    simp

variable (W)

/-- The localization functor to the constructed localized category for a morphism property
that has left calculus of fractions. -/
@[simps obj]
def Q : C ⥤ Localization W where
  obj X := X
  map f := Hom.mk (ofHom W f)
  map_id _ := rfl
  map_comp {X Y Z} f g := by
    change _ = Hom.comp _ _
    rw [Hom.comp_eq, comp_eq (ofHom W f) (ofHom W g) (ofHom W g) (by simp)]
    simp only [ofHom, comp₀, comp_id]

end Localization

end LeftFraction

end

end MorphismProperty

end CategoryTheory
