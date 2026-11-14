/-
Copyright (c) 2026 Edward van de Meent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edward van de Meent
-/
module
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# Pullback squares in cartesian monoidal categories.

We show that various pullback squares result from other pullback squares or equalizers, in
the setting of a category with chosen finite products, i.e. where we have
`[CartesianMonoidalCategory C]`.

## Main results
In a `[CartesianMonoidalCategory C]`,

- `IsPullback.fst_snd_toUnit_toUnit` shows that the product is the pullback of morphisms into the
  terminal object.
- `IsPullback.whiskerRight_horiz` shows a concrete pullback square for
  the pullback along the left projection.
- `IsPullback.whiskerLeft_horiz` shows a concrete pullback square for
  the pullback along the right projection.
- `IsPullback.tensor` shows that given two pullback squares, the pointwise product is a pullback.
- `IsPullback.comp_lift_diag_tensorHom` shows that given a pullback `W` of morphisms
  `f : X ⟶ Z` and `g : Y ⟶ Z`, we find that `W` is also the pullback of `lift (𝟙 Z) (𝟙 Z)`
  along `f ⊗ₘ g`.
- `IsPullback.of_isPullback_diag_tensorHom` shows that given a pullback `W` of `lift (𝟙 Z) (𝟙 Z)`
  along `f ⊗ₘ g`, we find that `W` is also the pullback of `f` along `g`.
- `IsPullback.comp_lift_of_isPullback` shows that given two pullback squares that share a top-right
  corner with morphisms `fᵢ` and `gᵢ` (indexed in the order top-left-right-bottom), the pullback
  of `f₁` and `g₁` is the pullback of `f₄ ⊗ₘ g₄` along `lift f₃ g₃`.
- `IsPullback.equalizer_monoidal` shows that for `f g : X ⟶ Z`, `equalizer f g` is also the pullback
  of `lift (𝟙 Z) (𝟙 Z)` along `lift f g : X ⟶ Z ⊗ Z`.
- `HasEqualizer.of_isPullback_monoidal` shows that given a pullback `W` of `lift (𝟙 Z) (𝟙 Z)`
  along `lift f g`, we find that `W` is also the equalizer of `f` and `g`.

-/

public section
universe v u

namespace CategoryTheory
open Limits MonoidalCategory CartesianMonoidalCategory
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/--
In a cartesian monoidal category, the following is a pullback square:
```
X ⊗ Y  -π₁→  X
  |          |
  π₂         !
  ↓          ↓
  Y   -!→   𝟙_ C
```
-/
lemma IsPullback.fst_snd_toUnit_toUnit (X Y : C) :
    IsPullback (fst X Y) (snd X Y) (toUnit _) (toUnit _) :=
  .of_isLimit_binaryFan_of_isTerminal (tensorProductIsBinaryProduct X Y) isTerminalTensorUnit

/--
In a cartesian monoidal category, the following is a pullback square:
```
     (f ▷ Z)
X ⊗ Z  →  Y ⊗ Z
  |          |
  π₁         π₁
  ↓          ↓
  X   -f→    Y
```
-/
lemma IsPullback.whiskerRight_horiz {X Y : C} (f : X ⟶ Y) (Z : C) :
    IsPullback (f ▷ Z) (fst X Z) (fst Y Z) f := by
  apply flip <| IsPullback.of_bot _ (by simp) (IsPullback.fst_snd_toUnit_toUnit _ _)
  simpa using (IsPullback.fst_snd_toUnit_toUnit _ _)

/--
In a cartesian monoidal category, the following is a pullback square:
```
    (Z ◁ f)
Z ⊗ X  →  Z ⊗ Y
  |          |
  π₂         π₂
  ↓          ↓
  X   -f→    Y
```
-/
lemma IsPullback.whiskerLeft_horiz {X Y : C} (f : X ⟶ Y) (Z : C) :
    IsPullback (Z ◁ f) (snd Z X) (snd Z Y) f := by
  let := BraidedCategory.ofCartesianMonoidalCategory (C := C)
  have hleft := IsPullback.whiskerRight_horiz f Z
  have : IsPullback (Z ◁ f) (β_ Z X).hom (β_ Z Y).hom (f ▷ Z) := .of_vert_isIso .mk
  simpa using this.paste_vert hleft

/--
In a cartesian monoidal category, given two pullback squares:
```
X₁ -f₁→ X₂
|       |
f₂      f₃
↓       ↓
X₃ -f₄→ X₄

Y₁ -g₁→ Y₂
|       |
g₂      g₃
↓       ↓
Y₃ -g₄→ Y₄
```
we get a new pullback square
```
      (f₁ ⊗ₘ g₁)
 X₁ ⊗ Y₁  →  X₂ ⊗ Y₂
    |            |
(f₂ ⊗ₘ g₂)  (f₃ ⊗ₘ g₃)
    ↓            ↓
 X₃ ⊗ Y₃  →  X₄ ⊗ Y₄
      (f₄ ⊗ₘ g₄)
```
-/
lemma IsPullback.tensor
    {X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ : C}
    {f₁ : X₁ ⟶ X₂} {f₂ : X₁ ⟶ X₃} {f₃ : X₂ ⟶ X₄} {f₄ : X₃ ⟶ X₄} (hf : IsPullback f₁ f₂ f₃ f₄)
    {g₁ : Y₁ ⟶ Y₂} {g₂ : Y₁ ⟶ Y₃} {g₃ : Y₂ ⟶ Y₄} {g₄ : Y₃ ⟶ Y₄} (hg : IsPullback g₁ g₂ g₃ g₄) :
    IsPullback (f₁ ⊗ₘ g₁) (f₂ ⊗ₘ g₂) (f₃ ⊗ₘ g₃) (f₄ ⊗ₘ g₄) := by
  rw [tensorHom_def f₁, tensorHom_def f₄]
  apply IsPullback.paste_horiz (v₁₂ := f₃ ⊗ₘ g₂)
  · exact IsPullback.of_bot
      (by simpa using (IsPullback.whiskerRight_horiz f₁ Y₁).paste_vert hf)
      (by ext <;> simp [hf.w])
      (IsPullback.whiskerRight_horiz _ _)
  · exact IsPullback.of_bot
      (by simpa using (IsPullback.whiskerLeft_horiz g₁ X₂).paste_vert hg)
      (by ext <;> simp [hg.w])
      (IsPullback.whiskerLeft_horiz _ _)

/--
In a cartesian monoidal category, if we have a pullback square,
```
X₁ -f₁→ X₂
|       |
f₂      f₃
↓       ↓
X₃ -f₄→ X₄
```
then the following is a pullback square:
```
     (f₁ ≫ f₃)
   X₁    →    X₄
   |          |
⟨f₁,f₂⟩       Δ
   ↓          ↓
X₂ ⊗ X₃ → X₄ ⊗ X₄
    (f₃ ⊗ f₄)
```
-/
lemma IsPullback.comp_lift_diag_tensorHom {X₁ X₂ X₃ X₄ : C}
    {f₁ : X₁ ⟶ X₂} {f₂ : X₁ ⟶ X₃}
    {f₃ : X₂ ⟶ X₄} {f₄ : X₃ ⟶ X₄} (hf : IsPullback f₁ f₂ f₃ f₄) :
    IsPullback (f₁ ≫ f₃)
      (CartesianMonoidalCategory.lift f₁ f₂) (CartesianMonoidalCategory.lift (𝟙 X₄) (𝟙 _))
      (f₃ ⊗ₘ f₄) :=
  IsPullback.mk' (by apply CartesianMonoidalCategory.hom_ext <;> simp [hf.w])
    (by
      simp only [CartesianMonoidalCategory.hom_ext_iff]
      introv _ _
      apply hf.hom_ext <;> cat_disch)
    (by
      simp only [CartesianMonoidalCategory.hom_ext_iff]
      introv _
      exact ⟨hf.lift (b ≫ fst _ _) (b ≫ snd _ _) (by cat_disch),by cat_disch⟩)

/--
In a cartesian monoidal category, if we have that the following square is a pullback square,
```
   W  -d→  Z
   |       |
   ι       Δ
   ↓       ↓
X ⊗ Y → Z ⊗ Z
    (f ⊗ g)
```
then the following is too:
```
     (ι ≫ π₁)
   W    →    X
   |         |
(ι ≫ π₂)     f
   ↓         ↓
   Y   -g→   Z
```
-/
lemma IsPullback.of_isPullback_diag_tensorHom {W X Y Z : C}
    {d : W ⟶ Z} {ι : W ⟶ X ⊗ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (hpb : IsPullback d
      ι (CartesianMonoidalCategory.lift (𝟙 Z) (𝟙 _))
      (f ⊗ₘ g)) : IsPullback (ι ≫ fst _ _) (ι ≫ snd _ _) f g :=
  IsPullback.mk' (by
    rw [Category.assoc, Category.assoc, ← tensorHom_fst f g, ← tensorHom_snd f g, ← hpb.w_assoc,
      ← hpb.w_assoc, CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_snd])
    (by
      simp_rw [← and_imp, ← Category.assoc, ← CartesianMonoidalCategory.hom_ext_iff]
      introv h
      have hw := congr($hpb.w ≫ snd _ _)
      simp_rw [Category.assoc, CartesianMonoidalCategory.lift_snd, Category.comp_id] at hw
      apply hpb.hom_ext _ h
      rw [hw, reassoc_of% h])
    (by
      introv h
      use hpb.lift (a ≫ f) (CartesianMonoidalCategory.lift a b) (by cat_disch)
      simp)

/--
Given two pullback squares that share a top-right corner with morphisms `fᵢ` and `gᵢ` (indexed in
the order top-left-right-bottom), the pullback of `f₁` and `g₁` is the pullback of `f₄ ⊗ₘ g₄` along
`lift f₃ g₃`.
-/
lemma IsPullback.comp_lift_of_isPullback_of_cartesianMonoidal {A₁ A₂ A₃ B₁ B₂ B₃ Z₁ Z₂ : C}
    {f₁ : A₁ ⟶ Z₁} {f₂ : A₁ ⟶ A₂} {f₃ : Z₁ ⟶ A₃} {f₄ : A₂ ⟶ A₃} (hf : IsPullback f₁ f₂ f₃ f₄)
    {g₁ : B₁ ⟶ Z₁} {g₂ : B₁ ⟶ B₂} {g₃ : Z₁ ⟶ B₃} {g₄ : B₂ ⟶ B₃} (hg : IsPullback g₁ g₂ g₃ g₄)
    {f' : Z₂ ⟶ A₁} {g' : Z₂ ⟶ B₁} (hf' : IsPullback f' g' f₁ g₁) :
    IsPullback (f' ≫ f₁)
      (CartesianMonoidalCategory.lift (f' ≫ f₂) (g' ≫ g₂))
      (CartesianMonoidalCategory.lift f₃ g₃)
      (f₄ ⊗ₘ g₄) := by
  simpa using hf'.comp_lift_diag_tensorHom.paste_vert (hf.tensor hg)

section equalizer

lemma IsPullback.equalizer_ι_comp_lift_diag_of_cartesianMonoidal {X Y : C} (f g : X ⟶ Y)
    [HasEqualizer f g] : IsPullback (equalizer.ι f g) (equalizer.ι f g ≫ f)
      (CartesianMonoidalCategory.lift f g) (CartesianMonoidalCategory.lift (𝟙 Y) (𝟙 Y)) :=
  IsPullback.mk' (by apply CartesianMonoidalCategory.hom_ext <;> simp [equalizer.condition f g])
    (by cat_disch)
    (by
      intro s m m' hm₂
      rw [CartesianMonoidalCategory.hom_ext_iff] at hm₂
      use (equalizer.lift m (by cat_disch))
      simpa [equalizer.lift_ι, equalizer.lift_ι_assoc] using hm₂.left)

/--
In a cartesian monoidal category, if we have that the following square is a pullback square,
```
W  -ι→  X
|       |
d     ⟨f,g⟩
↓       ↓
Y -Δ→ Y ⊗ Y
```
Then there is an equalizer of f and g.
-/
lemma HasEqualizer.of_isPullback_lift_diag_of_cartesianMonoidal {X Y : C} (f g : X ⟶ Y)
    {W : C} (ι : W ⟶ X) (d : W ⟶ Y) (hpb : IsPullback ι d (lift f g) (lift (𝟙 _) (𝟙 _))) :
    HasEqualizer f g :=
  ⟨⟨⟨Limits.Fork.ofι ι
    (by nth_rw 1 [← lift_snd f g, ← lift_fst f g, hpb.w_assoc, hpb.w_assoc, lift_fst, lift_snd]),
    (by
      refine Limits.Fork.IsLimit.mk _ (fun s => hpb.lift s.ι (s.ι ≫ f)
        (by simp [s.condition])) ?_ ?_
      · cat_disch
      · intro s m hm
        apply hpb.hom_ext (by simpa using hm)
        simp only [Fork.ofι_pt, Fork.ι_ofι, IsPullback.lift_snd] at hm ⊢
        rw [← Category.comp_id d, ← lift_fst (𝟙 Y) (𝟙 Y), ← hpb.w_assoc, lift_fst,
          reassoc_of% hm])⟩⟩⟩

end equalizer

end CategoryTheory
