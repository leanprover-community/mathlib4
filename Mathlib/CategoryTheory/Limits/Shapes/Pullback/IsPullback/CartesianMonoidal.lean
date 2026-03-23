/-
Copyright (c) 2026 Edward van de Meent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edward van de Meent
-/
module
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# Pullback in cartesian monoidal categories.

We show that various pullback squares result from other pullback squares or equalizers, in
the setting of a category with chosen finite products, i.e. where we have
`[CartesianMonoidalCategory C]`.

## Main results
In a `[CartesianMonoidalCategory C]`,

- `IsPullback.whiskerRight_horiz` shows a concrete pullback square for
  the pullback along the left projection.
- `IsPullback.tensor` shows that given two pullback squares, we can take the pointwise product.
- `IsPullback.pullback_monoidal` shows that given a pullback `W` of morphisms
  `f : X ⟶ Z` and `g : Y ⟶ Z`, we find that `W` is also the pullback of `lift (𝟙 Z) (𝟙 Z)`
  along `f ⊗ₘ g`.
- `IsPullback.of_pullback_monoidal` shows that given a pullback `W` of `lift (𝟙 Z) (𝟙 Z)`
  along `f ⊗ₘ g`, we find that `W` is also the pullback of `f` along `g`.

- `IsPullback.pullback_fst_monoidal` shows that given two pullback squares with morphisms `fᵢ` and
  `gᵢ` (indexed in the order top-left-right-bottom),
  the pullback of `f₁` and `g₁` is the pullback of `f₄ ⊗ₘ g₄` along `lift f₃ g₃`.
- `IsPullback.pullback_snd_monoidal` shows the same, but with the `fᵢ`, `gᵢ`, and resulting pullback
  squares flipped.

- `IsPullback.equalizer_monoidal` shows that for `f g : X ⟶ Z`, `equalizer f g` is also the pullback
  of `lift (𝟙 Z) (𝟙 Z)` along `lift f g : X ⟶ Z ⊗ Z`.
- `HasEqualizer.of_isPullback_monoidal` shows that given a pullback `W` of `lift (𝟙 Z) (𝟙 Z)`
  along `lift f g`, we find that `W` is also the equalizer of `f` and `g`.

-/

public section
universe v u

namespace CategoryTheory
open Limits MonoidalCategory CartesianMonoidalCategory
variable {C : Type u} [Category.{v} C]

/--
in any braided category, the following is a pullback square:
```
X₁ ⊗ X₂  -β→  X₂ ⊗ X₁
   |              |
(f ⊗ₘ g)      (g ⊗ₘ f)
   ↓              ↓
X₃ ⊗ X₄  -β→  X₄ ⊗ X₃
```
-/
lemma IsPullback.tensorHom_braiding [MonoidalCategory C] [BraidedCategory C] {X₁ X₂ X₃ X₄ : C}
    (f : X₁ ⟶ X₃) (g : X₂ ⟶ X₄) :
    IsPullback (f ⊗ₘ g) (β_ X₁ X₂).hom (β_ _ _).hom (g ⊗ₘ f) :=
  .of_vert_isIso (⟨BraidedCategory.braiding_naturality f g⟩)

variable [CartesianMonoidalCategory C]

/--
The following is a pullback square:
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
  refine IsPullback.of_isLimit' (by simp) ?_
  apply PullbackCone.IsLimit.mk _ fun s => CartesianMonoidalCategory.lift s.snd (s.fst ≫ snd _ _)
  · intro s
    ext <;> simp [s.condition]
  · intro s
    simp
  · intro s m hm₁ hm₂
    ext
    · simpa
    · simp [← hm₁]

/--
The following is a pullback square:
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
  have := BraidedCategory.ofCartesianMonoidalCategory (C := C)
  have hleft := IsPullback.whiskerRight_horiz f Z
  have := (IsPullback.tensorHom_braiding (𝟙 Z) f)
  simp only [tensorHom_id, id_tensorHom] at this
  simpa using this.paste_vert hleft


/--
given two pullback squares:
```
X₁ -f₁→ X₂

↓f₂     ↓f₃

X₃ -f₄→ X₄

Y₁ -g₁→ Y₂

↓g₂     ↓g₃

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
  rw [tensorHom_def f₁,tensorHom_def f₄]
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
If we have a pullback square,
```
X₁ -f₁→ X₂

↓f₂     ↓f₃

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
lemma IsPullback.pullback_monoidal {X₁ X₂ X₃ X₄ : C}
    {f₁ : X₁ ⟶ X₂} {f₂ : X₁ ⟶ X₃}
    {f₃ : X₂ ⟶ X₄} {f₄ : X₃ ⟶ X₄} (hf : IsPullback f₁ f₂ f₃ f₄) :
    IsPullback (f₁ ≫ f₃)
      (CartesianMonoidalCategory.lift f₁ f₂) (CartesianMonoidalCategory.lift (𝟙 X₄) (𝟙 _))
      (f₃ ⊗ₘ f₄) where
  w := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [hf.w]
  isLimit' := by
    constructor
    refine PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_
    · intro s
      refine hf.lift (s.snd ≫ fst _ _) (s.snd ≫ snd _ _) ?_
      have := s.condition
      simp only [CartesianMonoidalCategory.comp_lift, Category.comp_id,
        CartesianMonoidalCategory.hom_ext_iff, CartesianMonoidalCategory.lift_fst, Category.assoc,
        tensorHom_fst, CartesianMonoidalCategory.lift_snd, tensorHom_snd] at this
      simp [this.left, ← this.right]
    · intro s
      simpa using congr($(s.condition) ≫ fst _ _).symm
    · cat_disch
    · intro s m hm₁ hm₂
      simp only [CartesianMonoidalCategory.comp_lift, CartesianMonoidalCategory.hom_ext_iff,
        CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_snd] at hm₂ ⊢
      apply hf.hom_ext
      · simpa using hm₂.left
      · simpa [hm₁] using hm₂.right

/--
If we have that the following square is a pullback square,
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
lemma IsPullback.of_pullback_monoidal {W X Y Z : C}
    {d : W ⟶ Z} {ι : W ⟶ X ⊗ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (hpb : IsPullback d
      ι (CartesianMonoidalCategory.lift (𝟙 Z) (𝟙 _))
      (f ⊗ₘ g)) : IsPullback (ι ≫ fst _ _) (ι ≫ snd _ _) f g where
  w := by
    rw [Category.assoc, Category.assoc, ← tensorHom_fst f g, ← tensorHom_snd f g, ← hpb.w_assoc,
      ← hpb.w_assoc, CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_snd]
  isLimit' := ⟨by
    fapply PullbackCone.IsLimit.mk _
      (fun s => hpb.lift
        (s.fst ≫ f) (CartesianMonoidalCategory.lift s.fst s.snd) (by simp [s.condition]))
      (by
        intro s
        rw [hpb.lift_snd_assoc, CartesianMonoidalCategory.lift_fst])
      (by
        intro s
        simp only
        rw [hpb.lift_snd_assoc, CartesianMonoidalCategory.lift_snd])
      (by
        intro s m hm₁ hm₂
        apply hpb.hom_ext
        · rw [hpb.lift_fst,← Category.comp_id d, ← CartesianMonoidalCategory.lift_fst (𝟙 Z) (𝟙 Z),
            hpb.w_assoc, tensorHom_fst, reassoc_of% hm₁]
        · rw [hpb.lift_snd]
          apply CartesianMonoidalCategory.hom_ext <;> simpa)⟩

lemma IsPullback.pullback_fst_monoidal {A₁ A₂ A₃ B₁ B₂ B₃ Z₁ Z₂ : C}
    {f₁ : A₁ ⟶ Z₁} {f₂ : A₁ ⟶ A₂} {f₃ : Z₁ ⟶ A₃} {f₄ : A₂ ⟶ A₃} (hf : IsPullback f₁ f₂ f₃ f₄)
    {g₁ : B₁ ⟶ Z₁} {g₂ : B₁ ⟶ B₂} {g₃ : Z₁ ⟶ B₃} {g₄ : B₂ ⟶ B₃} (hg : IsPullback g₁ g₂ g₃ g₄)
    {f' : Z₂ ⟶ A₁} {g' : Z₂ ⟶ B₁} (hf' : IsPullback f' g' f₁ g₁) :
    IsPullback (f' ≫ f₁)
      (CartesianMonoidalCategory.lift (f' ≫ f₂) (g' ≫ g₂))
      (CartesianMonoidalCategory.lift f₃ g₃)
      (f₄ ⊗ₘ g₄) := by
  simpa using hf'.pullback_monoidal.paste_vert (hf.tensor hg)

lemma IsPullback.pullback_snd_monoidal {A₁ A₂ A₃ B₁ B₂ B₃ Z₁ Z₂ : C}
    {f₁ : A₁ ⟶ A₂} {f₂ : A₁ ⟶ Z₁} {f₃ : A₂ ⟶ A₃} {f₄ : Z₁ ⟶ A₃} (hf : IsPullback f₁ f₂ f₃ f₄)
    {g₁ : B₁ ⟶ B₂} {g₂ : B₁ ⟶ Z₁} {g₃ : B₂ ⟶ B₃} {g₄ : Z₁ ⟶ B₃} (hg : IsPullback g₁ g₂ g₃ g₄)
    {f' : Z₂ ⟶ A₁} {g' : Z₂ ⟶ B₁} (hf' : IsPullback f' g' f₂ g₂) :
    IsPullback (CartesianMonoidalCategory.lift (f' ≫ f₁) (g' ≫ g₁))
      (f' ≫ f₂) (f₃ ⊗ₘ g₃)
      (CartesianMonoidalCategory.lift f₄ g₄) := by
  exact (hf.flip.pullback_fst_monoidal hg.flip hf').flip

section equalizer

lemma IsPullback.equalizer_monoidal {X Y : C} (f g : X ⟶ Y) [HasEqualizer f g] :
    IsPullback (equalizer.ι f g) (equalizer.ι f g ≫ f)
      (CartesianMonoidalCategory.lift f g) (CartesianMonoidalCategory.lift (𝟙 Y) (𝟙 Y)) where
  w := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [equalizer.condition f g]
  isLimit' := by
    constructor
    refine PullbackCone.IsLimit.mk _ (fun s => (equalizer.lift s.fst ?_)) ?_ ?_ ?_
    · nth_rw 6 [← CartesianMonoidalCategory.lift_snd f g]
      nth_rw 4 [← CartesianMonoidalCategory.lift_fst f g]
      rw [s.condition_assoc, s.condition_assoc, CartesianMonoidalCategory.lift_fst,
        CartesianMonoidalCategory.lift_snd]
    · intro s
      simp [equalizer.lift_ι]
    · intro s
      simp only [equalizer.lift_ι_assoc]
      nth_rw 4 [← CartesianMonoidalCategory.lift_fst f g]
      rw [s.condition_assoc,CartesianMonoidalCategory.lift_fst,Category.comp_id]
    · intro s m hm₁ hm₂
      apply equalizer.hom_ext
      simp [equalizer.lift_ι, hm₁]

/--
If we have that the following square is a pullback square,
```
W  -ι→  X
|       |
d     ⟨f,g⟩
↓       ↓
Y -Δ→ Y ⊗ Y
```
Then there is an equalizer of f and g.
-/
lemma HasEqualizer.of_isPullback_monoidal {X Y : C} (f g : X ⟶ Y)
    {W : C} (ι : W ⟶ X) (d : W ⟶ Y) (hpb : IsPullback ι d (lift f g) (lift (𝟙 _) (𝟙 _))) :
    HasEqualizer f g := ⟨⟨⟨Limits.Fork.ofι ι (by
        let : BraidedCategory C := BraidedCategory.ofCartesianMonoidalCategory
        nth_rw 1 [← lift_snd f g,← lift_fst f g, hpb.w_assoc, hpb.w_assoc,lift_fst,lift_snd]),
      (by
        refine Limits.Fork.IsLimit.mk _ (fun s => hpb.lift s.ι (s.ι ≫ f)
          (by simp [dsimp% s.condition])) ?_ ?_
        · intro s
          simp
        · intro s m hm
          apply hpb.hom_ext (by simpa using hm)
          simp only [parallelPair_obj_zero, Fork.ofι_pt, Fork.ι_ofι, IsPullback.lift_snd] at hm ⊢
          rw [← Category.comp_id d, ← lift_fst (𝟙 Y) (𝟙 Y), ← hpb.w_assoc,lift_fst,reassoc_of% hm]
        )⟩
  ⟩⟩
end equalizer

end CategoryTheory
