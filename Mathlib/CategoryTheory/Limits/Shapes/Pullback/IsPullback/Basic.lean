/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Joël Riou, Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Pullback and pushout squares

We restate some results about pullbacks/pushouts in the language of `IsPullback` and `IsPushout`,
among which the pasting lemmas
-/

@[expose] public section

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]

namespace IsPullback

variable {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

/-- If `c` is a limiting binary product cone, and we have a terminal object,
then we have `IsPullback c.fst c.snd 0 0`
(where each `0` is the unique morphism to the terminal object). -/
theorem of_is_product {c : BinaryFan X Y} (h : Limits.IsLimit c) (t : IsTerminal Z) :
    IsPullback c.fst c.snd (t.from _) (t.from _) :=
  of_isLimit
    (isPullbackOfIsTerminalIsProduct _ _ _ _ t
      (IsLimit.ofIsoLimit h
        (Limits.Cones.ext (Iso.refl c.pt)
          (by
            rintro ⟨⟨⟩⟩ <;> simp))))

/-- A variant of `of_is_product` that is more useful with `apply`. -/
theorem of_is_product' (h : Limits.IsLimit (BinaryFan.mk fst snd)) (t : IsTerminal Z) :
    IsPullback fst snd (t.from _) (t.from _) :=
  of_is_product h t

variable (X Y) in
theorem of_hasBinaryProduct' [HasBinaryProduct X Y] [HasTerminal C] :
    IsPullback Limits.prod.fst Limits.prod.snd (terminal.from X) (terminal.from Y) :=
  of_is_product (limit.isLimit _) terminalIsTerminal

theorem of_iso_pullback (h : CommSq fst snd f g) [HasPullback f g] (i : P ≅ pullback f g)
    (w₁ : i.hom ≫ pullback.fst _ _ = fst) (w₂ : i.hom ≫ pullback.snd _ _ = snd) :
      IsPullback fst snd f g :=
  of_isLimit' h
    (Limits.IsLimit.ofIsoLimit (limit.isLimit _)
      (@PullbackCone.ext _ _ _ _ _ _ _ (PullbackCone.mk _ _ _) _ i w₁.symm w₂.symm).symm)

theorem of_horiz_isIso_mono [IsIso fst] [Mono g] (sq : CommSq fst snd f g) :
    IsPullback fst snd f g :=
  of_isLimit' sq
    (by
      refine
        PullbackCone.IsLimit.mk _ (fun s => s.fst ≫ inv fst) (by simp)
          (fun s => ?_) (by cat_disch)
      simp only [← cancel_mono g, Category.assoc, ← sq.w, IsIso.inv_hom_id_assoc, s.condition])

theorem of_horiz_isIso [IsIso fst] [IsIso g] (sq : CommSq fst snd f g) :
    IsPullback fst snd f g :=
  of_horiz_isIso_mono sq

lemma of_iso (h : IsPullback fst snd f g)
    {P' X' Y' Z' : C} {fst' : P' ⟶ X'} {snd' : P' ⟶ Y'} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'}
    (e₁ : P ≅ P') (e₂ : X ≅ X') (e₃ : Y ≅ Y') (e₄ : Z ≅ Z')
    (commfst : fst ≫ e₂.hom = e₁.hom ≫ fst')
    (commsnd : snd ≫ e₃.hom = e₁.hom ≫ snd')
    (commf : f ≫ e₄.hom = e₂.hom ≫ f')
    (commg : g ≫ e₄.hom = e₃.hom ≫ g') :
    IsPullback fst' snd' f' g' where
  w := by
    rw [← cancel_epi e₁.hom, ← reassoc_of% commfst, ← commf,
      ← reassoc_of% commsnd, ← commg, h.w_assoc]
  isLimit' :=
    ⟨(IsLimit.postcomposeInvEquiv
        (cospanExt e₂ e₃ e₄ commf.symm commg.symm) _).1
          (IsLimit.ofIsoLimit h.isLimit (by
            refine PullbackCone.ext e₁ ?_ ?_
            · change fst = e₁.hom ≫ fst' ≫ e₂.inv
              rw [← reassoc_of% commfst, e₂.hom_inv_id, Category.comp_id]
            · change snd = e₁.hom ≫ snd' ≫ e₃.inv
              rw [← reassoc_of% commsnd, e₃.hom_inv_id, Category.comp_id]))⟩

/-- Same as `IsPullback.of_iso`, but using the data and compatibilities involving
the inverse isomorphisms instead. -/
lemma of_iso' (h : IsPullback fst snd f g)
    {P' X' Y' Z' : C} {fst' : P' ⟶ X'} {snd' : P' ⟶ Y'} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'}
    (e₁ : P' ≅ P) (e₂ : X' ≅ X) (e₃ : Y' ≅ Y) (e₄ : Z' ≅ Z)
    (commfst : e₁.hom ≫ fst = fst' ≫ e₂.hom)
    (commsnd : e₁.hom ≫ snd = snd' ≫ e₃.hom)
    (commf : e₂.hom ≫ f = f' ≫ e₄.hom)
    (commg : e₃.hom ≫ g = g' ≫ e₄.hom) :
    IsPullback fst' snd' f' g' := by
  apply h.of_iso e₁.symm e₂.symm e₃.symm e₄.symm
  · simp only [Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, ← commfst, Iso.inv_hom_id_assoc]
  · simp only [Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, ← commsnd, Iso.inv_hom_id_assoc]
  · simp only [Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, ← commf, Iso.inv_hom_id_assoc]
  · simp only [Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, ← commg, Iso.inv_hom_id_assoc]

section

variable {P X Y : C} {fst : P ⟶ X} {snd : P ⟶ X} {f : X ⟶ Y} [Mono f]

lemma isIso_fst_of_mono (h : IsPullback fst snd f f) : IsIso fst :=
  h.cone.isIso_fst_of_mono_of_isLimit h.isLimit

lemma isIso_snd_iso_of_mono {P X Y : C} {fst : P ⟶ X} {snd : P ⟶ X} {f : X ⟶ Y} [Mono f]
    (h : IsPullback fst snd f f) : IsIso snd :=
  h.cone.isIso_snd_of_mono_of_isLimit h.isLimit

end

section

lemma isIso_fst_of_isIso (h : IsPullback fst snd f g) [IsIso g] : IsIso fst := by
  have := h.hasPullback
  rw [← h.isoPullback_hom_fst]
  infer_instance

lemma isIso_snd_of_isIso (h : IsPullback fst snd f g) [IsIso f] : IsIso snd := by
  have := h.hasPullback
  rw [← h.isoPullback_hom_snd]
  infer_instance

end

section
-- Objects here are arranged in a 3x2 grid, and indexed by their xy coordinates.
-- Morphisms are named `hᵢⱼ` for a horizontal morphism starting at `(i,j)`,
-- and `vᵢⱼ` for a vertical morphism starting at `(i,j)`.
/-- Paste two pullback squares "vertically" to obtain another pullback square.

The objects in the statement fit into the following diagram:
```
X₁₁ - h₁₁ -> X₁₂
|            |
v₁₁          v₁₂
↓            ↓
X₂₁ - h₂₁ -> X₂₂
|            |
v₂₁          v₂₂
↓            ↓
X₃₁ - h₃₁ -> X₃₂
```
-/
theorem paste_vert {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂}
    {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂}
    (s : IsPullback h₁₁ v₁₁ v₁₂ h₂₁) (t : IsPullback h₂₁ v₂₁ v₂₂ h₃₁) :
    IsPullback h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁ :=
  of_isLimit (pasteHorizIsPullback rfl t.isLimit s.isLimit)

/-- Paste two pullback squares "horizontally" to obtain another pullback square.

The objects in the statement fit into the following diagram:
```
X₁₁ - h₁₁ -> X₁₂ - h₁₂ -> X₁₃
|            |            |
v₁₁          v₁₂          v₁₃
↓            ↓            ↓
X₂₁ - h₂₁ -> X₂₂ - h₂₂ -> X₂₃
```
-/
theorem paste_horiz {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃}
    {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
    (s : IsPullback h₁₁ v₁₁ v₁₂ h₂₁) (t : IsPullback h₁₂ v₁₂ v₁₃ h₂₂) :
    IsPullback (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂) :=
  (paste_vert s.flip t.flip).flip

/-- Given a pullback square assembled from a commuting square on the top and
a pullback square on the bottom, the top square is a pullback square.

The objects in the statement fit into the following diagram:
```
X₁₁ - h₁₁ -> X₁₂
|            |
v₁₁          v₁₂
↓            ↓
X₂₁ - h₂₁ -> X₂₂
|            |
v₂₁          v₂₂
↓            ↓
X₃₁ - h₃₁ -> X₃₂
```
-/
theorem of_bot {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂}
    {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂}
    (s : IsPullback h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁) (p : h₁₁ ≫ v₁₂ = v₁₁ ≫ h₂₁)
    (t : IsPullback h₂₁ v₂₁ v₂₂ h₃₁) : IsPullback h₁₁ v₁₁ v₁₂ h₂₁ :=
  of_isLimit (leftSquareIsPullback (PullbackCone.mk h₁₁ _ p) rfl t.isLimit s.isLimit)

/-- Given a pullback square assembled from a commuting square on the left and
a pullback square on the right, the left square is a pullback square.

The objects in the statement fit into the following diagram:
```
X₁₁ - h₁₁ -> X₁₂ - h₁₂ -> X₁₃
|            |            |
v₁₁          v₁₂          v₁₃
↓            ↓            ↓
X₂₁ - h₂₁ -> X₂₂ - h₂₂ -> X₂₃
```
-/
theorem of_right {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂}
    {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
    (s : IsPullback (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂)) (p : h₁₁ ≫ v₁₂ = v₁₁ ≫ h₂₁)
    (t : IsPullback h₁₂ v₁₂ v₁₃ h₂₂) : IsPullback h₁₁ v₁₁ v₁₂ h₂₁ :=
  (of_bot s.flip p.symm t.flip).flip

theorem paste_vert_iff {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂}
    {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂}
    (s : IsPullback h₂₁ v₂₁ v₂₂ h₃₁) (e : h₁₁ ≫ v₁₂ = v₁₁ ≫ h₂₁) :
    IsPullback h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁ ↔ IsPullback h₁₁ v₁₁ v₁₂ h₂₁ :=
  ⟨fun h => h.of_bot e s, fun h => h.paste_vert s⟩

theorem paste_horiz_iff {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃}
    {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
    (s : IsPullback h₁₂ v₁₂ v₁₃ h₂₂) (e : h₁₁ ≫ v₁₂ = v₁₁ ≫ h₂₁) :
    IsPullback (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂) ↔ IsPullback h₁₁ v₁₁ v₁₂ h₂₁ :=
  ⟨fun h => h.of_right e s, fun h => h.paste_horiz s⟩

/-- Variant of `IsPullback.of_right` where `h₁₁` is induced from a morphism `h₁₃ : X₁₁ ⟶ X₁₃`, and
the universal property of the right square.

The objects fit in the following diagram:
```
X₁₁ - h₁₁ -> X₁₂ - h₁₂ -> X₁₃
|            |            |
v₁₁          v₁₂          v₁₃
↓            ↓            ↓
X₂₁ - h₂₁ -> X₂₂ - h₂₂ -> X₂₃
```
-/
theorem of_right' {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂}
    {h₂₂ : X₂₂ ⟶ X₂₃} {h₁₃ : X₁₁ ⟶ X₁₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
    (s : IsPullback h₁₃ v₁₁ v₁₃ (h₂₁ ≫ h₂₂)) (t : IsPullback h₁₂ v₁₂ v₁₃ h₂₂) :
    IsPullback (t.lift h₁₃ (v₁₁ ≫ h₂₁) (by rw [s.w, Category.assoc])) v₁₁ v₁₂ h₂₁ :=
  of_right ((t.lift_fst _ _ _) ▸ s) (t.lift_snd _ _ _) t

/-- Variant of `IsPullback.of_bot`, where `v₁₁` is induced from a morphism `v₃₁ : X₁₁ ⟶ X₃₁`, and
the universal property of the bottom square.

The objects in the statement fit into the following diagram:
```
X₁₁ - h₁₁ -> X₁₂
|            |
v₁₁          v₁₂
↓            ↓
X₂₁ - h₂₁ -> X₂₂
|            |
v₂₁          v₂₂
↓            ↓
X₃₁ - h₃₁ -> X₃₂
```
-/
theorem of_bot' {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂}
    {h₃₁ : X₃₁ ⟶ X₃₂} {v₃₁ : X₁₁ ⟶ X₃₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂}
    (s : IsPullback h₁₁ v₃₁ (v₁₂ ≫ v₂₂) h₃₁) (t : IsPullback h₂₁ v₂₁ v₂₂ h₃₁) :
    IsPullback h₁₁ (t.lift (h₁₁ ≫ v₁₂) v₃₁ (by rw [Category.assoc, s.w])) v₁₂ h₂₁ :=
  of_bot ((t.lift_snd _ _ _) ▸ s) (by simp only [lift_fst]) t

instance [HasPullbacksAlong f] (h : P ⟶ Y) : HasPullback h (pullback.fst g f) :=
  IsPullback.hasPullback (IsPullback.of_bot' (IsPullback.of_hasPullback (h ≫ g) f)
    (IsPullback.of_hasPullback g f))

theorem of_vert_isIso_mono [IsIso snd] [Mono f] (sq : CommSq fst snd f g) :
    IsPullback fst snd f g :=
  IsPullback.flip (of_horiz_isIso_mono sq.flip)

theorem of_vert_isIso [IsIso snd] [IsIso f] (sq : CommSq fst snd f g) :
    IsPullback fst snd f g :=
  of_vert_isIso_mono sq

lemma of_id_fst : IsPullback (𝟙 _) f f (𝟙 _) := IsPullback.of_horiz_isIso ⟨by simp⟩

lemma of_id_snd : IsPullback f (𝟙 _) (𝟙 _) f := IsPullback.of_vert_isIso ⟨by simp⟩

/-- The following diagram is a pullback
```
X --f--> Z
|        |
id       id
v        v
X --f--> Z
```
-/
lemma id_vert (f : X ⟶ Z) : IsPullback f (𝟙 X) (𝟙 Z) f :=
  of_vert_isIso ⟨by simp only [Category.id_comp, Category.comp_id]⟩

/-- The following diagram is a pullback
```
X --id--> X
|         |
f         f
v         v
Z --id--> Z
```
-/
lemma id_horiz (f : X ⟶ Z) : IsPullback (𝟙 X) f f (𝟙 Z) :=
  of_horiz_isIso ⟨by simp only [Category.id_comp, Category.comp_id]⟩

set_option backward.isDefEq.respectTransparency false in
/--
In a category, given a morphism `f : A ⟶ B` and an object `X`,
this is the obvious pullback diagram:
```
A ⨯ X ⟶ A
  |     |
  v     v
B ⨯ X ⟶ B
```
-/
lemma of_prod_fst_with_id {A B : C} (f : A ⟶ B) (X : C) [HasBinaryProduct A X]
    [HasBinaryProduct B X] :
    IsPullback prod.fst (prod.map f (𝟙 X)) f prod.fst where
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun s ↦ by
    refine ⟨prod.lift s.fst (s.snd ≫ prod.snd), ?_, ?_, ?_⟩
    · simp
    · ext
      · simp [PullbackCone.condition]
      · simp
    · intro m h₁ h₂
      dsimp at m h₁ h₂ ⊢
      ext
      · simpa using h₁
      · simp [← h₂])⟩

set_option backward.isDefEq.respectTransparency false in
lemma of_isLimit_binaryFan_of_isTerminal
    {X Y : C} {c : BinaryFan X Y} (hc : IsLimit c)
    {T : C} (hT : IsTerminal T) :
    IsPullback c.fst c.snd (hT.from _) (hT.from _) where
  isLimit' := ⟨PullbackCone.IsLimit.mk _
    (fun s ↦ hc.lift (BinaryFan.mk s.fst s.snd))
    (fun s ↦ hc.fac (BinaryFan.mk s.fst s.snd) ⟨.left⟩)
    (fun s ↦ hc.fac (BinaryFan.mk s.fst s.snd) ⟨.right⟩)
    (fun s m h₁ h₂ ↦ by
      apply BinaryFan.IsLimit.hom_ext hc
      · rw [h₁, hc.fac (BinaryFan.mk s.fst s.snd) ⟨.left⟩]
        rfl
      · rw [h₂, hc.fac (BinaryFan.mk s.fst s.snd) ⟨.right⟩]
        rfl)⟩
end

lemma mk' {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (w : fst ≫ f = snd ≫ g)
    (hom_ext : ∀ ⦃T : C⦄ ⦃φ φ' : T ⟶ P⦄ (_ : φ ≫ fst = φ' ≫ fst)
      (_ : φ ≫ snd = φ' ≫ snd), φ = φ')
    (exists_lift : ∀ ⦃T : C⦄ (a : T ⟶ X) (b : T ⟶ Y)
      (_ : a ≫ f = b ≫ g), ∃ (l : T ⟶ P), l ≫ fst = a ∧ l ≫ snd = b) :
    IsPullback fst snd f g where
  w := w
  isLimit' := by
    let l (s : PullbackCone f g) := exists_lift _ _ s.condition
    exact ⟨PullbackCone.IsLimit.mk _
      (fun s ↦ (l s).choose)
      (fun s ↦ (l s).choose_spec.1)
      (fun s ↦ (l s).choose_spec.2)
      (fun s m h₁ h₂ ↦ hom_ext
        (h₁.trans (l s).choose_spec.1.symm)
        (h₂.trans (l s).choose_spec.2.symm))⟩

end IsPullback
namespace IsPushout

variable {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}

/-- If `c` is a colimiting binary coproduct cocone, and we have an initial object,
then we have `IsPushout 0 0 c.inl c.inr`
(where each `0` is the unique morphism from the initial object). -/
theorem of_is_coproduct {c : BinaryCofan X Y} (h : Limits.IsColimit c) (t : IsInitial Z) :
    IsPushout (t.to _) (t.to _) c.inl c.inr :=
  of_isColimit
    (isPushoutOfIsInitialIsCoproduct _ _ _ _ t
      (IsColimit.ofIsoColimit h
        (Limits.Cocones.ext (Iso.refl c.pt)
          (by
            rintro ⟨⟨⟩⟩ <;> simp))))

/-- A variant of `of_is_coproduct` that is more useful with `apply`. -/
theorem of_is_coproduct' (h : Limits.IsColimit (BinaryCofan.mk inl inr)) (t : IsInitial Z) :
    IsPushout (t.to _) (t.to _) inl inr :=
  of_is_coproduct h t

variable (X Y) in
theorem of_hasBinaryCoproduct' [HasBinaryCoproduct X Y] [HasInitial C] :
    IsPushout (initial.to _) (initial.to _) (coprod.inl : X ⟶ _) (coprod.inr : Y ⟶ _) :=
  of_is_coproduct (colimit.isColimit _) initialIsInitial

theorem of_iso_pushout (h : CommSq f g inl inr) [HasPushout f g] (i : P ≅ pushout f g)
    (w₁ : inl ≫ i.hom = pushout.inl _ _) (w₂ : inr ≫ i.hom = pushout.inr _ _) :
      IsPushout f g inl inr :=
  of_isColimit' h
    (Limits.IsColimit.ofIsoColimit (colimit.isColimit _)
      (PushoutCocone.ext (s := PushoutCocone.mk ..) i w₁ w₂).symm)

lemma of_iso (h : IsPushout f g inl inr)
    {Z' X' Y' P' : C} {f' : Z' ⟶ X'} {g' : Z' ⟶ Y'} {inl' : X' ⟶ P'} {inr' : Y' ⟶ P'}
    (e₁ : Z ≅ Z') (e₂ : X ≅ X') (e₃ : Y ≅ Y') (e₄ : P ≅ P')
    (commf : f ≫ e₂.hom = e₁.hom ≫ f')
    (commg : g ≫ e₃.hom = e₁.hom ≫ g')
    (comminl : inl ≫ e₄.hom = e₂.hom ≫ inl')
    (comminr : inr ≫ e₄.hom = e₃.hom ≫ inr') :
    IsPushout f' g' inl' inr' where
  w := by
    rw [← cancel_epi e₁.hom, ← reassoc_of% commf, ← comminl,
      ← reassoc_of% commg, ← comminr, h.w_assoc]
  isColimit' :=
    ⟨(IsColimit.precomposeHomEquiv
        (spanExt e₁ e₂ e₃ commf.symm commg.symm) _).1
          (IsColimit.ofIsoColimit h.isColimit
            (PushoutCocone.ext e₄ comminl comminr))⟩

/-- Same as `IsPushout.of_iso`, but using the data and compatibilities involving
the inverse isomorphisms instead. -/
lemma of_iso' {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
    (h : IsPushout f g inl inr)
    {Z' X' Y' P' : C} {f' : Z' ⟶ X'} {g' : Z' ⟶ Y'} {inl' : X' ⟶ P'} {inr' : Y' ⟶ P'}
    (e₁ : Z' ≅ Z) (e₂ : X' ≅ X) (e₃ : Y' ≅ Y) (e₄ : P' ≅ P)
    (commf : e₁.hom ≫ f = f' ≫ e₂.hom)
    (commg : e₁.hom ≫ g = g' ≫ e₃.hom)
    (comminl : e₂.hom ≫ inl = inl' ≫ e₄.hom)
    (comminr : e₃.hom ≫ inr = inr' ≫ e₄.hom) :
    IsPushout f' g' inl' inr' := by
  apply h.of_iso e₁.symm e₂.symm e₃.symm e₄.symm
  · simp only [Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, ← commf, Iso.inv_hom_id_assoc]
  · simp only [Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, ← commg, Iso.inv_hom_id_assoc]
  · simp only [Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, ← comminl, Iso.inv_hom_id_assoc]
  · simp only [Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, ← comminr, Iso.inv_hom_id_assoc]

section

variable {P X Y : C} {inl : X ⟶ P} {inr : X ⟶ P} {f : Y ⟶ X} [Epi f]

lemma isIso_inl_iso_of_epi (h : IsPushout f f inl inr) : IsIso inl :=
  h.cocone.isIso_inl_of_epi_of_isColimit h.isColimit

lemma isIso_inr_iso_of_epi (h : IsPushout f f inl inr) : IsIso inr :=
  h.cocone.isIso_inr_of_epi_of_isColimit h.isColimit

end

section

lemma isIso_inl_of_isIso (h : IsPushout f g inl inr) [IsIso g] : IsIso inl := by
  have := h.hasPushout
  rw [← h.inl_isoPushout_inv]
  infer_instance

lemma isIso_inr_of_isIso (h : IsPushout f g inl inr) [IsIso f] : IsIso inr := by
  have := h.hasPushout
  rw [← h.inr_isoPushout_inv]
  infer_instance

end

-- Objects here are arranged in a 3x2 grid, and indexed by their xy coordinates.
-- Morphisms are named `hᵢⱼ` for a horizontal morphism starting at `(i,j)`,
-- and `vᵢⱼ` for a vertical morphism starting at `(i,j)`.
/-- Paste two pushout squares "vertically" to obtain another pushout square.

The objects in the statement fit into the following diagram:
```
X₁₁ - h₁₁ -> X₁₂
|            |
v₁₁          v₁₂
↓            ↓
X₂₁ - h₂₁ -> X₂₂
|            |
v₂₁          v₂₂
↓            ↓
X₃₁ - h₃₁ -> X₃₂
```
-/
theorem paste_vert {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂}
    {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂}
    (s : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) (t : IsPushout h₂₁ v₂₁ v₂₂ h₃₁) :
    IsPushout h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁ :=
  of_isColimit (pasteHorizIsPushout rfl s.isColimit t.isColimit)

/-- Paste two pushout squares "horizontally" to obtain another pushout square.

The objects in the statement fit into the following diagram:
```
X₁₁ - h₁₁ -> X₁₂ - h₁₂ -> X₁₃
|            |            |
v₁₁          v₁₂          v₁₃
↓            ↓            ↓
X₂₁ - h₂₁ -> X₂₂ - h₂₂ -> X₂₃
```
-/
theorem paste_horiz {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃}
    {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
    (s : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) (t : IsPushout h₁₂ v₁₂ v₁₃ h₂₂) :
    IsPushout (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂) :=
  (paste_vert s.flip t.flip).flip

/-- Given a pushout square assembled from a pushout square on the top and
a commuting square on the bottom, the bottom square is a pushout square.

The objects in the statement fit into the following diagram:
```
X₁₁ - h₁₁ -> X₁₂
|            |
v₁₁          v₁₂
↓            ↓
X₂₁ - h₂₁ -> X₂₂
|            |
v₂₁          v₂₂
↓            ↓
X₃₁ - h₃₁ -> X₃₂
```
-/
theorem of_top {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂}
    {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂}
    (s : IsPushout h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁) (p : h₂₁ ≫ v₂₂ = v₂₁ ≫ h₃₁)
    (t : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) : IsPushout h₂₁ v₂₁ v₂₂ h₃₁ :=
  of_isColimit <| rightSquareIsPushout
    (PushoutCocone.mk _ _ p) (cocone_inr _) t.isColimit s.isColimit

/-- Given a pushout square assembled from a pushout square on the left and
a commuting square on the right, the right square is a pushout square.

The objects in the statement fit into the following diagram:
```
X₁₁ - h₁₁ -> X₁₂ - h₁₂ -> X₁₃
|            |            |
v₁₁          v₁₂          v₁₃
↓            ↓            ↓
X₂₁ - h₂₁ -> X₂₂ - h₂₂ -> X₂₃
```
-/
theorem of_left {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂}
    {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
    (s : IsPushout (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂)) (p : h₁₂ ≫ v₁₃ = v₁₂ ≫ h₂₂)
    (t : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) : IsPushout h₁₂ v₁₂ v₁₃ h₂₂ :=
  (of_top s.flip p.symm t.flip).flip

theorem paste_vert_iff {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂}
    {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂}
    (s : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) (e : h₂₁ ≫ v₂₂ = v₂₁ ≫ h₃₁) :
    IsPushout h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁ ↔ IsPushout h₂₁ v₂₁ v₂₂ h₃₁ :=
  ⟨fun h => h.of_top e s, s.paste_vert⟩

theorem paste_horiz_iff {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃}
    {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
    (s : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) (e : h₁₂ ≫ v₁₃ = v₁₂ ≫ h₂₂) :
    IsPushout (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂) ↔ IsPushout h₁₂ v₁₂ v₁₃ h₂₂ :=
  ⟨fun h => h.of_left e s, s.paste_horiz⟩

/-- Variant of `IsPushout.of_top` where `v₂₂` is induced from a morphism `v₁₃ : X₁₂ ⟶ X₃₂`, and
the universal property of the top square.

The objects in the statement fit into the following diagram:
```
X₁₁ - h₁₁ -> X₁₂
|            |
v₁₁          v₁₂
↓            ↓
X₂₁ - h₂₁ -> X₂₂
|            |
v₂₁          v₂₂
↓            ↓
X₃₁ - h₃₁ -> X₃₂
```
-/
theorem of_top' {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂}
    {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₂ ⟶ X₃₂} {v₂₁ : X₂₁ ⟶ X₃₁}
    (s : IsPushout h₁₁ (v₁₁ ≫ v₂₁) v₁₃ h₃₁) (t : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) :
      IsPushout h₂₁ v₂₁ (t.desc v₁₃ (v₂₁ ≫ h₃₁) (by rw [s.w, Category.assoc])) h₃₁ :=
  of_top ((t.inl_desc _ _ _).symm ▸ s) (t.inr_desc _ _ _) t

/-- Variant of `IsPushout.of_right` where `h₂₂` is induced from a morphism `h₂₃ : X₂₁ ⟶ X₂₃`, and
the universal property of the left square.

The objects in the statement fit into the following diagram:
```
X₁₁ - h₁₁ -> X₁₂ - h₁₂ -> X₁₃
|            |            |
v₁₁          v₁₂          v₁₃
↓            ↓            ↓
X₂₁ - h₂₁ -> X₂₂ - h₂₂ -> X₂₃
```
-/
theorem of_left' {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂}
    {h₂₃ : X₂₁ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
    (s : IsPushout (h₁₁ ≫ h₁₂) v₁₁ v₁₃ h₂₃) (t : IsPushout h₁₁ v₁₁ v₁₂ h₂₁) :
    IsPushout h₁₂ v₁₂ v₁₃ (t.desc (h₁₂ ≫ v₁₃) h₂₃ (by rw [← Category.assoc, s.w])) :=
  of_left ((t.inr_desc _ _ _).symm ▸ s) (by simp only [inl_desc]) t

theorem of_horiz_isIso_epi [Epi f] [IsIso inr] (sq : CommSq f g inl inr) : IsPushout f g inl inr :=
  of_isColimit' sq
    (by
      refine
        PushoutCocone.IsColimit.mk _ (fun s => inv inr ≫ s.inr) (fun s => ?_)
          (by simp) (by simp)
      simp only [← cancel_epi f, s.condition, sq.w_assoc, IsIso.hom_inv_id_assoc])

theorem of_horiz_isIso [IsIso f] [IsIso inr] (sq : CommSq f g inl inr) : IsPushout f g inl inr :=
  of_horiz_isIso_epi sq

theorem of_vert_isIso_epi [Epi g] [IsIso inl] (sq : CommSq f g inl inr) : IsPushout f g inl inr :=
  (of_horiz_isIso_epi sq.flip).flip

theorem of_vert_isIso [IsIso g] [IsIso inl] (sq : CommSq f g inl inr) : IsPushout f g inl inr :=
  of_vert_isIso_epi sq

lemma of_id_fst : IsPushout (𝟙 _) f f (𝟙 _) := IsPushout.of_horiz_isIso ⟨by simp⟩

lemma of_id_snd : IsPushout f (𝟙 _) (𝟙 _) f := IsPushout.of_vert_isIso ⟨by simp⟩

/-- The following diagram is a pullback
```
X --f--> Z
|        |
id       id
v        v
X --f--> Z
```
-/
lemma id_vert (f : X ⟶ Z) : IsPushout f (𝟙 X) (𝟙 Z) f :=
  of_vert_isIso ⟨by simp only [Category.id_comp, Category.comp_id]⟩

/-- The following diagram is a pullback
```
X --id--> X
|         |
f         f
v         v
Z --id--> Z
```
-/
lemma id_horiz (f : X ⟶ Z) : IsPushout (𝟙 X) f f (𝟙 Z) :=
  of_horiz_isIso ⟨by simp only [Category.id_comp, Category.comp_id]⟩

set_option backward.isDefEq.respectTransparency false in
/--
In a category, given a morphism `f : A ⟶ B` and an object `X`,
this is the obvious pushout diagram:
```
A ⟶ A ⨿ X
|     |
v     v
B ⟶ B ⨿ X
```
-/
lemma of_coprod_inl_with_id {A B : C} (f : A ⟶ B) (X : C) [HasBinaryCoproduct A X]
    [HasBinaryCoproduct B X] :
    IsPushout coprod.inl f (coprod.map f (𝟙 X)) coprod.inl where
  w := by simp
  isColimit' := ⟨PushoutCocone.isColimitAux' _ (fun s ↦ by
    refine ⟨coprod.desc s.inr (coprod.inr ≫ s.inl), ?_, ?_, ?_⟩
    · ext
      · simp [PushoutCocone.condition]
      · simp
    · simp
    · intro m h₁ h₂
      dsimp at m h₁ h₂ ⊢
      ext
      · simpa using h₂
      · simp [← h₁])⟩

set_option backward.isDefEq.respectTransparency false in
lemma of_isColimit_binaryCofan_of_isInitial
    {X Y : C} {c : BinaryCofan X Y} (hc : IsColimit c)
    {I : C} (hI : IsInitial I) :
    IsPushout (hI.to _) (hI.to _) c.inr c.inl where
  w := hI.hom_ext _ _
  isColimit' := ⟨PushoutCocone.IsColimit.mk _
    (fun s ↦ hc.desc (BinaryCofan.mk s.inr s.inl))
    (fun s ↦ hc.fac (BinaryCofan.mk s.inr s.inl) ⟨.right⟩)
    (fun s ↦ hc.fac (BinaryCofan.mk s.inr s.inl) ⟨.left⟩)
    (fun s m h₁ h₂ ↦ by
      apply BinaryCofan.IsColimit.hom_ext hc
      · rw [h₂, hc.fac (BinaryCofan.mk s.inr s.inl) ⟨.left⟩]
        rfl
      · rw [h₁, hc.fac (BinaryCofan.mk s.inr s.inl) ⟨.right⟩]
        rfl)⟩

lemma mk' {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
    (w : f ≫ inl = g ≫ inr)
    (hom_ext : ∀ ⦃T : C⦄ ⦃φ φ' : P ⟶ T⦄ (_ : inl ≫ φ = inl ≫ φ')
      (_ : inr ≫ φ = inr ≫ φ'), φ = φ')
    (exists_desc : ∀ ⦃T : C⦄ (a : X ⟶ T) (b : Y ⟶ T)
      (_ : f ≫ a = g ≫ b), ∃ (l : P ⟶ T), inl ≫ l = a ∧ inr ≫ l = b) :
    IsPushout f g inl inr where
  w := w
  isColimit' := by
    let l (s : PushoutCocone f g) := exists_desc _ _ s.condition
    exact ⟨PushoutCocone.IsColimit.mk _
      (fun s ↦ (l s).choose)
      (fun s ↦ (l s).choose_spec.1)
      (fun s ↦ (l s).choose_spec.2)
      (fun s m h₁ h₂ ↦ hom_ext
        (h₁.trans (l s).choose_spec.1.symm)
        (h₂.trans (l s).choose_spec.2.symm))⟩

end IsPushout

section Equalizer

variable {X Y Z : C} {f f' : X ⟶ Y} {g g' : Y ⟶ Z}

/-- If `f : X ⟶ Y`, `g g' : Y ⟶ Z` forms a pullback square, then `f` is the equalizer of
`g` and `g'`. -/
noncomputable def IsPullback.isLimitFork (H : IsPullback f f g g') : IsLimit (Fork.ofι f H.w) := by
  fapply Fork.IsLimit.mk
  · exact fun s => H.isLimit.lift (PullbackCone.mk s.ι s.ι s.condition)
  · exact fun s => H.isLimit.fac _ WalkingCospan.left
  · intro s m e
    apply PullbackCone.IsLimit.hom_ext H.isLimit <;> refine e.trans ?_ <;> symm <;>
      exact H.isLimit.fac _ _

/-- If `f f' : X ⟶ Y`, `g : Y ⟶ Z` forms a pushout square, then `g` is the coequalizer of
`f` and `f'`. -/
noncomputable def IsPushout.isLimitFork (H : IsPushout f f' g g) :
    IsColimit (Cofork.ofπ g H.w) := by
  fapply Cofork.IsColimit.mk
  · exact fun s => H.isColimit.desc (PushoutCocone.mk s.π s.π s.condition)
  · exact fun s => H.isColimit.fac _ WalkingSpan.left
  · intro s m e
    apply PushoutCocone.IsColimit.hom_ext H.isColimit <;> refine e.trans ?_ <;> symm <;>
      exact H.isColimit.fac _ _

end Equalizer

section Functor

variable {D : Type u₂} [Category.{v₂} D]
variable (F : C ⥤ D) {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

set_option backward.isDefEq.respectTransparency false in
theorem Functor.map_isPullback [PreservesLimit (cospan h i) F] (s : IsPullback f g h i) :
    IsPullback (F.map f) (F.map g) (F.map h) (F.map i) := by
  refine
    IsPullback.of_isLimit' (F.map_commSq s.toCommSq)
      (IsLimit.equivOfNatIsoOfIso (cospanCompIso F h i) _ _ (WalkingCospan.ext ?_ ?_ ?_)
        (isLimitOfPreserves F s.isLimit))
  · rfl
  · simp
  · simp

set_option backward.isDefEq.respectTransparency false in
theorem Functor.map_isPushout [PreservesColimit (span f g) F] (s : IsPushout f g h i) :
    IsPushout (F.map f) (F.map g) (F.map h) (F.map i) := by
  refine
    IsPushout.of_isColimit' (F.map_commSq s.toCommSq)
      (IsColimit.equivOfNatIsoOfIso (spanCompIso F f g) _ _ (WalkingSpan.ext ?_ ?_ ?_)
        (isColimitOfPreserves F s.isColimit))
  · rfl
  · simp
  · simp

alias IsPullback.map := Functor.map_isPullback

alias IsPushout.map := Functor.map_isPushout

theorem IsPullback.of_map [ReflectsLimit (cospan h i) F] (e : f ≫ h = g ≫ i)
    (H : IsPullback (F.map f) (F.map g) (F.map h) (F.map i)) : IsPullback f g h i := by
  refine ⟨⟨e⟩, ⟨isLimitOfReflects F <| ?_⟩⟩
  refine
    (IsLimit.equivOfNatIsoOfIso (cospanCompIso F h i) _ _ (WalkingCospan.ext ?_ ?_ ?_)).symm
      H.isLimit
  exacts [Iso.refl _, (Category.comp_id _).trans (Category.id_comp _).symm,
    (Category.comp_id _).trans (Category.id_comp _).symm]

theorem IsPullback.of_map_of_faithful [ReflectsLimit (cospan h i) F] [F.Faithful]
    (H : IsPullback (F.map f) (F.map g) (F.map h) (F.map i)) : IsPullback f g h i :=
  H.of_map F (F.map_injective <| by simpa only [F.map_comp] using H.w)

theorem IsPullback.map_iff {D : Type*} [Category* D] (F : C ⥤ D) [PreservesLimit (cospan h i) F]
    [ReflectsLimit (cospan h i) F] (e : f ≫ h = g ≫ i) :
    IsPullback (F.map f) (F.map g) (F.map h) (F.map i) ↔ IsPullback f g h i :=
  ⟨fun h => h.of_map F e, fun h => h.map F⟩

theorem IsPushout.of_map [ReflectsColimit (span f g) F] (e : f ≫ h = g ≫ i)
    (H : IsPushout (F.map f) (F.map g) (F.map h) (F.map i)) : IsPushout f g h i := by
  refine ⟨⟨e⟩, ⟨isColimitOfReflects F <| ?_⟩⟩
  refine
    (IsColimit.equivOfNatIsoOfIso (spanCompIso F f g) _ _ (WalkingSpan.ext ?_ ?_ ?_)).symm
      H.isColimit
  exacts [Iso.refl _, (Category.comp_id _).trans (Category.id_comp _),
    (Category.comp_id _).trans (Category.id_comp _)]

theorem IsPushout.of_map_of_faithful [ReflectsColimit (span f g) F] [F.Faithful]
    (H : IsPushout (F.map f) (F.map g) (F.map h) (F.map i)) : IsPushout f g h i :=
  H.of_map F (F.map_injective <| by simpa only [F.map_comp] using H.w)

theorem IsPushout.map_iff {D : Type*} [Category* D] (F : C ⥤ D) [PreservesColimit (span f g) F]
    [ReflectsColimit (span f g) F] (e : f ≫ h = g ≫ i) :
    IsPushout (F.map f) (F.map g) (F.map h) (F.map i) ↔ IsPushout f g h i :=
  ⟨fun h => h.of_map F e, fun h => h.map F⟩

lemma IsPullback.app [HasPullbacks D] {F₁ F₂ F₃ F₄ : C ⥤ D}
    {f₁ : F₁ ⟶ F₂} {f₂ : F₁ ⟶ F₃} {f₃ : F₂ ⟶ F₄} {f₄ : F₃ ⟶ F₄} (h : IsPullback f₁ f₂ f₃ f₄)
    (X : C) : IsPullback (f₁.app X) (f₂.app X) (f₃.app X) (f₄.app X) := by
  exact h.map ((evaluation _ _).obj X)

lemma IsPullback.of_forall_isPullback_app {F₁ F₂ F₃ F₄ : C ⥤ D}
    {f₁ : F₁ ⟶ F₂} {f₂ : F₁ ⟶ F₃} {f₃ : F₂ ⟶ F₄} {f₄ : F₃ ⟶ F₄}
    (h : ∀ (X : C), IsPullback (f₁.app X) (f₂.app X) (f₃.app X) (f₄.app X)) :
    IsPullback f₁ f₂ f₃ f₄ where
  w := by
    ext X
    simpa using (h X).w
  isLimit' := ⟨evaluationJointlyReflectsLimits _ fun X =>
    (PullbackCone.isLimitMapConeEquiv _ _).symm (h X).isLimit⟩

lemma IsPullback.iff_app [HasPullbacks D] {F₁ F₂ F₃ F₄ : C ⥤ D}
    {f₁ : F₁ ⟶ F₂} {f₂ : F₁ ⟶ F₃} {f₃ : F₂ ⟶ F₄} {f₄ : F₃ ⟶ F₄} :
    IsPullback f₁ f₂ f₃ f₄ ↔ ∀ (X : C), IsPullback (f₁.app X) (f₂.app X) (f₃.app X) (f₄.app X) :=
  ⟨.app, .of_forall_isPullback_app⟩

lemma IsPushout.app [HasPushouts D] {F₁ F₂ F₃ F₄ : C ⥤ D}
    {f₁ : F₁ ⟶ F₂} {f₂ : F₁ ⟶ F₃} {f₃ : F₂ ⟶ F₄} {f₄ : F₃ ⟶ F₄} (h : IsPushout f₁ f₂ f₃ f₄)
    (X : C) : IsPushout (f₁.app X) (f₂.app X) (f₃.app X) (f₄.app X) := by
  exact h.map ((evaluation _ _).obj X)

lemma IsPushout.of_forall_isPushout_app {F₁ F₂ F₃ F₄ : C ⥤ D}
    {f₁ : F₁ ⟶ F₂} {f₂ : F₁ ⟶ F₃} {f₃ : F₂ ⟶ F₄} {f₄ : F₃ ⟶ F₄}
    (h : ∀ (X : C), IsPushout (f₁.app X) (f₂.app X) (f₃.app X) (f₄.app X)) :
    IsPushout f₁ f₂ f₃ f₄ where
  w := by
    ext X
    simpa using (h X).w
  isColimit' := ⟨evaluationJointlyReflectsColimits _ fun X =>
    (PushoutCocone.isColimitMapCoconeEquiv _ _).symm (h X).isColimit⟩

lemma IsPushout.iff_app [HasPushouts D] {F₁ F₂ F₃ F₄ : C ⥤ D}
    {f₁ : F₁ ⟶ F₂} {f₂ : F₁ ⟶ F₃} {f₃ : F₂ ⟶ F₄} {f₄ : F₃ ⟶ F₄} :
    IsPushout f₁ f₂ f₃ f₄ ↔ ∀ (X : C), IsPushout (f₁.app X) (f₂.app X) (f₃.app X) (f₄.app X) :=
  ⟨.app, .of_forall_isPushout_app⟩

end Functor

end CategoryTheory
