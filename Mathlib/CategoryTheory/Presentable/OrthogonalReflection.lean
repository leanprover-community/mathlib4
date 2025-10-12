/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
import Mathlib.CategoryTheory.ObjectProperty.Orthogonal
import Mathlib.CategoryTheory.SmallObject.TransfiniteIteration

/-!
# The Orthogonal-reflection construction

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

universe w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)

namespace OrthogonalReflection

variable (Z : C)

section

def D₁ : Type _ := Σ (f : W.toSet), f.1.left ⟶ Z

variable {W Z} in
def D₁.obj₁ (d : D₁ W Z) : C := d.1.1.left

variable {W Z} in
def D₁.obj₂ (d : D₁ W Z) : C := d.1.1.right

variable [HasCoproduct (D₁.obj₁ (W := W) (Z := Z))]

noncomputable abbrev D₁.l : ∐ (obj₁ (W := W) (Z := Z)) ⟶ Z :=
  Sigma.desc (fun d ↦ d.2)

variable {W Z} in
noncomputable abbrev D₁.ιLeft {X Y : C} (f : X ⟶ Y) (hf : W f) (g : X ⟶ Z) :
    X ⟶ ∐ (obj₁ (W := W) (Z := Z)) :=
  Sigma.ι (obj₁ (W := W) (Z := Z)) ⟨⟨Arrow.mk f, hf⟩, g⟩

variable {W Z} in
@[reassoc]
lemma D₁.ιLeft_comp_l {X Y : C} (f : X ⟶ Y) (hf : W f) (g : X ⟶ Z) :
    D₁.ιLeft f hf g ≫ D₁.l W Z = g := by
  apply Sigma.ι_desc

variable [HasCoproduct (D₁.obj₂ (W := W) (Z := Z))]

noncomputable abbrev D₁.t : ∐ (obj₁ (W := W) (Z := Z)) ⟶ ∐ (obj₂ (W := W) (Z := Z)) :=
  Limits.Sigma.map (fun d ↦ d.1.1.hom)

variable {W Z} in
noncomputable abbrev D₁.ιRight {X Y : C} (f : X ⟶ Y) (hf : W f) (g : X ⟶ Z) :
    Y ⟶ ∐ (obj₂ (W := W) (Z := Z)) :=
  Sigma.ι (obj₂ (W := W) (Z := Z)) ⟨⟨Arrow.mk f, hf⟩, g⟩

variable {W Z} in
@[reassoc]
lemma D₁.ιLeft_comp_t {X Y : C} (f : X ⟶ Y) (hf : W f) (g : X ⟶ Z) :
    D₁.ιLeft f hf g ≫ D₁.t W Z = f ≫ D₁.ιRight f hf g := by
  apply ι_colimMap

variable [HasPushouts C]

noncomputable abbrev D₁.colimit := pushout (D₁.t W Z) (D₁.l W Z)

noncomputable abbrev toColimit₁ : Z ⟶ D₁.colimit W Z := pushout.inr _ _

end

section

def D₂ : Type _ :=
  Σ (f : W.toSet),
    { pq : (f.1.right ⟶ Z) × (f.1.right ⟶ Z) // f.1.hom ≫ pq.1 = f.1.hom ≫ pq.2 }

@[simps]
def D₂.multispanShape : MultispanShape where
  L := D₂ W Z
  R := Unit
  fst _ := .unit
  snd _ := .unit

@[simps]
def D₂.multispanIndex : MultispanIndex (multispanShape W Z) C where
  left d := d.1.1.right
  right _ := Z
  fst d := d.2.1.1
  snd d := d.2.1.2

variable [HasMulticoequalizer (D₂.multispanIndex W Z)]

noncomputable abbrev D₂.colimit := multicoequalizer (multispanIndex W Z)

noncomputable abbrev toColimit₂ : Z ⟶ D₂.colimit W Z :=
  Multicoequalizer.π (D₂.multispanIndex W Z) .unit

variable {W Z} in
@[reassoc]
lemma D₂.condition {X Y : C} (f : X ⟶ Y) (hf : W f)
    {g₁ g₂ : Y ⟶ Z} (h : f ≫ g₁ = f ≫ g₂) :
      g₁ ≫ toColimit₂ W Z = g₂ ≫ toColimit₂ W Z :=
  Multicoequalizer.condition (D₂.multispanIndex W Z)
    ⟨⟨Arrow.mk f, hf⟩, ⟨g₁, g₂⟩, h⟩

end

section

variable [HasPushouts C] [HasCoproduct (D₁.obj₁ (W := W) (Z := Z))]
  [HasCoproduct (D₁.obj₂ (W := W) (Z := Z))]
  [HasMulticoequalizer (D₂.multispanIndex W Z)]

noncomputable abbrev succ : C := pushout (toColimit₁ W Z) (toColimit₂ W Z)

noncomputable def toSucc : Z ⟶ succ W Z := toColimit₁ W Z ≫ pushout.inl _ _

@[reassoc (attr := simp)]
lemma toColimit₁_inl : toColimit₁ W Z ≫ pushout.inl _ _ = toSucc W Z := rfl

@[reassoc (attr := simp)]
lemma toColimit₂_inr : toColimit₂ W Z ≫ pushout.inr _ _ = toSucc W Z := pushout.condition.symm

lemma isIso_toSucc_iff :
    IsIso (toSucc W Z) ↔ W.rightOrthogonal Z := by
  refine ⟨fun _ X Y f hf ↦ ?_, fun hZ ↦ ?_⟩
  · refine ⟨fun g₁ g₂ hg ↦ ?_,
      fun g ↦ ⟨D₁.ιRight f hf g ≫ pushout.inl _ _ ≫ pushout.inl _ _ ≫
        inv (toSucc W Z), ?_⟩⟩
    · dsimp at hg
      rw [← cancel_mono (toSucc W Z), ← toColimit₂_inr, D₂.condition_assoc _ hf hg]
    · dsimp
      rw [← D₁.ιLeft_comp_t_assoc, pushout.condition_assoc, D₁.ιLeft_comp_l_assoc]
      simp
  · choose g hg using fun (d : D₁ W Z) ↦ (hZ d.1.1.hom d.1.2).2 d.2
    let φ₁ : D₁.colimit W Z ⟶ Z := pushout.desc (Sigma.desc g) (𝟙 Z) (by cat_disch)
    let φ₂ : D₂.colimit W Z ⟶ Z := Multicoequalizer.desc _ _ (fun x ↦ 𝟙 Z) (by
      rintro ⟨⟨f, hf⟩, ⟨g₁, g₂⟩, hg⟩
      simpa using (hZ _ hf).1 hg)
    have hφ₂ : φ₂ ≫ toColimit₂ W Z = 𝟙 _ :=
      Multicoequalizer.hom_ext _ _ _ (fun ⟨⟩ ↦ by simp [φ₂])
    refine ⟨pushout.desc φ₁ φ₂ ?_, ?_, ?_⟩
    · simp [φ₁, φ₂]
    · rw [← toColimit₁_inl, Category.assoc, pushout.inl_desc]
      simp [φ₁]
    · ext : 1
      · rw [pushout.inl_desc_assoc, Category.comp_id]
        ext d
        · simp [φ₁]
          rw [← toColimit₁_inl]
          -- wrong!
          sorry
        · simp [φ₁]
      · rw [pushout.inr_desc_assoc, Category.comp_id,
          ← toColimit₂_inr, reassoc_of% hφ₂]

end

variable [HasPushouts C] [∀ Z, HasCoproduct (D₁.obj₁ (W := W) (Z := Z))]
  [∀ Z, HasCoproduct (D₁.obj₂ (W := W) (Z := Z))]
  [∀ Z, HasMulticoequalizer (D₂.multispanIndex W Z)]

open SmallObject

noncomputable def succStruct (Z₀ : C) : SuccStruct C where
  X₀ := Z₀
  succ Z := succ W Z
  toSucc Z := toSucc W Z

end OrthogonalReflection

end CategoryTheory
