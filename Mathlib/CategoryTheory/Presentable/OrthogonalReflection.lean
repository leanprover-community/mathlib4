/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.CategoryTheory.Localization.Bousfield
import Mathlib.CategoryTheory.SmallObject.Iteration.Basic

/-!
# The Orthogonal-reflection construction

Given `W : MorphismProperty C` (which should be small) and assuming the existence
of certain colimits in `C`, we construct a morphism `toSucc W Z : Z ⟶ succ W Z` for
any `Z : C`. This morphism belongs to `LeftBousfield.W W.isLocal` and
is an isomorphism iff `Z` belongs to `W.isLocal`.

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

universe w v u

namespace CategoryTheory

open Limits Localization

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)

namespace OrthogonalReflection

variable (Z : C)

/-- Given `W : MorphismProperty C` and `Z : C`, this is the index type
parametrising the data of a morphism `f : X ⟶ Y` satisfying `W`
and a morphism `X ⟶ Z`. -/
def D₁ : Type _ := Σ (f : W.toSet), f.1.left ⟶ Z

variable {W Z} in
/-- If `d : D₁ W Z` corresponds to the data of `f : X ⟶ Y` satisfying `W` and
of a morphism `X ⟶ Z`, this is the object `X`. -/
def D₁.obj₁ (d : D₁ W Z) : C := d.1.1.left

variable {W Z} in
/-- If `d : D₁ W Z` corresponds to the data of `f : X ⟶ Y` satisfying `W` and
of a morphism `X ⟶ Z`, this is the object `Y`. -/
def D₁.obj₂ (d : D₁ W Z) : C := d.1.1.right

variable [HasCoproduct (D₁.obj₁ (W := W) (Z := Z))]

/-- Considering all diagrams consisting of a morphism `f : X ⟶ Y` satisfying `W`
and of a morphism `d : X ⟶ Z`, this is the morphism from the coproduct of
all these `X` objects to `Z` given by these morphisms `d`. -/
noncomputable abbrev D₁.l : ∐ (obj₁ (W := W) (Z := Z)) ⟶ Z :=
  Sigma.desc (fun d ↦ d.2)

variable {W Z} in
/-- The inclusion of a summand in `∐ obj₁`. -/
noncomputable abbrev D₁.ιLeft {X Y : C} (f : X ⟶ Y) (hf : W f) (g : X ⟶ Z) :
    X ⟶ ∐ obj₁ (W := W) (Z := Z) :=
  Sigma.ι (obj₁ (W := W) (Z := Z)) ⟨⟨Arrow.mk f, hf⟩, g⟩

variable {W Z} in
@[reassoc]
lemma D₁.ιLeft_comp_l {X Y : C} (f : X ⟶ Y) (hf : W f) (g : X ⟶ Z) :
    D₁.ιLeft f hf g ≫ D₁.l W Z = g :=
  Sigma.ι_desc _ _

section

variable [HasCoproduct (D₁.obj₂ (W := W) (Z := Z))]

/-- The coproduct of all the morphisms `f` indexed by all diagrams
consisting of a morphism `f : X ⟶ Y` satisfying `W` and of a morphism `d : X ⟶ Z`. -/
noncomputable abbrev D₁.t : ∐ (obj₁ (W := W) (Z := Z)) ⟶ ∐ (obj₂ (W := W) (Z := Z)) :=
  Limits.Sigma.map (fun d ↦ d.1.1.hom)

variable {W Z} in
/-- The inclusion of a summand in `∐ obj₂`. -/
noncomputable abbrev D₁.ιRight {X Y : C} (f : X ⟶ Y) (hf : W f) (g : X ⟶ Z) :
    Y ⟶ ∐ (obj₂ (W := W) (Z := Z)) :=
  Sigma.ι (obj₂ (W := W) (Z := Z)) ⟨⟨Arrow.mk f, hf⟩, g⟩

variable {W Z} in
@[reassoc]
lemma D₁.ι_comp_t (d : D₁ W Z) :
    Sigma.ι _ d ≫ D₁.t W Z = d.1.1.hom ≫ Sigma.ι obj₂ d := by
  apply ι_colimMap

variable {W Z} in
@[reassoc]
lemma D₁.ιLeft_comp_t {X Y : C} (f : X ⟶ Y) (hf : W f) (g : X ⟶ Z) :
    D₁.ιLeft f hf g ≫ D₁.t W Z = f ≫ D₁.ιRight f hf g := by
  apply ι_colimMap

variable [HasPushouts C]

/-- The intermediate object in the definition of the morphism `toSucc W Z : Z ⟶ succ W Z`.
It is the pushout of the following square:
```lean
∐ D₁.obj₁ ⟶ ∐ D₁.obj₂
   |           |
   v           v
   Z      ⟶   step W Z
```
where the coproduct is taken over all the diagram consisting of a morphism `f : X ⟶ Y`
satisfying `W` and a morphism `X ⟶ Z`. The top map is the coproduct of all of these `f`.
-/
noncomputable abbrev step := pushout (D₁.t W Z) (D₁.l W Z)

/-- The canonical map from `Z` to the pushout of `D₁.t W Z` and `D₁.l W Z`. -/
noncomputable abbrev toStep : Z ⟶ step W Z := pushout.inr _ _

/-- The index type parametrising the data of two morphisms `g₁ g₂ : Y ⟶ step W Z`, and
a map `f : X ⟶ Y` satisfying `W` such that `f ≫ g₁ = f ≫ g₂`. -/
def D₂ : Type _ :=
  Σ (f : W.toSet),
    { pq : (f.1.right ⟶ step W Z) × (f.1.right ⟶ step W Z) // f.1.hom ≫ pq.1 = f.1.hom ≫ pq.2 }

/-- The shape of the multicoequalizer of all pairs of morphisms `g₁ g₂ : Y ⟶ step W Z` with
a `f : X ⟶ Y` satisfying `W` such that `f ≫ g₁ = f ≫ g₂`. -/
@[simps]
def D₂.multispanShape : MultispanShape where
  L := D₂ W Z
  R := Unit
  fst _ := .unit
  snd _ := .unit

/-- The diagram of the multicoequalizer of all pair of morphisms `g₁ g₂ : Y ⟶ step W Z` with
a `f : X ⟶ Y` satisfying `W` such that `f ≫ g₁ = f ≫ g₂`. -/
@[simps]
noncomputable def D₂.multispanIndex : MultispanIndex (multispanShape W Z) C where
  left d := d.1.1.right
  right _ := step W Z
  fst d := d.2.1.1
  snd d := d.2.1.2

variable [HasMulticoequalizer (D₂.multispanIndex W Z)]

/-- The object `succ W Z` is the multicoequalizer of all pairs of morphisms
 `g₁ g₂ : Y ⟶ step W Z` with a `f : X ⟶ Y` satisfying `W` such that `f ≫ g₁ = f ≫ g₂`. -/
noncomputable abbrev succ := multicoequalizer (D₂.multispanIndex W Z)

/-- The projection from `Z` to the multicoequalizer of all morphisms `g₁ g₂ : Y ⟶ step W Z` with
a `f : X ⟶ Y` satisfying `W` such that `f ≫ g₁ = f ≫ g₂`. -/
noncomputable abbrev fromStep : step W Z ⟶ succ W Z :=
  Multicoequalizer.π (D₂.multispanIndex W Z) .unit

variable {W Z} in
@[reassoc]
lemma D₂.condition {X Y : C} (f : X ⟶ Y) (hf : W f)
    {g₁ g₂ : Y ⟶ step W Z} (h : f ≫ g₁ = f ≫ g₂) :
      g₁ ≫ fromStep W Z = g₂ ≫ fromStep W Z :=
  Multicoequalizer.condition (D₂.multispanIndex W Z)
    ⟨⟨Arrow.mk f, hf⟩, ⟨g₁, g₂⟩, h⟩

/-- The morphism `Z ⟶ succ W Z`. -/
noncomputable abbrev toSucc : Z ⟶ succ W Z := toStep W Z ≫ fromStep W Z

variable {W Z} in
lemma toSucc_injectivity {X Y : C} (f : X ⟶ Y) (hf : W f)
    (g₁ g₂ : Y ⟶ Z) (hg : f ≫ g₁ = f ≫ g₂) :
    g₁ ≫ toSucc W Z = g₂ ≫ toSucc W Z := by
  simpa using D₂.condition f hf (g₁ := g₁ ≫ toStep W Z) (g₂ := g₂ ≫ toStep W Z)
    (by simp [reassoc_of% hg])

variable {W Z} in
lemma toSucc_surjectivity {X Y : C} (f : X ⟶ Y) (hf : W f) (g : X ⟶ Z) :
    ∃ (g' : Y ⟶ succ W Z), f ≫ g' = g ≫ toSucc W Z :=
  ⟨D₁.ιRight f hf g ≫ pushout.inl _ _ ≫ fromStep W Z, by
    simp [← D₁.ιLeft_comp_t_assoc, pushout.condition_assoc]⟩

lemma leftBousfieldW_isLocal_toSucc :
    LeftBousfield.W W.isLocal (toSucc W Z) := by
  refine fun T hT ↦ ⟨fun φ₁ φ₂ h ↦ ?_, fun g ↦ ?_⟩
  · ext ⟨⟩
    simp only [Category.assoc] at h
    dsimp
    ext d
    · apply (hT d.1.1.hom d.1.2).1
      simp only [← D₁.ι_comp_t_assoc, pushout.condition_assoc, h]
    · exact h
  · choose f hf using fun (d : D₁ W Z) ↦ (hT d.1.1.hom d.1.2).2 (d.2 ≫ g)
    exact ⟨Multicoequalizer.desc _ _ (fun ⟨⟩ ↦ pushout.desc (Sigma.desc f) g)
      (fun d ↦ (hT d.1.1.hom d.1.2).1 (by simp [reassoc_of% d.2.2])), by simp⟩

lemma isIso_toSucc_iff :
    IsIso (toSucc W Z) ↔ W.isLocal Z := by
  refine ⟨fun _ X Y f hf ↦ ?_, fun hZ ↦ ?_⟩
  · refine ⟨fun g₁ g₂ h ↦ ?_, fun g ↦ ?_⟩
    · simpa [← cancel_mono (toSucc W Z)] using
        D₂.condition f hf (g₁ := g₁ ≫ toStep W Z) (g₂ := g₂ ≫ toStep W Z)
          (by simp [reassoc_of% h])
    · have hZ := IsIso.hom_inv_id (toSucc W Z)
      simp only [Category.assoc] at hZ
      exact ⟨D₁.ιRight f hf g ≫ pushout.inl _ _ ≫ fromStep W Z ≫ inv (toSucc W Z),
        by simp [← D₁.ιLeft_comp_t_assoc, pushout.condition_assoc, hZ]⟩
  · obtain ⟨f, hf⟩ := (leftBousfieldW_isLocal_toSucc W Z _ hZ).2 (𝟙 _)
    dsimp at hf
    refine ⟨f, hf, ?_⟩
    ext ⟨⟩
    dsimp
    ext d
    · simp only [Category.assoc] at hf
      simp only [Category.comp_id, ← Category.assoc]
      refine D₂.condition _ d.1.2 ?_
      rw [Category.assoc, Category.assoc, Category.assoc]
      rw [← D₁.ι_comp_t_assoc, pushout.condition_assoc, reassoc_of% hf,
        ← D₁.ι_comp_t_assoc, pushout.condition]
    · simp [reassoc_of% hf]

end

open SmallObject

variable [HasPushouts C]
  [∀ Z, HasCoproduct (D₁.obj₁ (W := W) (Z := Z))]
  [∀ Z, HasCoproduct (D₁.obj₂ (W := W) (Z := Z))]
  [∀ Z, HasMulticoequalizer (D₂.multispanIndex W Z)]

/-- The successor structure of the orthogonal-reflection construction. -/
noncomputable def succStruct (Z₀ : C) : SuccStruct C where
  X₀ := Z₀
  succ Z := succ W Z
  toSucc Z := toSucc W Z

end OrthogonalReflection

end CategoryTheory
