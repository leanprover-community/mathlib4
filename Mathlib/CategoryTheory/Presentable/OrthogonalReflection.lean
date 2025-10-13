/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
import Mathlib.CategoryTheory.Localization.Bousfield
import Mathlib.CategoryTheory.SmallObject.TransfiniteIteration

/-!
# The Orthogonal-reflection construction

Given `W : MorphismProperty C` (which should be small) and assuming the existence
of certain colimits in `C`, we construct a morphism `toSucc W Z : Z ⟶ succ W Z` for
any `Z : C`. This morphism belongs to `LeftBousfield.W W.rightOrthogonal` and
has the property that for any morphism `f : X ⟶ Y` satisfying `W`,
any defect of bijectivity of the precomposition `(Y ⟶ Z) → (X ⟶ Z)` disappear
in the map `(Y ⟶ succ W Z) ⟶ (X ⟶ succ W Z)` (see lemmas `toSucc_surjectivity` and
`toSucc_injectivity`).

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

universe w v u

namespace CategoryTheory

open Limits Localization

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)

namespace OrthogonalReflection

variable (Z : C)

section

/-- The index type parametrising the data of a morphism `f : X ⟶ Y` satisfying `W`
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
    X ⟶ ∐ (obj₁ (W := W) (Z := Z)) :=
  Sigma.ι (obj₁ (W := W) (Z := Z)) ⟨⟨Arrow.mk f, hf⟩, g⟩

variable {W Z} in
@[reassoc]
lemma D₁.ιLeft_comp_l {X Y : C} (f : X ⟶ Y) (hf : W f) (g : X ⟶ Z) :
    D₁.ιLeft f hf g ≫ D₁.l W Z = g := by
  apply Sigma.ι_desc

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
lemma D₁.ιLeft_comp_t {X Y : C} (f : X ⟶ Y) (hf : W f) (g : X ⟶ Z) :
    D₁.ιLeft f hf g ≫ D₁.t W Z = f ≫ D₁.ιRight f hf g := by
  apply ι_colimMap

variable [HasPushouts C]

/-- The canonical map from `Z` to the pushout of `D₁.t W Z` and `D₁.l W Z`. -/
noncomputable abbrev toColimit₁ : Z ⟶ pushout (D₁.t W Z) (D₁.l W Z) := pushout.inr _ _

end

section

/-- The index type parametrising the data of two morphisms `g₁ g₂ : Y ⟶ Z`, and
a map `f : X ⟶ Y` satisfying `W` such that `f ≫ g₁ = f ≫ g₂`. -/
def D₂ : Type _ :=
  Σ (f : W.toSet),
    { pq : (f.1.right ⟶ Z) × (f.1.right ⟶ Z) // f.1.hom ≫ pq.1 = f.1.hom ≫ pq.2 }

/-- The shape of the multicoequalizer of all morphisms `g₁ g₂ : Y ⟶ Z` with
a `f : X ⟶ Y` satisfying `W` such that `f ≫ g₁ = f ≫ g₂`. -/
@[simps]
def D₂.multispanShape : MultispanShape where
  L := D₂ W Z
  R := Unit
  fst _ := .unit
  snd _ := .unit

/-- The diagram of the multicoequalizer of all morphisms `g₁ g₂ : Y ⟶ Z` with
a `f : X ⟶ Y` satisfying `W` such that `f ≫ g₁ = f ≫ g₂`. -/
@[simps]
def D₂.multispanIndex : MultispanIndex (multispanShape W Z) C where
  left d := d.1.1.right
  right _ := Z
  fst d := d.2.1.1
  snd d := d.2.1.2

variable [HasMulticoequalizer (D₂.multispanIndex W Z)]

/-- The projection from `Z` to the multicoequalizer of all morphisms `g₁ g₂ : Y ⟶ Z` with
a `f : X ⟶ Y` satisfying `W` such that `f ≫ g₁ = f ≫ g₂`. -/
noncomputable abbrev toColimit₂ : Z ⟶ multicoequalizer (D₂.multispanIndex W Z) :=
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

/-- The pushout of the two constructions `toColimit₁ W Z` and `toColimit₂ W Z`.
The morphism `toColimit₁ W Z : toColimit₁ : Z ⟶ pushout (D₁.t W Z) (D₁.l W Z)` allows
to "extend" any morphism `X ⟶ Z` to `Y ⟶ pushout (D₁.t W Z) (D₁.l W Z)` for any `f : X ⟶ Y`
satisfying `W` (see `toSucc_surjectivity`),
while `toColimit₂ W Z : Z ⟶ multicoequalizer (D₂.multispanIndex W Z)` allows
to "coequalize" two morphisms `g₁ g₂ : Y ⟶ Z` such that `f ≫ g₁ = f ≫ g₂` with `f : X ⟶ Y`
satisfying `W` (see `toSucc_injectivity`). -/
noncomputable abbrev succ : C := pushout (toColimit₁ W Z) (toColimit₂ W Z)

/-- The morphism `Z ⟶ succ W Z`. -/
noncomputable def toSucc : Z ⟶ succ W Z := toColimit₁ W Z ≫ pushout.inl _ _

@[reassoc]
lemma toColimit₁_inl : toColimit₁ W Z ≫ pushout.inl _ _ = toSucc W Z := rfl

@[reassoc]
lemma toColimit₂_inr : toColimit₂ W Z ≫ pushout.inr _ _ = toSucc W Z := pushout.condition.symm

variable {W Z} in
lemma toSucc_surjectivity {X Y : C} (f : X ⟶ Y) (hf : W f) (g : X ⟶ Z) :
    ∃ (g' : Y ⟶ succ W Z), f ≫ g' = g ≫ toSucc W Z :=
  ⟨D₁.ιRight f hf g ≫ pushout.inl _ _ ≫ pushout.inl _ _, by
    simp [← D₁.ιLeft_comp_t_assoc, pushout.condition_assoc, toColimit₁_inl]⟩

variable {W Z} in
lemma toSucc_injectivity {X Y : C} (f : X ⟶ Y) (hf : W f)
    (g₁ g₂ : Y ⟶ Z) (hg : f ≫ g₁ = f ≫ g₂) :
    g₁ ≫ toSucc W Z = g₂ ≫ toSucc W Z := by
  simp only [← toColimit₂_inr, D₂.condition_assoc _ hf hg]

lemma leftBousfieldW_rightOrthogonal_toSucc :
    LeftBousfield.W W.rightOrthogonal (toSucc W Z) := by
  refine fun T hT ↦ ⟨fun φ₁ φ₂ h ↦ ?_, fun g ↦ ?_⟩
  · ext d
    · apply (hT d.1.1.hom d.1.2).1
      simpa only [← D₁.ιLeft_comp_l_assoc _ d.1.2 d.2, ← toColimit₁_inl_assoc,
        ← pushout.condition_assoc, ι_colimMap_assoc] using d.2 ≫= h
    · simpa [toColimit₁_inl_assoc]
    · simp only [← toColimit₂_inr, Category.assoc] at h
      simpa
  · choose f hf using fun (d : D₁ W Z) ↦ (hT d.1.1.hom d.1.2).2 (d.2 ≫ g)
    refine ⟨pushout.desc (pushout.desc (Sigma.desc f) g (by aesop))
      (Multicoequalizer.desc _ _ (fun _ ↦ g)
        ((fun d ↦ (hT d.1.1.hom d.1.2).1 (by simp [reassoc_of% d.2.2])))) (by simp), ?_⟩
    dsimp
    rw [← toColimit₂_inr_assoc, pushout.inr_desc]
    simp

/-! On page 33 of the book by Adámek and Rosický, it is claimed that the morphism
`toSucc W Z` is an isomorphism iff the object `Z` is orthogonal to `W`, and theorem 1.38
on the same page states that after doing a suitable transfinite iteration, the
construction stops, i.e. we find an object `Z'` such that `toSucc W Z'` is an isomorphism.

Here is a counter-example. Let `Ab` be the category of abelian groups.
Assume `W : MorphismProperty Ab` only contains the multiplication by `2` on `ℤ`.
The abelian group `ℚ` belongs to `W.rightOrthogonal`, but I claim that
the corresponding morphism `toSucc W ℚ` is not an isomorphism. As `ℚ` is already
in `W.rightOrthogonal`, the morphism `toColimit₂` is an isomorphism (there is
nothing to coequalize), so that `toSucc W ℚ` identifies to the morphism `toColimit₁ W Q`,
but the cokernel of this morphism identifies to a (nontrivial) coproduct of copies of `ℤ/2ℤ`.

-/

end

variable [HasPushouts C] [∀ Z, HasCoproduct (D₁.obj₁ (W := W) (Z := Z))]
  [∀ Z, HasCoproduct (D₁.obj₂ (W := W) (Z := Z))]
  [∀ Z, HasMulticoequalizer (D₂.multispanIndex W Z)]

open SmallObject

/-- The successor structure of the orthogonal-reflection construction. -/
noncomputable def succStruct (Z₀ : C) : SuccStruct C where
  X₀ := Z₀
  succ Z := succ W Z
  toSucc Z := toSucc W Z

end OrthogonalReflection

end CategoryTheory
