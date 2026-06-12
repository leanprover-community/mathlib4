/-
Copyright (c) 2024 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Limits.IsConnected
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Comma.StructuredArrow.CommaMap

/-!
# Finality of Projections in Comma Categories

We show that `fst L R` is final if `R` is and that `snd L R` is initial if `L` is.
As a corollary, we show that `Comma L R` with `L : A ⥤ T` and `R : B ⥤ T` is connected if `R` is
final and `A` is connected.

We then use this in a proof that derives finality of `map` between two comma categories
on a quasi-commutative diagram of functors, some of which need to be final.

Finally we prove filteredness of a `Comma L R` and finality of `snd L R`, given that `R` is final
and `A` and `B` are filtered.

## References

* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Lemma 3.4.3 -- 3.4.5
-/

@[expose] public section

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

namespace CategoryTheory

namespace Comma

open Limits Functor CostructuredArrow

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {T : Type u₃} [Category.{v₃} T]
variable (L : A ⥤ T) (R : B ⥤ T)

set_option backward.defeqAttrib.useBackward true in
/-- The functor from the costructured arrow category on `snd L R` over `b : B` to the
costructured arrow category on `L` over `R.obj b`. It is left adjoint to
`costructuredArrowSndInclusion`, see `costructuredArrowSndAdjunction`. -/
@[simps]
def costructuredArrowSndProj (b : B) :
    CostructuredArrow (snd L R) b ⥤ CostructuredArrow L (R.obj b) where
  obj X := CostructuredArrow.mk (X.left.hom ≫ R.map X.hom)
  map f := CostructuredArrow.homMk f.left.left (by
    have h := CostructuredArrow.w f
    dsimp at h ⊢
    rw [reassoc_of% f.left.w, ← R.map_comp, h])

set_option backward.defeqAttrib.useBackward true in
/-- The functor from the costructured arrow category on `L` over `R.obj b` to the costructured
arrow category on `snd L R` over `b : B`, exhibiting the former as a reflective subcategory of
the latter, see `costructuredArrowSndAdjunction`. -/
@[simps]
def costructuredArrowSndInclusion (b : B) :
    CostructuredArrow L (R.obj b) ⥤ CostructuredArrow (snd L R) b where
  obj X := ⟨⟨X.left, b, X.hom⟩, ⟨⟨⟩⟩, 𝟙 b⟩
  map f := CostructuredArrow.homMk ⟨f.left, 𝟙 b, by simp⟩ (by simp)

set_option backward.defeqAttrib.useBackward true in
/-- The functor `costructuredArrowSndProj` is left adjoint to
`costructuredArrowSndInclusion`. -/
@[simps]
def costructuredArrowSndAdjunction (b : B) :
    costructuredArrowSndProj L R b ⊣ costructuredArrowSndInclusion L R b where
  unit :=
    { app X := CostructuredArrow.homMk ⟨𝟙 X.left.left, X.hom, by simp⟩ (by simp)
      naturality _ _ f := by
        ext
        · simp
        · simpa using CostructuredArrow.w f }
  counit := { app X := CostructuredArrow.homMk (𝟙 X.left) (by simp) }
  left_triangle_components X := by ext; simp
  right_triangle_components Y := by ext <;> simp

section Relative

lemma exists_eq_of_isCofiltered_costructuredArrow {b : B}
    [IsCofiltered (CostructuredArrow L (R.obj b))] {a₁ a₂ : A}
    (s₁ : L.obj a₁ ⟶ R.obj b) (s₂ : L.obj a₂ ⟶ R.obj b) :
    ∃ (a : A) (t₁ : a ⟶ a₁) (t₂ : a ⟶ a₂), L.map t₁ ≫ s₁ = L.map t₂ ≫ s₂ := by
  obtain ⟨W, p₁, p₂, -⟩ := IsCofilteredOrEmpty.cone_objs
    (CostructuredArrow.mk s₁) (CostructuredArrow.mk s₂)
  exact ⟨W.left, p₁.left, p₂.left, (CostructuredArrow.w p₁).trans (CostructuredArrow.w p₂).symm⟩

set_option backward.isDefEq.respectTransparency false in
lemma isCofiltered_of_isCofiltered_costructuredArrow [IsCofiltered A] [IsCofiltered B]
    [∀ b, IsCofiltered (CostructuredArrow L (R.obj b))] : IsCofiltered (Comma L R) := by
  have : Nonempty (Comma L R) := by
    obtain ⟨b⟩ := IsCofiltered.nonempty (C := B)
    obtain ⟨X⟩ : Nonempty (CostructuredArrow L (R.obj b)) := IsCofiltered.nonempty
    exact ⟨⟨X.left, b, X.hom⟩⟩
  have : IsCofilteredOrEmpty (Comma L R) := by
    refine ⟨fun j₁ j₂ ↦ ?_, fun j₁ j₂ u v ↦ ?_⟩
    · obtain ⟨Q⟩ : Nonempty (CostructuredArrow L (R.obj (IsCofiltered.min j₁.right j₂.right))) :=
        IsCofiltered.nonempty
      obtain ⟨ia, va₁, va₂, heqa⟩ := exists_eq_of_isCofiltered_costructuredArrow L R
        (Q.hom ≫ R.map (IsCofiltered.minToLeft j₁.right j₂.right)) j₁.hom
      obtain ⟨ib, vb₁, vb₂, heqb⟩ := exists_eq_of_isCofiltered_costructuredArrow L R
        (Q.hom ≫ R.map (IsCofiltered.minToRight j₁.right j₂.right)) j₂.hom
      obtain ⟨i₀, il₀, ir₀, heq⟩ := IsCofiltered.cospan va₁ vb₁
      refine ⟨⟨i₀, IsCofiltered.min j₁.right j₂.right, L.map (il₀ ≫ va₁) ≫ Q.hom⟩,
        ⟨il₀ ≫ va₂, IsCofiltered.minToLeft _ _, ?_⟩,
        ⟨ir₀ ≫ vb₂, IsCofiltered.minToRight _ _, ?_⟩, trivial⟩
      · simp [← heqa]
      · simp only [Functor.map_comp, Category.assoc, ← heqb]
        simp only [← Functor.map_comp_assoc, ← heq]
    · obtain ⟨Q⟩ : Nonempty (CostructuredArrow L (R.obj (IsCofiltered.eq u.right v.right))) :=
        IsCofiltered.nonempty
      obtain ⟨ia, va₁, va₂, heqa⟩ := exists_eq_of_isCofiltered_costructuredArrow L R
        (Q.hom ≫ R.map (IsCofiltered.eqHom u.right v.right)) j₁.hom
      obtain ⟨i₀, α, β, hα, hβ⟩ := IsCofiltered.bowtie u.left (va₂ ≫ v.left) (𝟙 _) va₂
      refine ⟨⟨i₀, IsCofiltered.eq u.right v.right, L.map (β ≫ va₁) ≫ Q.hom⟩,
        ⟨β ≫ va₂, IsCofiltered.eqHom u.right v.right, ?_⟩, ?_⟩
      · simp [← heqa]
      · ext
        · simp only [Category.comp_id] at hβ
          subst hβ
          simpa using hα
        · simp [← IsCofiltered.eq_condition]
  constructor

set_option backward.isDefEq.respectTransparency false in
lemma initial_fst_of_isCofiltered_costructuredArrow [IsCofiltered A] [IsCofiltered B]
    [∀ b, IsCofiltered (CostructuredArrow L (R.obj b))] : (fst L R).Initial := by
  have := isCofiltered_of_isCofiltered_costructuredArrow L R
  rw [Functor.initial_iff_of_isCofiltered]
  refine ⟨fun a ↦ ?_, fun {a} A' s s' ↦ ?_⟩
  · obtain ⟨b⟩ := IsCofiltered.nonempty (C := B)
    obtain ⟨X⟩ : Nonempty (CostructuredArrow L (R.obj b)) := IsCofiltered.nonempty
    exact ⟨⟨IsCofiltered.min a X.left, b, L.map (IsCofiltered.minToRight a X.left) ≫ X.hom⟩,
      ⟨IsCofiltered.minToLeft a X.left⟩⟩
  · exact ⟨⟨_, A'.right, L.map (IsCofiltered.eqHom s s') ≫ A'.hom⟩,
      ⟨IsCofiltered.eqHom s s', 𝟙 A'.right, by simp⟩, IsCofiltered.eq_condition s s'⟩

lemma initial_snd_of_isConnected_costructuredArrow
    [∀ b, IsConnected (CostructuredArrow L (R.obj b))] : (snd L R).Initial where
  out b := by
    have := final_of_adjunction (costructuredArrowSndAdjunction L R b)
    rw [← isConnected_iff_of_final (costructuredArrowSndInclusion L R b)]
    infer_instance

lemma isFiltered_of_isFiltered_structuredArrow [IsFiltered A] [IsFiltered B]
    [∀ a, IsFiltered (StructuredArrow (L.obj a) R)] : IsFiltered (Comma L R) := by
  have (a : Aᵒᵖ) : IsCofiltered (CostructuredArrow R.op (L.op.obj a)) :=
    IsCofiltered.of_equivalence (structuredArrowOpEquivalence R (L.obj a.unop))
  have : IsCofiltered (Comma R.op L.op) := isCofiltered_of_isCofiltered_costructuredArrow _ _
  exact IsFiltered.of_equivalence (opEquiv L R).symm

lemma final_fst_of_isConnected_structuredArrow
    [∀ a, IsConnected (StructuredArrow (L.obj a) R)] : (fst L R).Final := by
  have (a : Aᵒᵖ) : IsConnected (CostructuredArrow R.op (L.op.obj a)) :=
    (isConnected_iff_of_equivalence (structuredArrowOpEquivalence R (L.obj a.unop))).mp
      inferInstance
  have : (snd R.op L.op).Initial := initial_snd_of_isConnected_costructuredArrow _ _
  have : ((opFunctor L R).leftOp ⋙ snd R.op L.op).Initial :=
    initial_equivalence_comp (opEquiv L R).functor.leftOp _
  have : (fst L R).op.Initial := initial_of_natIso <| opFunctorCompSnd _ _
  apply final_of_initial_op

lemma final_snd_of_isFiltered_structuredArrow [IsFiltered A] [IsFiltered B]
    [∀ a, IsFiltered (StructuredArrow (L.obj a) R)] : (snd L R).Final := by
  have (a : Aᵒᵖ) : IsCofiltered (CostructuredArrow R.op (L.op.obj a)) :=
    IsCofiltered.of_equivalence (structuredArrowOpEquivalence R (L.obj a.unop))
  have : (fst R.op L.op).Initial := initial_fst_of_isCofiltered_costructuredArrow _ _
  have : ((opFunctor L R).leftOp ⋙ fst R.op L.op).Initial :=
    initial_equivalence_comp (opEquiv L R).functor.leftOp _
  have : (snd L R).op.Initial := initial_of_natIso <| opFunctorCompFst _ _
  apply final_of_initial_op

end Relative

section NonSmall

instance initial_snd [L.Initial] : (snd L R).Initial :=
  initial_snd_of_isConnected_costructuredArrow L R

instance final_fst [R.Final] : (fst L R).Final :=
  final_fst_of_isConnected_structuredArrow L R

/-- `Comma L R` with `L : A ⥤ T` and `R : B ⥤ T` is connected if `R` is final and `A` is
connected. -/
instance isConnected_comma_of_final [IsConnected A] [R.Final] : IsConnected (Comma L R) := by
  rwa [isConnected_iff_of_final (fst L R)]

/-- `Comma L R` with `L : A ⥤ T` and `R : B ⥤ T` is connected if `L` is initial and `B` is
connected. -/
instance isConnected_comma_of_initial [IsConnected B] [L.Initial] : IsConnected (Comma L R) := by
  rwa [isConnected_iff_of_initial (snd L R)]

end NonSmall

set_option backward.defeqAttrib.useBackward true in
/-- Let the following diagram commute up to isomorphism:

```
      L       R
  A  ---→ T  ←--- B
  |       |       |
  | F     | H     | G
  ↓       ↓       ↓
  A' ---→ T' ←--- B'
      L'      R'
```

Let `F`, `G`, `R` and `R'` be final and `B` be filtered. Then, the induced functor between the comma
categories of the first and second row of the diagram is final. -/
lemma map_final {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B] {T : Type u₃}
    [Category.{v₃} T] {L : A ⥤ T} {R : B ⥤ T} {A' : Type u₄} [Category.{v₄} A'] {B' : Type u₅}
    [Category.{v₅} B'] {T' : Type u₆} [Category.{v₆} T'] {L' : A' ⥤ T'} {R' : B' ⥤ T'} {F : A ⥤ A'}
    {G : B ⥤ B'} {H : T ⥤ T'} (iL : F ⋙ L' ≅ L ⋙ H) (iR : G ⋙ R' ≅ R ⋙ H) [IsFiltered B]
    [R.Final] [R'.Final] [F.Final] [G.Final] :
    (Comma.map iL.hom iR.inv).Final := ⟨fun ⟨i₂, j₂, u₂⟩ => by
  haveI := final_of_natIso iR
  rw [isConnected_iff_of_equivalence (StructuredArrow.commaMapEquivalence iL.hom iR.inv _)]
  have : StructuredArrow.map₂ u₂ iR.hom ≅ StructuredArrow.post j₂ G R' ⋙
      StructuredArrow.map₂ (G := 𝟭 _) (F := 𝟭 _) (R' := R ⋙ H) u₂ iR.hom ⋙
      StructuredArrow.pre _ R H :=
    eqToIso (by
      congr
      · simp
      · ext; simp) ≪≫
    (StructuredArrow.map₂CompMap₂Iso _ _ _ _).symm ≪≫
    isoWhiskerLeft _ ((StructuredArrow.map₂CompMap₂Iso _ _ _ _).symm ≪≫
      isoWhiskerLeft _ (StructuredArrow.preIsoMap₂ _ _ _).symm) ≪≫
    isoWhiskerRight (StructuredArrow.postIsoMap₂ j₂ G R').symm _
  haveI := final_of_natIso this.symm
  rw [IsIso.Iso.inv_inv]
  infer_instance⟩

section Filtered

/-- Let `A` and `B` be filtered categories, `R : B ⥤ T` be final and `L : A ⥤ T`. Then, the
comma category `Comma L R` is filtered. -/
instance isFiltered_of_final [IsFiltered A] [IsFiltered B] [R.Final] : IsFiltered (Comma L R) := by
  have := R.final_iff_isFiltered_structuredArrow.mp inferInstance
  exact isFiltered_of_isFiltered_structuredArrow L R

/-- Let `A` and `B` be cofiltered categories, `L : A ⥤ T` be initial and `R : B ⥤ T`. Then, the
comma category `Comma L R` is cofiltered. -/
lemma isCofiltered_of_initial [IsCofiltered A] [IsCofiltered B] [L.Initial] :
    IsCofiltered (Comma L R) := by
  have := L.initial_iff_isCofiltered_costructuredArrow.mp inferInstance
  exact isCofiltered_of_isCofiltered_costructuredArrow L R

/-- Let `A` and `B` be filtered categories, `R : B ⥤ T` be final and `R : A ⥤ T`. Then, the
projection `snd L R : Comma L R ⥤ B` is final. -/
instance final_snd [IsFiltered A] [IsFiltered B] [R.Final] : (snd L R).Final := by
  have := R.final_iff_isFiltered_structuredArrow.mp inferInstance
  exact final_snd_of_isFiltered_structuredArrow L R

/-- Let `A` and `B` be cofiltered categories, `L : A ⥤ T` be initial and `R : B ⥤ T`. Then, the
projection `fst L R : Comma L R ⥤ A` is initial. -/
instance initial_fst [IsCofiltered A] [IsCofiltered B] [L.Initial] : (fst L R).Initial := by
  have := L.initial_iff_isCofiltered_costructuredArrow.mp inferInstance
  exact initial_fst_of_isCofiltered_costructuredArrow L R

end Filtered

end Comma

end CategoryTheory
