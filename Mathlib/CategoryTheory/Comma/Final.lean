/-
Copyright (c) 2024 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.IsConnected
public import Mathlib.CategoryTheory.Limits.Sifted
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Grothendieck
public import Mathlib.CategoryTheory.Comma.StructuredArrow.CommaMap

/-!
# Finality of Projections in Comma Categories

We show that `fst L R` is final if `R` is and that `snd L R` is initial if `L` is.
As a corollary, we show that `Comma L R` with `L : A ⥤ T` and `R : B ⥤ T` is connected if `R` is
final and `A` is connected.

We then use this in a proof that derives finality of `map` between two comma categories
on a quasi-commutative diagram of functors, some of which need to be final.

Finally we prove filteredness of a `Comma L R` and finality of `snd L R`, given that `R` is final
and `A` and `B` are filtered. More generally, we show that `Comma L R` is filtered and both
projections are final under the weaker, "relative" assumption that `StructuredArrow (L.obj a) R`
is filtered for every `a : A`, together with the dual results for cofiltered categories.

## References

* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Lemma 3.4.3 -- 3.4.5
-/

public section

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

namespace CategoryTheory

namespace Comma

open Limits Functor CostructuredArrow

section Small

variable {A : Type v₁} [Category.{v₁} A]
variable {B : Type v₁} [Category.{v₁} B]
variable {T : Type v₁} [Category.{v₁} T]
variable (L : A ⥤ T) (R : B ⥤ T)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma final_fst_small [R.Final] : (fst L R).Final := by
  rw [Functor.final_iff_isIso_colimit_pre]
  intro G
  let i : colimit G ≅ colimit (fst L R ⋙ G) :=
    colimitIsoColimitGrothendieck L G ≪≫
    (Final.colimitIso (Grothendieck.pre (functor L) R) (grothendieckProj L ⋙ G)).symm ≪≫
    HasColimit.isoOfNatIso (Iso.refl _) ≪≫
    Final.colimitIso (grothendieckPrecompFunctorEquivalence L R).functor (fst L R ⋙ G)
  convert! i.isIso_inv
  apply colimit.hom_ext
  intro ⟨a, b, f⟩
  simp only [colimit.ι_pre, comp_obj, fst_obj, grothendieckPrecompFunctorEquivalence_functor,
    Iso.trans_inv, Iso.symm_inv, Category.assoc, i]
  change _ = colimit.ι (fst L R ⋙ G)
    ((grothendieckPrecompFunctorToComma L R).obj ⟨b, CostructuredArrow.mk f⟩) ≫ _
  simp

end Small

section NonSmall

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {T : Type u₃} [Category.{v₃} T]
variable (L : A ⥤ T) (R : B ⥤ T)

instance final_fst [R.Final] : (fst L R).Final := by
  let sA : A ≌ AsSmall.{max u₁ u₂ u₃ v₁ v₂ v₃} A := AsSmall.equiv
  let sB : B ≌ AsSmall.{max u₁ u₂ u₃ v₁ v₂ v₃} B := AsSmall.equiv
  let sT : T ≌ AsSmall.{max u₁ u₂ u₃ v₁ v₂ v₃} T := AsSmall.equiv
  let L' := sA.inverse ⋙ L ⋙ sT.functor
  let R' := sB.inverse ⋙ R ⋙ sT.functor
  let fC : Comma L R ⥤ Comma L' R' :=
    map (F₁ := sA.functor) (F := sT.functor) (F₂ := sB.functor)
      (isoWhiskerRight sA.unitIso (L ⋙ sT.functor)).hom
      (isoWhiskerRight sB.unitIso (R ⋙ sT.functor)).hom
  have : Final (fst L' R') := final_fst_small _ _
  apply final_of_natIso (F := (fC ⋙ fst L' R' ⋙ sA.inverse))
  exact (Functor.associator _ _ _).symm.trans (Iso.compInverseIso (mapFst _ _))

instance initial_snd [L.Initial] : (snd L R).Initial := by
  have : ((opFunctor L R).leftOp ⋙ fst R.op L.op).Final :=
    final_equivalence_comp (opEquiv L R).functor.leftOp (fst R.op L.op)
  have : (snd L R).op.Final := final_of_natIso (opFunctorCompFst _ _)
  apply initial_of_final_op

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

section Relative

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {T : Type u₃} [Category.{v₃} T]
variable (L : A ⥤ T) (R : B ⥤ T)

/-- Any two morphisms into an object in the image of `R` can be equalized if the relevant
costructured arrow category is cofiltered. -/
private lemma exists_eq_of_isCofiltered_costructuredArrow {b : B}
    [IsCofiltered (CostructuredArrow L (R.obj b))] {a₁ a₂ : A}
    (s₁ : L.obj a₁ ⟶ R.obj b) (s₂ : L.obj a₂ ⟶ R.obj b) :
    ∃ (a : A) (t₁ : a ⟶ a₁) (t₂ : a ⟶ a₂), L.map t₁ ≫ s₁ = L.map t₂ ≫ s₂ := by
  obtain ⟨W, p₁, p₂, -⟩ := IsCofilteredOrEmpty.cone_objs
    (CostructuredArrow.mk s₁) (CostructuredArrow.mk s₂)
  exact ⟨W.left, p₁.left, p₂.left, (CostructuredArrow.w p₁).trans (CostructuredArrow.w p₂).symm⟩

set_option backward.isDefEq.respectTransparency false in
/-- For `Comma L R` to be cofiltered, it suffices that `A` and `B` are cofiltered and that the
costructured arrow categories of `L` over objects in the image of `R` are cofiltered.

This is a relative version of `isCofiltered_of_initial`: by
`Functor.initial_iff_isCofiltered_costructuredArrow`, `L` is initial if and only if
`CostructuredArrow L d` is cofiltered for *all* `d : T`. -/
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
/-- If `A` and `B` are cofiltered and the costructured arrow categories of `L` over objects in
the image of `R` are cofiltered, then `fst L R` is initial.

This is a relative version of `initial_fst`, cf.
`Functor.initial_iff_isCofiltered_costructuredArrow`. -/
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

set_option backward.isDefEq.respectTransparency false in
/-- If `A` and `B` are cofiltered and the costructured arrow categories of `L` over objects in
the image of `R` are cofiltered, then `snd L R` is initial.

This is a relative version of `initial_snd`, cf.
`Functor.initial_iff_isCofiltered_costructuredArrow`. -/
lemma initial_snd_of_isCofiltered_costructuredArrow [IsCofiltered A] [IsCofiltered B]
    [∀ b, IsCofiltered (CostructuredArrow L (R.obj b))] : (snd L R).Initial := by
  have := isCofiltered_of_isCofiltered_costructuredArrow L R
  rw [Functor.initial_iff_of_isCofiltered]
  refine ⟨fun b ↦ ?_, fun {b} A' s s' ↦ ?_⟩
  · obtain ⟨X⟩ : Nonempty (CostructuredArrow L (R.obj b)) := IsCofiltered.nonempty
    exact ⟨⟨X.left, b, X.hom⟩, ⟨𝟙 b⟩⟩
  · obtain ⟨Q⟩ : Nonempty (CostructuredArrow L (R.obj (IsCofiltered.eq s s'))) :=
      IsCofiltered.nonempty
    obtain ⟨ib, vb₁, vb₂, heqb⟩ := exists_eq_of_isCofiltered_costructuredArrow L R
      (Q.hom ≫ R.map (IsCofiltered.eqHom s s')) A'.hom
    refine ⟨⟨ib, IsCofiltered.eq s s', L.map vb₁ ≫ Q.hom⟩,
      ⟨vb₂, IsCofiltered.eqHom s s', by simp [heqb]⟩, ?_⟩
    simpa using IsCofiltered.eq_condition s s'

variable {A : Type u₄} [Category.{v₄} A]
variable {B : Type u₅} [Category.{v₅} B]
variable {T : Type u₆} [Category.{v₆} T]
variable (L : A ⥤ T) (R : B ⥤ T)

/-- For `Comma L R` to be filtered, it suffices that `A` and `B` are filtered and that the
structured arrow categories of `R` under objects in the image of `L` are filtered.

This is a relative version of `isFiltered_of_final`: by
`Functor.final_iff_isFiltered_structuredArrow`, `R` is final if and only if
`StructuredArrow d R` is filtered for *all* `d : T`. -/
lemma isFiltered_of_isFiltered_structuredArrow [IsFiltered A] [IsFiltered B]
    [∀ a, IsFiltered (StructuredArrow (L.obj a) R)] : IsFiltered (Comma L R) := by
  have (a : Aᵒᵖ) : IsCofiltered (CostructuredArrow R.op (L.op.obj a)) :=
    IsCofiltered.of_equivalence (structuredArrowOpEquivalence R (L.obj a.unop))
  have : IsCofiltered (Comma R.op L.op) := isCofiltered_of_isCofiltered_costructuredArrow _ _
  exact IsFiltered.of_equivalence (opEquiv L R).symm

/-- If `A` and `B` are filtered and the structured arrow categories of `R` under objects in the
image of `L` are filtered, then `fst L R` is final.

This is a relative version of `final_fst`, cf. `Functor.final_iff_isFiltered_structuredArrow`. -/
lemma final_fst_of_isFiltered_structuredArrow [IsFiltered A] [IsFiltered B]
    [∀ a, IsFiltered (StructuredArrow (L.obj a) R)] : (fst L R).Final := by
  have (a : Aᵒᵖ) : IsCofiltered (CostructuredArrow R.op (L.op.obj a)) :=
    IsCofiltered.of_equivalence (structuredArrowOpEquivalence R (L.obj a.unop))
  have : (snd R.op L.op).Initial := initial_snd_of_isCofiltered_costructuredArrow _ _
  have : ((opFunctor L R).leftOp ⋙ snd R.op L.op).Initial :=
    initial_equivalence_comp (opEquiv L R).functor.leftOp _
  have : (fst L R).op.Initial := initial_of_natIso <| opFunctorCompSnd _ _
  apply final_of_initial_op

/-- If `A` and `B` are filtered and the structured arrow categories of `R` under objects in the
image of `L` are filtered, then `snd L R` is final.

This is a relative version of `final_snd`, cf. `Functor.final_iff_isFiltered_structuredArrow`. -/
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

section Filtered

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {T : Type u₃} [Category.{v₃} T]
variable (L : A ⥤ T) (R : B ⥤ T)

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
