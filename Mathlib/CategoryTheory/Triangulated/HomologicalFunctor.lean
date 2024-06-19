/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Shift.ShiftSequence
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.CategoryTheory.Triangulated.Subcategory

/-! # Homological functors

In this file, given a functor `F : C ⥤ A` from a pretriangulated category to
an abelian category, we define the type class `F.IsHomological`, which is the property
that `F` sends distinguished triangles in `C` to exact sequences in `A`.

If `F` is a homological functor, we define the strictly full triangulated subcategory
`F.homologicalKernel`.

Note: depending on the sources, homological functors are sometimes
called cohomological functors, while certain authors use "cohomological functors"
for "contravariant" functors (i.e. functors `Cᵒᵖ ⥤ A`).

## TODO

* The long exact sequence in homology attached to an homological functor.

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*][verdier1996]

-/

namespace CategoryTheory

open Category Limits Pretriangulated ZeroObject Preadditive

variable {C D A : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]
  [Category D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ (n : ℤ), (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D]
  [Category A] [Abelian A]

namespace Functor

variable (F : C ⥤ A)

/-- A functor from a pretriangulated category to an abelian category is an homological functor
if it sends distinguished triangles to exact sequences. -/
class IsHomological extends F.PreservesZeroMorphisms : Prop where
  exact (T : Triangle C) (hT : T ∈ distTriang C) :
    ((shortComplexOfDistTriangle T hT).map F).Exact

lemma map_distinguished_exact [F.IsHomological] (T : Triangle C) (hT : T ∈ distTriang C) :
    ((shortComplexOfDistTriangle T hT).map F).Exact :=
  IsHomological.exact _ hT

instance (L : C ⥤ D) (F : D ⥤ A) [L.CommShift ℤ] [L.IsTriangulated] [F.IsHomological] :
    (L ⋙ F).IsHomological where
  exact T hT := F.map_distinguished_exact _ (L.map_distinguished T hT)

lemma IsHomological.mk' [F.PreservesZeroMorphisms]
    (hF : ∀ (T : Pretriangulated.Triangle C) (hT : T ∈ distTriang C),
      ∃ (T' : Pretriangulated.Triangle C) (e : T ≅ T'),
      ((shortComplexOfDistTriangle T' (isomorphic_distinguished _ hT _ e.symm)).map F).Exact) :
    F.IsHomological where
  exact T hT := by
    obtain ⟨T', e, h'⟩ := hF T hT
    exact (ShortComplex.exact_iff_of_iso
      (F.mapShortComplex.mapIso ((shortComplexOfDistTriangleIsoOfIso e hT)))).2 h'

variable [F.IsHomological]

lemma IsHomological.of_iso {F₁ F₂ : C ⥤ A} [F₁.IsHomological] (e : F₁ ≅ F₂) :
    F₂.IsHomological :=
  have := preservesZeroMorphisms_of_iso e
  ⟨fun T hT => ShortComplex.exact_of_iso (ShortComplex.mapNatIso _ e)
    (F₁.map_distinguished_exact T hT)⟩

/-- The kernel of a homological functor `F : C ⥤ A` is the strictly full
triangulated subcategory consisting of objects `X` such that
for all `n : ℤ`, `F.obj (X⟦n⟧)` is zero. -/
def homologicalKernel [F.IsHomological] :
    Triangulated.Subcategory C := Triangulated.Subcategory.mk'
  (fun X => ∀ (n : ℤ), IsZero (F.obj (X⟦n⟧)))
  (fun n => by
    rw [IsZero.iff_id_eq_zero, ← F.map_id, ← Functor.map_id,
      id_zero, Functor.map_zero, Functor.map_zero])
  (fun X a hX b => IsZero.of_iso (hX (a + b)) (F.mapIso ((shiftFunctorAdd C a b).app X).symm))
  (fun T hT h₁ h₃ n => (F.map_distinguished_exact _
    (Triangle.shift_distinguished T hT n)).isZero_of_both_zeros
      (IsZero.eq_of_src (h₁ n) _ _) (IsZero.eq_of_tgt (h₃ n) _ _))

instance [F.IsHomological] : ClosedUnderIsomorphisms F.homologicalKernel.P := by
  dsimp only [homologicalKernel]
  infer_instance

lemma mem_homologicalKernel_iff [F.IsHomological] [F.ShiftSequence ℤ] (X : C) :
    F.homologicalKernel.P X ↔ ∀ (n : ℤ), IsZero ((F.shift n).obj X) := by
  simp only [← fun (n : ℤ) => Iso.isZero_iff ((F.isoShift n).app X)]
  rfl

noncomputable instance (priority := 100) [F.IsHomological] :
    PreservesLimitsOfShape (Discrete WalkingPair) F := by
  suffices ∀ (X₁ X₂ : C), PreservesLimit (pair X₁ X₂) F from
    ⟨fun {X} => preservesLimitOfIsoDiagram F (diagramIsoPair X).symm⟩
  intro X₁ X₂
  have : HasBinaryBiproduct (F.obj X₁) (F.obj X₂) := HasBinaryBiproducts.has_binary_biproduct _ _
  have : Mono (F.biprodComparison X₁ X₂) := by
    rw [mono_iff_cancel_zero]
    intro Z f hf
    let S := (ShortComplex.mk _ _ (biprod.inl_snd (X := X₁) (Y := X₂))).map F
    have : Mono S.f := by dsimp [S]; infer_instance
    have ex : S.Exact := F.map_distinguished_exact _ (binaryBiproductTriangle_distinguished X₁ X₂)
    obtain ⟨g, rfl⟩ := ex.lift' f (by simpa using hf =≫ biprod.snd)
    dsimp [S] at hf ⊢
    replace hf := hf =≫ biprod.fst
    simp only [assoc, biprodComparison_fst, zero_comp, ← F.map_comp, biprod.inl_fst,
      F.map_id, comp_id] at hf
    rw [hf, zero_comp]
  have : PreservesBinaryBiproduct X₁ X₂ F := preservesBinaryBiproductOfMonoBiprodComparison _
  apply Limits.preservesBinaryProductOfPreservesBinaryBiproduct

instance (priority := 100) [F.IsHomological] : F.Additive :=
  F.additive_of_preserves_binary_products

end Functor

end CategoryTheory
