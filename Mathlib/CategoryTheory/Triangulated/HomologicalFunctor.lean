/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Shift.ShiftSequence
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.CategoryTheory.Triangulated.Subcategory

/-! # Homological functors

In this file, given a functor `F : C ⥤ A` from a pretriangulated category to
an abelian category, we define the type class `F.IsHomological`, which is the property
that `F` sends distinguished triangles in `C` to exact sequences in `A`.

If `F` has been endowed with `[F.ShiftSequence ℤ]`, then we may think
of the functor `F` as a `H^0`, and then the `H^n` functors are the functors `F.shift n : C ⥤ A`:
we have isomorphisms `(F.shift n).obj X ≅ F.obj (X⟦n⟧)`, but through the choice of this
"shift sequence", the user may provide functors with better definitional properties.

Given a triangle `T` in `C`, we define a connecting homomorphism
`F.homologySequenceδ T n₀ n₁ h : (F.shift n₀).obj T.obj₃ ⟶ (F.shift n₁).obj T.obj₁`
under the assumption `h : n₀ + 1 = n₁`. When `T` is distinguished, this connecting
homomorphism is part of a long exact sequence
`... ⟶ (F.shift n₀).obj T.obj₁ ⟶ (F.shift n₀).obj T.obj₂ ⟶ (F.shift n₀).obj T.obj₃ ⟶ ...`

The exactness of this long exact sequence is given by three lemmas
`F.homologySequence_exact₁`, `F.homologySequence_exact₂` and `F.homologySequence_exact₃`.

If `F` is a homological functor, we define the strictly full triangulated subcategory
`F.homologicalKernel`: it consists of objects `X : C` such that for all `n : ℤ`,
`(F.shift n).obj X` (or `F.obj (X⟦n⟧)`) is zero. We show that a morphism `f` in `C`
belongs to `F.homologicalKernel.W` (i.e. the cone of `f` is in this kernel) iff
`(F.shift n).map f` is an isomorphism for all `n : ℤ`.

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

lemma isHomological_of_localization (L : C ⥤ D)
    [L.CommShift ℤ] [L.IsTriangulated] [L.mapArrow.EssSurj] (F : D ⥤ A)
    (G : C ⥤ A) (e : L ⋙ F ≅ G) [G.IsHomological] :
    F.IsHomological := by
  have : F.PreservesZeroMorphisms := preservesZeroMorphisms_of_map_zero_object
    (F.mapIso L.mapZeroObject.symm ≪≫ e.app _ ≪≫ G.mapZeroObject)
  have : (L ⋙ F).IsHomological := IsHomological.of_iso e.symm
  refine IsHomological.mk' _ (fun T hT => ?_)
  rw [L.distTriang_iff] at hT
  obtain ⟨T₀, e, hT₀⟩ := hT
  exact ⟨L.mapTriangle.obj T₀, e, (L ⋙ F).map_distinguished_exact _ hT₀⟩

section

variable [F.IsHomological] [F.ShiftSequence ℤ] (T T' : Triangle C) (hT : T ∈ distTriang C)
  (hT' : T' ∈ distTriang C) (φ : T ⟶ T') (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁)

/-- The connecting homomorphism in the long exact sequence attached to an homological
functor and a distinguished triangle. -/
noncomputable def homologySequenceδ :
    (F.shift n₀).obj T.obj₃ ⟶ (F.shift n₁).obj T.obj₁ :=
  F.shiftMap T.mor₃ n₀ n₁ (by rw [add_comm 1, h])

variable {T T'}

@[reassoc]
lemma homologySequenceδ_naturality :
    (F.shift n₀).map φ.hom₃ ≫ F.homologySequenceδ T' n₀ n₁ h =
      F.homologySequenceδ T n₀ n₁ h ≫ (F.shift n₁).map φ.hom₁ := by
  dsimp only [homologySequenceδ]
  rw [← shiftMap_comp', ← φ.comm₃, shiftMap_comp]

variable (T)

@[reassoc]
lemma comp_homologySequenceδ :
    (F.shift n₀).map T.mor₂ ≫ F.homologySequenceδ T n₀ n₁ h = 0 := by
  dsimp only [homologySequenceδ]
  rw [← F.shiftMap_comp', comp_distTriang_mor_zero₂₃ _ hT, shiftMap_zero]

@[reassoc]
lemma homologySequenceδ_comp :
    F.homologySequenceδ T n₀ n₁ h ≫ (F.shift n₁).map T.mor₁ = 0 := by
  dsimp only [homologySequenceδ]
  rw [← F.shiftMap_comp, comp_distTriang_mor_zero₃₁ _ hT, shiftMap_zero]

@[reassoc]
lemma homologySequence_comp  :
    (F.shift n₀).map T.mor₁ ≫ (F.shift n₀).map T.mor₂ = 0 := by
  rw [← Functor.map_comp, comp_distTriang_mor_zero₁₂ _ hT, Functor.map_zero]

attribute [local simp] smul_smul

lemma homologySequence_exact₂ :
    (ShortComplex.mk _ _ (F.homologySequence_comp T hT n₀)).Exact := by
  refine' ShortComplex.exact_of_iso _ (F.map_distinguished_exact _
    (Triangle.shift_distinguished _ hT n₀))
  exact ShortComplex.isoMk ((F.isoShift n₀).app _)
    (n₀.negOnePow • ((F.isoShift n₀).app _)) ((F.isoShift n₀).app _) (by simp) (by simp)

lemma homologySequence_exact₃ :
    (ShortComplex.mk _ _ (F.comp_homologySequenceδ T hT _ _ h)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (F.homologySequence_exact₂ _ (rot_of_distTriang _ hT) n₀)
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    ((F.shiftIso 1 n₀ n₁ (by linarith)).app _) (by simp) (by simp [homologySequenceδ, shiftMap])

lemma homologySequence_exact₁ :
    (ShortComplex.mk _ _ (F.homologySequenceδ_comp T hT _ _ h)).Exact := by
  refine' ShortComplex.exact_of_iso _ (F.homologySequence_exact₂ _ (inv_rot_of_distTriang _ hT) n₁)
  refine' ShortComplex.isoMk (-((F.shiftIso (-1) n₁ n₀ (by linarith)).app _))
    (Iso.refl _) (Iso.refl _) _ (by simp)
  dsimp
  simp only [homologySequenceδ, neg_comp, map_neg, comp_id,
    F.shiftIso_hom_app_comp_shiftMap_of_add_eq_zero T.mor₃ (-1) (neg_add_self 1) n₀ n₁ (by omega)]

lemma homologySequence_epi_shift_map_mor₁_iff :
    Epi ((F.shift n₀).map T.mor₁) ↔ (F.shift n₀).map T.mor₂ = 0 :=
  (F.homologySequence_exact₂ T hT n₀).epi_f_iff

lemma homologySequence_mono_shift_map_mor₁_iff :
    Mono ((F.shift n₁).map T.mor₁) ↔ F.homologySequenceδ T n₀ n₁ h = 0 :=
  (F.homologySequence_exact₁ T hT n₀ n₁ h).mono_g_iff

lemma homologySequence_epi_shift_map_mor₂_iff :
    Epi ((F.shift n₀).map T.mor₂) ↔ F.homologySequenceδ T n₀ n₁ h = 0 :=
  (F.homologySequence_exact₃ T hT n₀ n₁ h).epi_f_iff

lemma homologySequence_mono_shift_map_mor₂_iff :
    Mono ((F.shift n₀).map T.mor₂) ↔ (F.shift n₀).map T.mor₁ = 0 :=
  (F.homologySequence_exact₂ T hT n₀).mono_g_iff

lemma mem_homologicalKernel_W_iff {X Y : C} (f : X ⟶ Y) :
    F.homologicalKernel.W f ↔ ∀ (n : ℤ), IsIso ((F.shift n).map f) := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
  apply (F.homologicalKernel.mem_W_iff_of_distinguished _ hT).trans
  have h₁ := fun n => (F.homologySequence_exact₃ _ hT n _ rfl).isZero_X₂_iff
  have h₂ := fun n => F.homologySequence_mono_shift_map_mor₁_iff _ hT n _ rfl
  have h₃ := fun n => F.homologySequence_epi_shift_map_mor₁_iff _ hT n
  dsimp at h₁ h₂ h₃ ⊢
  simp only [mem_homologicalKernel_iff, h₁, ← h₂, ← h₃]
  constructor
  · intro h n
    obtain ⟨m, rfl⟩ : ∃ (m : ℤ), n = m + 1 := ⟨n - 1, by simp⟩
    have := (h (m + 1)).1
    have := (h m).2
    apply isIso_of_mono_of_epi
  · intros
    constructor <;> infer_instance

end

end Functor

end CategoryTheory
