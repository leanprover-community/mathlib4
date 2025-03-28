/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Shift.ShiftSequence
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.Algebra.Homology.ExactSequence

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

variable {C D A : Type*} [Category C] [HasShift C ℤ]
  [Category D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ (n : ℤ), (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D]
  [Category A]

namespace Functor

variable (F : C ⥤ A)

section Pretriangulated

variable [HasZeroObject C] [Preadditive C] [∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive]
  [Pretriangulated C] [Abelian A]

/-- A functor from a pretriangulated category to an abelian category is an homological functor
if it sends distinguished triangles to exact sequences. -/
class IsHomological : Prop extends F.PreservesZeroMorphisms where
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

instance [F.IsHomological] : F.homologicalKernel.P.IsClosedUnderIsomorphisms := by
  dsimp only [homologicalKernel]
  infer_instance

lemma mem_homologicalKernel_iff [F.IsHomological] [F.ShiftSequence ℤ] (X : C) :
    F.homologicalKernel.P X ↔ ∀ (n : ℤ), IsZero ((F.shift n).obj X) := by
  simp only [← fun (n : ℤ) => Iso.isZero_iff ((F.isoShift n).app X)]
  rfl

noncomputable instance (priority := 100) [F.IsHomological] :
    PreservesLimitsOfShape (Discrete WalkingPair) F := by
  suffices ∀ (X₁ X₂ : C), PreservesLimit (pair X₁ X₂) F from
    ⟨fun {X} => preservesLimit_of_iso_diagram F (diagramIsoPair X).symm⟩
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
  have : PreservesBinaryBiproduct X₁ X₂ F := preservesBinaryBiproduct_of_mono_biprodComparison _
  apply Limits.preservesBinaryProduct_of_preservesBinaryBiproduct

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

end Pretriangulated

section

/-- The connecting homomorphism in the long exact sequence attached to an homological
functor and a distinguished triangle. -/
noncomputable def homologySequenceδ
    [F.ShiftSequence ℤ] (T : Triangle C) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (F.shift n₀).obj T.obj₃ ⟶ (F.shift n₁).obj T.obj₁ :=
  F.shiftMap T.mor₃ n₀ n₁ (by rw [add_comm 1, h])

variable {T T'}

@[reassoc]
lemma homologySequenceδ_naturality
    [F.ShiftSequence ℤ] (T T' : Triangle C) (φ : T ⟶ T') (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (F.shift n₀).map φ.hom₃ ≫ F.homologySequenceδ T' n₀ n₁ h =
      F.homologySequenceδ T n₀ n₁ h ≫ (F.shift n₁).map φ.hom₁ := by
  dsimp only [homologySequenceδ]
  rw [← shiftMap_comp', ← φ.comm₃, shiftMap_comp]

variable (T)
variable [HasZeroObject C] [Preadditive C] [∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive]
  [Pretriangulated C] [Abelian A] [F.IsHomological]
variable [F.ShiftSequence ℤ] (T T' : Triangle C) (hT : T ∈ distTriang C)
  (hT' : T' ∈ distTriang C) (φ : T ⟶ T') (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁)

section
include hT
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
  refine ShortComplex.exact_of_iso ?_ (F.map_distinguished_exact _
    (Triangle.shift_distinguished _ hT n₀))
  exact ShortComplex.isoMk ((F.isoShift n₀).app _)
    (n₀.negOnePow • ((F.isoShift n₀).app _)) ((F.isoShift n₀).app _)
    (by dsimp; simp) (by dsimp; simp)

lemma homologySequence_exact₃ :
    (ShortComplex.mk _ _ (F.comp_homologySequenceδ T hT _ _ h)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (F.homologySequence_exact₂ _ (rot_of_distTriang _ hT) n₀)
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    ((F.shiftIso 1 n₀ n₁ (by omega)).app _) (by simp) (by simp [homologySequenceδ, shiftMap])

lemma homologySequence_exact₁ :
    (ShortComplex.mk _ _ (F.homologySequenceδ_comp T hT _ _ h)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (F.homologySequence_exact₂ _ (inv_rot_of_distTriang _ hT) n₁)
  refine ShortComplex.isoMk (-((F.shiftIso (-1) n₁ n₀ (by omega)).app _))
    (Iso.refl _) (Iso.refl _) ?_ (by simp)
  dsimp
  simp only [homologySequenceδ, neg_comp, map_neg, comp_id,
    F.shiftIso_hom_app_comp_shiftMap_of_add_eq_zero T.mor₃ (-1) (neg_add_cancel 1) n₀ n₁ (by omega)]

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
end

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

open ComposableArrows

/-- The exact sequence with six terms starting from `(F.shift n₀).obj T.obj₁` until
`(F.shift n₁).obj T.obj₃` when `T` is a distinguished triangle and `F` a homological functor. -/
@[simp] noncomputable def homologySequenceComposableArrows₅ : ComposableArrows A 5 :=
  mk₅ ((F.shift n₀).map T.mor₁) ((F.shift n₀).map T.mor₂)
    (F.homologySequenceδ T n₀ n₁ h) ((F.shift n₁).map T.mor₁) ((F.shift n₁).map T.mor₂)

include hT in
lemma homologySequenceComposableArrows₅_exact :
    (F.homologySequenceComposableArrows₅ T n₀ n₁ h).Exact :=
  exact_of_δ₀ (F.homologySequence_exact₂ T hT n₀).exact_toComposableArrows
    (exact_of_δ₀ (F.homologySequence_exact₃ T hT n₀ n₁ h).exact_toComposableArrows
      (exact_of_δ₀ (F.homologySequence_exact₁ T hT n₀ n₁ h).exact_toComposableArrows
        (F.homologySequence_exact₂ T hT n₁).exact_toComposableArrows))

variable {T T'}

@[simp] noncomputable def homologySequenceComposableArrows₅_map_of_triangle_map :
    F.homologySequenceComposableArrows₅ T n₀ n₁ h ⟶
    F.homologySequenceComposableArrows₅ T' n₀ n₁ h := by
  refine homMk₅ ((F.shift n₀).map φ.hom₁) ((F.shift n₀).map φ.hom₂) ((F.shift n₀).map φ.hom₃)
    ((F.shift n₁).map φ.hom₁) ((F.shift n₁).map φ.hom₂) ((F.shift n₁).map φ.hom₃) ?_ ?_ ?_ ?_ ?_
  · change (F.shift n₀).map T.mor₁ ≫ (F.shift n₀).map φ.hom₂ =
      (F.shift n₀).map φ.hom₁ ≫ (F.shift n₀).map T'.mor₁
    rw [← map_comp, φ.comm₁, map_comp]
  · change (F.shift n₀).map T.mor₂ ≫ (F.shift n₀).map φ.hom₃ =
      (F.shift n₀).map φ.hom₂ ≫ (F.shift n₀).map T'.mor₂
    rw [← map_comp, φ.comm₂, map_comp]
  · change F.homologySequenceδ T n₀ n₁ h ≫ (F.shift n₁).map φ.hom₁ =
      (F.shift n₀).map φ.hom₃ ≫ F.homologySequenceδ T' n₀ n₁ h
    simp only [homologySequenceδ]
    rw [← Functor.shiftMap_comp, φ.comm₃, ← Functor.shiftMap_comp']
  · change (F.shift n₁).map T.mor₁ ≫ (F.shift n₁).map φ.hom₂ =
      (F.shift n₁).map φ.hom₁ ≫ (F.shift n₁).map T'.mor₁
    rw [← map_comp, φ.comm₁, map_comp]
  · change (F.shift n₁).map T.mor₂ ≫ (F.shift n₁).map φ.hom₃ =
      (F.shift n₁).map φ.hom₂ ≫ (F.shift n₁).map T'.mor₂
    rw [← map_comp, φ.comm₂, map_comp]

variable (T) (G : C ⥤ A) [G.ShiftSequence ℤ]

@[simp] noncomputable def homologySequenceComposableArrows₅_hom_of_natTrans
    (α : ShiftSequenceHom F ℤ G) : F.homologySequenceComposableArrows₅ T n₀ n₁ h ⟶
    G.homologySequenceComposableArrows₅ T n₀ n₁ h := by
  refine homMk₅ ((α.app n₀).app T.obj₁) ((α.app n₀).app T.obj₂) ((α.app n₀).app T.obj₃)
    ((α.app n₁).app T.obj₁) (((α.app n₁).app T.obj₂)) (((α.app n₁).app T.obj₃))
    ((α.app n₀).naturality _ ) ((α.app n₀).naturality _ ) ?_ ((α.app n₁).naturality _ )
    ((α.app n₁).naturality _ )
  change (F.homologySequenceδ T n₀ n₁ h) ≫ (α.app n₁).app T.obj₁ = (α.app n₀).app T.obj₃ ≫
    (G.homologySequenceδ T n₀ n₁ h)
  simp [homologySequenceδ, shiftMap]
  have := α.compatibility 1 n₀ n₁ (by rw [← h, add_comm])
  apply_fun (fun h ↦ h.app T.obj₁) at this
  simp only [comp_obj, NatTrans.comp_app, whiskerLeft_app] at this
  rw [← this]
  simp

@[simp] noncomputable def homologySequenceComposableArrows₅_iso_of_natIso
    (α : ShiftSequenceIso F ℤ G) :
    F.homologySequenceComposableArrows₅ T n₀ n₁ h ≅
    G.homologySequenceComposableArrows₅ T n₀ n₁ h := by
  refine isoMk₅ ((α.app n₀).app T.obj₁) ((α.app n₀).app T.obj₂) ((α.app n₀).app T.obj₃)
    ((α.app n₁).app T.obj₁) (((α.app n₁).app T.obj₂)) (((α.app n₁).app T.obj₃))
    ((α.app n₀).hom.naturality _ ) ((α.app n₀).hom.naturality _ ) ?_ ((α.app n₁).hom.naturality _ )
    ((α.app n₁).hom.naturality _ )
  change (F.homologySequenceδ T n₀ n₁ h) ≫ (α.app n₁).hom.app T.obj₁ = (α.app n₀).hom.app T.obj₃ ≫
    (G.homologySequenceδ T n₀ n₁ h)
  simp [homologySequenceδ, shiftMap]
  have := α.compatibility 1 n₀ n₁ (by rw [← h, add_comm])
  apply_fun (fun h ↦ h.app T.obj₁) at this
  simp only [comp_obj, NatTrans.comp_app, whiskerLeft_app] at this
  rw [← this]
  simp


variable {A' B : Type*} [Category A'] [Category B] (G' : C ⥤ A') [G'.ShiftSequence ℤ]
  (I : A ⥤ B) (J : A' ⥤ B)

variable (H : D ⥤ C) [H.CommShift ℤ] [(H ⋙ F).ShiftSequence ℤ] (T'' : Triangle D)

set_option maxHeartbeats 500000 in
noncomputable def homologySequenceComposableArrows₅_mapTriangle_iso :
    F.homologySequenceComposableArrows₅ (H.mapTriangle.obj T'') n₀ n₁ h ≅
    @Functor.homologySequenceComposableArrows₅ _ _ _ _ _ (H ⋙ F) (ShiftSequence.comp_left F ℤ H)
    T'' n₀ n₁ h := by
  refine isoMk₅ (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_ ?_ ?_
  · simp only [Nat.reduceAdd, mapTriangle_obj, homologySequenceComposableArrows₅, Triangle.mk_obj₁,
    Triangle.mk_obj₂, Triangle.mk_obj₃, Triangle.mk_mor₁, Triangle.mk_mor₂, mk₅.eq_1, mk₄.eq_1,
    mk₃.eq_1, mk₂.eq_1, id_eq, Int.reduceNeg, Int.Nat.cast_ofNat_Int, Nat.cast_ofNat, Int.reduceSub,
    Int.reduceAdd, Fin.zero_eta, Fin.isValue, precomp_obj, Precomp.obj_zero, Fin.mk_one,
    Precomp.obj_one, map', homOfLE_leOfHom, precomp_map, Precomp.map_zero_one, Iso.refl_hom,
    comp_id, id_comp]
    rfl
  · simp only [Nat.reduceAdd, mapTriangle_obj, homologySequenceComposableArrows₅, Triangle.mk_obj₁,
    Triangle.mk_obj₂, Triangle.mk_obj₃, Triangle.mk_mor₁, Triangle.mk_mor₂, mk₅.eq_1, mk₄.eq_1,
    mk₃.eq_1, mk₂.eq_1, id_eq, Int.reduceNeg, Nat.cast_ofNat, Int.Nat.cast_ofNat_Int, Int.reduceSub,
    Int.reduceAdd, Fin.mk_one, Fin.isValue, precomp_obj, Precomp.obj_one, Fin.zero_eta,
    Precomp.obj_zero, Fin.reduceFinMk, map', homOfLE_leOfHom, precomp_map, Iso.refl_hom, comp_id,
    id_comp]
    rfl
  · change F.homologySequenceδ (H.mapTriangle.obj T'') n₀ n₁ h ≫ 𝟙 _ =
      𝟙 _ ≫ @Functor.homologySequenceδ _ _ _ _ _ (H ⋙ F) (ShiftSequence.comp_left F ℤ H)
      T'' n₀ n₁ h
    simp only [mapTriangle_obj, Triangle.mk_obj₃, Triangle.mk_obj₁, homologySequenceδ, shiftMap,
      Triangle.mk_mor₃, map_comp, assoc, comp_id, id_comp]
    have : @Functor.shiftIso _ _ _ _ (H ⋙ F) _ _ _ (ShiftSequence.comp_left F ℤ H)
      1 n₀ n₁ (by rw [← h, add_comm]) =
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (CommShift.iso 1) (F.shift n₀) ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (F.shiftIso 1 n₀ n₁ (by rw [← h, add_comm]))
      := rfl
    rw [this]
    simp only [Iso.trans_hom, Iso.symm_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom,
      NatTrans.comp_app, comp_obj, associator_inv_app, whiskerRight_app, associator_hom_app,
      whiskerLeft_app, id_comp]
    erw [id_comp]
    rfl
  · simp only [Nat.reduceAdd, mapTriangle_obj, homologySequenceComposableArrows₅, Triangle.mk_obj₁,
    Triangle.mk_obj₂, Triangle.mk_obj₃, Triangle.mk_mor₁, Triangle.mk_mor₂, mk₅.eq_1, mk₄.eq_1,
    mk₃.eq_1, mk₂.eq_1, id_eq, Int.reduceNeg, Nat.cast_ofNat, Int.reduceSub, Int.reduceAdd,
    Int.Nat.cast_ofNat_Int, Fin.reduceFinMk, precomp_obj, Fin.isValue, map', homOfLE_leOfHom,
    precomp_map, Iso.refl_hom, comp_id, id_comp]
    rfl
  · simp only [Nat.reduceAdd, mapTriangle_obj, homologySequenceComposableArrows₅, Triangle.mk_obj₁,
    Triangle.mk_obj₂, Triangle.mk_obj₃, Triangle.mk_mor₁, Triangle.mk_mor₂, mk₅.eq_1, mk₄.eq_1,
    mk₃.eq_1, mk₂.eq_1, id_eq, Int.reduceNeg, Nat.cast_ofNat, Int.reduceSub, Int.reduceAdd,
    Int.Nat.cast_ofNat_Int, Fin.reduceFinMk, precomp_obj, Fin.isValue, map', homOfLE_leOfHom,
    precomp_map, Iso.refl_hom, comp_id, id_comp]
    rfl

variable {B : Type*} [Category B] (I : A ⥤ B)

noncomputable def homologySequenceComposableArrows₅_comp_iso :
    F.homologySequenceComposableArrows₅ T n₀ n₁ h ⋙ I ≅
    @Functor.homologySequenceComposableArrows₅ _ _ _ _ _ (F ⋙ I) (ShiftSequence.comp_right F ℤ I)
    T n₀ n₁ h := by
  refine isoMk₅ (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_ ?_ ?_
  · simp only [Nat.reduceAdd, homologySequenceComposableArrows₅, mk₅.eq_1, mk₄.eq_1, mk₃.eq_1,
    mk₂.eq_1, id_eq, Int.reduceNeg, Int.Nat.cast_ofNat_Int, Nat.cast_ofNat, Int.reduceSub,
    Int.reduceAdd, Fin.zero_eta, Fin.isValue, comp_obj, precomp_obj, Precomp.obj_zero, Fin.mk_one,
    Precomp.obj_one, map', homOfLE_leOfHom, comp_map, precomp_map, Precomp.map_zero_one,
    Iso.refl_hom, comp_id, id_comp]
    rfl
  · simp only [Nat.reduceAdd, homologySequenceComposableArrows₅, mk₅.eq_1, mk₄.eq_1, mk₃.eq_1,
    mk₂.eq_1, id_eq, Int.reduceNeg, Nat.cast_ofNat, Int.Nat.cast_ofNat_Int, Int.reduceSub,
    Int.reduceAdd, Fin.mk_one, Fin.isValue, comp_obj, precomp_obj, Precomp.obj_one, Fin.zero_eta,
    Precomp.obj_zero, Fin.reduceFinMk, map', homOfLE_leOfHom, comp_map, precomp_map, Iso.refl_hom,
    comp_id, id_comp]
    rfl
  · change I.map (F.homologySequenceδ T n₀ n₁ h) ≫ 𝟙 _ = 𝟙 _ ≫ @Functor.homologySequenceδ _ _ _ _ _
      (F ⋙ I) (ShiftSequence.comp_right F ℤ I) T n₀ n₁ h
    simp only [homologySequenceδ, shiftMap, map_comp, comp_id, id_comp]
    have : @Functor.shiftIso _ _ _ _  (F ⋙ I) _ _ _ (ShiftSequence.comp_right F ℤ I) 1 n₀ n₁
      (by rw [← h, add_comm]) = (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (F.shiftIso 1 n₀ n₁ (by rw [← h, add_comm])) _  := rfl
    rw [this]
    simp only [Iso.trans_hom, Iso.symm_hom, isoWhiskerRight_hom, NatTrans.comp_app, comp_obj,
      associator_inv_app, whiskerRight_app]
    erw [id_comp]; rfl
  · simp only [Nat.reduceAdd, homologySequenceComposableArrows₅, mk₅.eq_1, mk₄.eq_1, mk₃.eq_1,
    mk₂.eq_1, id_eq, Int.reduceNeg, Nat.cast_ofNat, Int.reduceSub, Int.reduceAdd,
    Int.Nat.cast_ofNat_Int, Fin.reduceFinMk, comp_obj, Fin.isValue, precomp_obj, map',
    homOfLE_leOfHom, comp_map, precomp_map, Iso.refl_hom, comp_id, id_comp]
    rfl
  · simp only [Nat.reduceAdd, homologySequenceComposableArrows₅, mk₅.eq_1, mk₄.eq_1, mk₃.eq_1,
    mk₂.eq_1, id_eq, Int.reduceNeg, Nat.cast_ofNat, Int.reduceSub, Int.reduceAdd,
    Int.Nat.cast_ofNat_Int, Fin.reduceFinMk, comp_obj, Fin.isValue, precomp_obj, map',
    homOfLE_leOfHom, comp_map, precomp_map, Iso.refl_hom, comp_id, id_comp]
    rfl

end

end Functor

end CategoryTheory
