/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Homology.ImageToKernel
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.CategoryTheory.GradedObject

#align_import algebra.homology.homology from "leanprover-community/mathlib"@"618ea3d5c99240cd7000d8376924906a148bf9ff"

/-!
# The homology of a complex

Given `C : HomologicalComplex V c`, we have `C.cycles' i` and `C.boundaries i`,
both defined as subobjects of `C.X i`.

We show these are functorial with respect to chain maps,
as `cyclesMap' f i` and `boundariesMap f i`.

As a consequence we construct `homologyFunctor' i : HomologicalComplex V c ⥤ V`,
computing the `i`-th homology.

Note: Some definitions (specifically, names containing components `homology`, `cycles`)
in this file have the suffix `'` so as to allow the development of the
new homology API of homological complex (starting from
`Algebra.Homology.ShortComplex.HomologicalComplex`). It is planned that these definitions
shall be removed and replaced by the new API.

-/


universe v u

open CategoryTheory CategoryTheory.Limits

variable {ι : Type*}
variable {V : Type u} [Category.{v} V] [HasZeroMorphisms V]
variable {c : ComplexShape ι} (C : HomologicalComplex V c)

open scoped Classical
open ZeroObject

noncomputable section

namespace HomologicalComplex

section Cycles

variable [HasKernels V]

/-- The cycles at index `i`, as a subobject. -/
abbrev cycles' (i : ι) : Subobject (C.X i) :=
  kernelSubobject (C.dFrom i)
#align homological_complex.cycles HomologicalComplex.cycles'

theorem cycles'_eq_kernelSubobject {i j : ι} (r : c.Rel i j) :
    C.cycles' i = kernelSubobject (C.d i j) :=
  C.kernel_from_eq_kernel r
#align homological_complex.cycles_eq_kernel_subobject HomologicalComplex.cycles'_eq_kernelSubobject

/-- The underlying object of `C.cycles' i` is isomorphic to `kernel (C.d i j)`,
for any `j` such that `Rel i j`. -/
def cycles'IsoKernel {i j : ι} (r : c.Rel i j) : (C.cycles' i : V) ≅ kernel (C.d i j) :=
  Subobject.isoOfEq _ _ (C.cycles'_eq_kernelSubobject r) ≪≫ kernelSubobjectIso (C.d i j)
#align homological_complex.cycles_iso_kernel HomologicalComplex.cycles'IsoKernel

theorem cycles_eq_top {i} (h : ¬c.Rel i (c.next i)) : C.cycles' i = ⊤ := by
  rw [eq_top_iff]
  apply le_kernelSubobject
  rw [C.dFrom_eq_zero h, comp_zero]
#align homological_complex.cycles_eq_top HomologicalComplex.cycles_eq_top

end Cycles

section Boundaries

variable [HasImages V]

/-- The boundaries at index `i`, as a subobject. -/
abbrev boundaries (C : HomologicalComplex V c) (j : ι) : Subobject (C.X j) :=
  imageSubobject (C.dTo j)
#align homological_complex.boundaries HomologicalComplex.boundaries

theorem boundaries_eq_imageSubobject [HasEqualizers V] {i j : ι} (r : c.Rel i j) :
    C.boundaries j = imageSubobject (C.d i j) :=
  C.image_to_eq_image r
#align homological_complex.boundaries_eq_image_subobject HomologicalComplex.boundaries_eq_imageSubobject

/-- The underlying object of `C.boundaries j` is isomorphic to `image (C.d i j)`,
for any `i` such that `Rel i j`. -/
def boundariesIsoImage [HasEqualizers V] {i j : ι} (r : c.Rel i j) :
    (C.boundaries j : V) ≅ image (C.d i j) :=
  Subobject.isoOfEq _ _ (C.boundaries_eq_imageSubobject r) ≪≫ imageSubobjectIso (C.d i j)
#align homological_complex.boundaries_iso_image HomologicalComplex.boundariesIsoImage

theorem boundaries_eq_bot [HasZeroObject V] {j} (h : ¬c.Rel (c.prev j) j) : C.boundaries j = ⊥ := by
  rw [eq_bot_iff]
  refine imageSubobject_le _ 0 ?_
  rw [C.dTo_eq_zero h, zero_comp]
#align homological_complex.boundaries_eq_bot HomologicalComplex.boundaries_eq_bot

end Boundaries

section

variable [HasKernels V] [HasImages V]

theorem boundaries_le_cycles' (C : HomologicalComplex V c) (i : ι) :
    C.boundaries i ≤ C.cycles' i :=
  image_le_kernel _ _ (C.dTo_comp_dFrom i)
#align homological_complex.boundaries_le_cycles HomologicalComplex.boundaries_le_cycles'

/-- The canonical map from `boundaries i` to `cycles' i`. -/
abbrev boundariesToCycles' (C : HomologicalComplex V c) (i : ι) :
    (C.boundaries i : V) ⟶ (C.cycles' i : V) :=
  imageToKernel _ _ (C.dTo_comp_dFrom i)
#align homological_complex.boundaries_to_cycles HomologicalComplex.boundariesToCycles'

/-- Prefer `boundariesToCycles'`. -/
@[simp 1100]
theorem imageToKernel_as_boundariesToCycles' (C : HomologicalComplex V c) (i : ι) (h) :
    (C.boundaries i).ofLE (C.cycles' i) h = C.boundariesToCycles' i := rfl
#align homological_complex.image_to_kernel_as_boundaries_to_cycles HomologicalComplex.imageToKernel_as_boundariesToCycles'

variable [HasCokernels V]

/-- The homology of a complex at index `i`. -/
abbrev homology' (C : HomologicalComplex V c) (i : ι) : V :=
  _root_.homology' (C.dTo i) (C.dFrom i) (C.dTo_comp_dFrom i)
#align homological_complex.homology HomologicalComplex.homology'

/-- The `j`th homology of a homological complex (as kernel of 'the differential from `Cⱼ`' modulo
the image of 'the differential to `Cⱼ`') is isomorphic to the kernel of `d : Cⱼ → Cₖ` modulo
the image of `d : Cᵢ → Cⱼ` when `Rel i j` and `Rel j k`. -/
def homology'Iso (C : HomologicalComplex V c) {i j k : ι} (hij : c.Rel i j) (hjk : c.Rel j k) :
    C.homology' j ≅ _root_.homology' (C.d i j) (C.d j k) (C.d_comp_d i j k) :=
  homology'.mapIso _ _
    (Arrow.isoMk (C.xPrevIso hij) (Iso.refl _) <| by dsimp; rw [C.dTo_eq hij, Category.comp_id])
    (Arrow.isoMk (Iso.refl _) (C.xNextIso hjk) <| by
      dsimp
      rw [C.dFrom_comp_xNextIso hjk, Category.id_comp])
    rfl
#align homological_complex.homology_iso HomologicalComplex.homology'Iso

end

end HomologicalComplex

/-- The 0th homology of a chain complex is isomorphic to the cokernel of `d : C₁ ⟶ C₀`. -/
def ChainComplex.homology'ZeroIso [HasKernels V] [HasImages V] [HasCokernels V]
    (C : ChainComplex V ℕ) [Epi (factorThruImage (C.d 1 0))] :
    C.homology' 0 ≅ cokernel (C.d 1 0) :=
  (homology'.mapIso _ _
      (Arrow.isoMk (C.xPrevIso rfl) (Iso.refl _) <| by
        rw [C.dTo_eq rfl]
        exact (Category.comp_id _).symm : Arrow.mk (C.dTo 0) ≅ Arrow.mk (C.d 1 0))
      (Arrow.isoMk (Iso.refl _) (Iso.refl _) <| by
        simp [C.dFrom_eq_zero fun h : _ = _ =>
          one_ne_zero <| by rwa [ChainComplex.next_nat_zero, Nat.zero_add] at h] :
        Arrow.mk (C.dFrom 0) ≅ Arrow.mk 0)
      rfl).trans <|
    homology'OfZeroRight _
#align chain_complex.homology_zero_iso ChainComplex.homology'ZeroIso

/-- The 0th cohomology of a cochain complex is isomorphic to the kernel of `d : C₀ → C₁`. -/
def CochainComplex.homology'ZeroIso [HasZeroObject V] [HasKernels V] [HasImages V] [HasCokernels V]
    (C : CochainComplex V ℕ) : C.homology' 0 ≅ kernel (C.d 0 1) :=
  (homology'.mapIso _ _
      (Arrow.isoMk (C.xPrevIsoSelf (by rw [CochainComplex.prev_nat_zero]; exact one_ne_zero))
          (Iso.refl _) (by simp) : Arrow.mk (C.dTo 0) ≅ Arrow.mk 0)
      (Arrow.isoMk (Iso.refl _) (C.xNextIso rfl) (by simp) :
        Arrow.mk (C.dFrom 0) ≅ Arrow.mk (C.d 0 1)) <|
      by simp).trans <|
    homology'OfZeroLeft _
#align cochain_complex.homology_zero_iso CochainComplex.homology'ZeroIso

/-- The `n + 1`th homology of a chain complex (as kernel of 'the differential from `Cₙ₊₁`' modulo
the image of 'the differential to `Cₙ₊₁`') is isomorphic to the kernel of `d : Cₙ₊₁ → Cₙ` modulo
the image of `d : Cₙ₊₂ → Cₙ₊₁`. -/
def ChainComplex.homology'SuccIso [HasKernels V] [HasImages V] [HasCokernels V]
    (C : ChainComplex V ℕ) (n : ℕ) :
    C.homology' (n + 1) ≅ homology' (C.d (n + 2) (n + 1)) (C.d (n + 1) n) (C.d_comp_d _ _ _) :=
  C.homology'Iso rfl rfl
#align chain_complex.homology_succ_iso ChainComplex.homology'SuccIso

/-- The `n + 1`th cohomology of a cochain complex (as kernel of 'the differential from `Cₙ₊₁`'
modulo the image of 'the differential to `Cₙ₊₁`') is isomorphic to the kernel of `d : Cₙ₊₁ → Cₙ₊₂`
modulo the image of `d : Cₙ → Cₙ₊₁`. -/
def CochainComplex.homology'SuccIso [HasKernels V] [HasImages V] [HasCokernels V]
    (C : CochainComplex V ℕ) (n : ℕ) :
    C.homology' (n + 1) ≅ homology' (C.d n (n + 1)) (C.d (n + 1) (n + 2)) (C.d_comp_d _ _ _) :=
  C.homology'Iso rfl rfl
#align cochain_complex.homology_succ_iso CochainComplex.homology'SuccIso

open HomologicalComplex

/-! Computing the cycles is functorial. -/


section

variable [HasKernels V]
variable {C₁ C₂ C₃ : HomologicalComplex V c} (f : C₁ ⟶ C₂)

/-- The morphism between cycles induced by a chain map. -/
abbrev cycles'Map (f : C₁ ⟶ C₂) (i : ι) : (C₁.cycles' i : V) ⟶ (C₂.cycles' i : V) :=
  Subobject.factorThru _ ((C₁.cycles' i).arrow ≫ f.f i) (kernelSubobject_factors _ _ (by simp))
#align cycles_map cycles'Map

@[reassoc, elementwise] -- @[simp] -- Porting note (#10618): simp can prove this
theorem cycles'Map_arrow (f : C₁ ⟶ C₂) (i : ι) :
    cycles'Map f i ≫ (C₂.cycles' i).arrow = (C₁.cycles' i).arrow ≫ f.f i := by simp
#align cycles_map_arrow cycles'Map_arrow

attribute [simp 1100] cycles'Map_arrow_assoc
attribute [simp] cycles'Map_arrow_apply

@[simp]
theorem cycles'Map_id (i : ι) : cycles'Map (𝟙 C₁) i = 𝟙 _ := by
  dsimp only [cycles'Map]
  simp
#align cycles_map_id cycles'Map_id

@[simp]
theorem cycles'Map_comp (f : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) (i : ι) :
    cycles'Map (f ≫ g) i = cycles'Map f i ≫ cycles'Map g i := by
  dsimp only [cycles'Map]
  simp [Subobject.factorThru_right]
#align cycles_map_comp cycles'Map_comp

variable (V c)

/-- Cycles as a functor. -/
@[simps]
def cycles'Functor (i : ι) : HomologicalComplex V c ⥤ V where
  obj C := C.cycles' i
  map {C₁ C₂} f := cycles'Map f i
#align cycles_functor cycles'Functor

end

/-! Computing the boundaries is functorial. -/


section

variable [HasImages V] [HasImageMaps V]
variable {C₁ C₂ C₃ : HomologicalComplex V c} (f : C₁ ⟶ C₂)

/-- The morphism between boundaries induced by a chain map. -/
abbrev boundariesMap (f : C₁ ⟶ C₂) (i : ι) : (C₁.boundaries i : V) ⟶ (C₂.boundaries i : V) :=
  imageSubobjectMap (f.sqTo i)
#align boundaries_map boundariesMap

variable (V c)

/-- Boundaries as a functor. -/
@[simps]
def boundariesFunctor (i : ι) : HomologicalComplex V c ⥤ V where
  obj C := C.boundaries i
  map {C₁ C₂} f := imageSubobjectMap (f.sqTo i)
#align boundaries_functor boundariesFunctor

end

section

/-! The `boundariesToCycles` morphisms are natural. -/


variable [HasEqualizers V] [HasImages V] [HasImageMaps V]
variable {C₁ C₂ : HomologicalComplex V c} (f : C₁ ⟶ C₂)

@[reassoc (attr := simp)]
theorem boundariesToCycles'_naturality (i : ι) :
    boundariesMap f i ≫ C₂.boundariesToCycles' i =
      C₁.boundariesToCycles' i ≫ cycles'Map f i := by
  ext
  simp
#align boundaries_to_cycles_naturality boundariesToCycles'_naturality

variable (V c)

/-- The natural transformation from the boundaries functor to the cycles functor. -/
@[simps]
def boundariesToCycles'NatTrans (i : ι) : boundariesFunctor V c i ⟶ cycles'Functor V c i where
  app C := C.boundariesToCycles' i
  naturality _ _ f := boundariesToCycles'_naturality f i
#align boundaries_to_cycles_nat_trans boundariesToCycles'NatTrans

/-- The `i`-th homology, as a functor to `V`. -/
@[simps]
def homology'Functor [HasCokernels V] (i : ι) : HomologicalComplex V c ⥤ V where
  -- It would be nice if we could just write
  -- `cokernel (boundariesToCyclesNatTrans V c i)`
  -- here, but universe implementation details get in the way...
  obj C := C.homology' i
  map {C₁ C₂} f := homology'.map _ _ (f.sqTo i) (f.sqFrom i) rfl
#align homology_functor homology'Functor

/-- The homology functor from `ι`-indexed complexes to `ι`-graded objects in `V`. -/
@[simps]
def gradedHomology'Functor [HasCokernels V] : HomologicalComplex V c ⥤ GradedObject ι V where
  obj C i := C.homology' i
  map {C C'} f i := (homology'Functor V c i).map f
#align graded_homology_functor gradedHomology'Functor

end
