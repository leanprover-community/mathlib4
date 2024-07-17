/-
Copyright (c) 2022 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Amelia Livingston, Joël Riou
-/
import Mathlib.CategoryTheory.Abelian.Opposite
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.ImageToKernel
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

#align_import algebra.homology.opposite from "leanprover-community/mathlib"@"8c75ef3517d4106e89fe524e6281d0b0545f47fc"

/-!
# Opposite categories of complexes
Given a preadditive category `V`, the opposite of its category of chain complexes is equivalent to
the category of cochain complexes of objects in `Vᵒᵖ`. We define this equivalence, and another
analogous equivalence (for a general category of homological complexes with a general
complex shape).

We then show that when `V` is abelian, if `C` is a homological complex, then the homology of
`op(C)` is isomorphic to `op` of the homology of `C` (and the analogous result for `unop`).

## Implementation notes
It is convenient to define both `op` and `opSymm`; this is because given a complex shape `c`,
`c.symm.symm` is not defeq to `c`.

## Tags
opposite, chain complex, cochain complex, homology, cohomology, homological complex
-/


noncomputable section

open Opposite CategoryTheory CategoryTheory.Limits

section

variable {V : Type*} [Category V] [Abelian V]

theorem imageToKernel_op {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) :
    imageToKernel g.op f.op (by rw [← op_comp, w, op_zero]) =
      (imageSubobjectIso _ ≪≫ (imageOpOp _).symm).hom ≫
        (cokernel.desc f (factorThruImage g)
              (by rw [← cancel_mono (image.ι g), Category.assoc, image.fac, w, zero_comp])).op ≫
          (kernelSubobjectIso _ ≪≫ kernelOpOp _).inv := by
  ext
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, kernelOpOp_inv, Category.assoc,
    imageToKernel_arrow, kernelSubobject_arrow', kernel.lift_ι, ← op_comp, cokernel.π_desc,
    ← imageSubobject_arrow, ← imageUnopOp_inv_comp_op_factorThruImage g.op]
  rfl
#align image_to_kernel_op imageToKernel_op

theorem imageToKernel_unop {X Y Z : Vᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) :
    imageToKernel g.unop f.unop (by rw [← unop_comp, w, unop_zero]) =
      (imageSubobjectIso _ ≪≫ (imageUnopUnop _).symm).hom ≫
        (cokernel.desc f (factorThruImage g)
              (by rw [← cancel_mono (image.ι g), Category.assoc, image.fac, w, zero_comp])).unop ≫
          (kernelSubobjectIso _ ≪≫ kernelUnopUnop _).inv := by
  ext
  dsimp only [imageUnopUnop]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, kernelUnopUnop_inv, Category.assoc,
    imageToKernel_arrow, kernelSubobject_arrow', kernel.lift_ι, cokernel.π_desc, Iso.unop_inv,
    ← unop_comp, factorThruImage_comp_imageUnopOp_inv, Quiver.Hom.unop_op, imageSubobject_arrow]
#align image_to_kernel_unop imageToKernel_unop

end

namespace HomologicalComplex

variable {ι V : Type*} [Category V] {c : ComplexShape ι}

section

variable [HasZeroMorphisms V]

/-- Sends a complex `X` with objects in `V` to the corresponding complex with objects in `Vᵒᵖ`. -/
@[simps]
protected def op (X : HomologicalComplex V c) : HomologicalComplex Vᵒᵖ c.symm where
  X i := op (X.X i)
  d i j := (X.d j i).op
  shape i j hij := by simp only; rw [X.shape j i hij, op_zero]
  d_comp_d' _ _ _ _ _ := by rw [← op_comp, X.d_comp_d, op_zero]
#align homological_complex.op HomologicalComplex.op

/-- Sends a complex `X` with objects in `V` to the corresponding complex with objects in `Vᵒᵖ`. -/
@[simps]
protected def opSymm (X : HomologicalComplex V c.symm) : HomologicalComplex Vᵒᵖ c where
  X i := op (X.X i)
  d i j := (X.d j i).op
  shape i j hij := by simp only; rw [X.shape j i hij, op_zero]
  d_comp_d' _ _ _ _ _ := by rw [← op_comp, X.d_comp_d, op_zero]
#align homological_complex.op_symm HomologicalComplex.opSymm

/-- Sends a complex `X` with objects in `Vᵒᵖ` to the corresponding complex with objects in `V`. -/
@[simps]
protected def unop (X : HomologicalComplex Vᵒᵖ c) : HomologicalComplex V c.symm where
  X i := unop (X.X i)
  d i j := (X.d j i).unop
  shape i j hij := by simp only; rw [X.shape j i hij, unop_zero]
  d_comp_d' _ _ _ _ _ := by rw [← unop_comp, X.d_comp_d, unop_zero]
#align homological_complex.unop HomologicalComplex.unop

/-- Sends a complex `X` with objects in `Vᵒᵖ` to the corresponding complex with objects in `V`. -/
@[simps]
protected def unopSymm (X : HomologicalComplex Vᵒᵖ c.symm) : HomologicalComplex V c where
  X i := unop (X.X i)
  d i j := (X.d j i).unop
  shape i j hij := by simp only; rw [X.shape j i hij, unop_zero]
  d_comp_d' _ _ _ _ _ := by rw [← unop_comp, X.d_comp_d, unop_zero]
#align homological_complex.unop_symm HomologicalComplex.unopSymm

variable (V c)

/-- Auxiliary definition for `opEquivalence`. -/
@[simps]
def opFunctor : (HomologicalComplex V c)ᵒᵖ ⥤ HomologicalComplex Vᵒᵖ c.symm where
  obj X := (unop X).op
  map f :=
    { f := fun i => (f.unop.f i).op
      comm' := fun i j _ => by simp only [op_d, ← op_comp, f.unop.comm] }
#align homological_complex.op_functor HomologicalComplex.opFunctor

/-- Auxiliary definition for `opEquivalence`. -/
@[simps]
def opInverse : HomologicalComplex Vᵒᵖ c.symm ⥤ (HomologicalComplex V c)ᵒᵖ where
  obj X := op X.unopSymm
  map f := Quiver.Hom.op
    { f := fun i => (f.f i).unop
      comm' := fun i j _ => by simp only [unopSymm_d, ← unop_comp, f.comm] }
#align homological_complex.op_inverse HomologicalComplex.opInverse

/-- Auxiliary definition for `opEquivalence`. -/
def opUnitIso : 𝟭 (HomologicalComplex V c)ᵒᵖ ≅ opFunctor V c ⋙ opInverse V c :=
  NatIso.ofComponents
    (fun X =>
      (HomologicalComplex.Hom.isoOfComponents (fun i => Iso.refl _) fun i j _ => by
            simp only [Iso.refl_hom, Category.id_comp, unopSymm_d, op_d, Quiver.Hom.unop_op,
              Category.comp_id] :
          (Opposite.unop X).op.unopSymm ≅ unop X).op)
    (by
      intro X Y f
      refine Quiver.Hom.unop_inj ?_
      ext x
      simp only [Quiver.Hom.unop_op, Functor.id_map, Iso.op_hom, Functor.comp_map, unop_comp,
        comp_f, Hom.isoOfComponents_hom_f]
      erw [Category.id_comp, Category.comp_id (f.unop.f x)])
#align homological_complex.op_unit_iso HomologicalComplex.opUnitIso

/-- Auxiliary definition for `opEquivalence`. -/
def opCounitIso : opInverse V c ⋙ opFunctor V c ≅ 𝟭 (HomologicalComplex Vᵒᵖ c.symm) :=
  NatIso.ofComponents
    fun X => HomologicalComplex.Hom.isoOfComponents fun i => Iso.refl _
#align homological_complex.op_counit_iso HomologicalComplex.opCounitIso

/-- Given a category of complexes with objects in `V`, there is a natural equivalence between its
opposite category and a category of complexes with objects in `Vᵒᵖ`. -/
@[simps]
def opEquivalence : (HomologicalComplex V c)ᵒᵖ ≌ HomologicalComplex Vᵒᵖ c.symm where
  functor := opFunctor V c
  inverse := opInverse V c
  unitIso := opUnitIso V c
  counitIso := opCounitIso V c
  functor_unitIso_comp X := by
    ext
    simp only [opUnitIso, opCounitIso, NatIso.ofComponents_hom_app, Iso.op_hom, comp_f,
      opFunctor_map_f, Quiver.Hom.unop_op, Hom.isoOfComponents_hom_f]
    exact Category.comp_id _
#align homological_complex.op_equivalence HomologicalComplex.opEquivalence

/-- Auxiliary definition for `unopEquivalence`. -/
@[simps]
def unopFunctor : (HomologicalComplex Vᵒᵖ c)ᵒᵖ ⥤ HomologicalComplex V c.symm where
  obj X := (unop X).unop
  map f :=
    { f := fun i => (f.unop.f i).unop
      comm' := fun i j _ => by simp only [unop_d, ← unop_comp, f.unop.comm] }
#align homological_complex.unop_functor HomologicalComplex.unopFunctor

/-- Auxiliary definition for `unopEquivalence`. -/
@[simps]
def unopInverse : HomologicalComplex V c.symm ⥤ (HomologicalComplex Vᵒᵖ c)ᵒᵖ where
  obj X := op X.opSymm
  map f := Quiver.Hom.op
    { f := fun i => (f.f i).op
      comm' := fun i j _ => by simp only [opSymm_d, ← op_comp, f.comm] }
#align homological_complex.unop_inverse HomologicalComplex.unopInverse

/-- Auxiliary definition for `unopEquivalence`. -/
def unopUnitIso : 𝟭 (HomologicalComplex Vᵒᵖ c)ᵒᵖ ≅ unopFunctor V c ⋙ unopInverse V c :=
  NatIso.ofComponents
    (fun X =>
      (HomologicalComplex.Hom.isoOfComponents (fun i => Iso.refl _) fun i j _ => by
            simp only [Iso.refl_hom, Category.id_comp, unopSymm_d, op_d, Quiver.Hom.unop_op,
              Category.comp_id] :
          (Opposite.unop X).op.unopSymm ≅ unop X).op)
    (by
      intro X Y f
      refine Quiver.Hom.unop_inj ?_
      ext x
      simp only [Quiver.Hom.unop_op, Functor.id_map, Iso.op_hom, Functor.comp_map, unop_comp,
        comp_f, Hom.isoOfComponents_hom_f]
      erw [Category.id_comp, Category.comp_id (f.unop.f x)])
#align homological_complex.unop_unit_iso HomologicalComplex.unopUnitIso

/-- Auxiliary definition for `unopEquivalence`. -/
def unopCounitIso : unopInverse V c ⋙ unopFunctor V c ≅ 𝟭 (HomologicalComplex V c.symm) :=
  NatIso.ofComponents
    fun X => HomologicalComplex.Hom.isoOfComponents fun i => Iso.refl _
#align homological_complex.unop_counit_iso HomologicalComplex.unopCounitIso

/-- Given a category of complexes with objects in `Vᵒᵖ`, there is a natural equivalence between its
opposite category and a category of complexes with objects in `V`. -/
@[simps]
def unopEquivalence : (HomologicalComplex Vᵒᵖ c)ᵒᵖ ≌ HomologicalComplex V c.symm where
  functor := unopFunctor V c
  inverse := unopInverse V c
  unitIso := unopUnitIso V c
  counitIso := unopCounitIso V c
  functor_unitIso_comp X := by
    ext
    simp only [opUnitIso, opCounitIso, NatIso.ofComponents_hom_app, Iso.op_hom, comp_f,
      opFunctor_map_f, Quiver.Hom.unop_op, Hom.isoOfComponents_hom_f]
    exact Category.comp_id _
#align homological_complex.unop_equivalence HomologicalComplex.unopEquivalence

instance (K : HomologicalComplex V c) (i : ι) [K.HasHomology i] :
    K.op.HasHomology i :=
  (inferInstance : (K.sc i).op.HasHomology)

instance (K : HomologicalComplex Vᵒᵖ c) (i : ι) [K.HasHomology i] :
    K.unop.HasHomology i :=
  (inferInstance : (K.sc i).unop.HasHomology)

variable {V c}

/-- If `K` is a homological complex, then the homology of `K.op` identifies to
the opposite of the homology of `K`. -/
def homologyOp (K : HomologicalComplex V c) (i : ι) [K.HasHomology i] :
    K.op.homology i ≅ op (K.homology i) :=
  (K.sc i).homologyOpIso

/-- If `K` is a homological complex in the opposite category,
then the homology of `K.unop` identifies to the opposite of the homology of `K`. -/
def homologyUnop (K : HomologicalComplex Vᵒᵖ c) (i : ι) [K.HasHomology i] :
    K.unop.homology i ≅ unop (K.homology i) :=
  (K.unop.homologyOp i).unop

end

section

variable [Preadditive V]

instance opFunctor_additive : (@opFunctor ι V _ c _).Additive where
#align homological_complex.op_functor_additive HomologicalComplex.opFunctor_additive

instance unopFunctor_additive : (@unopFunctor ι V _ c _).Additive where
#align homological_complex.unop_functor_additive HomologicalComplex.unopFunctor_additive

end

end HomologicalComplex
