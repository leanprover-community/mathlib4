/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Joël Riou
-/
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.CategoryTheory.Abelian.Homology

#align_import algebra.homology.quasi_iso from "leanprover-community/mathlib"@"956af7c76589f444f2e1313911bad16366ea476d"

/-!
# Quasi-isomorphisms

A chain map is a quasi-isomorphism if it induces isomorphisms on homology.

## Future work

Define the derived category as the localization at quasi-isomorphisms?
-/


open CategoryTheory

open CategoryTheory.Limits

universe v u

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [HasZeroMorphisms V] [HasZeroObject V]

variable [HasEqualizers V] [HasImages V] [HasImageMaps V] [HasCokernels V]

variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}

/-- A chain map is a quasi-isomorphism if it induces isomorphisms on homology.
-/
class QuasiIso' (f : C ⟶ D) : Prop where
  isIso : ∀ i, IsIso ((homology'Functor V c i).map f)
#align quasi_iso QuasiIso'

attribute [instance] QuasiIso'.isIso

instance (priority := 100) quasiIso'_of_iso (f : C ⟶ D) [IsIso f] : QuasiIso' f where
  isIso i := by
    change IsIso ((homology'Functor V c i).mapIso (asIso f)).hom
    infer_instance
#align quasi_iso_of_iso quasiIso'_of_iso

instance quasiIso'_comp (f : C ⟶ D) [QuasiIso' f] (g : D ⟶ E) [QuasiIso' g] :
    QuasiIso' (f ≫ g) where
  isIso i := by
    rw [Functor.map_comp]
    infer_instance
#align quasi_iso_comp quasiIso'_comp

theorem quasiIso'_of_comp_left (f : C ⟶ D) [QuasiIso' f] (g : D ⟶ E) [QuasiIso' (f ≫ g)] :
    QuasiIso' g :=
  { isIso := fun i => IsIso.of_isIso_fac_left ((homology'Functor V c i).map_comp f g).symm }
#align quasi_iso_of_comp_left quasiIso'_of_comp_left

theorem quasiIso'_of_comp_right (f : C ⟶ D) (g : D ⟶ E) [QuasiIso' g] [QuasiIso' (f ≫ g)] :
    QuasiIso' f :=
  { isIso := fun i => IsIso.of_isIso_fac_right ((homology'Functor V c i).map_comp f g).symm }
#align quasi_iso_of_comp_right quasiIso'_of_comp_right

namespace HomotopyEquiv

section

variable {W : Type*} [Category W] [Preadditive W] [HasCokernels W] [HasImages W] [HasEqualizers W]
  [HasZeroObject W] [HasImageMaps W]

/-- A homotopy equivalence is a quasi-isomorphism. -/
theorem toQuasiIso' {C D : HomologicalComplex W c} (e : HomotopyEquiv C D) : QuasiIso' e.hom :=
  ⟨fun i => by
    refine' ⟨⟨(homology'Functor W c i).map e.inv, _⟩⟩
    simp only [← Functor.map_comp, ← (homology'Functor W c i).map_id]
    constructor <;> apply homology'_map_eq_of_homotopy
    exacts [e.homotopyHomInvId, e.homotopyInvHomId]⟩
#align homotopy_equiv.to_quasi_iso HomotopyEquiv.toQuasiIso'

theorem toQuasiIso'_inv {C D : HomologicalComplex W c} (e : HomotopyEquiv C D) (i : ι) :
    (@asIso _ _ _ _ _ (e.toQuasiIso'.1 i)).inv = (homology'Functor W c i).map e.inv := by
  symm
  haveI := e.toQuasiIso'.1 i -- Porting note: Added this to get `asIso_hom` to work.
  simp only [← Iso.hom_comp_eq_id, asIso_hom, ← Functor.map_comp,
    ← (homology'Functor W c i).map_id, homology'_map_eq_of_homotopy e.homotopyHomInvId _]
#align homotopy_equiv.to_quasi_iso_inv HomotopyEquiv.toQuasiIso'_inv

end

end HomotopyEquiv

namespace HomologicalComplex.Hom

section ToSingle₀

variable {W : Type*} [Category W] [Abelian W]

section

variable {X : ChainComplex W ℕ} {Y : W} (f : X ⟶ (ChainComplex.single₀ _).obj Y) [hf : QuasiIso' f]

/-- If a chain map `f : X ⟶ Y[0]` is a quasi-isomorphism, then the cokernel of the differential
`d : X₁ → X₀` is isomorphic to `Y`. -/
noncomputable def toSingle₀CokernelAtZeroIso : cokernel (X.d 1 0) ≅ Y :=
  X.homology'ZeroIso.symm.trans
    ((@asIso _ _ _ _ _ (hf.1 0)).trans ((ChainComplex.homology'Functor0Single₀ W).app Y))
#align homological_complex.hom.to_single₀_cokernel_at_zero_iso HomologicalComplex.Hom.toSingle₀CokernelAtZeroIso

theorem toSingle₀CokernelAtZeroIso_hom_eq [hf : QuasiIso' f] :
    f.toSingle₀CokernelAtZeroIso.hom =
      cokernel.desc (X.d 1 0) (f.f 0) (by rw [← f.2 1 0 rfl]; exact comp_zero) := by
  ext
  dsimp only [toSingle₀CokernelAtZeroIso, ChainComplex.homology'ZeroIso, homology'OfZeroRight,
    homology'.mapIso, ChainComplex.homology'Functor0Single₀, cokernel.map]
  dsimp [asIso]
  simp only [cokernel.π_desc, Category.assoc, homology'.map_desc, cokernel.π_desc_assoc]
  simp [homology'.desc, Iso.refl_inv (X.X 0)]
#align homological_complex.hom.to_single₀_cokernel_at_zero_iso_hom_eq HomologicalComplex.Hom.toSingle₀CokernelAtZeroIso_hom_eq

theorem to_single₀_epi_at_zero [hf : QuasiIso' f] : Epi (f.f 0) := by
  constructor
  intro Z g h Hgh
  rw [← cokernel.π_desc (X.d 1 0) (f.f 0) (by rw [← f.2 1 0 rfl]; exact comp_zero),
    ← toSingle₀CokernelAtZeroIso_hom_eq] at Hgh
  rw [(@cancel_epi _ _ _ _ _ _ (epi_comp _ _) _ _).1 Hgh]
#align homological_complex.hom.to_single₀_epi_at_zero HomologicalComplex.Hom.to_single₀_epi_at_zero

theorem to_single₀_exact_d_f_at_zero [hf : QuasiIso' f] : Exact (X.d 1 0) (f.f 0) := by
  rw [Preadditive.exact_iff_homology'_zero]
  have h : X.d 1 0 ≫ f.f 0 = 0 := by
    simp only [← f.2 1 0 rfl, ChainComplex.single₀_obj_X_d, comp_zero]
  refine' ⟨h, Nonempty.intro (homology'IsoKernelDesc _ _ _ ≪≫ _)⟩
  suffices IsIso (cokernel.desc _ _ h) by apply kernel.ofMono
  rw [← toSingle₀CokernelAtZeroIso_hom_eq]
  infer_instance
#align homological_complex.hom.to_single₀_exact_d_f_at_zero HomologicalComplex.Hom.to_single₀_exact_d_f_at_zero

theorem to_single₀_exact_at_succ [hf : QuasiIso' f] (n : ℕ) :
    Exact (X.d (n + 2) (n + 1)) (X.d (n + 1) n) :=
  (Preadditive.exact_iff_homology'_zero _ _).2
    ⟨X.d_comp_d _ _ _,
      ⟨(ChainComplex.homology'SuccIso _ _).symm.trans
          ((@asIso _ _ _ _ _ (hf.1 (n + 1))).trans homology'ZeroZero)⟩⟩
#align homological_complex.hom.to_single₀_exact_at_succ HomologicalComplex.Hom.to_single₀_exact_at_succ

end

section

variable {X : CochainComplex W ℕ} {Y : W} (f : (CochainComplex.single₀ _).obj Y ⟶ X)

/-- If a cochain map `f : Y[0] ⟶ X` is a quasi-isomorphism, then the kernel of the differential
`d : X₀ → X₁` is isomorphic to `Y`. -/
noncomputable def fromSingle₀KernelAtZeroIso [hf : QuasiIso' f] : kernel (X.d 0 1) ≅ Y :=
  X.homology'ZeroIso.symm.trans
    ((@asIso _ _ _ _ _ (hf.1 0)).symm.trans ((CochainComplex.homologyFunctor0Single₀ W).app Y))
#align homological_complex.hom.from_single₀_kernel_at_zero_iso HomologicalComplex.Hom.fromSingle₀KernelAtZeroIso

theorem fromSingle₀KernelAtZeroIso_inv_eq [hf : QuasiIso' f] :
    f.fromSingle₀KernelAtZeroIso.inv =
      kernel.lift (X.d 0 1) (f.f 0) (by rw [f.2 0 1 rfl]; exact zero_comp) := by
  ext
  dsimp only [fromSingle₀KernelAtZeroIso, CochainComplex.homology'ZeroIso, homology'OfZeroLeft,
    homology'.mapIso, CochainComplex.homologyFunctor0Single₀, kernel.map]
  simp only [Iso.trans_inv, Iso.app_inv, Iso.symm_inv, Category.assoc, equalizer_as_kernel,
    kernel.lift_ι]
  dsimp [asIso]
  simp only [Category.assoc, homology'.π_map, cokernelZeroIsoTarget_hom,
    cokernelIsoOfEq_hom_comp_desc, kernelSubobject_arrow, homology'.π_map_assoc, IsIso.inv_comp_eq]
  simp [homology'.π, kernelSubobjectMap_comp, Iso.refl_hom (X.X 0), Category.comp_id]
#align homological_complex.hom.from_single₀_kernel_at_zero_iso_inv_eq HomologicalComplex.Hom.fromSingle₀KernelAtZeroIso_inv_eq

theorem from_single₀_mono_at_zero [hf : QuasiIso' f] : Mono (f.f 0) := by
  constructor
  intro Z g h Hgh
  rw [← kernel.lift_ι (X.d 0 1) (f.f 0) (by rw [f.2 0 1 rfl]; exact zero_comp),
    ← fromSingle₀KernelAtZeroIso_inv_eq] at Hgh
  rw [(@cancel_mono _ _ _ _ _ _ (mono_comp _ _) _ _).1 Hgh]
#align homological_complex.hom.from_single₀_mono_at_zero HomologicalComplex.Hom.from_single₀_mono_at_zero

theorem from_single₀_exact_f_d_at_zero [hf : QuasiIso' f] : Exact (f.f 0) (X.d 0 1) := by
  rw [Preadditive.exact_iff_homology'_zero]
  have h : f.f 0 ≫ X.d 0 1 = 0 := by
    simp only [HomologicalComplex.Hom.comm, CochainComplex.single₀_obj_X_d, zero_comp]
  refine' ⟨h, Nonempty.intro (homology'IsoCokernelLift _ _ _ ≪≫ _)⟩
  suffices IsIso (kernel.lift (X.d 0 1) (f.f 0) h) by apply cokernel.ofEpi
  rw [← fromSingle₀KernelAtZeroIso_inv_eq f]
  infer_instance
#align homological_complex.hom.from_single₀_exact_f_d_at_zero HomologicalComplex.Hom.from_single₀_exact_f_d_at_zero

theorem from_single₀_exact_at_succ [hf : QuasiIso' f] (n : ℕ) :
    Exact (X.d n (n + 1)) (X.d (n + 1) (n + 2)) :=
  (Preadditive.exact_iff_homology'_zero _ _).2
    ⟨X.d_comp_d _ _ _,
      ⟨(CochainComplex.homology'SuccIso _ _).symm.trans
          ((@asIso _ _ _ _ _ (hf.1 (n + 1))).symm.trans homology'ZeroZero)⟩⟩
#align homological_complex.hom.from_single₀_exact_at_succ HomologicalComplex.Hom.from_single₀_exact_at_succ

end

end ToSingle₀

end HomologicalComplex.Hom

variable {A : Type*} [Category A] [Abelian A] {B : Type*} [Category B] [Abelian B] (F : A ⥤ B)
  [Functor.Additive F] [PreservesFiniteLimits F] [PreservesFiniteColimits F] [Faithful F]

theorem CategoryTheory.Functor.quasiIso'_of_map_quasiIso' {C D : HomologicalComplex A c}
    (f : C ⟶ D) (hf : QuasiIso' ((F.mapHomologicalComplex _).map f)) : QuasiIso' f :=
  ⟨fun i =>
    haveI : IsIso (F.map ((homology'Functor A c i).map f)) := by
      rw [← Functor.comp_map, ← NatIso.naturality_2 (F.homology'FunctorIso i) f, Functor.comp_map]
      infer_instance
    isIso_of_reflects_iso _ F⟩
#align category_theory.functor.quasi_iso_of_map_quasi_iso CategoryTheory.Functor.quasiIso'_of_map_quasiIso'
