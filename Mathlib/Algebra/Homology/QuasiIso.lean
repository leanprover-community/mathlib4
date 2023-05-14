/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Joël Riou

! This file was ported from Lean 3 source module algebra.homology.quasi_iso
! leanprover-community/mathlib commit 956af7c76589f444f2e1313911bad16366ea476d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Homology.Homotopy
import Mathbin.CategoryTheory.Abelian.Homology

/-!
# Quasi-isomorphisms

A chain map is a quasi-isomorphism if it induces isomorphisms on homology.

## Future work

Define the derived category as the localization at quasi-isomorphisms?
-/


open CategoryTheory

open CategoryTheory.Limits

universe v u

variable {ι : Type _}

variable {V : Type u} [Category.{v} V] [HasZeroMorphisms V] [HasZeroObject V]

variable [HasEqualizers V] [HasImages V] [HasImageMaps V] [HasCokernels V]

variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}

/-- A chain map is a quasi-isomorphism if it induces isomorphisms on homology.
-/
class QuasiIso (f : C ⟶ D) : Prop where
  IsIso : ∀ i, IsIso ((homologyFunctor V c i).map f)
#align quasi_iso QuasiIso

attribute [instance] QuasiIso.isIso

instance (priority := 100) quasiIso_of_iso (f : C ⟶ D) [IsIso f] : QuasiIso f
    where IsIso i :=
    by
    change is_iso ((homologyFunctor V c i).mapIso (as_iso f)).Hom
    infer_instance
#align quasi_iso_of_iso quasiIso_of_iso

instance quasiIso_comp (f : C ⟶ D) [QuasiIso f] (g : D ⟶ E) [QuasiIso g] : QuasiIso (f ≫ g)
    where IsIso i := by
    rw [functor.map_comp]
    infer_instance
#align quasi_iso_comp quasiIso_comp

theorem quasiIso_of_comp_left (f : C ⟶ D) [QuasiIso f] (g : D ⟶ E) [QuasiIso (f ≫ g)] :
    QuasiIso g :=
  { IsIso := fun i => IsIso.of_isIso_fac_left ((homologyFunctor V c i).map_comp f g).symm }
#align quasi_iso_of_comp_left quasiIso_of_comp_left

theorem quasiIso_of_comp_right (f : C ⟶ D) (g : D ⟶ E) [QuasiIso g] [QuasiIso (f ≫ g)] :
    QuasiIso f :=
  { IsIso := fun i => IsIso.of_isIso_fac_right ((homologyFunctor V c i).map_comp f g).symm }
#align quasi_iso_of_comp_right quasiIso_of_comp_right

namespace HomotopyEquiv

section

variable {W : Type _} [Category W] [Preadditive W] [HasCokernels W] [HasImages W] [HasEqualizers W]
  [HasZeroObject W] [HasImageMaps W]

/-- An homotopy equivalence is a quasi-isomorphism. -/
theorem to_quasiIso {C D : HomologicalComplex W c} (e : HomotopyEquiv C D) : QuasiIso e.Hom :=
  ⟨fun i => by
    refine' ⟨⟨(homologyFunctor W c i).map e.inv, _⟩⟩
    simp only [← functor.map_comp, ← (homologyFunctor W c i).map_id]
    constructor <;> apply homology_map_eq_of_homotopy
    exacts[e.homotopy_hom_inv_id, e.homotopy_inv_hom_id]⟩
#align homotopy_equiv.to_quasi_iso HomotopyEquiv.to_quasiIso

theorem to_quasiIso_inv {C D : HomologicalComplex W c} (e : HomotopyEquiv C D) (i : ι) :
    (@asIso _ _ _ _ _ (e.to_quasiIso.1 i)).inv = (homologyFunctor W c i).map e.inv :=
  by
  symm
  simp only [← iso.hom_comp_eq_id, as_iso_hom, ← functor.map_comp, ← (homologyFunctor W c i).map_id,
    homology_map_eq_of_homotopy e.homotopy_hom_inv_id _]
#align homotopy_equiv.to_quasi_iso_inv HomotopyEquiv.to_quasiIso_inv

end

end HomotopyEquiv

namespace HomologicalComplex.Hom

section ToSingle₀

variable {W : Type _} [Category W] [Abelian W]

section

variable {X : ChainComplex W ℕ} {Y : W} (f : X ⟶ (ChainComplex.single₀ _).obj Y) [hf : QuasiIso f]

/-- If a chain map `f : X ⟶ Y[0]` is a quasi-isomorphism, then the cokernel of the differential
`d : X₁ → X₀` is isomorphic to `Y.` -/
noncomputable def toSingle₀CokernelAtZeroIso : cokernel (X.d 1 0) ≅ Y :=
  X.homologyZeroIso.symm.trans
    ((@asIso _ _ _ _ _ (hf.1 0)).trans ((ChainComplex.homologyFunctor0Single₀ W).app Y))
#align homological_complex.hom.to_single₀_cokernel_at_zero_iso HomologicalComplex.Hom.toSingle₀CokernelAtZeroIso

theorem toSingle₀CokernelAtZeroIso_hom_eq [hf : QuasiIso f] :
    f.toSingle₀CokernelAtZeroIso.Hom =
      cokernel.desc (X.d 1 0) (f.f 0) (by rw [← f.2 1 0 rfl] <;> exact comp_zero) :=
  by
  ext
  dsimp only [to_single₀_cokernel_at_zero_iso, ChainComplex.homologyZeroIso, homologyOfZeroRight,
    homology.mapIso, ChainComplex.homologyFunctor0Single₀, cokernel.map]
  dsimp
  simp only [cokernel.π_desc, category.assoc, homology.map_desc, cokernel.π_desc_assoc]
  simp [homology.desc, iso.refl_inv (X.X 0)]
#align homological_complex.hom.to_single₀_cokernel_at_zero_iso_hom_eq HomologicalComplex.Hom.toSingle₀CokernelAtZeroIso_hom_eq

theorem to_single₀_epi_at_zero [hf : QuasiIso f] : Epi (f.f 0) :=
  by
  constructor
  intro Z g h Hgh
  rw [← cokernel.π_desc (X.d 1 0) (f.f 0) (by rw [← f.2 1 0 rfl] <;> exact comp_zero), ←
    to_single₀_cokernel_at_zero_iso_hom_eq] at Hgh
  rw [(@cancel_epi _ _ _ _ _ _ (epi_comp _ _) _ _).1 Hgh]
#align homological_complex.hom.to_single₀_epi_at_zero HomologicalComplex.Hom.to_single₀_epi_at_zero

theorem to_single₀_exact_d_f_at_zero [hf : QuasiIso f] : Exact (X.d 1 0) (f.f 0) :=
  by
  rw [preadditive.exact_iff_homology_zero]
  have h : X.d 1 0 ≫ f.f 0 = 0 := by
    simp only [← f.2 1 0 rfl, ChainComplex.single₀_obj_X_d, comp_zero]
  refine' ⟨h, Nonempty.intro (homologyIsoKernelDesc _ _ _ ≪≫ _)⟩
  · suffices is_iso (cokernel.desc _ _ h) by
      haveI := this
      apply kernel.of_mono
    rw [← to_single₀_cokernel_at_zero_iso_hom_eq]
    infer_instance
#align homological_complex.hom.to_single₀_exact_d_f_at_zero HomologicalComplex.Hom.to_single₀_exact_d_f_at_zero

theorem to_single₀_exact_at_succ [hf : QuasiIso f] (n : ℕ) :
    Exact (X.d (n + 2) (n + 1)) (X.d (n + 1) n) :=
  (Preadditive.exact_iff_homology_zero _ _).2
    ⟨X.d_comp_d _ _ _,
      ⟨(ChainComplex.homologySuccIso _ _).symm.trans
          ((@asIso _ _ _ _ _ (hf.1 (n + 1))).trans homologyZeroZero)⟩⟩
#align homological_complex.hom.to_single₀_exact_at_succ HomologicalComplex.Hom.to_single₀_exact_at_succ

end

section

variable {X : CochainComplex W ℕ} {Y : W} (f : (CochainComplex.single₀ _).obj Y ⟶ X)

/-- If a cochain map `f : Y[0] ⟶ X` is a quasi-isomorphism, then the kernel of the differential
`d : X₀ → X₁` is isomorphic to `Y.` -/
noncomputable def fromSingle₀KernelAtZeroIso [hf : QuasiIso f] : kernel (X.d 0 1) ≅ Y :=
  X.homologyZeroIso.symm.trans
    ((@asIso _ _ _ _ _ (hf.1 0)).symm.trans ((CochainComplex.homologyFunctor0Single₀ W).app Y))
#align homological_complex.hom.from_single₀_kernel_at_zero_iso HomologicalComplex.Hom.fromSingle₀KernelAtZeroIso

theorem fromSingle₀KernelAtZeroIso_inv_eq [hf : QuasiIso f] :
    f.fromSingle₀KernelAtZeroIso.inv =
      kernel.lift (X.d 0 1) (f.f 0) (by rw [f.2 0 1 rfl] <;> exact zero_comp) :=
  by
  ext
  dsimp only [from_single₀_kernel_at_zero_iso, CochainComplex.homologyZeroIso, homologyOfZeroLeft,
    homology.mapIso, CochainComplex.homologyFunctor0Single₀, kernel.map]
  simp only [iso.trans_inv, iso.app_inv, iso.symm_inv, category.assoc, equalizer_as_kernel,
    kernel.lift_ι]
  dsimp
  simp only [category.assoc, homology.π_map, cokernel_zero_iso_target_hom,
    cokernel_iso_of_eq_hom_comp_desc, kernel_subobject_arrow, homology.π_map_assoc,
    is_iso.inv_comp_eq]
  simp [homology.π, kernel_subobject_map_comp, iso.refl_hom (X.X 0), category.comp_id]
#align homological_complex.hom.from_single₀_kernel_at_zero_iso_inv_eq HomologicalComplex.Hom.fromSingle₀KernelAtZeroIso_inv_eq

theorem from_single₀_mono_at_zero [hf : QuasiIso f] : Mono (f.f 0) :=
  by
  constructor
  intro Z g h Hgh
  rw [← kernel.lift_ι (X.d 0 1) (f.f 0) (by rw [f.2 0 1 rfl] <;> exact zero_comp), ←
    from_single₀_kernel_at_zero_iso_inv_eq] at Hgh
  rw [(@cancel_mono _ _ _ _ _ _ (mono_comp _ _) _ _).1 Hgh]
#align homological_complex.hom.from_single₀_mono_at_zero HomologicalComplex.Hom.from_single₀_mono_at_zero

theorem from_single₀_exact_f_d_at_zero [hf : QuasiIso f] : Exact (f.f 0) (X.d 0 1) :=
  by
  rw [preadditive.exact_iff_homology_zero]
  have h : f.f 0 ≫ X.d 0 1 = 0 := by
    simp only [HomologicalComplex.Hom.comm, CochainComplex.single₀_obj_X_d, zero_comp]
  refine' ⟨h, Nonempty.intro (homologyIsoCokernelLift _ _ _ ≪≫ _)⟩
  · suffices is_iso (kernel.lift (X.d 0 1) (f.f 0) h)
      by
      haveI := this
      apply cokernel.of_epi
    rw [← from_single₀_kernel_at_zero_iso_inv_eq f]
    infer_instance
#align homological_complex.hom.from_single₀_exact_f_d_at_zero HomologicalComplex.Hom.from_single₀_exact_f_d_at_zero

theorem from_single₀_exact_at_succ [hf : QuasiIso f] (n : ℕ) :
    Exact (X.d n (n + 1)) (X.d (n + 1) (n + 2)) :=
  (Preadditive.exact_iff_homology_zero _ _).2
    ⟨X.d_comp_d _ _ _,
      ⟨(CochainComplex.homologySuccIso _ _).symm.trans
          ((@asIso _ _ _ _ _ (hf.1 (n + 1))).symm.trans homologyZeroZero)⟩⟩
#align homological_complex.hom.from_single₀_exact_at_succ HomologicalComplex.Hom.from_single₀_exact_at_succ

end

end ToSingle₀

end HomologicalComplex.Hom

variable {A : Type _} [Category A] [Abelian A] {B : Type _} [Category B] [Abelian B] (F : A ⥤ B)
  [Functor.Additive F] [PreservesFiniteLimits F] [PreservesFiniteColimits F] [Faithful F]

theorem CategoryTheory.Functor.quasiIso_of_map_quasiIso {C D : HomologicalComplex A c} (f : C ⟶ D)
    (hf : QuasiIso ((F.mapHomologicalComplex _).map f)) : QuasiIso f :=
  ⟨fun i =>
    haveI : is_iso (F.map ((homologyFunctor A c i).map f)) :=
      by
      rw [← functor.comp_map, ← nat_iso.naturality_2 (F.homology_functor_iso i) f, functor.comp_map]
      infer_instance
    is_iso_of_reflects_iso _ F⟩
#align category_theory.functor.quasi_iso_of_map_quasi_iso CategoryTheory.Functor.quasiIso_of_map_quasiIso

