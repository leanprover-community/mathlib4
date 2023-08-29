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
class QuasiIso (f : C ⟶ D) : Prop where
  IsIso : ∀ i, IsIso ((homologyFunctor V c i).map f)
#align quasi_iso QuasiIso

attribute [instance] QuasiIso.IsIso

instance (priority := 100) quasiIso_of_iso (f : C ⟶ D) [IsIso f] : QuasiIso f where
  IsIso i := by
    change IsIso ((homologyFunctor V c i).mapIso (asIso f)).hom
    -- ⊢ IsIso ((homologyFunctor V c i).mapIso (asIso f)).hom
    infer_instance
    -- 🎉 no goals
#align quasi_iso_of_iso quasiIso_of_iso

instance quasiIso_comp (f : C ⟶ D) [QuasiIso f] (g : D ⟶ E) [QuasiIso g] : QuasiIso (f ≫ g) where
  IsIso i := by
    rw [Functor.map_comp]
    -- ⊢ IsIso ((homologyFunctor V c i).map f ≫ (homologyFunctor V c i).map g)
    infer_instance
    -- 🎉 no goals
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

variable {W : Type*} [Category W] [Preadditive W] [HasCokernels W] [HasImages W] [HasEqualizers W]
  [HasZeroObject W] [HasImageMaps W]

/-- A homotopy equivalence is a quasi-isomorphism. -/
theorem toQuasiIso {C D : HomologicalComplex W c} (e : HomotopyEquiv C D) : QuasiIso e.hom :=
  ⟨fun i => by
    refine' ⟨⟨(homologyFunctor W c i).map e.inv, _⟩⟩
    -- ⊢ (homologyFunctor W c i).map e.hom ≫ (homologyFunctor W c i).map e.inv = 𝟙 (( …
    simp only [← Functor.map_comp, ← (homologyFunctor W c i).map_id]
    -- ⊢ (homologyFunctor W c i).map (e.hom ≫ e.inv) = (homologyFunctor W c i).map (𝟙 …
    constructor <;> apply homology_map_eq_of_homotopy
    -- ⊢ (homologyFunctor W c i).map (e.hom ≫ e.inv) = (homologyFunctor W c i).map (𝟙 …
                    -- ⊢ Homotopy (e.hom ≫ e.inv) (𝟙 C)
                    -- ⊢ Homotopy (e.inv ≫ e.hom) (𝟙 D)
    exacts [e.homotopyHomInvId, e.homotopyInvHomId]⟩
    -- 🎉 no goals
#align homotopy_equiv.to_quasi_iso HomotopyEquiv.toQuasiIso

theorem toQuasiIso_inv {C D : HomologicalComplex W c} (e : HomotopyEquiv C D) (i : ι) :
    (@asIso _ _ _ _ _ (e.toQuasiIso.1 i)).inv = (homologyFunctor W c i).map e.inv := by
  symm
  -- ⊢ (homologyFunctor W c i).map e.inv = (asIso ((homologyFunctor W c i).map e.ho …
  haveI := e.toQuasiIso.1 i -- Porting note: Added this to get `asIso_hom` to work.
  -- ⊢ (homologyFunctor W c i).map e.inv = (asIso ((homologyFunctor W c i).map e.ho …
  simp only [← Iso.hom_comp_eq_id, asIso_hom, ← Functor.map_comp, ← (homologyFunctor W c i).map_id,
    homology_map_eq_of_homotopy e.homotopyHomInvId _]
#align homotopy_equiv.to_quasi_iso_inv HomotopyEquiv.toQuasiIso_inv

end

end HomotopyEquiv

namespace HomologicalComplex.Hom

section ToSingle₀

variable {W : Type*} [Category W] [Abelian W]

section

variable {X : ChainComplex W ℕ} {Y : W} (f : X ⟶ (ChainComplex.single₀ _).obj Y) [hf : QuasiIso f]

/-- If a chain map `f : X ⟶ Y[0]` is a quasi-isomorphism, then the cokernel of the differential
`d : X₁ → X₀` is isomorphic to `Y`. -/
noncomputable def toSingle₀CokernelAtZeroIso : cokernel (X.d 1 0) ≅ Y :=
  X.homologyZeroIso.symm.trans
    ((@asIso _ _ _ _ _ (hf.1 0)).trans ((ChainComplex.homologyFunctor0Single₀ W).app Y))
#align homological_complex.hom.to_single₀_cokernel_at_zero_iso HomologicalComplex.Hom.toSingle₀CokernelAtZeroIso

theorem toSingle₀CokernelAtZeroIso_hom_eq [hf : QuasiIso f] :
    f.toSingle₀CokernelAtZeroIso.hom =
      cokernel.desc (X.d 1 0) (f.f 0) (by rw [← f.2 1 0 rfl]; exact comp_zero) := by
                                          -- ⊢ HomologicalComplex.Hom.f f 1 ≫ d ((ChainComplex.single₀ W).obj Y) 1 0 = 0
                                                              -- 🎉 no goals
  ext
  -- ⊢ coequalizer.π (d X 1 0) 0 ≫ (toSingle₀CokernelAtZeroIso f).hom = coequalizer …
  dsimp only [toSingle₀CokernelAtZeroIso, ChainComplex.homologyZeroIso, homologyOfZeroRight,
    homology.mapIso, ChainComplex.homologyFunctor0Single₀, cokernel.map]
  dsimp [asIso]
  -- ⊢ cokernel.π (d X 1 0) ≫ ((cokernel.desc (d X 1 0) (cokernel.π (image.ι (d X 1 …
  simp only [cokernel.π_desc, Category.assoc, homology.map_desc, cokernel.π_desc_assoc]
  -- ⊢ kernelZeroIsoSource.inv ≫ (kernelSubobjectIso 0).inv ≫ cokernel.π (imageToKe …
  simp [homology.desc, Iso.refl_inv (X.X 0)]
  -- 🎉 no goals
#align homological_complex.hom.to_single₀_cokernel_at_zero_iso_hom_eq HomologicalComplex.Hom.toSingle₀CokernelAtZeroIso_hom_eq

theorem to_single₀_epi_at_zero [hf : QuasiIso f] : Epi (f.f 0) := by
  constructor
  -- ⊢ ∀ {Z : W} (g h : HomologicalComplex.X ((ChainComplex.single₀ W).obj Y) 0 ⟶ Z …
  intro Z g h Hgh
  -- ⊢ g = h
  rw [← cokernel.π_desc (X.d 1 0) (f.f 0) (by rw [← f.2 1 0 rfl]; exact comp_zero),
    ← toSingle₀CokernelAtZeroIso_hom_eq] at Hgh
  rw [(@cancel_epi _ _ _ _ _ _ (epi_comp _ _) _ _).1 Hgh]
  -- 🎉 no goals
#align homological_complex.hom.to_single₀_epi_at_zero HomologicalComplex.Hom.to_single₀_epi_at_zero

theorem to_single₀_exact_d_f_at_zero [hf : QuasiIso f] : Exact (X.d 1 0) (f.f 0) := by
  rw [Preadditive.exact_iff_homology_zero]
  -- ⊢ ∃ w, Nonempty (_root_.homology (d X 1 0) (HomologicalComplex.Hom.f f 0) w ≅ 0)
  have h : X.d 1 0 ≫ f.f 0 = 0 := by
    simp only [← f.2 1 0 rfl, ChainComplex.single₀_obj_X_d, comp_zero]
  refine' ⟨h, Nonempty.intro (homologyIsoKernelDesc _ _ _ ≪≫ _)⟩
  -- ⊢ kernel (cokernel.desc (d X 1 0) (HomologicalComplex.Hom.f f 0) h) ≅ 0
  suffices IsIso (cokernel.desc _ _ h) by apply kernel.ofMono
  -- ⊢ IsIso (cokernel.desc (d X 1 0) (HomologicalComplex.Hom.f f 0) h)
  rw [← toSingle₀CokernelAtZeroIso_hom_eq]
  -- ⊢ IsIso (toSingle₀CokernelAtZeroIso f).hom
  infer_instance
  -- 🎉 no goals
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
`d : X₀ → X₁` is isomorphic to `Y`. -/
noncomputable def fromSingle₀KernelAtZeroIso [hf : QuasiIso f] : kernel (X.d 0 1) ≅ Y :=
  X.homologyZeroIso.symm.trans
    ((@asIso _ _ _ _ _ (hf.1 0)).symm.trans ((CochainComplex.homologyFunctor0Single₀ W).app Y))
#align homological_complex.hom.from_single₀_kernel_at_zero_iso HomologicalComplex.Hom.fromSingle₀KernelAtZeroIso

theorem fromSingle₀KernelAtZeroIso_inv_eq [hf : QuasiIso f] :
    f.fromSingle₀KernelAtZeroIso.inv =
      kernel.lift (X.d 0 1) (f.f 0) (by rw [f.2 0 1 rfl]; exact zero_comp) := by
                                        -- ⊢ d ((CochainComplex.single₀ W).obj Y) 0 1 ≫ HomologicalComplex.Hom.f f 1 = 0
                                                          -- 🎉 no goals
  ext
  -- ⊢ (fromSingle₀KernelAtZeroIso f).inv ≫ equalizer.ι (d X 0 1) 0 = kernel.lift ( …
  dsimp only [fromSingle₀KernelAtZeroIso, CochainComplex.homologyZeroIso, homologyOfZeroLeft,
    homology.mapIso, CochainComplex.homologyFunctor0Single₀, kernel.map]
  simp only [Iso.trans_inv, Iso.app_inv, Iso.symm_inv, Category.assoc, equalizer_as_kernel,
    kernel.lift_ι]
  dsimp [asIso]
  -- ⊢ ((inv (Subobject.arrow (kernelSubobject 0)) ≫ homology.π 0 0 (_ : 0 ≫ 0 = 0) …
  simp only [Category.assoc, homology.π_map, cokernelZeroIsoTarget_hom,
    cokernelIsoOfEq_hom_comp_desc, kernelSubobject_arrow, homology.π_map_assoc, IsIso.inv_comp_eq]
  simp [homology.π, kernelSubobjectMap_comp, Iso.refl_hom (X.X 0), Category.comp_id]
  -- 🎉 no goals
#align homological_complex.hom.from_single₀_kernel_at_zero_iso_inv_eq HomologicalComplex.Hom.fromSingle₀KernelAtZeroIso_inv_eq

theorem from_single₀_mono_at_zero [hf : QuasiIso f] : Mono (f.f 0) := by
  constructor
  -- ⊢ ∀ {Z : W} (g h : Z ⟶ HomologicalComplex.X ((CochainComplex.single₀ W).obj Y) …
  intro Z g h Hgh
  -- ⊢ g = h
  rw [← kernel.lift_ι (X.d 0 1) (f.f 0) (by rw [f.2 0 1 rfl]; exact zero_comp),
    ← fromSingle₀KernelAtZeroIso_inv_eq] at Hgh
  rw [(@cancel_mono _ _ _ _ _ _ (mono_comp _ _) _ _).1 Hgh]
  -- 🎉 no goals
#align homological_complex.hom.from_single₀_mono_at_zero HomologicalComplex.Hom.from_single₀_mono_at_zero

theorem from_single₀_exact_f_d_at_zero [hf : QuasiIso f] : Exact (f.f 0) (X.d 0 1) := by
  rw [Preadditive.exact_iff_homology_zero]
  -- ⊢ ∃ w, Nonempty (_root_.homology (HomologicalComplex.Hom.f f 0) (d X 0 1) w ≅ 0)
  have h : f.f 0 ≫ X.d 0 1 = 0 := by
    simp only [HomologicalComplex.Hom.comm, CochainComplex.single₀_obj_X_d, zero_comp]
  refine' ⟨h, Nonempty.intro (homologyIsoCokernelLift _ _ _ ≪≫ _)⟩
  -- ⊢ cokernel (kernel.lift (d X 0 1) (HomologicalComplex.Hom.f f 0) h) ≅ 0
  suffices IsIso (kernel.lift (X.d 0 1) (f.f 0) h) by apply cokernel.ofEpi
  -- ⊢ IsIso (kernel.lift (d X 0 1) (HomologicalComplex.Hom.f f 0) h)
  rw [← fromSingle₀KernelAtZeroIso_inv_eq f]
  -- ⊢ IsIso (fromSingle₀KernelAtZeroIso f).inv
  infer_instance
  -- 🎉 no goals
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

variable {A : Type*} [Category A] [Abelian A] {B : Type*} [Category B] [Abelian B] (F : A ⥤ B)
  [Functor.Additive F] [PreservesFiniteLimits F] [PreservesFiniteColimits F] [Faithful F]

theorem CategoryTheory.Functor.quasiIso_of_map_quasiIso {C D : HomologicalComplex A c} (f : C ⟶ D)
    (hf : QuasiIso ((F.mapHomologicalComplex _).map f)) : QuasiIso f :=
  ⟨fun i =>
    haveI : IsIso (F.map ((homologyFunctor A c i).map f)) := by
      rw [← Functor.comp_map, ← NatIso.naturality_2 (F.homologyFunctorIso i) f, Functor.comp_map]
      -- ⊢ IsIso (NatTrans.app (homologyFunctorIso F i).hom C ≫ (homologyFunctor B c i) …
      infer_instance
      -- 🎉 no goals
    isIso_of_reflects_iso _ F⟩
#align category_theory.functor.quasi_iso_of_map_quasi_iso CategoryTheory.Functor.quasiIso_of_map_quasiIso
