/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Joël Riou
-/
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.CategoryTheory.Abelian.Homology
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

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

/- redundant with the new homology API

section

variable {ι : Type _}

variable {V : Type u} [Category.{v} V] [HasZeroMorphisms V] [HasZeroObject V]

variable [HasEqualizers V] [HasImages V] [HasImageMaps V] [HasCokernels V]

variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}

/-- A chain map is a quasi-isomorphism if it induces isomorphisms on homology.
-/
class QuasiIso' (f : C ⟶ D) : Prop where
  IsIso : ∀ i, IsIso ((homology'Functor V c i).map f)
#align quasi_iso QuasiIso'

attribute [instance] QuasiIso'.IsIso

instance (priority := 100) quasiIso'_of_iso (f : C ⟶ D) [IsIso f] : QuasiIso' f where
  IsIso i := by
    change IsIso ((homology'Functor V c i).mapIso (asIso f)).hom
    infer_instance
#align quasi_iso_of_iso quasiIso'_of_iso

instance quasiIso'_comp (f : C ⟶ D) [QuasiIso' f] (g : D ⟶ E) [QuasiIso' g] : QuasiIso' (f ≫ g) where
  IsIso i := by
    rw [Functor.map_comp]
    infer_instance
#align quasi_iso_comp quasiIso'_comp

theorem quasiIso'_of_comp_left (f : C ⟶ D) [QuasiIso' f] (g : D ⟶ E) [QuasiIso' (f ≫ g)] :
    QuasiIso' g :=
  { IsIso := fun i => IsIso.of_isIso_fac_left ((homology'Functor V c i).map_comp f g).symm }
#align quasi_iso_of_comp_left quasiIso'_of_comp_left

theorem quasiIso'_of_comp_right (f : C ⟶ D) (g : D ⟶ E) [QuasiIso' g] [QuasiIso' (f ≫ g)] :
    QuasiIso' f :=
  { IsIso := fun i => IsIso.of_isIso_fac_right ((homology'Functor V c i).map_comp f g).symm }
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
    constructor <;> apply homology_map_eq_of_homotopy
    exacts [e.homotopyHomInvId, e.homotopyInvHomId]⟩
#align homotopy_equiv.to_quasi_iso HomotopyEquiv.toQuasiIso'

theorem toQuasiIso'_inv {C D : HomologicalComplex W c} (e : HomotopyEquiv C D) (i : ι) :
    (@asIso _ _ _ _ _ (e.toQuasiIso'.1 i)).inv = (homology'Functor W c i).map e.inv := by
  symm
  haveI := e.toQuasiIso'.1 i -- Porting note: Added this to get `asIso_hom` to work.
  simp only [← Iso.hom_comp_eq_id, asIso_hom, ← Functor.map_comp, ← (homology'Functor W c i).map_id,
    homology_map_eq_of_homotopy e.homotopyHomInvId _]
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
    ((@asIso _ _ _ _ _ (hf.1 0)).symm.trans ((CochainComplex.homology'Functor0Single₀ W).app Y))
#align homological_complex.hom.from_single₀_kernel_at_zero_iso HomologicalComplex.Hom.fromSingle₀KernelAtZeroIso

theorem fromSingle₀KernelAtZeroIso_inv_eq [hf : QuasiIso' f] :
    f.fromSingle₀KernelAtZeroIso.inv =
      kernel.lift (X.d 0 1) (f.f 0) (by rw [f.2 0 1 rfl]; exact zero_comp) := by
  ext
  dsimp only [fromSingle₀KernelAtZeroIso, CochainComplex.homology'ZeroIso, homology'OfZeroLeft,
    homology'.mapIso, CochainComplex.homology'Functor0Single₀, kernel.map]
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

theorem CategoryTheory.Functor.quasiIso'_of_map_quasiIso' {C D : HomologicalComplex A c} (f : C ⟶ D)
    (hf : QuasiIso' ((F.mapHomologicalComplex _).map f)) : QuasiIso' f :=
  ⟨fun i =>
    haveI : IsIso (F.map ((homology'Functor A c i).map f)) := by
      rw [← Functor.comp_map, ← NatIso.naturality_2 (F.homology'FunctorIso i) f, Functor.comp_map]
      infer_instance
    isIso_of_reflects_iso _ F⟩
#align category_theory.functor.quasi_iso_of_map_quasi_iso CategoryTheory.Functor.quasiIso'_of_map_quasiIso'

end-/

section

variable {ι : Type _}

variable {V : Type u} [Category.{v} V] [HasZeroMorphisms V]

variable {c : ComplexShape ι} {C D E F : HomologicalComplex V c}

class QuasiIsoAt (f : C ⟶ D) (i : ι) [C.HasHomology i] [D.HasHomology i] : Prop where
  quasiIso : ShortComplex.QuasiIso ((HomologicalComplex.shortComplexFunctor V c i).map f)

lemma quasiIsoAt_iff (f : C ⟶ D) (i : ι) [C.HasHomology i] [D.HasHomology i] :
    QuasiIsoAt f i ↔
      ShortComplex.QuasiIso ((HomologicalComplex.shortComplexFunctor V c i).map f) := by
  constructor
  · intro h
    exact h.quasiIso
  · intro h
    exact ⟨h⟩

lemma quasiIsoAt_iff' (f : C ⟶ D) (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
    [C.HasHomology j] [D.HasHomology j] [(C.sc' i j k).HasHomology] [(D.sc' i j k).HasHomology] :
    QuasiIsoAt f j ↔
      ShortComplex.QuasiIso ((HomologicalComplex.shortComplexFunctor' V c i j k).map f) := by
  rw [quasiIsoAt_iff]
  exact ShortComplex.quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoOfNatIso (HomologicalComplex.natIsoSc' V c i j k hi hk) (Arrow.mk f))

lemma quasiIsoAt_iff_isIso_homologyMap (f : C ⟶ D) (i : ι)
    [C.HasHomology i] [D.HasHomology i] :
    QuasiIsoAt f i ↔ IsIso ((HomologicalComplex.homologyMap f i)) := by
  rw [quasiIsoAt_iff, ShortComplex.quasiIso_iff]
  rfl

lemma quasiIsoAt_iff_exactAt (f : C ⟶ D) (i : ι) [C.HasHomology i] [D.HasHomology i]
    (hC : C.ExactAt i) :
    QuasiIsoAt f i ↔ D.ExactAt i := by
  simp only [quasiIsoAt_iff, ShortComplex.quasiIso_iff, HomologicalComplex.exactAt_iff,
    ShortComplex.exact_iff_isZero_homology] at hC ⊢
  constructor
  · intro h
    exact IsZero.of_iso hC (@asIso _ _ _ _ _ h).symm
  · intro hD
    exact ⟨⟨0, IsZero.eq_of_src hC _ _, IsZero.eq_of_tgt hD _ _⟩⟩

lemma quasiIsoAt_iff_exactAt' (f : C ⟶ D) (i : ι) [C.HasHomology i] [D.HasHomology i]
    (hD : D.ExactAt i) :
    QuasiIsoAt f i ↔ C.ExactAt i := by
  simp only [quasiIsoAt_iff, ShortComplex.quasiIso_iff, HomologicalComplex.exactAt_iff,
    ShortComplex.exact_iff_isZero_homology] at hD ⊢
  constructor
  · intro h
    exact IsZero.of_iso hD (@asIso _ _ _ _ _ h)
  · intro hC
    exact ⟨⟨0, IsZero.eq_of_src hC _ _, IsZero.eq_of_tgt hD _ _⟩⟩

instance (f : C ⟶ D) (i : ι) [C.HasHomology i] [D.HasHomology i] [hf : QuasiIsoAt f i] :
    IsIso (HomologicalComplex.homologyMap f i) := by
  simpa only [quasiIsoAt_iff, ShortComplex.quasiIso_iff] using hf

@[simps! hom]
noncomputable def isoOfQuasiIsoAt (f : C ⟶ D) (i : ι) [C.HasHomology i] [D.HasHomology i]
    [QuasiIsoAt f i] : C.homology i ≅ D.homology i :=
  asIso (HomologicalComplex.homologyMap f i)

@[reassoc (attr := simp)]
lemma isoOfQuasiIsoAt_hom_inv_id (f : C ⟶ D) (i : ι) [C.HasHomology i] [D.HasHomology i]
    [QuasiIsoAt f i] :
    HomologicalComplex.homologyMap f i ≫ (isoOfQuasiIsoAt f i).inv = 𝟙 _ :=
  (isoOfQuasiIsoAt f i).hom_inv_id

@[reassoc (attr := simp)]
lemma isoOfQuasiIsoAt_inv_hom_id (f : C ⟶ D) (i : ι) [C.HasHomology i] [D.HasHomology i]
    [QuasiIsoAt f i] :
    (isoOfQuasiIsoAt f i).inv ≫ HomologicalComplex.homologyMap f i = 𝟙 _ :=
  (isoOfQuasiIsoAt f i).inv_hom_id

class QuasiIso (f : C ⟶ D) [∀ i, C.HasHomology i] [∀ i, D.HasHomology i] : Prop where
  quasiIso : ∀ i, QuasiIsoAt f i := by infer_instance

attribute [instance] QuasiIso.quasiIso

instance quasiIsoAt_of_isIso (f : C ⟶ D) [IsIso f] (i : ι) [C.HasHomology i] [D.HasHomology i] :
    QuasiIsoAt f i := by
  rw [quasiIsoAt_iff]
  infer_instance

instance quasiIso_of_isIso (f : C ⟶ D) [IsIso f] [∀ i, C.HasHomology i] [∀ i, D.HasHomology i] :
    QuasiIso f where

lemma quasiIso_iff_mem_qis (f : C ⟶ D) [CategoryWithHomology V] :
    QuasiIso f ↔ HomologicalComplex.qis _ _ f := by
  dsimp [HomologicalComplex.qis]
  simp only [← quasiIsoAt_iff_isIso_homologyMap f]
  constructor
  · intro h i
    infer_instance
  · intro h
    exact ⟨h⟩

lemma CochainComplex.quasiIsoAt₀_iff {K L : CochainComplex V ℕ} (f : K ⟶ L)
    [K.HasHomology 0] [L.HasHomology 0] [(K.sc' 0 0 1).HasHomology] [(L.sc' 0 0 1).HasHomology] :
    QuasiIsoAt f 0 ↔
      ShortComplex.QuasiIso ((HomologicalComplex.shortComplexFunctor' V _ 0 0 1).map f) :=
  quasiIsoAt_iff' _ _ _ _ (by simp) (by simp)

lemma ChainComplex.quasiIsoAt₀_iff {K L : ChainComplex V ℕ} (f : K ⟶ L)
    [K.HasHomology 0] [L.HasHomology 0] [(K.sc' 1 0 0).HasHomology] [(L.sc' 1 0 0).HasHomology] :
    QuasiIsoAt f 0 ↔
      ShortComplex.QuasiIso ((HomologicalComplex.shortComplexFunctor' V _ 1 0 0).map f) :=
  quasiIsoAt_iff' _ _ _ _ (by simp) (by simp)

lemma quasiIsoAt_comp'' (φ : C ⟶ D) (φ' : D ⟶ E) (n : ι) [C.HasHomology n]
    [D.HasHomology n] [E.HasHomology n]
    (hφ : QuasiIsoAt φ n) (hφ' : QuasiIsoAt φ' n) :
    QuasiIsoAt (φ ≫ φ') n := by
  rw [quasiIsoAt_iff] at hφ hφ' ⊢
  rw [Functor.map_comp]
  exact ShortComplex.quasiIso_comp _ _

instance quasiIsoAt_comp (φ : C ⟶ D) (φ' : D ⟶ E) (n : ι)
    [C.HasHomology n] [D.HasHomology n] [E.HasHomology n]
    [hφ : QuasiIsoAt φ n] [hφ' : QuasiIsoAt φ' n] :
    QuasiIsoAt (φ ≫ φ') n :=
  quasiIsoAt_comp'' φ φ' n hφ hφ'

lemma quasiIso_comp'' (φ : C ⟶ D) (φ' : D ⟶ E)
    [∀ n, C.HasHomology n] [∀ n, D.HasHomology n] [∀ n, E.HasHomology n]
    (_ : QuasiIso φ) (_ : QuasiIso φ') :
    QuasiIso (φ ≫ φ') where
  quasiIso n := quasiIsoAt_comp φ φ' n

instance quasiIso_comp (φ : C ⟶ D) (φ' : D ⟶ E)
    [∀ n, C.HasHomology n] [∀ n, D.HasHomology n] [∀ n, E.HasHomology n]
    [hφ : QuasiIso φ] [hφ' : QuasiIso φ'] :
    QuasiIso (φ ≫ φ') :=
  quasiIso_comp'' φ φ' hφ hφ'

lemma quasiIsoAt_of_comp_left'' (φ : C ⟶ D) (φ' : D ⟶ E) (n : ι)
    [C.HasHomology n] [D.HasHomology n] [E.HasHomology n]
    (hφ : QuasiIsoAt φ n) (hφφ' : QuasiIsoAt (φ ≫ φ') n) :
    QuasiIsoAt φ' n := by
  rw [quasiIsoAt_iff] at hφ hφφ' ⊢
  rw [Functor.map_comp] at hφφ'
  exact ShortComplex.quasiIso_of_comp_left (hφ := hφ) (hφφ' := hφφ')

lemma quasiIsoAt_of_comp_left (φ : C ⟶ D) (φ' : D ⟶ E) (n : ι)
    [C.HasHomology n] [D.HasHomology n] [E.HasHomology n]
    [hφ : QuasiIsoAt φ n] [hφφ' : QuasiIsoAt (φ ≫ φ') n] :
    QuasiIsoAt φ' n :=
  quasiIsoAt_of_comp_left'' φ φ' n hφ hφφ'

lemma quasiIso_of_comp_left'' (φ : C ⟶ D) (φ' : D ⟶ E)
    [∀ n, C.HasHomology n] [∀ n, D.HasHomology n] [∀ n, E.HasHomology n]
    (_ : QuasiIso φ) (_ : QuasiIso (φ ≫ φ')) :
    QuasiIso φ' where
  quasiIso n := quasiIsoAt_of_comp_left φ φ' n

lemma quasiIso_of_comp_left (φ : C ⟶ D) (φ' : D ⟶ E)
    [∀ n, C.HasHomology n] [∀ n, D.HasHomology n] [∀ n, E.HasHomology n]
    [hφ : QuasiIso φ] [hφφ' : QuasiIso (φ ≫ φ')] :
    QuasiIso φ' :=
  quasiIso_of_comp_left'' φ φ' hφ hφφ'

@[simp]
lemma quasiIsoAt_iff_comp_left'' (φ : C ⟶ D) (φ' : D ⟶ E) (n : ι)
    [C.HasHomology n] [D.HasHomology n] [E.HasHomology n]
    (hφ : QuasiIsoAt φ n) :
    QuasiIsoAt (φ ≫ φ') n ↔ QuasiIsoAt φ' n := by
  constructor
  · intro hφφ'
    exact quasiIsoAt_of_comp_left φ φ' n
  · intro hφ
    infer_instance

@[simp]
lemma quasiIsoAt_iff_comp_left (φ : C ⟶ D) (φ' : D ⟶ E) (n : ι)
    [C.HasHomology n] [D.HasHomology n] [E.HasHomology n]
    [hφ : QuasiIsoAt φ n] :
    QuasiIsoAt (φ ≫ φ') n ↔ QuasiIsoAt φ' n :=
  quasiIsoAt_iff_comp_left'' φ φ' n hφ

@[simp]
lemma quasiIso_iff_comp_left'' (φ : C ⟶ D) (φ' : D ⟶ E)
    [∀ n, C.HasHomology n] [∀ n, D.HasHomology n] [∀ n, E.HasHomology n]
    (hφ : QuasiIso φ) :
    QuasiIso (φ ≫ φ') ↔ QuasiIso φ' := by
  constructor
  · intro
    exact quasiIso_of_comp_left φ φ'
  · intro hφ'
    infer_instance

@[simp]
lemma quasiIso_iff_comp_left (φ : C ⟶ D) (φ' : D ⟶ E)
    [∀ n, C.HasHomology n] [∀ n, D.HasHomology n] [∀ n, E.HasHomology n]
    [hφ : QuasiIso φ] :
    QuasiIso (φ ≫ φ') ↔ QuasiIso φ' :=
  quasiIso_iff_comp_left'' φ φ' hφ

-----

lemma quasiIsoAt_of_comp_right'' (φ : C ⟶ D) (φ' : D ⟶ E) (n : ι)
    [C.HasHomology n] [D.HasHomology n] [E.HasHomology n]
    (hφ' : QuasiIsoAt φ' n) (hφφ' : QuasiIsoAt (φ ≫ φ') n) :
    QuasiIsoAt φ n := by
  rw [quasiIsoAt_iff] at hφ' hφφ' ⊢
  rw [Functor.map_comp] at hφφ'
  exact ShortComplex.quasiIso_of_comp_right (hφ' := hφ') (hφφ' := hφφ')

lemma quasiIsoAt_of_comp_right (φ : C ⟶ D) (φ' : D ⟶ E) (n : ι)
    [C.HasHomology n] [D.HasHomology n] [E.HasHomology n]
    [hφ' : QuasiIsoAt φ' n] [hφφ' : QuasiIsoAt (φ ≫ φ') n] :
    QuasiIsoAt φ n :=
  quasiIsoAt_of_comp_right'' φ φ' n hφ' hφφ'

lemma quasiIso_of_comp_right'' (φ : C ⟶ D) (φ' : D ⟶ E)
    [∀ n, C.HasHomology n] [∀ n, D.HasHomology n] [∀ n, E.HasHomology n]
    (_ : QuasiIso φ') (_ : QuasiIso (φ ≫ φ')) :
    QuasiIso φ where
  quasiIso n := quasiIsoAt_of_comp_right φ φ' n

lemma quasiIso_of_comp_right (φ : C ⟶ D) (φ' : D ⟶ E)
    [∀ n, C.HasHomology n] [∀ n, D.HasHomology n] [∀ n, E.HasHomology n]
    [hφ' : QuasiIso φ'] [hφφ' : QuasiIso (φ ≫ φ')] :
    QuasiIso φ :=
  quasiIso_of_comp_right'' φ φ' hφ' hφφ'

@[simp]
lemma quasiIsoAt_iff_comp_right'' (φ : C ⟶ D) (φ' : D ⟶ E) (n : ι)
    [C.HasHomology n] [D.HasHomology n] [E.HasHomology n]
    (hφ' : QuasiIsoAt φ' n) :
    QuasiIsoAt (φ ≫ φ') n ↔ QuasiIsoAt φ n := by
  constructor
  · intro hφφ'
    exact quasiIsoAt_of_comp_right φ φ' n
  · intro hφ
    infer_instance

@[simp]
lemma quasiIsoAt_iff_comp_right (φ : C ⟶ D) (φ' : D ⟶ E) (n : ι)
    [C.HasHomology n] [D.HasHomology n] [E.HasHomology n]
    [hφ' : QuasiIsoAt φ' n] :
    QuasiIsoAt (φ ≫ φ') n ↔ QuasiIsoAt φ n :=
  quasiIsoAt_iff_comp_right'' φ φ' n hφ'

@[simp]
lemma quasiIso_iff_comp_right'' (φ : C ⟶ D) (φ' : D ⟶ E)
    [∀ n, C.HasHomology n] [∀ n, D.HasHomology n] [∀ n, E.HasHomology n]
    (hφ' : QuasiIso φ') :
    QuasiIso (φ ≫ φ') ↔ QuasiIso φ := by
  constructor
  · intro
    exact quasiIso_of_comp_right φ φ'
  · intro hφ
    infer_instance

@[simp]
lemma quasiIso_iff_comp_right (φ : C ⟶ D) (φ' : D ⟶ E)
    [∀ n, C.HasHomology n] [∀ n, D.HasHomology n] [∀ n, E.HasHomology n]
    [hφ' : QuasiIso φ'] :
    QuasiIso (φ ≫ φ') ↔ QuasiIso φ :=
  quasiIso_iff_comp_right'' φ φ' hφ'

lemma quasiIsoAt_of_arrow_mk_iso'
    (φ : C ⟶ D) (φ' : E ⟶ F) (e : Arrow.mk φ ≅ Arrow.mk φ') (n : ι)
    [C.HasHomology n] [D.HasHomology n] [E.HasHomology n] [F.HasHomology n]
    (hφ : QuasiIsoAt φ n) : QuasiIsoAt φ' n := by
  let α : E ⟶ C := e.inv.left
  let β : D ⟶ F := e.hom.right
  suffices φ' = α ≫ φ ≫ β by
    rw [this]
    infer_instance
  simp only [Arrow.w_mk_right_assoc, Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom,
    ← Arrow.comp_right, e.inv_hom_id, Arrow.id_right, Category.comp_id]

lemma quasiIsoAt_of_arrow_mk_iso
    (φ : C ⟶ D) (φ' : E ⟶ F) (e : Arrow.mk φ ≅ Arrow.mk φ') (n : ι)
    [C.HasHomology n] [D.HasHomology n] [E.HasHomology n] [F.HasHomology n]
    [QuasiIsoAt φ n] : QuasiIsoAt φ' n :=
  quasiIsoAt_of_arrow_mk_iso' φ φ' e n inferInstance

lemma quasiIsoAt_iff_of_arrow_mk_iso
    (φ : C ⟶ D) (φ' : E ⟶ F) (e : Arrow.mk φ ≅ Arrow.mk φ') (n : ι)
    [C.HasHomology n] [D.HasHomology n] [E.HasHomology n] [F.HasHomology n] :
    QuasiIsoAt φ n ↔ QuasiIsoAt φ' n :=
  ⟨quasiIsoAt_of_arrow_mk_iso' φ φ' e n, quasiIsoAt_of_arrow_mk_iso' φ' φ e.symm n⟩

lemma quasiIso_of_arrow_mk_iso'
    (φ : C ⟶ D) (φ' : E ⟶ F) (e : Arrow.mk φ ≅ Arrow.mk φ')
    [∀ n, C.HasHomology n] [∀ n, D.HasHomology n] [∀ n, E.HasHomology n] [∀ n, F.HasHomology n]
    (_ : QuasiIso φ) : QuasiIso φ' where
  quasiIso n := quasiIsoAt_of_arrow_mk_iso φ φ' e n

lemma quasiIso_of_arrow_mk_iso
    (φ : C ⟶ D) (φ' : E ⟶ F) (e : Arrow.mk φ ≅ Arrow.mk φ')
    [∀ n, C.HasHomology n] [∀ n, D.HasHomology n] [∀ n, E.HasHomology n] [∀ n, F.HasHomology n]
    [QuasiIso φ] : QuasiIso φ' :=
  quasiIso_of_arrow_mk_iso' φ φ' e inferInstance

lemma quasiIso_iff_of_arrow_mk_iso
    (φ : C ⟶ D) (φ' : E ⟶ F) (e : Arrow.mk φ ≅ Arrow.mk φ')
    [∀ n, C.HasHomology n] [∀ n, D.HasHomology n] [∀ n, E.HasHomology n] [∀ n, F.HasHomology n] :
    QuasiIso φ ↔ QuasiIso φ' :=
  ⟨quasiIso_of_arrow_mk_iso' φ φ' e, quasiIso_of_arrow_mk_iso' φ' φ e.symm⟩

end

section

variable {C D : Type _} [Category C] [Preadditive C]
  [Category D] [Preadditive D] (F : C ⥤ D) [F.Additive]
  {ι : Type _} {c : ComplexShape ι} {K L : HomologicalComplex C c} (f : K ⟶ L)

instance CategoryTheory.Functor.map_quasiIsoAt_of_preservesHomology
    [F.PreservesHomology] (n : ι)
    [K.HasHomology n] [L.HasHomology n]
    [((F.mapHomologicalComplex c).obj K).HasHomology n]
    [((F.mapHomologicalComplex c).obj L).HasHomology n]
    [hf : QuasiIsoAt f n] : QuasiIsoAt ((F.mapHomologicalComplex c).map f) n := by
  rw [quasiIsoAt_iff] at hf ⊢
  exact ShortComplex.quasiIso_map_of_preservesRightHomology F ((HomologicalComplex.shortComplexFunctor C c n).map f)

instance CategoryTheory.Functor.map_quasiIso_of_preservesHomology
    [F.PreservesHomology] [∀ n, K.HasHomology n] [∀ n, L.HasHomology n]
    [∀ n, ((F.mapHomologicalComplex c).obj K).HasHomology n]
    [∀ n, ((F.mapHomologicalComplex c).obj L).HasHomology n]
    [QuasiIso f] : QuasiIso ((F.mapHomologicalComplex c).map f) where

lemma CategoryTheory.Functor.quasiIsoAt_of_map_quasiIsoAt_of_preservesHomology
    [F.PreservesHomology] [ReflectsIsomorphisms F] (n : ι)
    [K.HasHomology n] [L.HasHomology n]
    [((F.mapHomologicalComplex c).obj K).HasHomology n]
    [((F.mapHomologicalComplex c).obj L).HasHomology n]
    (hf : QuasiIsoAt ((F.mapHomologicalComplex c).map f) n) :
    QuasiIsoAt f n := by
  rw [quasiIsoAt_iff] at hf ⊢
  exact (ShortComplex.quasiIso_map_iff_of_preservesRightHomology
    F ((HomologicalComplex.shortComplexFunctor C c n).map f)).1  hf

lemma CategoryTheory.Functor.quasiIso_of_map_quasiIso_of_preservesHomology
    [F.PreservesHomology] [ReflectsIsomorphisms F] [∀ n, K.HasHomology n] [∀ n, L.HasHomology n]
    [∀ n, ((F.mapHomologicalComplex c).obj K).HasHomology n]
    [∀ n, ((F.mapHomologicalComplex c).obj L).HasHomology n]
    (_ : QuasiIso ((F.mapHomologicalComplex c).map f)) :
    QuasiIso f where
  quasiIso n := F.quasiIsoAt_of_map_quasiIsoAt_of_preservesHomology f n inferInstance

end

section

variable {A : Type _} [Category A] [Preadditive A] {ι : Type _} {c : ComplexShape ι}
  {K L : HomologicalComplex A c} (e : HomotopyEquiv K L) [DecidableRel c.Rel]

instance HomotopyEquiv.toQuasiIsoAt (n : ι) [K.HasHomology n] [L.HasHomology n] :
    QuasiIsoAt e.hom n := by
  rw [quasiIsoAt_iff, ShortComplex.quasiIso_iff]
  exact IsIso.of_iso (e.toHomologyIso n)

def HomotopyEquiv.toQuasiIso [∀ n, K.HasHomology n] [∀ n, L.HasHomology n] :
    QuasiIso e.hom :=
  ⟨fun _ => inferInstance⟩

end
