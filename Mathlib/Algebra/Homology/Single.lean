/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Homology.HomologicalComplex

#align_import algebra.homology.single from "leanprover-community/mathlib"@"324a7502510e835cdbd3de1519b6c66b51fb2467"

/-!
# Chain complexes supported in a single degree

We define `single V j c : V ⥤ HomologicalComplex V c`,
which constructs complexes in `V` of shape `c`, supported in degree `j`.

-/

open CategoryTheory Category Limits ZeroObject

universe v u

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V] [HasZeroObject V]

namespace HomologicalComplex

variable {ι : Type*} [DecidableEq ι] (c : ComplexShape ι)

/-- The functor `V ⥤ HomologicalComplex V c` creating a chain complex supported in a single degree.
-/
noncomputable def single (j : ι) : V ⥤ HomologicalComplex V c where
  obj A :=
    { X := fun i => if i = j then A else 0
      d := fun i j => 0 }
  map f :=
    { f := fun i => if h : i = j then eqToHom (by dsimp; rw [if_pos h]) ≫ f ≫
              eqToHom (by dsimp; rw [if_pos h]) else 0 }
  map_id A := by
    ext
    dsimp
    split_ifs with h
    · subst h
      simp
    · rw [if_neg h]
      simp
  map_comp f g := by
    ext
    dsimp
    split_ifs with h
    · subst h
      simp
    · simp
#align homological_complex.single HomologicalComplex.single

/-- The functor `V ⥤ ChainComplex V ℕ` creating a chain complex supported in degree zero. -/
noncomputable abbrev _root_.ChainComplex.single₀ : V ⥤ ChainComplex V ℕ :=
  single V (ComplexShape.down ℕ) 0

/-- The functor `V ⥤ CochainComplex V ℕ` creating a cochain complex supported in degree zero. -/
noncomputable abbrev _root_.CochainComplex.single₀ : V ⥤ CochainComplex V ℕ :=
  single V (ComplexShape.up ℕ) 0

variable {V}

@[simp]
lemma single_obj_X_self (j : ι) (A : V) :
    ((single V c j).obj A).X j = A := if_pos rfl

lemma isZero_single_obj_X (j : ι) (A : V) (i : ι) (hi : i ≠ j) :
    IsZero (((single V c j).obj A).X i) := by
  dsimp [single]
  rw [if_neg hi]
  exact Limits.isZero_zero V

/-- The object in degree `i` of `(single V c h).obj A` is just `A` when `i = j`. -/
noncomputable def singleObjXIsoOfEq (j : ι) (A : V) (i : ι) (hi : i = j) :
    ((single V c j).obj A).X i ≅ A :=
  eqToIso (by subst hi; simp [single])

/-- The object in degree `j` of `(single V c h).obj A` is just `A`. -/
noncomputable def singleObjXSelf (j : ι) (A : V) : ((single V c j).obj A).X j ≅ A :=
  singleObjXIsoOfEq c j A j rfl
set_option linter.uppercaseLean3 false in
#align homological_complex.single_obj_X_self HomologicalComplex.singleObjXSelf

@[simp]
lemma single_obj_d (j : ι) (A : V) (k l : ι) :
    ((single V c j).obj A).d k l = 0 := rfl

@[reassoc]
theorem single_map_f_self (j : ι) {A B : V} (f : A ⟶ B) :
    ((single V c j).map f).f j = (singleObjXSelf c j A).hom ≫
      f ≫ (singleObjXSelf c j B).inv := by
  dsimp [single]
  rw [dif_pos rfl]
  rfl
#align homological_complex.single_map_f_self HomologicalComplex.single_map_f_self

@[ext]
lemma from_single_hom_ext {K : HomologicalComplex V c} {j : ι} {A : V}
    {f g : (single V c j).obj A ⟶ K} (hfg : f.f j = g.f j) : f = g := by
  ext i
  by_cases i = j
  · subst h
    exact hfg
  · apply (isZero_single_obj_X c j A i h).eq_of_src

@[ext]
lemma to_single_hom_ext {K : HomologicalComplex V c} {j : ι} {A : V}
    {f g : K ⟶ (single V c j).obj A} (hfg : f.f j = g.f j) : f = g := by
  ext i
  by_cases i = j
  · subst h
    exact hfg
  · apply (isZero_single_obj_X c j A i h).eq_of_tgt

instance (j : ι) : Faithful (single V c j) where
  map_injective {A B f g} w := by
    rw [← cancel_mono (singleObjXSelf c j B).inv,
      ← cancel_epi (singleObjXSelf c j A).hom, ← single_map_f_self,
      ← single_map_f_self, w]

noncomputable instance (j : ι) : Full (single V c j) where
  preimage {A B} f := (singleObjXSelf c j A).inv ≫ f.f j ≫ (singleObjXSelf c j B).hom
  witness f := by
    ext
    simp [single_map_f_self]

variable {c}

/-- Constructor for morphisms to a single homological complex. -/
noncomputable def mkHomToSingle {K : HomologicalComplex V c} {j : ι} {A : V} (φ : K.X j ⟶ A)
    (hφ : ∀ (i : ι), c.Rel i j → K.d i j ≫ φ = 0) :
    K ⟶ (single V c j).obj A where
  f i :=
    if hi : i = j
      then (K.XIsoOfEq hi).hom ≫ φ ≫ (singleObjXIsoOfEq c j A i hi).inv
      else 0
  comm' i k hik := by
    dsimp
    rw [comp_zero]
    split_ifs with hk
    · subst hk
      simp only [XIsoOfEq_rfl, Iso.refl_hom, id_comp, reassoc_of% hφ i hik, zero_comp]
    · apply (isZero_single_obj_X c j A k hk).eq_of_tgt

@[simp]
lemma mkHomToSingle_f {K : HomologicalComplex V c} {j : ι} {A : V} (φ : K.X j ⟶ A)
    (hφ : ∀ (i : ι), c.Rel i j → K.d i j ≫ φ = 0) :
    (mkHomToSingle φ hφ).f j = φ ≫ (singleObjXSelf c j A).inv := by
  dsimp [mkHomToSingle]
  rw [dif_pos rfl, id_comp]
  rfl

/-- Constructor for morphisms from a single homological complex. -/
noncomputable def mkHomFromSingle {K : HomologicalComplex V c} {j : ι} {A : V} (φ : A ⟶ K.X j)
    (hφ : ∀ (k : ι), c.Rel j k → φ ≫ K.d j k = 0) :
    (single V c j).obj A ⟶ K where
  f i :=
    if hi : i = j
      then (singleObjXIsoOfEq c j A i hi).hom ≫ φ ≫ (K.XIsoOfEq hi).inv
      else 0
  comm' i k hik := by
    dsimp
    rw [zero_comp]
    split_ifs with hi
    · subst hi
      simp only [XIsoOfEq_rfl, Iso.refl_inv, comp_id, assoc, hφ k hik, comp_zero]
    · apply (isZero_single_obj_X c j A i hi).eq_of_src

@[simp]
lemma mkHomFromSingle_f {K : HomologicalComplex V c} {j : ι} {A : V} (φ : A ⟶ K.X j)
    (hφ : ∀ (k : ι), c.Rel j k → φ ≫ K.d j k = 0) :
    (mkHomFromSingle φ hφ).f j = (singleObjXSelf c j A).hom ≫ φ := by
  dsimp [mkHomFromSingle]
  rw [dif_pos rfl, comp_id]
  rfl

end HomologicalComplex

variable {V}

namespace ChainComplex

@[simp]
lemma single₀ObjXSelf (X : V) :
    HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 X = Iso.refl _ := rfl

/-- Morphisms from an `ℕ`-indexed chain complex `C`
to a single object chain complex with `X` concentrated in degree 0
are the same as morphisms `f : C.X 0 ⟶ X` such that `C.d 1 0 ≫ f = 0`.
-/
@[simps]
noncomputable def toSingle₀Equiv (C : ChainComplex V ℕ) (X : V) :
    (C ⟶ (single₀ V).obj X) ≃ { f : C.X 0 ⟶ X // C.d 1 0 ≫ f = 0 } where
  toFun φ := ⟨φ.f 0, by rw [← φ.comm 1 0, HomologicalComplex.single_obj_d, comp_zero]⟩
  invFun f := HomologicalComplex.mkHomToSingle f.1 (fun i hi => by
    obtain rfl : i = 1 := by simpa using hi.symm
    exact f.2)
  left_inv φ := by
    ext
    dsimp
    simp only [HomologicalComplex.mkHomToSingle_f, single₀ObjXSelf, Iso.refl_inv]
    erw [comp_id]
  right_inv f := by
    ext
    simp only [HomologicalComplex.mkHomToSingle_f, single₀ObjXSelf, Iso.refl_inv]
    erw [comp_id]

end ChainComplex

namespace CochainComplex

@[simp]
lemma single₀ObjXSelf (X : V) :
    HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 X = Iso.refl _ := rfl

/-- Morphisms from a single object cochain complex with `X` concentrated in degree 0
to an `ℕ`-indexed cochain complex `C`
are the same as morphisms `f : X ⟶ C.X 0` such that `f ≫ C.d 0 1 = 0`. -/
noncomputable def fromSingle₀Equiv (C : CochainComplex V ℕ) (X : V) :
    ((single₀ V).obj X ⟶ C) ≃ { f : X ⟶ C.X 0 // f ≫ C.d 0 1 = 0 } where
  toFun φ := ⟨φ.f 0, by rw [φ.comm 0 1, HomologicalComplex.single_obj_d, zero_comp]⟩
  invFun f := HomologicalComplex.mkHomFromSingle f.1 (fun i hi => by
    obtain rfl : i = 1 := by simpa using hi.symm
    exact f.2)
  left_inv φ := by aesop_cat
  right_inv := by aesop_cat

end CochainComplex

/-

namespace ChainComplex

variable [HasEqualizers V] [HasCokernels V] [HasImages V] [HasImageMaps V]

/-- Sending objects to chain complexes supported at `0` then taking `0`-th homology
is the same as doing nothing.
-/
noncomputable def homology'Functor0Single₀ : single₀ V ⋙ homology'Functor V _ 0 ≅ 𝟭 V :=
  NatIso.ofComponents (fun X => homology'.congr _ _ (by simp) (by simp) ≪≫ homology'ZeroZero)
    fun f => by
      -- Porting note: why can't `aesop_cat` do this?
      dsimp
      ext
      simp
#align chain_complex.homology_functor_0_single₀ ChainComplex.homology'Functor0Single₀

/-- Sending objects to chain complexes supported at `0` then taking `(n+1)`-st homology
is the same as the zero functor.
-/
noncomputable def homology'FunctorSuccSingle₀ (n : ℕ) :
    single₀ V ⋙ homology'Functor V _ (n + 1) ≅ 0 :=
  NatIso.ofComponents
    (fun X =>
      homology'.congr _ _ (by simp) (by simp) ≪≫
        homology'ZeroZero ≪≫ (Functor.zero_obj _).isoZero.symm)
    fun f => (Functor.zero_obj _).eq_of_tgt _ _
#align chain_complex.homology_functor_succ_single₀ ChainComplex.homology'FunctorSuccSingle₀

end

namespace CochainComplex

variable [HasEqualizers V] [HasCokernels V] [HasImages V] [HasImageMaps V]

/-- Sending objects to cochain complexes supported at `0` then taking `0`-th homology
is the same as doing nothing.
-/
noncomputable def homologyFunctor0Single₀ : single₀ V ⋙ homology'Functor V _ 0 ≅ 𝟭 V :=
  NatIso.ofComponents (fun X => homology'.congr _ _ (by simp) (by simp) ≪≫ homology'ZeroZero)
    fun f => by
      -- Porting note: why can't `aesop_cat` do this?
      dsimp
      ext
      simp
#align cochain_complex.homology_functor_0_single₀ CochainComplex.homologyFunctor0Single₀

/-- Sending objects to cochain complexes supported at `0` then taking `(n+1)`-st homology
is the same as the zero functor.
-/
noncomputable def homology'FunctorSuccSingle₀ (n : ℕ) :
    single₀ V ⋙ homology'Functor V _ (n + 1) ≅ 0 :=
  NatIso.ofComponents
    (fun X =>
      homology'.congr _ _ (by simp) (by simp) ≪≫
        homology'ZeroZero ≪≫ (Functor.zero_obj _).isoZero.symm)
    fun f => (Functor.zero_obj _).eq_of_tgt _ _
#align cochain_complex.homology_functor_succ_single₀ CochainComplex.homology'FunctorSuccSingle₀

end CochainComplex

-/
