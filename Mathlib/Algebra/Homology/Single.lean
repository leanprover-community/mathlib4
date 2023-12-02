/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Homology.HomologicalComplex

#align_import algebra.homology.single from "leanprover-community/mathlib"@"324a7502510e835cdbd3de1519b6c66b51fb2467"

/-!
# Homological complexes supported in a single degree

We define `single V j c : V ⥤ HomologicalComplex V c`,
which constructs complexes in `V` of shape `c`, supported in degree `j`.

In `ChainComplex.toSingle₀Equiv` we characterize chain maps to an
`ℕ`-indexed complex concentrated in degree 0; they are equivalent to
`{ f : C.X 0 ⟶ X // C.d 1 0 ≫ f = 0 }`.
(This is useful translating between a projective resolution and
an augmented exact complex of projectives.)

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

<<<<<<< HEAD
def singleObjXIsoOfEq (j : ι) (A : V) (i : ι) (hi : i = j) :
    ((single V c j).obj A).X i ≅ A := eqToIso (by subst hi ; simp)

lemma isZeroSingleObjX (j : ι) (A : V) (i : ι) (hi : i ≠ j) :
    IsZero (((single V c j).obj A).X i) := by
  dsimp
  rw [if_neg hi]
  apply Limits.isZero_zero

@[simp 1100]
=======
@[simp]
lemma single_obj_d (j : ι) (A : V) (k l : ι) :
    ((single V c j).obj A).d k l = 0 := rfl

@[reassoc]
>>>>>>> origin/homology-sequence-computation
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
  by_cases h : i = j
  · subst h
    exact hfg
  · apply (isZero_single_obj_X c j A i h).eq_of_src

@[ext]
lemma to_single_hom_ext {K : HomologicalComplex V c} {j : ι} {A : V}
    {f g : K ⟶ (single V c j).obj A} (hfg : f.f j = g.f j) : f = g := by
  ext i
  by_cases h : i = j
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

namespace ChainComplex

<<<<<<< HEAD
/-- `ChainComplex.single₀ V` is the embedding of `V` into `ChainComplex V ℕ`
as chain complexes supported in degree 0.

This is naturally isomorphic to `single V _ 0`, but has better definitional properties.
-/
def single₀ : V ⥤ ChainComplex V ℕ where
  obj X :=
    { X := fun n =>
        match n with
        | 0 => X
        | _ + 1 => 0
      d := fun i j => 0 }
  map f :=
    { f := fun n =>
        match n with
        | 0 => f
        | n + 1 => 0 }
  map_id X := by
    ext (_|_)
    · rfl
    · simp
  map_comp f g := by
    ext (_|_)
    · rfl
    · simp
#align chain_complex.single₀ ChainComplex.single₀

@[simp]
theorem single₀_obj_X_0 (X : V) : ((single₀ V).obj X).X 0 = X :=
  rfl
set_option linter.uppercaseLean3 false in
#align chain_complex.single₀_obj_X_0 ChainComplex.single₀_obj_X_0

@[simp]
theorem single₀_obj_X_succ (X : V) (n : ℕ) : ((single₀ V).obj X).X (n + 1) = 0 :=
  rfl
set_option linter.uppercaseLean3 false in
#align chain_complex.single₀_obj_X_succ ChainComplex.single₀_obj_X_succ

@[simp]
theorem single₀_obj_X_d (X : V) (i j : ℕ) : ((single₀ V).obj X).d i j = 0 :=
  rfl
set_option linter.uppercaseLean3 false in
#align chain_complex.single₀_obj_X_d ChainComplex.single₀_obj_X_d

@[simp]
theorem single₀_obj_X_dTo (X : V) (j : ℕ) : ((single₀ V).obj X).dTo j = 0 := by
  rw [dTo_eq ((single₀ V).obj X) rfl]
  simp
set_option linter.uppercaseLean3 false in
#align chain_complex.single₀_obj_X_d_to ChainComplex.single₀_obj_X_dTo

@[simp]
theorem single₀_obj_x_dFrom (X : V) (i : ℕ) : ((single₀ V).obj X).dFrom i = 0 := by
  cases i
  · rw [dFrom_eq_zero]
    simp
  · erw [dFrom_eq ((single₀ V).obj X) rfl]
    simp
set_option linter.uppercaseLean3 false in
#align chain_complex.single₀_obj_X_d_from ChainComplex.single₀_obj_x_dFrom

@[simp]
theorem single₀_map_f_0 {X Y : V} (f : X ⟶ Y) : ((single₀ V).map f).f 0 = f :=
  rfl
#align chain_complex.single₀_map_f_0 ChainComplex.single₀_map_f_0

@[simp]
theorem single₀_map_f_succ {X Y : V} (f : X ⟶ Y) (n : ℕ) : ((single₀ V).map f).f (n + 1) = 0 :=
  rfl
#align chain_complex.single₀_map_f_succ ChainComplex.single₀_map_f_succ

/-section

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

end-/
=======
/-- The functor `V ⥤ ChainComplex V ℕ` creating a chain complex supported in degree zero. -/
noncomputable abbrev single₀ : V ⥤ ChainComplex V ℕ :=
  HomologicalComplex.single V (ComplexShape.down ℕ) 0
>>>>>>> origin/homology-sequence-computation

variable {V}

@[simp, nolint simpNF]
lemma single₀_obj_zero (A : V) :
    ((single₀ V).obj A).X 0 = A := rfl

@[simp]
lemma single₀_map_f_zero {A B : V} (f : A ⟶ B) :
    ((single₀ V).map f).f 0 = f := by
  rw [HomologicalComplex.single_map_f_self]
  dsimp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
  erw [comp_id, id_comp]


@[simp]
lemma single₀ObjXSelf (X : V) :
    HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 X = Iso.refl _ := rfl

/-- Morphisms from an `ℕ`-indexed chain complex `C`
to a single object chain complex with `X` concentrated in degree 0
are the same as morphisms `f : C.X 0 ⟶ X` such that `C.d 1 0 ≫ f = 0`.
-/
@[simps apply_coe]
noncomputable def toSingle₀Equiv (C : ChainComplex V ℕ) (X : V) :
    (C ⟶ (single₀ V).obj X) ≃ { f : C.X 0 ⟶ X // C.d 1 0 ≫ f = 0 } where
  toFun φ := ⟨φ.f 0, by rw [← φ.comm 1 0, HomologicalComplex.single_obj_d, comp_zero]⟩
  invFun f := HomologicalComplex.mkHomToSingle f.1 (fun i hi => by
    obtain rfl : i = 1 := by simpa using hi.symm
    exact f.2)
  left_inv φ := by aesop_cat
  right_inv f := by aesop_cat

@[simp]
lemma toSingle₀Equiv_symm_apply_f_zero {C : ChainComplex V ℕ} {X : V}
    (f : C.X 0 ⟶ X) (hf : C.d 1 0 ≫ f = 0) :
    ((toSingle₀Equiv C X).symm ⟨f, hf⟩).f 0 = f := by
  simp [toSingle₀Equiv]

/-- Morphisms from a single object chain complex with `X` concentrated in degree 0
to an `ℕ`-indexed chain complex `C` are the same as morphisms `f : X → C.X 0`.
-/
@[simps apply]
noncomputable def fromSingle₀Equiv (C : ChainComplex V ℕ) (X : V) :
    ((single₀ V).obj X ⟶ C) ≃ (X ⟶ C.X 0) where
  toFun f := f.f 0
  invFun f := HomologicalComplex.mkHomFromSingle f (fun i hi => by simp at hi)
  left_inv := by aesop_cat
  right_inv := by aesop_cat
#align chain_complex.from_single₀_equiv ChainComplex.fromSingle₀Equiv

@[simp]
lemma fromSingle₀Equiv_symm_apply_f_zero
    {C : ChainComplex V ℕ} {X : V} (f : X ⟶ C.X 0) :
    ((fromSingle₀Equiv C X).symm f).f 0 = f := by
  simp [fromSingle₀Equiv]

@[simp]
lemma fromSingle₀Equiv_symm_apply_f_succ
    {C : ChainComplex V ℕ} {X : V} (f : X ⟶ C.X 0) (n : ℕ) :
    ((fromSingle₀Equiv C X).symm f).f (n + 1) = 0 := rfl

end ChainComplex

namespace CochainComplex

<<<<<<< HEAD
/-- `CochainComplex.single₀ V` is the embedding of `V` into `CochainComplex V ℕ`
as cochain complexes supported in degree 0.

This is naturally isomorphic to `single V _ 0`, but has better definitional properties.
-/
def single₀ : V ⥤ CochainComplex V ℕ where
  obj X :=
    { X := fun n =>
        match n with
        | 0 => X
        | _ + 1 => 0
      d := fun i j => 0 }
  map f :=
    { f := fun n =>
        match n with
        | 0 => f
        | n + 1 => 0 }
  map_id X := by
    ext (_|_)
    · rfl
    · simp
  map_comp f g := by
    ext (_|_)
    · rfl
    · simp
#align cochain_complex.single₀ CochainComplex.single₀

@[simp]
theorem single₀_obj_X_0 (X : V) : ((single₀ V).obj X).X 0 = X :=
  rfl
set_option linter.uppercaseLean3 false in
#align cochain_complex.single₀_obj_X_0 CochainComplex.single₀_obj_X_0

@[simp]
theorem single₀_obj_X_succ (X : V) (n : ℕ) : ((single₀ V).obj X).X (n + 1) = 0 :=
  rfl
set_option linter.uppercaseLean3 false in
#align cochain_complex.single₀_obj_X_succ CochainComplex.single₀_obj_X_succ

@[simp]
theorem single₀_obj_X_d (X : V) (i j : ℕ) : ((single₀ V).obj X).d i j = 0 :=
  rfl
set_option linter.uppercaseLean3 false in
#align cochain_complex.single₀_obj_X_d CochainComplex.single₀_obj_X_d

@[simp]
theorem single₀_obj_x_dFrom (X : V) (j : ℕ) : ((single₀ V).obj X).dFrom j = 0 := by
  rw [dFrom_eq ((single₀ V).obj X) rfl]
  simp
set_option linter.uppercaseLean3 false in
#align cochain_complex.single₀_obj_X_d_from CochainComplex.single₀_obj_x_dFrom

@[simp]
theorem single₀_obj_x_dTo (X : V) (i : ℕ) : ((single₀ V).obj X).dTo i = 0 := by
  cases i
  · rw [dTo_eq_zero]
    simp
  · erw [dTo_eq ((single₀ V).obj X) rfl]
    simp
set_option linter.uppercaseLean3 false in
#align cochain_complex.single₀_obj_X_d_to CochainComplex.single₀_obj_x_dTo

@[simp]
theorem single₀_map_f_0 {X Y : V} (f : X ⟶ Y) : ((single₀ V).map f).f 0 = f :=
  rfl
#align cochain_complex.single₀_map_f_0 CochainComplex.single₀_map_f_0

@[simp]
theorem single₀_map_f_succ {X Y : V} (f : X ⟶ Y) (n : ℕ) : ((single₀ V).map f).f (n + 1) = 0 :=
  rfl
#align cochain_complex.single₀_map_f_succ CochainComplex.single₀_map_f_succ

/-section

variable [HasEqualizers V] [HasCokernels V] [HasImages V] [HasImageMaps V]

/-- Sending objects to cochain complexes supported at `0` then taking `0`-th homology
is the same as doing nothing.
-/
noncomputable def homology'Functor0Single₀ : single₀ V ⋙ homology'Functor V _ 0 ≅ 𝟭 V :=
  NatIso.ofComponents (fun X => homology'.congr _ _ (by simp) (by simp) ≪≫ homology'ZeroZero)
    fun f => by
      -- Porting note: why can't `aesop_cat` do this?
      dsimp
      ext
      simp
#align cochain_complex.homology_functor_0_single₀ CochainComplex.homology'Functor0Single₀

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

end-/
=======
/-- The functor `V ⥤ CochainComplex V ℕ` creating a cochain complex supported in degree zero. -/
noncomputable abbrev single₀ : V ⥤ CochainComplex V ℕ :=
  HomologicalComplex.single V (ComplexShape.up ℕ) 0
>>>>>>> origin/homology-sequence-computation

variable {V}

@[simp, nolint simpNF]
lemma single₀_obj_zero (A : V) :
    ((single₀ V).obj A).X 0 = A := rfl

@[simp]
lemma single₀_map_f_zero {A B : V} (f : A ⟶ B) :
    ((single₀ V).map f).f 0 = f := by
  rw [HomologicalComplex.single_map_f_self]
  dsimp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
  erw [comp_id, id_comp]

@[simp]
lemma single₀ObjXSelf (X : V) :
    HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 X = Iso.refl _ := rfl

/-- Morphisms from a single object cochain complex with `X` concentrated in degree 0
to an `ℕ`-indexed cochain complex `C`
are the same as morphisms `f : X ⟶ C.X 0` such that `f ≫ C.d 0 1 = 0`. -/
@[simps apply_coe]
noncomputable def fromSingle₀Equiv (C : CochainComplex V ℕ) (X : V) :
    ((single₀ V).obj X ⟶ C) ≃ { f : X ⟶ C.X 0 // f ≫ C.d 0 1 = 0 } where
  toFun φ := ⟨φ.f 0, by rw [φ.comm 0 1, HomologicalComplex.single_obj_d, zero_comp]⟩
  invFun f := HomologicalComplex.mkHomFromSingle f.1 (fun i hi => by
    obtain rfl : i = 1 := by simpa using hi.symm
    exact f.2)
  left_inv φ := by aesop_cat
  right_inv := by aesop_cat

@[simp]
lemma fromSingle₀Equiv_symm_apply_f_zero {C : CochainComplex V ℕ} {X : V}
    (f : X ⟶ C.X 0) (hf : f ≫ C.d 0 1 = 0) :
    ((fromSingle₀Equiv C X).symm ⟨f, hf⟩).f 0 = f := by
  simp [fromSingle₀Equiv]

/-- Morphisms to a single object cochain complex with `X` concentrated in degree 0
to an `ℕ`-indexed cochain complex `C` are the same as morphisms `f : C.X 0 ⟶ X`.
-/
@[simps apply]
noncomputable def toSingle₀Equiv (C : CochainComplex V ℕ) (X : V) :
    (C ⟶ (single₀ V).obj X) ≃ (C.X 0 ⟶ X) where
  toFun f := f.f 0
  invFun f := HomologicalComplex.mkHomToSingle f (fun i hi => by simp at hi)
  left_inv := by aesop_cat
  right_inv := by aesop_cat

@[simp]
lemma toSingle₀Equiv_symm_apply_f_zero
    {C : CochainComplex V ℕ} {X : V} (f : C.X 0 ⟶ X) :
    ((toSingle₀Equiv C X).symm f).f 0 = f := by
  simp [toSingle₀Equiv]

@[simp]
lemma toSingle₀Equiv_symm_apply_f_succ
    {C : CochainComplex V ℕ} {X : V} (f : C.X 0 ⟶ X) (n : ℕ) :
    ((toSingle₀Equiv C X).symm f).f (n + 1) = 0 := by
  rfl

end CochainComplex
