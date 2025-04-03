/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Homology.Homology
import Mathlib.Algebra.Homology.Single
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

#align_import algebra.homology.additive from "leanprover-community/mathlib"@"200eda15d8ff5669854ff6bcc10aaf37cb70498f"

/-!
# Homology is an additive functor

When `V` is preadditive, `HomologicalComplex V c` is also preadditive,
and `homologyFunctor` is additive.

-/


universe v u

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits HomologicalComplex

variable {ι : Type*}
variable {V : Type u} [Category.{v} V] [Preadditive V]
variable {W : Type*} [Category W] [Preadditive W]
variable {W₁ W₂ : Type*} [Category W₁] [Category W₂] [HasZeroMorphisms W₁] [HasZeroMorphisms W₂]
variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}
variable (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

namespace HomologicalComplex

instance : Zero (C ⟶ D) :=
  ⟨{ f := fun i => 0 }⟩

instance : Add (C ⟶ D) :=
  ⟨fun f g => { f := fun i => f.f i + g.f i }⟩

instance : Neg (C ⟶ D) :=
  ⟨fun f => { f := fun i => -f.f i }⟩

instance : Sub (C ⟶ D) :=
  ⟨fun f g => { f := fun i => f.f i - g.f i }⟩

instance hasNatScalar : SMul ℕ (C ⟶ D) :=
  ⟨fun n f =>
    { f := fun i => n • f.f i
      comm' := fun i j _ => by simp [Preadditive.nsmul_comp, Preadditive.comp_nsmul] }⟩
#align homological_complex.has_nat_scalar HomologicalComplex.hasNatScalar

instance hasIntScalar : SMul ℤ (C ⟶ D) :=
  ⟨fun n f =>
    { f := fun i => n • f.f i
      comm' := fun i j _ => by simp [Preadditive.zsmul_comp, Preadditive.comp_zsmul] }⟩
#align homological_complex.has_int_scalar HomologicalComplex.hasIntScalar

@[simp]
theorem zero_f_apply (i : ι) : (0 : C ⟶ D).f i = 0 :=
  rfl
#align homological_complex.zero_f_apply HomologicalComplex.zero_f_apply

@[simp]
theorem add_f_apply (f g : C ⟶ D) (i : ι) : (f + g).f i = f.f i + g.f i :=
  rfl
#align homological_complex.add_f_apply HomologicalComplex.add_f_apply

@[simp]
theorem neg_f_apply (f : C ⟶ D) (i : ι) : (-f).f i = -f.f i :=
  rfl
#align homological_complex.neg_f_apply HomologicalComplex.neg_f_apply

@[simp]
theorem sub_f_apply (f g : C ⟶ D) (i : ι) : (f - g).f i = f.f i - g.f i :=
  rfl
#align homological_complex.sub_f_apply HomologicalComplex.sub_f_apply

@[simp]
theorem nsmul_f_apply (n : ℕ) (f : C ⟶ D) (i : ι) : (n • f).f i = n • f.f i :=
  rfl
#align homological_complex.nsmul_f_apply HomologicalComplex.nsmul_f_apply

@[simp]
theorem zsmul_f_apply (n : ℤ) (f : C ⟶ D) (i : ι) : (n • f).f i = n • f.f i :=
  rfl
#align homological_complex.zsmul_f_apply HomologicalComplex.zsmul_f_apply

instance : AddCommGroup (C ⟶ D) :=
  Function.Injective.addCommGroup Hom.f HomologicalComplex.hom_f_injective
    (by aesop_cat) (by aesop_cat) (by aesop_cat) (by aesop_cat) (by aesop_cat) (by aesop_cat)

-- Porting note: proofs had to be provided here, otherwise Lean tries to apply
-- `Preadditive.add_comp/comp_add` to `HomologicalComplex V c`
instance : Preadditive (HomologicalComplex V c) where
  add_comp _ _ _ f f' g := by
    ext
    simp only [comp_f, add_f_apply]
    rw [Preadditive.add_comp]
  comp_add _ _ _ f g g' := by
    ext
    simp only [comp_f, add_f_apply]
    rw [Preadditive.comp_add]

/-- The `i`-th component of a chain map, as an additive map from chain maps to morphisms. -/
@[simps!]
def Hom.fAddMonoidHom {C₁ C₂ : HomologicalComplex V c} (i : ι) : (C₁ ⟶ C₂) →+ (C₁.X i ⟶ C₂.X i) :=
  AddMonoidHom.mk' (fun f => Hom.f f i) fun _ _ => rfl
#align homological_complex.hom.f_add_monoid_hom HomologicalComplex.Hom.fAddMonoidHom

end HomologicalComplex

namespace HomologicalComplex

instance eval_additive (i : ι) : (eval V c i).Additive where
#align homological_complex.eval_additive HomologicalComplex.eval_additive

instance cycles'_additive [HasEqualizers V] : (cycles'Functor V c i).Additive where
#align homological_complex.cycles_additive HomologicalComplex.cycles'_additive

variable [HasImages V] [HasImageMaps V]

instance boundaries_additive : (boundariesFunctor V c i).Additive where
#align homological_complex.boundaries_additive HomologicalComplex.boundaries_additive

variable [HasEqualizers V] [HasCokernels V]

instance homology_additive : (homology'Functor V c i).Additive where
  map_add {_ _ f g} := by
    dsimp [homology'Functor]
    ext
    simp only [homology'.π_map, Preadditive.comp_add, ← Preadditive.add_comp]
    congr
    ext
    simp
#align homological_complex.homology_additive HomologicalComplex.homology_additive

end HomologicalComplex

namespace CategoryTheory

/-- An additive functor induces a functor between homological complexes.
This is sometimes called the "prolongation".
-/
@[simps]
def Functor.mapHomologicalComplex (F : W₁ ⥤ W₂) [F.PreservesZeroMorphisms] (c : ComplexShape ι) :
    HomologicalComplex W₁ c ⥤ HomologicalComplex W₂ c where
  obj C :=
    { X := fun i => F.obj (C.X i)
      d := fun i j => F.map (C.d i j)
      shape := fun i j w => by
        dsimp only
        rw [C.shape _ _ w, F.map_zero]
      d_comp_d' := fun i j k _ _ => by rw [← F.map_comp, C.d_comp_d, F.map_zero] }
  map f :=
    { f := fun i => F.map (f.f i)
      comm' := fun i j _ => by
        dsimp
        rw [← F.map_comp, ← F.map_comp, f.comm] }
#align category_theory.functor.map_homological_complex CategoryTheory.Functor.mapHomologicalComplex

instance (F : W₁ ⥤ W₂) [F.PreservesZeroMorphisms] (c : ComplexShape ι) :
    (F.mapHomologicalComplex c).PreservesZeroMorphisms where

instance Functor.map_homogical_complex_additive (F : V ⥤ W) [F.Additive] (c : ComplexShape ι) :
    (F.mapHomologicalComplex c).Additive where
#align category_theory.functor.map_homogical_complex_additive CategoryTheory.Functor.map_homogical_complex_additive

variable (W₁)

/-- The functor on homological complexes induced by the identity functor is
isomorphic to the identity functor. -/
@[simps!]
def Functor.mapHomologicalComplexIdIso (c : ComplexShape ι) :
    (𝟭 W₁).mapHomologicalComplex c ≅ 𝟭 _ :=
  NatIso.ofComponents fun K => Hom.isoOfComponents fun i => Iso.refl _
#align category_theory.functor.map_homological_complex_id_iso CategoryTheory.Functor.mapHomologicalComplexIdIso

instance Functor.mapHomologicalComplex_reflects_iso (F : W₁ ⥤ W₂) [F.PreservesZeroMorphisms]
    [ReflectsIsomorphisms F] (c : ComplexShape ι) :
    ReflectsIsomorphisms (F.mapHomologicalComplex c) :=
  ⟨fun f => by
    intro
    haveI : ∀ n : ι, IsIso (F.map (f.f n)) := fun n =>
        ((HomologicalComplex.eval W₂ c n).mapIso
          (asIso ((F.mapHomologicalComplex c).map f))).isIso_hom
    haveI := fun n => isIso_of_reflects_iso (f.f n) F
    exact HomologicalComplex.Hom.isIso_of_components f⟩
#align category_theory.functor.map_homological_complex_reflects_iso CategoryTheory.Functor.mapHomologicalComplex_reflects_iso

variable {W₁}

/-- A natural transformation between functors induces a natural transformation
between those functors applied to homological complexes.
-/
@[simps]
def NatTrans.mapHomologicalComplex {F G : W₁ ⥤ W₂}
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (α : F ⟶ G)
    (c : ComplexShape ι) : F.mapHomologicalComplex c ⟶ G.mapHomologicalComplex c where
  app C := { f := fun i => α.app _ }
#align category_theory.nat_trans.map_homological_complex CategoryTheory.NatTrans.mapHomologicalComplex

@[simp]
theorem NatTrans.mapHomologicalComplex_id
    (c : ComplexShape ι) (F : W₁ ⥤ W₂) [F.PreservesZeroMorphisms] :
    NatTrans.mapHomologicalComplex (𝟙 F) c = 𝟙 (F.mapHomologicalComplex c) := by aesop_cat
#align category_theory.nat_trans.map_homological_complex_id CategoryTheory.NatTrans.mapHomologicalComplex_id

@[simp]
theorem NatTrans.mapHomologicalComplex_comp (c : ComplexShape ι) {F G H : W₁ ⥤ W₂}
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] [H.PreservesZeroMorphisms]
    (α : F ⟶ G) (β : G ⟶ H) :
    NatTrans.mapHomologicalComplex (α ≫ β) c =
      NatTrans.mapHomologicalComplex α c ≫ NatTrans.mapHomologicalComplex β c := by
  aesop_cat
#align category_theory.nat_trans.map_homological_complex_comp CategoryTheory.NatTrans.mapHomologicalComplex_comp

@[reassoc (attr := simp 1100)]
theorem NatTrans.mapHomologicalComplex_naturality {c : ComplexShape ι} {F G : W₁ ⥤ W₂}
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    (α : F ⟶ G) {C D : HomologicalComplex W₁ c} (f : C ⟶ D) :
    (F.mapHomologicalComplex c).map f ≫ (NatTrans.mapHomologicalComplex α c).app D =
      (NatTrans.mapHomologicalComplex α c).app C ≫ (G.mapHomologicalComplex c).map f := by
  aesop_cat
#align category_theory.nat_trans.map_homological_complex_naturality CategoryTheory.NatTrans.mapHomologicalComplex_naturality

/-- A natural isomorphism between functors induces a natural isomorphism
between those functors applied to homological complexes.
-/
@[simps!]
def NatIso.mapHomologicalComplex {F G : W₁ ⥤ W₂} [F.PreservesZeroMorphisms]
    [G.PreservesZeroMorphisms] (α : F ≅ G) (c : ComplexShape ι) :
    F.mapHomologicalComplex c ≅ G.mapHomologicalComplex c where
  hom := NatTrans.mapHomologicalComplex α.hom c
  inv := NatTrans.mapHomologicalComplex α.inv c
  hom_inv_id := by simp only [← NatTrans.mapHomologicalComplex_comp, α.hom_inv_id,
    NatTrans.mapHomologicalComplex_id]
  inv_hom_id := by simp only [← NatTrans.mapHomologicalComplex_comp, α.inv_hom_id,
    NatTrans.mapHomologicalComplex_id]
#align category_theory.nat_iso.map_homological_complex CategoryTheory.NatIso.mapHomologicalComplex

/-- An equivalence of categories induces an equivalences between the respective categories
of homological complex.
-/
@[simps]
def Equivalence.mapHomologicalComplex (e : W₁ ≌ W₂) [e.functor.PreservesZeroMorphisms]
    (c : ComplexShape ι) :
    HomologicalComplex W₁ c ≌ HomologicalComplex W₂ c where
  functor := e.functor.mapHomologicalComplex c
  inverse := e.inverse.mapHomologicalComplex c
  unitIso :=
    (Functor.mapHomologicalComplexIdIso W₁ c).symm ≪≫ NatIso.mapHomologicalComplex e.unitIso c
  counitIso := NatIso.mapHomologicalComplex e.counitIso c ≪≫
  Functor.mapHomologicalComplexIdIso W₂ c
#align category_theory.equivalence.map_homological_complex CategoryTheory.Equivalence.mapHomologicalComplex

end CategoryTheory

namespace ChainComplex

variable {α : Type*} [AddRightCancelSemigroup α] [One α] [DecidableEq α]

theorem map_chain_complex_of (F : W₁ ⥤ W₂) [F.PreservesZeroMorphisms] (X : α → W₁)
    (d : ∀ n, X (n + 1) ⟶ X n) (sq : ∀ n, d (n + 1) ≫ d n = 0) :
    (F.mapHomologicalComplex _).obj (ChainComplex.of X d sq) =
      ChainComplex.of (fun n => F.obj (X n)) (fun n => F.map (d n)) fun n => by
        rw [← F.map_comp, sq n, Functor.map_zero] := by
  refine HomologicalComplex.ext rfl ?_
  rintro i j (rfl : j + 1 = i)
  simp only [CategoryTheory.Functor.mapHomologicalComplex_obj_d, of_d, eqToHom_refl, comp_id,
    id_comp]
#align chain_complex.map_chain_complex_of ChainComplex.map_chain_complex_of

end ChainComplex

variable [HasZeroObject W₁] [HasZeroObject W₂]

namespace HomologicalComplex

instance (W : Type*) [Category W] [Preadditive W] [HasZeroObject W] [DecidableEq ι] (j : ι) :
    (single W c j).Additive where
  map_add {_ _ f g} := by ext; simp [single]

variable (F : W₁ ⥤ W₂) [F.PreservesZeroMorphisms]
    (c : ComplexShape ι) [DecidableEq ι]

/-- Turning an object into a complex supported at `j` then applying a functor is
the same as applying the functor then forming the complex.
-/
noncomputable def singleMapHomologicalComplex (j : ι) :
    single W₁ c j ⋙ F.mapHomologicalComplex _ ≅ F ⋙ single W₂ c j :=
  NatIso.ofComponents
    (fun X =>
      { hom := { f := fun i => if h : i = j then eqToHom (by simp [h]) else 0 }
        inv := { f := fun i => if h : i = j then eqToHom (by simp [h]) else 0 }
        hom_inv_id := by
          ext i
          dsimp
          split_ifs with h
          · simp [h]
          · rw [zero_comp, ← F.map_id,
              (isZero_single_obj_X c j X _ h).eq_of_src (𝟙 _) 0, F.map_zero]
        inv_hom_id := by
          ext i
          dsimp
          split_ifs with h
          · simp [h]
          · apply (isZero_single_obj_X c j _ _ h).eq_of_src })
    fun f => by
      ext i
      dsimp
      split_ifs with h
      · subst h
        simp [single_map_f_self, singleObjXSelf, singleObjXIsoOfEq, eqToHom_map]
      · apply (isZero_single_obj_X c j _ _ h).eq_of_tgt
#align homological_complex.single_map_homological_complex HomologicalComplex.singleMapHomologicalComplex

@[simp]
theorem singleMapHomologicalComplex_hom_app_self (j : ι) (X : W₁) :
    ((singleMapHomologicalComplex F c j).hom.app X).f j =
      F.map (singleObjXSelf c j X).hom ≫ (singleObjXSelf c j (F.obj X)).inv := by
  simp [singleMapHomologicalComplex, singleObjXSelf, singleObjXIsoOfEq, eqToHom_map]
#align homological_complex.single_map_homological_complex_hom_app_self HomologicalComplex.singleMapHomologicalComplex_hom_app_self

@[simp]
theorem singleMapHomologicalComplex_hom_app_ne {i j : ι} (h : i ≠ j) (X : W₁) :
    ((singleMapHomologicalComplex F c j).hom.app X).f i = 0 := by
  simp [singleMapHomologicalComplex, h]
#align homological_complex.single_map_homological_complex_hom_app_ne HomologicalComplex.singleMapHomologicalComplex_hom_app_ne

@[simp]
theorem singleMapHomologicalComplex_inv_app_self (j : ι) (X : W₁) :
    ((singleMapHomologicalComplex F c j).inv.app X).f j =
      (singleObjXSelf c j (F.obj X)).hom ≫ F.map (singleObjXSelf c j X).inv := by
  simp [singleMapHomologicalComplex, singleObjXSelf, singleObjXIsoOfEq, eqToHom_map]
#align homological_complex.single_map_homological_complex_inv_app_self HomologicalComplex.singleMapHomologicalComplex_inv_app_self

@[simp]
theorem singleMapHomologicalComplex_inv_app_ne {i j : ι} (h : i ≠ j) (X : W₁) :
    ((singleMapHomologicalComplex F c j).inv.app X).f i = 0 := by
  simp [singleMapHomologicalComplex, h]
#align homological_complex.single_map_homological_complex_inv_app_ne HomologicalComplex.singleMapHomologicalComplex_inv_app_ne

end HomologicalComplex
