/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Homology.Single
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

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
variable {c : ComplexShape ι} {C D : HomologicalComplex V c}
variable (f : C ⟶ D) (i : ι)

namespace HomologicalComplex

instance : Zero (C ⟶ D) :=
  ⟨{ f := fun _ => 0 }⟩

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

instance hasIntScalar : SMul ℤ (C ⟶ D) :=
  ⟨fun n f =>
    { f := fun i => n • f.f i
      comm' := fun i j _ => by simp [Preadditive.zsmul_comp, Preadditive.comp_zsmul] }⟩

@[simp]
theorem zero_f_apply (i : ι) : (0 : C ⟶ D).f i = 0 :=
  rfl

@[simp]
theorem add_f_apply (f g : C ⟶ D) (i : ι) : (f + g).f i = f.f i + g.f i :=
  rfl

@[simp]
theorem neg_f_apply (f : C ⟶ D) (i : ι) : (-f).f i = -f.f i :=
  rfl

@[simp]
theorem sub_f_apply (f g : C ⟶ D) (i : ι) : (f - g).f i = f.f i - g.f i :=
  rfl

@[simp]
theorem nsmul_f_apply (n : ℕ) (f : C ⟶ D) (i : ι) : (n • f).f i = n • f.f i :=
  rfl

@[simp]
theorem zsmul_f_apply (n : ℤ) (f : C ⟶ D) (i : ι) : (n • f).f i = n • f.f i :=
  rfl

instance : AddCommGroup (C ⟶ D) :=
  Function.Injective.addCommGroup Hom.f HomologicalComplex.hom_f_injective
    (by cat_disch) (by cat_disch) (by cat_disch) (by cat_disch) (by cat_disch) (by cat_disch)

instance : Preadditive (HomologicalComplex V c) where

/-- The `i`-th component of a chain map, as an additive map from chain maps to morphisms. -/
@[simps!]
def Hom.fAddMonoidHom {C₁ C₂ : HomologicalComplex V c} (i : ι) : (C₁ ⟶ C₂) →+ (C₁.X i ⟶ C₂.X i) :=
  AddMonoidHom.mk' (fun f => Hom.f f i) fun _ _ => rfl

instance eval_additive (i : ι) : (eval V c i).Additive where

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
        rw [C.shape _ _ w, F.map_zero]
      d_comp_d' := fun i j k _ _ => by rw [← F.map_comp, C.d_comp_d, F.map_zero] }
  map f :=
    { f := fun i => F.map (f.f i)
      comm' := fun i j _ => by
        dsimp
        rw [← F.map_comp, ← F.map_comp, f.comm] }

instance (F : W₁ ⥤ W₂) [F.PreservesZeroMorphisms] (c : ComplexShape ι) :
    (F.mapHomologicalComplex c).PreservesZeroMorphisms where

instance Functor.map_homogical_complex_additive (F : V ⥤ W) [F.Additive] (c : ComplexShape ι) :
    (F.mapHomologicalComplex c).Additive where

variable (W₁)

/-- The functor on homological complexes induced by the identity functor is
isomorphic to the identity functor. -/
@[simps!]
def Functor.mapHomologicalComplexIdIso (c : ComplexShape ι) :
    (𝟭 W₁).mapHomologicalComplex c ≅ 𝟭 _ :=
  NatIso.ofComponents fun K => Hom.isoOfComponents fun _ => Iso.refl _

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

variable {W₁}

/-- A natural transformation between functors induces a natural transformation
between those functors applied to homological complexes.
-/
@[simps]
def NatTrans.mapHomologicalComplex {F G : W₁ ⥤ W₂}
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (α : F ⟶ G)
    (c : ComplexShape ι) : F.mapHomologicalComplex c ⟶ G.mapHomologicalComplex c where
  app C := { f := fun _ => α.app _ }

@[simp]
theorem NatTrans.mapHomologicalComplex_id
    (c : ComplexShape ι) (F : W₁ ⥤ W₂) [F.PreservesZeroMorphisms] :
    NatTrans.mapHomologicalComplex (𝟙 F) c = 𝟙 (F.mapHomologicalComplex c) := by cat_disch

@[simp]
theorem NatTrans.mapHomologicalComplex_comp (c : ComplexShape ι) {F G H : W₁ ⥤ W₂}
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] [H.PreservesZeroMorphisms]
    (α : F ⟶ G) (β : G ⟶ H) :
    NatTrans.mapHomologicalComplex (α ≫ β) c =
      NatTrans.mapHomologicalComplex α c ≫ NatTrans.mapHomologicalComplex β c := by
  cat_disch

@[reassoc]
theorem NatTrans.mapHomologicalComplex_naturality {c : ComplexShape ι} {F G : W₁ ⥤ W₂}
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    (α : F ⟶ G) {C D : HomologicalComplex W₁ c} (f : C ⟶ D) :
    (F.mapHomologicalComplex c).map f ≫ (NatTrans.mapHomologicalComplex α c).app D =
      (NatTrans.mapHomologicalComplex α c).app C ≫ (G.mapHomologicalComplex c).map f := by
  simp

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
          · simp
          · rw [zero_comp, ← F.map_id,
              (isZero_single_obj_X c j X _ h).eq_of_src (𝟙 _) 0, F.map_zero]
        inv_hom_id := by
          ext i
          dsimp
          split_ifs with h
          · simp
          · apply (isZero_single_obj_X c j _ _ h).eq_of_src })
    fun f => by
      ext i
      dsimp
      split_ifs with h
      · subst h
        simp [single_map_f_self, singleObjXSelf, singleObjXIsoOfEq, eqToHom_map]
      · apply (isZero_single_obj_X c j _ _ h).eq_of_tgt

@[simp]
theorem singleMapHomologicalComplex_hom_app_self (j : ι) (X : W₁) :
    ((singleMapHomologicalComplex F c j).hom.app X).f j =
      F.map (singleObjXSelf c j X).hom ≫ (singleObjXSelf c j (F.obj X)).inv := by
  simp [singleMapHomologicalComplex, singleObjXSelf, singleObjXIsoOfEq, eqToHom_map]

@[simp]
theorem singleMapHomologicalComplex_hom_app_ne {i j : ι} (h : i ≠ j) (X : W₁) :
    ((singleMapHomologicalComplex F c j).hom.app X).f i = 0 := by
  simp [singleMapHomologicalComplex, h]

@[simp]
theorem singleMapHomologicalComplex_inv_app_self (j : ι) (X : W₁) :
    ((singleMapHomologicalComplex F c j).inv.app X).f j =
      (singleObjXSelf c j (F.obj X)).hom ≫ F.map (singleObjXSelf c j X).inv := by
  simp [singleMapHomologicalComplex, singleObjXSelf, singleObjXIsoOfEq, eqToHom_map]

@[simp]
theorem singleMapHomologicalComplex_inv_app_ne {i j : ι} (h : i ≠ j) (X : W₁) :
    ((singleMapHomologicalComplex F c j).inv.app X).f i = 0 := by
  simp [singleMapHomologicalComplex, h]

end HomologicalComplex
