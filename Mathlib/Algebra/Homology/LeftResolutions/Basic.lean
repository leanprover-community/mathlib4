/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Left resolutions

Given a fully faithful functor `ι : C ⥤ A` to an abelian category,
we introduce a structure `Abelian.LeftResolutions ι` which gives
a functor `F : A ⥤ C` and a natural epimorphism
`π.app X : ι.obj (F.obj X) ⟶ X` for all `X : A`.
This is used in order to construct a resolution functor
`LeftResolutions.chainComplexFunctor : A ⥤ ChainComplex C ℕ`.

This shall be used in order to construct functorial flat resolutions.

-/

namespace CategoryTheory.Abelian

open Category Limits Preadditive ZeroObject

variable {A C : Type*} [Category C] [Category A] (ι : C ⥤ A)

/-- Given a fully faithful functor `ι : C ⥤ A`, this structure contains the data
of a functor `F : A ⥤ C` and a functorial epimorphism
`π.app X : ι.obj (F.obj X) ⟶ X` for all `X : A`. -/
structure LeftResolutions where
  /-- a functor which sends `X : A` to an object `F.obj X` with an epimorphism
    `π.app X : ι.obj (F.obj X) ⟶ X` -/
  F : A ⥤ C
  /-- the natural epimorphism -/
  π : F ⋙ ι ⟶ 𝟭 A
  epi_π (X : A) : Epi (π.app X) := by infer_instance

namespace LeftResolutions

attribute [instance] epi_π

variable {ι} (Λ : LeftResolutions ι) (X Y Z : A) (f : X ⟶ Y) (g : Y ⟶ Z)

@[reassoc (attr := simp)]
lemma π_naturality : ι.map (Λ.F.map f) ≫ Λ.π.app Y = Λ.π.app X ≫ f :=
  Λ.π.naturality f

variable [ι.Full] [ι.Faithful] [HasZeroMorphisms C] [Abelian A]

/-- Given `ι : C ⥤ A`, `Λ : LeftResolutions ι`, `X : A`, this is a chain complex
which is a (functorial) resolution of `A` that is obtained inductively by using
the epimorphisms given by `Λ`. -/
noncomputable def chainComplex : ChainComplex C ℕ :=
  ChainComplex.mk' _ _ (ι.preimage (Λ.π.app (kernel (Λ.π.app X)) ≫ kernel.ι _))
    (fun f => ⟨_, ι.preimage (Λ.π.app (kernel (ι.map f)) ≫ kernel.ι _),
      ι.map_injective (by simp)⟩)

/-- Given `Λ : LeftResolutions ι`, the chain complex `Λ.chainComplex X`
identifies in degree `0` to `Λ.F.obj X`. -/
noncomputable def chainComplexXZeroIso :
    (Λ.chainComplex X).X 0 ≅ Λ.F.obj X := Iso.refl _

/-- Given `Λ : LeftResolutions ι`, the chain complex `Λ.chainComplex X`
identifies in degree `1` to `Λ.F.obj (kernel (Λ.π.app X))`. -/
noncomputable def chainComplexXOneIso :
    (Λ.chainComplex X).X 1 ≅ Λ.F.obj (kernel (Λ.π.app X)) := Iso.refl _

@[reassoc]
lemma map_chainComplex_d_1_0 :
    ι.map ((Λ.chainComplex X).d 1 0) =
      ι.map (Λ.chainComplexXOneIso X).hom ≫ Λ.π.app (kernel (Λ.π.app X)) ≫ kernel.ι _ ≫
      ι.map (Λ.chainComplexXZeroIso X).inv := by
  simp [chainComplexXOneIso, chainComplexXZeroIso, chainComplex]

/-- The isomorphism which gives the inductive step of the construction of `Λ.chainComplex X`. -/
noncomputable def chainComplexXIso (n : ℕ) :
    (Λ.chainComplex X).X (n + 2) ≅ Λ.F.obj (kernel (ι.map ((Λ.chainComplex X).d (n + 1) n))) := by
  apply ChainComplex.mk'XIso

lemma map_chainComplex_d (n : ℕ) :
    ι.map ((Λ.chainComplex X).d (n + 2) (n + 1)) =
    ι.map (Λ.chainComplexXIso X n).hom ≫ Λ.π.app (kernel (ι.map ((Λ.chainComplex X).d (n + 1) n))) ≫
      kernel.ι (ι.map ((Λ.chainComplex X).d (n + 1) n)) := by
  have := ι.map_preimage (Λ.π.app _ ≫ kernel.ι (ι.map ((Λ.chainComplex X).d (n + 1) n)))
  dsimp at this
  rw [← this, ← Functor.map_comp]
  congr 1
  apply ChainComplex.mk'_d

attribute [irreducible] chainComplex

lemma exactAt_map_chainComplex_succ (n : ℕ) :
    ((ι.mapHomologicalComplex _).obj (Λ.chainComplex X)).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n
    (ComplexShape.prev_eq' _ (by dsimp; omega)) (by simp),
    ShortComplex.exact_iff_epi_kernel_lift]
  convert epi_comp (ι.map (Λ.chainComplexXIso X n).hom) (Λ.π.app _)
  rw [← cancel_mono (kernel.ι _), kernel.lift_ι]
  simp [map_chainComplex_d]

variable {X Y Z}

/-- The morphism `Λ.chainComplex X ⟶ Λ.chainComplex Y` of chain complexes
induced by `f : X ⟶ Y`. -/
noncomputable def chainComplexMap : Λ.chainComplex X ⟶ Λ.chainComplex Y :=
  ChainComplex.mkHom _ _
    ((Λ.chainComplexXZeroIso X).hom ≫ Λ.F.map f ≫ (Λ.chainComplexXZeroIso Y).inv)
    ((Λ.chainComplexXOneIso X).hom ≫
      Λ.F.map (kernel.map _ _ (ι.map (Λ.F.map f)) f (Λ.π.naturality f).symm) ≫
      (Λ.chainComplexXOneIso Y).inv)
    (ι.map_injective (by
        dsimp
        simp only [Category.assoc, Functor.map_comp, map_chainComplex_d_1_0]
        simp only [← ι.map_comp, ← ι.map_comp_assoc, Iso.inv_hom_id_assoc,
          Iso.inv_hom_id, comp_id]
        simp))
    (fun n p ↦
      ⟨(Λ.chainComplexXIso X n).hom ≫ (Λ.F.map
        (kernel.map _ _ (ι.map p.2.1) (ι.map p.1) (by
          rw [← ι.map_comp, ← ι.map_comp, p.2.2]))) ≫ (Λ.chainComplexXIso Y n).inv,
            ι.map_injective (by simp [map_chainComplex_d])⟩)

@[simp]
lemma chainComplexMap_f_0 :
    (Λ.chainComplexMap f).f 0 =
      ((Λ.chainComplexXZeroIso X).hom ≫ Λ.F.map f ≫ (Λ.chainComplexXZeroIso Y).inv) := rfl

@[simp]
lemma chainComplexMap_f_1 :
    (Λ.chainComplexMap f).f 1 =
    (Λ.chainComplexXOneIso X).hom ≫
      Λ.F.map (kernel.map _ _ (ι.map (Λ.F.map f)) f (Λ.π.naturality f).symm) ≫
      (Λ.chainComplexXOneIso Y).inv := rfl

@[simp]
lemma chainComplexMap_f_succ_succ (n : ℕ) :
    (Λ.chainComplexMap f).f (n + 2) =
      (Λ.chainComplexXIso X n).hom ≫
        Λ.F.map (kernel.map _ _ (ι.map ((Λ.chainComplexMap f).f (n + 1)))
          (ι.map ((Λ.chainComplexMap f).f n))
          (by rw [← ι.map_comp, ← ι.map_comp, HomologicalComplex.Hom.comm])) ≫
          (Λ.chainComplexXIso Y n).inv := by
  apply ChainComplex.mkHom_f_succ_succ

variable (X) in
@[simp]
lemma chainComplexMap_id : Λ.chainComplexMap (𝟙 X) = 𝟙 _ := by
  ext n
  induction n with
  | zero => simp
  | succ n hn => obtain _ | n := n <;> simp [hn]

variable (X Y) in
@[simp]
lemma chainComplexMap_zero [Λ.F.PreservesZeroMorphisms] :
    Λ.chainComplexMap (0 : X ⟶ Y) = 0 := by
  ext n
  induction n with
  | zero => simp
  | succ n hn => obtain _|n := n <;> simp [hn]

@[reassoc, simp]
lemma chainComplexMap_comp :
    Λ.chainComplexMap (f ≫ g) = Λ.chainComplexMap f ≫ Λ.chainComplexMap g := by
  ext n
  induction n with
  | zero => simp
  | succ n hn =>
    obtain _ | n := n
    all_goals
      dsimp
      simp only [chainComplexMap_f_succ_succ, assoc, Iso.cancel_iso_hom_left,
        Iso.inv_hom_id_assoc, ← Λ.F.map_comp_assoc, Iso.cancel_iso_inv_right_assoc]
      congr 1
      cat_disch

/-- Given `ι : C ⥤ A`, `Λ : LeftResolutions ι`, this is a
functor `A ⥤ ChainComplex C ℕ` which sends `X : A` to a resolution consisting
of objects in `C`. -/
noncomputable def chainComplexFunctor : A ⥤ ChainComplex C ℕ where
  obj X := Λ.chainComplex X
  map f := Λ.chainComplexMap f

end LeftResolutions

end CategoryTheory.Abelian
