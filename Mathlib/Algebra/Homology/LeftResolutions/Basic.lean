/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.Embedding.ExtendMap
import Mathlib.Algebra.Homology.Embedding.CochainComplex

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
  hπ (X : A) : Epi (π.app X) := by infer_instance

namespace LeftResolutions

attribute [instance] hπ

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
      ι.map_injective (by simp [ι.map_zero])⟩)

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
        simp [-Functor.map_comp, ← Λ.F.map_comp_assoc, ← ι.map_comp]
        congr 1
        simp [← cancel_mono (kernel.ι _), hn]

/-- Given `ι : C ⥤ A`, `Λ : LeftResolutions ι`, this is a
functor `A ⥤ ChainComplex C ℕ` which sends `X : A` to a resolution consisting
of objects in `C`. -/
noncomputable def chainComplexFunctor : A ⥤ ChainComplex C ℕ where
  obj X := Λ.chainComplex X
  map f := Λ.chainComplexMap f

variable [HasZeroObject C]

noncomputable def cochainComplexFunctor : A ⥤ CochainComplex C ℤ :=
  Λ.chainComplexFunctor ⋙ ComplexShape.embeddingDownNat.extendFunctor _

variable (X)

noncomputable abbrev cochainComplex : CochainComplex C ℤ := Λ.cochainComplexFunctor.obj X

noncomputable def cochainComplexXZeroIso : (Λ.cochainComplex X).X 0 ≅ Λ.F.obj X :=
  (Λ.chainComplex X).extendXIso _ (by dsimp) ≪≫ Λ.chainComplexXZeroIso X

noncomputable def cochainComplexXNegOneIso :
    (Λ.cochainComplex X).X (-1) ≅ Λ.F.obj (kernel (Λ.π.app X)) :=
  (Λ.chainComplex X).extendXIso _ (by dsimp) ≪≫ Λ.chainComplexXOneIso X

lemma cochainComplex_d_neg_one_zero :
    ι.map ((cochainComplex Λ X).d (-1) 0) = ι.map (cochainComplexXNegOneIso Λ X).hom ≫
      Λ.π.app (kernel (Λ.π.app X)) ≫ kernel.ι (Λ.π.app X) ≫
        ι.map (cochainComplexXZeroIso Λ X).inv := by
  dsimp [cochainComplex, cochainComplexFunctor, chainComplexFunctor,
    cochainComplexXNegOneIso]
  rw [(Λ.chainComplex X).extend_d_eq ComplexShape.embeddingDownNat (i := 1) (j := 0)
      (by simp) (by simp), ι.map_comp, ι.map_comp, map_chainComplex_d_1_0,
      ι.map_comp, Category.assoc, Category.assoc, Category.assoc, Category.assoc, ← ι.map_comp]
  rfl

noncomputable def cochainComplexπ :
    (ι.mapHomologicalComplex _).obj (Λ.cochainComplex X) ⟶
      (HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj X :=
  HomologicalComplex.mkHomToSingle (ι.map (Λ.cochainComplexXZeroIso X).hom ≫ Λ.π.app X) (by
    rintro i hi
    dsimp at hi
    obtain rfl : i = -1 := by omega
    dsimp
    rw [cochainComplex_d_neg_one_zero, assoc, assoc, assoc, ← ι.map_comp_assoc,
      Iso.inv_hom_id, ι.map_id, id_comp, kernel.condition, comp_zero, comp_zero])

lemma cochainComplexπ_f_0 :
    (Λ.cochainComplexπ X).f 0 = ι.map (Λ.cochainComplexXZeroIso X).hom ≫ Λ.π.app X ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).inv := by
  simp [cochainComplexπ ]

@[simps]
noncomputable def cochainComplexNatTransπ :
    Λ.cochainComplexFunctor ⋙ ι.mapHomologicalComplex _ ⟶
      HomologicalComplex.single A (ComplexShape.up ℤ) 0 where
  app _ := Λ.cochainComplexπ _
  naturality X Y f := by
    ext
    dsimp [cochainComplexFunctor, cochainComplexπ, cochainComplexXZeroIso, chainComplexFunctor]
    simp only [Functor.map_comp, assoc, HomologicalComplex.mkHomToSingle_f,
      Functor.mapHomologicalComplex_obj_X]
    rw [HomologicalComplex.extendMap_f _ _ (i := 0) (by dsimp)]
    dsimp
    rw [← ι.map_comp_assoc, assoc, assoc, Iso.inv_hom_id, comp_id,
      HomologicalComplex.single_map_f_self, Iso.inv_hom_id_assoc]
    erw [← Λ.π.naturality_assoc f]
    dsimp
    rw [← ι.map_comp_assoc, assoc, assoc, assoc, Iso.inv_hom_id, comp_id,
      ι.map_comp, ι.map_comp, assoc, assoc]

instance : (Λ.cochainComplex X).IsStrictlyLE 0 where
  isZero i hi := by
    dsimp [cochainComplex, cochainComplexFunctor]
    apply HomologicalComplex.isZero_extend_X
    intro j
    simpa using hi j

instance : CochainComplex.IsGE
    ((ι.mapHomologicalComplex _).obj (Λ.cochainComplex X)) 0 where
  exactAt i hi := by
    apply HomologicalComplex.ExactAt.of_iso _
      ((ComplexShape.embeddingDownNat.mapExtendFunctorNatIso ι).symm.app (Λ.chainComplex X))
    dsimp
    obtain ⟨j, hj⟩ : ∃ (j : ℕ), (ComplexShape.embeddingDownNat).f (j + 1) = i := by
      have : i ≤ -1 := by
        by_contra!
        obtain ⟨k, hk⟩ := @Int.eq_ofNat_of_zero_le (a := i) (by omega)
        exact hi k (by dsimp; omega)
      obtain ⟨j, hj⟩ := Int.le.dest this
      exact ⟨j, by dsimp; omega⟩
    rw [HomologicalComplex.extend_exactAt_iff _ _ hj]
    apply exactAt_map_chainComplex_succ


open CochainComplex

instance : QuasiIsoAt (Λ.cochainComplexπ X) 0 := by
  rw [quasiIsoAt_iff' _ (-1) 0 1 (by simp) (by simp),
    ShortComplex.quasiIso_iff_of_zeros' _ _ (by rfl) (by rfl)]; swap
  · apply (ι.map_isZero (isZero_of_isStrictlyLE _ 0 _ (by omega))).eq_of_tgt
  let S := ShortComplex.mk (Λ.π.app (kernel (Λ.π.app X)) ≫ kernel.ι _) (Λ.π.app X) (by simp)
  have hS : S.Exact := by
    rw [S.exact_iff_epi_kernel_lift,
      show kernel.lift S.g S.f S.zero = Λ.π.app (kernel (Λ.π.app X)) by
        rw [← cancel_mono (kernel.ι _), kernel.lift_ι]]
    infer_instance
  refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2 ⟨hS, by infer_instance⟩
  refine ShortComplex.isoMk (ι.mapIso (Λ.cochainComplexXNegOneIso X))
    (ι.mapIso (Λ.cochainComplexXZeroIso X))
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X) ?_ ?_
  · dsimp
    rw [cochainComplex_d_neg_one_zero, assoc, assoc, assoc, ← ι.map_comp,
      Iso.inv_hom_id, ι.map_id]
    dsimp
    rw [comp_id]
  · simp [cochainComplexπ_f_0, S]

instance : QuasiIso (Λ.cochainComplexπ X) where
  quasiIsoAt i := by
    by_cases hi : i = 0
    · subst hi
      infer_instance
    · rw [quasiIsoAt_iff_exactAt]
      · exact HomologicalComplex.exactAt_single_obj _ _ _ _ hi
      · by_cases hi' : 0 < i
        · exact exactAt_of_isLE _ 0 _ hi'
        · exact exactAt_of_isGE _ 0 _ (by omega)

instance : QuasiIso (Λ.cochainComplexNatTransπ.app X) := by
  dsimp
  infer_instance

end LeftResolutions

end CategoryTheory.Abelian
