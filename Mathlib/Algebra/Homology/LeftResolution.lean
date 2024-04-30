import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.BicomplexColumns

open CategoryTheory Category Limits Preadditive ZeroObject


@[simp]
lemma CategoryTheory.Limits.kernel.map_id {C : Type*} [Category C] [HasZeroMorphisms C]
    {X Y : C} (f : X ⟶ Y) [HasKernel f] (q : Y ⟶ Y)
    (w : f ≫ q = 𝟙 _ ≫ f) : kernel.map f f (𝟙 _) q w = 𝟙 _ := by
  simp only [← cancel_mono (kernel.ι f), lift_ι, comp_id, id_comp]

@[simp]
lemma CategoryTheory.Limits.kernel.map_zero {C : Type*} [Category C] [HasZeroMorphisms C]
    {X Y X' Y' : C} (f : X ⟶ Y) (f' : X' ⟶ Y') [HasKernel f] [HasKernel f'] (q : Y ⟶ Y')
    (w : f ≫ q = 0 ≫ f') : kernel.map f f' 0 q w = 0 := by
  simp only [← cancel_mono (kernel.ι f'), lift_ι, comp_zero, zero_comp]

namespace ChainComplex

variable {C : Type*} [Category C] [Preadditive C]

section

variable {K L : ChainComplex C ℕ} (φ₀ : K.X 0 ⟶ L.X 0) (φ₁ : K.X 1 ⟶ L.X 1)
  (comm₀₁ : φ₁ ≫ L.d 1 0 = K.d 1 0 ≫ φ₀)
  (ind : ∀ {n : ℕ} (φ : K.X n ⟶ L.X n) (φ' : K.X (n + 1) ⟶ L.X (n + 1))
    (_ : φ' ≫ L.d (n + 1) n = K.d (n + 1) n ≫ φ), K.X (n + 2) ⟶ L.X (n + 2))
  (hind : ∀ {n : ℕ} (φ : K.X n ⟶ L.X n) (φ' : K.X (n + 1) ⟶ L.X (n + 1))
    (h : φ' ≫ L.d (n + 1) n = K.d (n + 1) n ≫ φ), ind φ φ' h ≫ L.d _ _ = K.d _ _ ≫ φ')

namespace homMkInduction

open Classical in
noncomputable def f : ∀ n, K.X n ⟶ L.X n
  | 0 => φ₀
  | 1 => φ₁
  | n + 2 =>
      if h : f (n + 1) ≫ L.d (n + 1) n = K.d (n + 1) n ≫ f n then ind _ _ h else 0

@[simp]
lemma f_zero : f φ₀ φ₁ ind 0 = φ₀ := rfl

@[simp]
lemma f_one : f φ₀ φ₁ ind 1 = φ₁ := rfl

lemma comm (n : ℕ) : f φ₀ φ₁ ind (n + 1) ≫ L.d _ _ = K.d _ _ ≫ f φ₀ φ₁ ind n := by
  induction n with
  | zero => exact comm₀₁
  | succ n hn =>
      dsimp [f]
      rw [dif_pos hn]
      apply hind

lemma f_succ_succ (n : ℕ) :
    f φ₀ φ₁ ind (n + 2) = ind (f φ₀ φ₁ ind n) (f φ₀ φ₁ ind (n + 1))
      (comm φ₀ φ₁ comm₀₁ ind hind n) :=
  dif_pos _

end homMkInduction

noncomputable def homMkInduction : K ⟶ L where
  f := homMkInduction.f φ₀ φ₁ ind
  comm' := by
    rintro _ n rfl
    exact homMkInduction.comm φ₀ φ₁ comm₀₁ ind hind n

@[simp]
lemma homMkInduction_f_0 : (homMkInduction φ₀ φ₁ comm₀₁ ind hind).f 0 = φ₀ := rfl

@[simp]
lemma homMkInduction_f_1 : (homMkInduction φ₀ φ₁ comm₀₁ ind hind).f 1 = φ₁ := rfl

@[simp]
lemma homMkInduction_f (n : ℕ) :
    (homMkInduction φ₀ φ₁ comm₀₁ ind hind).f (n + 2) =
      ind ((homMkInduction φ₀ φ₁ comm₀₁ ind hind).f n)
        ((homMkInduction φ₀ φ₁ comm₀₁ ind hind).f (n + 1)) (by simp) :=
  homMkInduction.f_succ_succ φ₀ φ₁ comm₀₁ ind hind n

end

end ChainComplex

namespace CochainComplex

variable {C A : Type*} [Category C] [Abelian C] [Category A] [Preadditive A]
  [HasZeroObject A] [HasBinaryBiproducts A]
  (ι : A ⥤ C) [ι.Full] [ι.Faithful] [ι.PreservesZeroMorphisms] [ι.Additive]

structure LeftResolutions where
  F : C ⥤ A
  π : F ⋙ ι ⟶ 𝟭 C
  hπ (X : C) : Epi (π.app X) := by infer_instance

namespace LeftResolutions

attribute [instance] hπ

variable {ι}
variable (Λ : LeftResolutions ι)
variable (X Y Z : C) (f : X ⟶ Y) (g : Y ⟶ Z)

@[pp_dot]
noncomputable def chainComplex : ChainComplex A ℕ :=
  ChainComplex.mk' _ _ (ι.preimage (Λ.π.app (kernel (Λ.π.app X)) ≫ kernel.ι _))
    (fun f => ⟨_, ι.preimage (Λ.π.app (kernel (ι.map f)) ≫ kernel.ι _),
      ι.map_injective (by simp)⟩)

@[pp_dot]
noncomputable def chainComplexXZeroIso :
    (Λ.chainComplex X).X 0 ≅ Λ.F.obj X := Iso.refl _

@[pp_dot]
noncomputable def chainComplexXOneIso :
    (Λ.chainComplex X).X 1 ≅ Λ.F.obj (kernel (Λ.π.app X)) := Iso.refl _

@[reassoc]
lemma map_chainComplex_d_1_0 :
    ι.map ((Λ.chainComplex X).d 1 0) =
      ι.map (Λ.chainComplexXOneIso X).hom ≫ Λ.π.app (kernel (Λ.π.app X)) ≫ kernel.ι _ ≫
      ι.map (Λ.chainComplexXZeroIso X).inv := by
  simp [chainComplexXOneIso, chainComplexXZeroIso, chainComplex]

@[reassoc (attr := simp)]
lemma map_chainComplex_d_1_0_comp_π :
    ι.map ((Λ.chainComplex X).d 1 0) ≫ ι.map (Λ.chainComplexXZeroIso X).hom ≫ Λ.π.app X = 0 := by
  rw [map_chainComplex_d_1_0, assoc, assoc, assoc, ← ι.map_comp_assoc, Iso.inv_hom_id, ι.map_id,
    id_comp, kernel.condition, comp_zero, comp_zero]

@[pp_dot]
noncomputable def chainComplexXIso (n : ℕ) :
    (Λ.chainComplex X).X (n + 2) ≅ Λ.F.obj (kernel (ι.map ((Λ.chainComplex X).d (n + 1) n))) := by
  apply ChainComplex.mk'XIso

@[simp]
lemma map_chainComplex_d (n : ℕ) :
    ι.map ((Λ.chainComplex X).d (n + 2) (n + 1)) =
    ι.map (Λ.chainComplexXIso X n).hom ≫ Λ.π.app (kernel (ι.map ((Λ.chainComplex X).d (n + 1) n))) ≫
      kernel.ι (ι.map ((Λ.chainComplex X).d (n + 1) n)) := by
  erw [← ι.image_preimage (Λ.π.app _ ≫ kernel.ι (ι.map ((Λ.chainComplex X).d (n + 1) n)))]
  rw [← Functor.map_comp]
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
  simp

variable {X Y Z}

namespace chainComplexMap

noncomputable def ind {n : ℕ} (φ : (Λ.chainComplex X).X n ⟶ (Λ.chainComplex Y).X n)
    (φ' : (Λ.chainComplex X).X (n + 1) ⟶ (Λ.chainComplex Y).X (n + 1))
    (h : φ' ≫ (Λ.chainComplex Y).d (n + 1) n = (Λ.chainComplex X).d (n + 1) n ≫ φ) :
    (Λ.chainComplex X).X (n + 2) ⟶ (Λ.chainComplex Y).X (n + 2) :=
  (Λ.chainComplexXIso X n).hom ≫ (Λ.F.map
          (kernel.map _ _ (ι.map φ') (ι.map φ) (by
            rw [← ι.map_comp, ← ι.map_comp, h]))) ≫ (Λ.chainComplexXIso Y n).inv

lemma hind {n : ℕ} (φ : (Λ.chainComplex X).X n ⟶ (Λ.chainComplex Y).X n)
    (φ' : (Λ.chainComplex X).X (n + 1) ⟶ (Λ.chainComplex Y).X (n + 1))
    (h : φ' ≫ (Λ.chainComplex Y).d (n + 1) n = (Λ.chainComplex X).d (n + 1) n ≫ φ) :
    ind Λ φ φ' h ≫ HomologicalComplex.d _ _ _ = HomologicalComplex.d _ _ _ ≫ φ' :=
  ι.map_injective (by
    dsimp [ind]
    simp only [ι.map_comp, assoc, map_chainComplex_d]
    nth_rw 3 [← ι.map_comp_assoc]
    rw [Iso.inv_hom_id, ι.map_id, id_comp]
    dsimp
    erw [← NatTrans.naturality]
    dsimp
    nth_rw 2 [← ι.map_comp_assoc]
    rw [← Λ.F.map_comp, kernel.lift_ι]
    erw [← NatTrans.naturality]
    rfl)

end chainComplexMap

@[pp_dot]
noncomputable def chainComplexMap : Λ.chainComplex X ⟶ Λ.chainComplex Y :=
  ChainComplex.homMkInduction
    ((Λ.chainComplexXZeroIso X).hom ≫ Λ.F.map f ≫ (Λ.chainComplexXZeroIso Y).inv)
    ((Λ.chainComplexXOneIso X).hom ≫
      Λ.F.map (kernel.map _ _ (ι.map (Λ.F.map f)) f (Λ.π.naturality f).symm) ≫
      (Λ.chainComplexXOneIso Y).inv) (ι.map_injective (by
        dsimp
        simp only [assoc, Functor.map_comp, map_chainComplex_d_1_0]
        simp only [← ι.map_comp, ← ι.map_comp_assoc, Iso.inv_hom_id_assoc,
          Iso.inv_hom_id, comp_id]
        simp only [Functor.comp_obj, Functor.id_obj, Functor.map_comp, assoc]
        erw [← NatTrans.naturality_assoc]
        dsimp
        nth_rw 2 [← ι.map_comp_assoc]
        rw [← Λ.F.map_comp, kernel.lift_ι]
        simp only [Functor.map_comp, assoc]
        erw [← NatTrans.naturality_assoc, ← NatTrans.naturality_assoc]
        dsimp))
      (chainComplexMap.ind Λ) (chainComplexMap.hind Λ)

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
  apply ChainComplex.homMkInduction_f

variable (X) in
@[simp]
noncomputable def chainComplexMap_id : Λ.chainComplexMap (𝟙 X) = 𝟙 _ := by
  ext n
  induction n with
  | zero => simp
  | succ n hn =>
      obtain _|n := n
      · dsimp
        simp
      · dsimp
        simp [hn]

@[reassoc (attr := simp)]
lemma chainComplexMap_comp :
    Λ.chainComplexMap (f ≫ g) = Λ.chainComplexMap f ≫ Λ.chainComplexMap g := by
  ext n
  induction n with
  | zero => simp
  | succ n hn =>
      obtain _|n := n
      · simp [-Functor.map_comp, ← Λ.F.map_comp_assoc, ← ι.map_comp]
        congr 1
        rw [← cancel_mono (kernel.ι _)]
        simp
      · simp [-Functor.map_comp, ← Λ.F.map_comp_assoc]
        congr 1
        rw [← cancel_mono (kernel.ι _)]
        simp [hn]

noncomputable def chainComplexFunctor : C ⥤ ChainComplex A ℕ where
  obj := Λ.chainComplex
  map := Λ.chainComplexMap

noncomputable def cochainComplexFunctor : C ⥤ CochainComplex A ℤ :=
  Λ.chainComplexFunctor ⋙ (ComplexShape.embeddingDownNat).extendFunctor _

variable (X)

noncomputable abbrev cochainComplex : CochainComplex A ℤ := Λ.cochainComplexFunctor.obj X

noncomputable def cochainComplexXZeroIso : (Λ.cochainComplex X).X 0 ≅ Λ.F.obj X :=
  (Λ.chainComplex X).extendXIso _ (by dsimp) ≪≫ Λ.chainComplexXZeroIso X

noncomputable def cochainComplexXNegOneIso :
    (Λ.cochainComplex X).X (-1) ≅ Λ.F.obj (kernel (Λ.π.app X)) :=
  (Λ.chainComplex X).extendXIso _ (by dsimp) ≪≫ Λ.chainComplexXOneIso X

noncomputable def cochainComplexπ :
    (ι.mapHomologicalComplex _).obj (Λ.cochainComplex X) ⟶
      (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj X :=
  HomologicalComplex.mkHomToSingle (ι.map (Λ.cochainComplexXZeroIso X).hom ≫ Λ.π.app X) (by
    rintro i hi
    dsimp at hi
    obtain rfl : i = -1 := by omega
    dsimp [cochainComplex, cochainComplexFunctor,
      cochainComplexXZeroIso, chainComplexFunctor]
    rw [← ι.map_comp_assoc,
      (Λ.chainComplex X).extend_d_eq ComplexShape.embeddingDownNat (i := 1) (j := 0)
      (by simp) (by simp), assoc, assoc, Iso.inv_hom_id_assoc,
      ι.map_comp, ι.map_comp, assoc, assoc, map_chainComplex_d_1_0_comp_π, comp_zero])

@[simps]
noncomputable def cochainComplexNatTransπ :
    Λ.cochainComplexFunctor ⋙ ι.mapHomologicalComplex _ ⟶
      HomologicalComplex.single C (ComplexShape.up ℤ) 0 where
  app := Λ.cochainComplexπ
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

end LeftResolutions

end CochainComplex


/-variable {F : C ⥤ C} (π : F ⟶ 𝟭 C)

variable [HasKernels C]
variable (X Y Z : C) (φ φ' : X ⟶ Y) (ψ : Y ⟶ Z)

noncomputable def leftResolution' : ChainComplex C ℕ :=
  mk' _ _ (π.app X) (fun {X₀ X₁} f =>
    ⟨_, π.app (kernel f) ≫ kernel.ι _, by simp⟩)

noncomputable def leftResolution'XZeroIso : (leftResolution' π X).X 0 ≅ X := Iso.refl _
noncomputable def leftResolution'XOneIso : (leftResolution' π X).X 1 ≅ F.obj X := Iso.refl _

@[simp]
lemma leftResolution'_d_1_0 : (leftResolution' π X).d 1 0 =
    (leftResolution'XOneIso π X).hom ≫ π.app X ≫ (leftResolution'XZeroIso π X).inv := by
  simp [leftResolution'XOneIso, leftResolution'XZeroIso, leftResolution']

noncomputable def leftResolution'XIso (n : ℕ) :
    (leftResolution' π X).X (n + 2) ≅ F.obj (kernel ((leftResolution' π X).d (n + 1) n)) := by
  apply mk'XIso

@[simp]
lemma leftResolution'_d (n : ℕ) :
    (leftResolution' π X).d (n + 2) (n + 1) = (leftResolution'XIso π X n).hom ≫
      π.app _ ≫ kernel.ι ((leftResolution' π X).d (n + 1) n) := by apply mk'_d

attribute [irreducible] leftResolution'

attribute [local instance] epi_comp

section

variable [∀ X, Epi (π.app X)]

instance epi_leftResolution'_d_1_0 : Epi ((leftResolution' π X).d 1 0) := by
  rw [leftResolution'_d_1_0]
  infer_instance

lemma leftResolution'_exactAt (n : ℕ) : (leftResolution' π X).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp only [prev]; omega) (by simp),
    ShortComplex.exact_iff_epi_kernel_lift]
  convert (epi_comp (leftResolution'XIso π X n).hom (π.app _))
  rw [← cancel_mono (kernel.ι _), kernel.lift_ι]
  simp

end

variable {X Y Z}

noncomputable def leftResolution'Map : leftResolution' π X ⟶ leftResolution' π Y :=
  homMkInduction ((leftResolution'XZeroIso π X).hom ≫ φ ≫ (leftResolution'XZeroIso π Y).inv)
    ((leftResolution'XOneIso π X).hom ≫ F.map φ ≫ (leftResolution'XOneIso π Y).inv)
    (by simp) (fun {n} φ φ' h => (leftResolution'XIso π X n).hom ≫
      F.map (kernel.map _ _ φ' φ h.symm) ≫ (leftResolution'XIso π Y n).inv) (by simp)

@[simp]
lemma leftResolution'Map_f_0 :
    (leftResolution'Map π φ).f 0 =
      (leftResolution'XZeroIso π X).hom ≫ φ ≫ (leftResolution'XZeroIso π Y).inv := by
  simp [leftResolution'Map]

@[simp]
lemma leftResolution'Map_f_1 :
    (leftResolution'Map π φ).f 1 =
      (leftResolution'XOneIso π X).hom ≫ F.map φ ≫ (leftResolution'XOneIso π Y).inv := by
  simp [leftResolution'Map]

@[simp]
lemma leftResolution'Map_f (n : ℕ) :
    (leftResolution'Map π φ).f (n + 2) =
      (leftResolution'XIso π X n).hom ≫
      F.map (kernel.map _ _ ((leftResolution'Map π φ).f (n + 1))
        ((leftResolution'Map π φ).f n) (by simp)) ≫ (leftResolution'XIso π Y n).inv :=
  homMkInduction_f _ _ _ _ (by simp) _

variable (X) in
@[simp]
lemma leftResolution'Map_id :
    leftResolution'Map π (𝟙 X) = 𝟙 _ := by
  ext n
  induction n with
  | zero => simp
  | succ n hn =>
      obtain _|n := n
      · simp
      · simp [hn]

@[reassoc (attr := simp)]
lemma leftResolution'Map_comp :
    leftResolution'Map π (φ ≫ ψ) = leftResolution'Map π φ ≫ leftResolution'Map π ψ := by
  ext n
  induction n with
  | zero => simp
  | succ n hn =>
      obtain _|n := n
      · simp
      · simp only [leftResolution'Map_f, hn, HomologicalComplex.comp_f, assoc,
          Iso.inv_hom_id_assoc, Iso.cancel_iso_hom_left, ← F.map_comp_assoc]
        congr 2
        simp [← cancel_mono (kernel.ι _)]

variable (K L) in
@[simp]
lemma leftResolution'Map_zero [F.PreservesZeroMorphisms] :
    leftResolution'Map π (0 : K ⟶ L) = 0 := by
  ext n
  induction n with
  | zero => simp
  | succ n hn =>
      obtain _|n := n
      · simp
      · simp [hn]

@[simp]
lemma leftResolution'Map_add [F.Additive] :
    leftResolution'Map π (φ + φ') = leftResolution'Map π φ + leftResolution'Map π φ' := by
  ext n
  induction n with
  | zero => simp
  | succ n hn =>
      obtain _|n := n
      · simp
      · simp only [leftResolution'Map_f, hn, HomologicalComplex.add_f_apply]
        rw [← comp_add, ← add_comp, ← F.map_add]
        congr 3
        aesop_cat

@[simps]
noncomputable def leftResolution'Functor : C ⥤ ChainComplex C ℕ where
  obj := leftResolution' π
  map φ := leftResolution'Map π φ

instance [F.PreservesZeroMorphisms] : (leftResolution'Functor π).PreservesZeroMorphisms where

instance [F.Additive] : (leftResolution'Functor π).Additive where

noncomputable def leftResolutionFunctor : C ⥤ ChainComplex C ℕ :=
  leftResolution'Functor π ⋙ (ComplexShape.embeddingDownNatGE 1).restrictionFunctor C

instance [F.PreservesZeroMorphisms] : (leftResolutionFunctor π).PreservesZeroMorphisms := by
  dsimp only [leftResolutionFunctor]
  infer_instance

instance [F.Additive] : (leftResolutionFunctor π).Additive := by
  dsimp only [leftResolutionFunctor]
  infer_instance

noncomputable def leftResolutionFunctorπ₀ :
    leftResolutionFunctor π ⋙ HomologicalComplex.eval _ _ 0 ⟶ 𝟭 _ where
  app K := (leftResolution' π K).d 1 0 ≫ (leftResolution'XZeroIso π K).hom
  naturality _ _ f := by
    dsimp [leftResolutionFunctor]
    rw [leftResolution'Map_f_1]
    simp

@[reassoc (attr := simp)]
lemma leftResolutionFunctorπ₀_naturality :
    ((leftResolutionFunctor π).map φ).f 0 ≫ (leftResolutionFunctorπ₀ π).app Y =
      (leftResolutionFunctorπ₀ π).app X ≫ φ :=
  (leftResolutionFunctorπ₀ π).naturality φ

@[reassoc (attr := simp)]
lemma d_leftResolutionFunctorπ₀_app (n : ℕ) :
    ((leftResolutionFunctor π).obj X).d n 0 ≫ (leftResolutionFunctorπ₀ π).app X = 0 := by
  dsimp [leftResolutionFunctor, leftResolutionFunctorπ₀]
  rw [HomologicalComplex.d_comp_d_assoc, zero_comp]

noncomputable def leftResolutionFunctorπ :
    leftResolutionFunctor π ⟶ HomologicalComplex.single C _ 0 where
  app X := (toSingle₀Equiv _ _).symm ⟨(leftResolutionFunctorπ₀ π).app X, by simp⟩
  naturality X Y φ := (toSingle₀Equiv _ _).injective (by aesop_cat)

variable (X)

lemma leftResolutionFunctorπ₀_obj_exactAt [∀ X, Epi (π.app X)] (n : ℕ) :
    ((leftResolutionFunctor π).obj X).ExactAt (n + 1) := by
  have ex := leftResolution'_exactAt π X (n + 1)
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp; rfl) (by simp)]
  rw [HomologicalComplex.exactAt_iff' _ (n + 3) (n + 2) (n + 1) (by simp; rfl) (by simp)] at ex
  exact ex

instance [∀ X, Epi (π.app X)] : QuasiIso ((leftResolutionFunctorπ π).app X) := by
  rw [quasiIso_iff]
  rintro (_|n)
  · have ex := (leftResolution'_exactAt π X) 0
    rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)] at ex
    rw [ChainComplex.quasiIsoAt₀_iff,
      ShortComplex.quasiIso_iff_of_zeros' _ (by simp) (by rfl) (by rfl) ]
    refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2 ⟨ex, by dsimp; infer_instance⟩
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
      (leftResolution'XZeroIso π X).symm (by simp [leftResolutionFunctor])
      (by simp [leftResolutionFunctorπ, leftResolutionFunctorπ₀])
  · rw [quasiIsoAt_iff_exactAt]
    · exact exactAt_succ_single_obj X n
    · exact (leftResolutionFunctorπ₀_obj_exactAt π X n)

end ChainComplex

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D] [HasZeroObject C] [HasZeroMorphisms C]
  [HasZeroMorphisms D] [HasCokernels D]

@[simps]
noncomputable def Functor.modCokernelFromZero (F : C ⥤ D) : C ⥤ D where
  obj X := cokernel (F.map (0 : 0 ⟶ X))
  map φ := cokernel.map _ _ (𝟙 _) (F.map φ) (by rw [id_comp, ← F.map_comp, zero_comp])

instance (F : C ⥤ D) : F.modCokernelFromZero.PreservesZeroMorphisms where
  map_zero X Y := by
    dsimp
    ext
    simpa only [coequalizer_as_cokernel, cokernel.π_desc, comp_zero,
      ← F.map_comp_assoc, zero_comp]
      using (F.map (0 : X ⟶ 0)) ≫= cokernel.condition (F.map (0 : 0 ⟶ Y))

namespace NatTrans

variable [HasZeroObject D] {F : D ⥤ D} (ε : F ⟶ 𝟭 _)

noncomputable def fromModCokernelFromZero : F.modCokernelFromZero ⟶ 𝟭 _ where
  app X := cokernel.desc _ (ε.app X) (by rw [ε.naturality, Functor.id_map, comp_zero])

instance (X : D) [Epi (ε.app X)] : Epi ((fromModCokernelFromZero ε).app X) := by
  have h : cokernel.π _ ≫ (fromModCokernelFromZero ε).app X = ε.app X :=
    by simp [fromModCokernelFromZero]
  exact epi_of_epi_fac h

end NatTrans

end CategoryTheory
-/
