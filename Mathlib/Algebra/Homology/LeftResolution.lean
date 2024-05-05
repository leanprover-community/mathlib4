import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
import Mathlib.Algebra.Homology.Embedding.ExtendMap
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.BicomplexRows
import Mathlib.Algebra.Homology.CochainComplexMinus
import Mathlib.Algebra.Homology.TotalComplexMap

open CategoryTheory Category Limits Preadditive ZeroObject ComplexShape

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
    (prev_eq' _ (by dsimp; omega)) (by simp),
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
lemma chainComplexMap_id : Λ.chainComplexMap (𝟙 X) = 𝟙 _ := by
  ext n
  induction n with
  | zero => simp
  | succ n hn =>
      obtain _|n := n
      · dsimp
        simp
      · simp [hn]

variable (X Y) in
@[simp]
lemma chainComplexMap_zero [Λ.F.PreservesZeroMorphisms] :
    Λ.chainComplexMap (0 : X ⟶ Y) = 0 := by
  ext n
  induction n with
  | zero => simp
  | succ n hn =>
      obtain _|n := n
      · simp
      · simp [hn]

@[reassoc, simp]
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

@[pp_dot]
noncomputable def chainComplexFunctor : C ⥤ ChainComplex A ℕ where
  obj := Λ.chainComplex
  map := Λ.chainComplexMap

@[pp_dot]
noncomputable def cochainComplexFunctor : C ⥤ CochainComplex A ℤ :=
  Λ.chainComplexFunctor ⋙ (embeddingDownNat).extendFunctor _

variable (X)

@[pp_dot]
noncomputable abbrev cochainComplex : CochainComplex A ℤ := Λ.cochainComplexFunctor.obj X

@[pp_dot]
noncomputable def cochainComplexXZeroIso : (Λ.cochainComplex X).X 0 ≅ Λ.F.obj X :=
  (Λ.chainComplex X).extendXIso _ (by dsimp) ≪≫ Λ.chainComplexXZeroIso X

@[pp_dot]
noncomputable def cochainComplexXNegOneIso :
    (Λ.cochainComplex X).X (-1) ≅ Λ.F.obj (kernel (Λ.π.app X)) :=
  (Λ.chainComplex X).extendXIso _ (by dsimp) ≪≫ Λ.chainComplexXOneIso X

lemma cochainComplex_d_neg_one_zero :
    ι.map ((cochainComplex Λ X).d (-1) 0) = ι.map (cochainComplexXNegOneIso Λ X).hom ≫
      Λ.π.app (kernel (Λ.π.app X)) ≫ kernel.ι (Λ.π.app X) ≫
        ι.map (cochainComplexXZeroIso Λ X).inv := by
  dsimp [cochainComplex, cochainComplexFunctor, chainComplexFunctor,
    cochainComplexXNegOneIso]
  rw [(Λ.chainComplex X).extend_d_eq embeddingDownNat (i := 1) (j := 0)
      (by simp) (by simp), ι.map_comp, ι.map_comp, map_chainComplex_d_1_0,
      ι.map_comp, assoc, assoc, assoc, assoc, ← ι.map_comp]
  rfl

@[pp_dot]
noncomputable def cochainComplexπ :
    (ι.mapHomologicalComplex _).obj (Λ.cochainComplex X) ⟶
      (HomologicalComplex.single C (up ℤ) 0).obj X :=
  HomologicalComplex.mkHomToSingle (ι.map (Λ.cochainComplexXZeroIso X).hom ≫ Λ.π.app X) (by
    rintro i hi
    dsimp at hi
    obtain rfl : i = -1 := by omega
    dsimp
    rw [cochainComplex_d_neg_one_zero, assoc, assoc, assoc, ← ι.map_comp_assoc,
      Iso.inv_hom_id, ι.map_id, id_comp, kernel.condition, comp_zero, comp_zero])

lemma cochainComplexπ_f_0 :
    (Λ.cochainComplexπ X).f 0 = ι.map (Λ.cochainComplexXZeroIso X).hom ≫ Λ.π.app X ≫
      (HomologicalComplex.singleObjXSelf (up ℤ) 0 X).inv := by
  simp [cochainComplexπ ]

@[simps, pp_dot]
noncomputable def cochainComplexNatTransπ :
    Λ.cochainComplexFunctor ⋙ ι.mapHomologicalComplex _ ⟶
      HomologicalComplex.single C (up ℤ) 0 where
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

instance : CochainComplex.IsGE
    ((ι.mapHomologicalComplex _).obj (Λ.cochainComplex X)) 0 where
  exactAt i hi := by
    apply HomologicalComplex.ExactAt.of_iso _
      (((embeddingDownNat).mapExtendFunctorNatIso ι).symm.app (Λ.chainComplex X))
    dsimp
    obtain ⟨j, hj⟩ : ∃ (j : ℕ), (embeddingDownNat).f (j + 1) = i := by
      have : i ≤ -1 := by
        by_contra!
        obtain ⟨k, hk⟩ := @Int.eq_ofNat_of_zero_le (a := i) (by omega)
        exact hi k (by dsimp; omega)
      obtain ⟨j, hj⟩ := Int.eq_add_ofNat_of_le this
      exact ⟨j, by dsimp; omega⟩
    rw [HomologicalComplex.extend_exactAt_iff _ _ hj]
    apply exactAt_map_chainComplex_succ

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
  refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2 ⟨hS, by dsimp; infer_instance⟩
  refine' ShortComplex.isoMk (ι.mapIso (Λ.cochainComplexXNegOneIso X))
    (ι.mapIso (Λ.cochainComplexXZeroIso X))
    (HomologicalComplex.singleObjXSelf (up ℤ) 0 X) _ _
  · dsimp
    rw [cochainComplex_d_neg_one_zero, assoc, assoc, assoc, ← ι.map_comp,
      Iso.inv_hom_id, ι.map_id]
    dsimp
    rw [comp_id]
  · simp [cochainComplexπ_f_0]

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

variable [Λ.F.PreservesZeroMorphisms]

instance : Λ.chainComplexFunctor.PreservesZeroMorphisms where
  map_zero _ _ := by
    simp [chainComplexFunctor]

instance : Λ.cochainComplexFunctor.PreservesZeroMorphisms where
  map_zero _ _ := by
    simp [cochainComplexFunctor]

noncomputable def bicomplexFunctor :
    CochainComplex C ℤ ⥤ HomologicalComplex₂ A (up ℤ) (up ℤ) :=
      Λ.cochainComplexFunctor.mapHomologicalComplex (up ℤ)

instance (K : CochainComplex C ℤ) (i : ℤ) :
    CochainComplex.IsStrictlyLE ((Λ.bicomplexFunctor.obj K).X i) 0 := by
  dsimp [bicomplexFunctor]
  infer_instance

instance (K : CochainComplex C ℤ) (i : ℤ) :
    IsStrictlyLE (((bicomplexFunctor Λ ⋙
      Functor.mapHomologicalComplex₂ ι (up ℤ) (up ℤ)).obj K).X i) 0 := by
  dsimp [Functor.mapHomologicalComplex₂]
  infer_instance

instance (K : CochainComplex C ℤ) (i : ℤ) [K.IsStrictlyLE i] :
    CochainComplex.IsStrictlyLE (Λ.bicomplexFunctor.obj K) i := by
  dsimp [bicomplexFunctor]
  infer_instance

instance (K : CochainComplex C ℤ) (i : ℤ) [K.IsStrictlyLE i] :
    CochainComplex.IsStrictlyLE ((ι.mapHomologicalComplex₂ _ _).obj
      (Λ.bicomplexFunctor.obj K)) i := by
  dsimp [bicomplexFunctor, Functor.mapHomologicalComplex₂]
  infer_instance

instance (K : CochainComplex C ℤ) (i : ℤ) [K.IsStrictlyLE i]:
    IsStrictlyLE ((bicomplexFunctor Λ ⋙
      Functor.mapHomologicalComplex₂ ι (up ℤ) (up ℤ)).obj K) i := by
  dsimp
  infer_instance

instance (K : CochainComplex C ℤ) (i : ℤ)  :
    CochainComplex.IsStrictlyLE (((ι.mapHomologicalComplex₂ _ _).obj
      (Λ.bicomplexFunctor.obj K)).X i) 0 := by
  dsimp [bicomplexFunctor, Functor.mapHomologicalComplex₂]
  infer_instance

variable [HasFiniteCoproducts A]

instance (K : CochainComplex.Minus C) :
    (Λ.bicomplexFunctor.obj K.obj).HasTotal (up ℤ) := by
  obtain ⟨i, hi⟩ := K.2
  exact HomologicalComplex₂.hasTotal_of_isStrictlyLE _ i 0

instance (K : CochainComplex.Minus C) :
    ((ι.mapHomologicalComplex₂ _ _).obj (Λ.bicomplexFunctor.obj K.obj)).HasTotal (up ℤ) := by
  obtain ⟨i, hi⟩ := K.2
  exact HomologicalComplex₂.hasTotal_of_isStrictlyLE _ i 0

instance (K : CochainComplex.Minus C) :
    ((Λ.bicomplexFunctor ⋙ ι.mapHomologicalComplex₂ _ _).obj K.obj).HasTotal (up ℤ) := by
  dsimp
  infer_instance

instance (K : CochainComplex C ℤ) (i : ℤ) :
    IsStrictlyLE (((HomologicalComplex₂.singleRow C (up ℤ) (up ℤ) 0).obj K).X i) 0 := by
  dsimp [HomologicalComplex₂.singleRow]
  infer_instance

instance (K : CochainComplex C ℤ) (i : ℤ) [K.IsStrictlyLE i] :
    IsStrictlyLE ((HomologicalComplex₂.singleRow C (up ℤ) (up ℤ) 0).obj K) i := by
  dsimp [HomologicalComplex₂.singleRow]
  infer_instance

instance (K : CochainComplex C ℤ) :
    ((HomologicalComplex₂.singleRow C (up ℤ) (up ℤ) 0).obj K).HasTotal (up ℤ) := fun i =>
  hasCoproduct_of_isZero_but_one _ ⟨⟨i, 0⟩, by simp⟩ (by
    rintro ⟨⟨p, q⟩, hpq⟩ h
    apply HomologicalComplex.isZero_single_obj_X
    rintro rfl
    obtain rfl : p = i := by simpa using hpq
    exact h rfl)

instance (K : CochainComplex C ℤ) (i : ℤ) [K.IsStrictlyLE i]
    [(Λ.bicomplexFunctor.obj K).HasTotal (up ℤ)]:
    CochainComplex.IsStrictlyLE ((Λ.bicomplexFunctor.obj K).total (up ℤ)) i where
  isZero n hn := by
    rw [IsZero.iff_id_eq_zero]
    ext i₁ i₂ h
    dsimp at h hn
    apply IsZero.eq_of_src
    by_cases hi₂ : 0 < i₂
    · exact CochainComplex.isZero_of_isStrictlyLE _ 0 _ hi₂
    · have : IsZero (((Λ.bicomplexFunctor).obj K).X i₁) := by
        apply CochainComplex.isZero_of_isStrictlyLE _ i
        by_contra!
        obtain ⟨k, hk⟩ := Int.eq_add_ofNat_of_le (show n ≤ i by omega)
        exact hn k (by omega)
      exact (HomologicalComplex.eval _ _ i₂).map_isZero this

noncomputable abbrev bicomplexπ :
    Λ.bicomplexFunctor ⋙ ι.mapHomologicalComplex₂ (up ℤ) (up ℤ) ⟶
      HomologicalComplex₂.singleRow C (up ℤ) (up ℤ) 0 :=
  NatTrans.mapHomologicalComplex Λ.cochainComplexNatTransπ (up ℤ)

section

variable (K L : CochainComplex.Minus C) (φ : K ⟶ L)

noncomputable def totalπ'  :
    ((ι.mapHomologicalComplex₂ _ _).obj (Λ.bicomplexFunctor.obj K.obj)).total (up ℤ) ⟶
      ((HomologicalComplex₂.singleRow C (up ℤ) (up ℤ) 0).obj K.obj).total (up ℤ) :=
  HomologicalComplex₂.total.map (Λ.bicomplexπ.app K.obj) (up ℤ)

variable {K L} in
@[reassoc (attr := simp)]
lemma totalπ'_naturality :
    (HomologicalComplex₂.total.map
      ((ι.mapHomologicalComplex₂ (up ℤ) (up ℤ)).map
        (Λ.bicomplexFunctor.map φ)) (up ℤ)) ≫ Λ.totalπ' L =
      Λ.totalπ' K ≫ HomologicalComplex₂.total.map
        ((HomologicalComplex₂.singleRow C (up ℤ) (up ℤ) 0).map φ) (up ℤ) := by
  dsimp [totalπ']
  simp only [← HomologicalComplex₂.total.map_comp]
  congr 1
  ext x y
  by_cases hy : y = 0
  · subst hy
    have eq := Λ.π.naturality (φ.f x)
    dsimp at eq
    dsimp [cochainComplexπ, bicomplexFunctor, cochainComplexFunctor]
    simp only [HomologicalComplex.mkHomToSingle_f, Functor.mapHomologicalComplex_obj_X, assoc,
      HomologicalComplex.single_map_f_self, Iso.inv_hom_id_assoc, ← reassoc_of% eq,
      ← ι.map_comp_assoc]
    simp only [← assoc]
    congr 3
    rw [HomologicalComplex.extendMap_f (i := 0) (h := by rfl)]
    dsimp [cochainComplexXZeroIso, chainComplexFunctor]
    simp
  · apply IsZero.eq_of_tgt
    apply HomologicalComplex₂.isZero_singleRow_X_X
    exact hy

instance : QuasiIso (Λ.totalπ' K) := by
  obtain ⟨i, hi⟩ := K.2
  apply HomologicalComplex₂.total.quasiIso_map_of_isStrictlyGE_of_isStrictlyLE _ i 0
  dsimp [bicomplexπ]
  infer_instance

noncomputable instance : ι.PreservesTotalComplex ((bicomplexFunctor Λ).obj K.obj) (up ℤ) := by
  apply Nonempty.some
  have ⟨i, hi⟩ := K.2
  exact ⟨HomologicalComplex₂.preservesTotal_of_isStrictlyLE _ i 0 ι⟩

noncomputable def totalπ :
    (ι.mapHomologicalComplex _).obj ((Λ.bicomplexFunctor.obj K.obj).total (up ℤ)) ⟶ K.obj :=
  (HomologicalComplex₂.mapTotalIso _ _ _).inv ≫ Λ.totalπ' K ≫
    (HomologicalComplex₂.singleRow₀ObjTotal K.obj).hom

instance : QuasiIso (Λ.totalπ K) := by
  dsimp only [totalπ]
  infer_instance

@[pp_dot]
noncomputable def resolutionFunctor : CochainComplex.Minus C ⥤ CochainComplex.Minus A where
  obj K := ⟨((Λ.bicomplexFunctor.obj K.obj).total (up ℤ)), by
    obtain ⟨i, hi⟩ := K.2
    exact ⟨i, inferInstance⟩⟩
  map {K L} φ := HomologicalComplex₂.total.map (Λ.bicomplexFunctor.map φ) (up ℤ)
  map_id K := by
    dsimp
    erw [Λ.bicomplexFunctor.map_id, HomologicalComplex₂.total.map_id]
    rfl
  map_comp φ ψ := by
    dsimp
    erw [Λ.bicomplexFunctor.map_comp, HomologicalComplex₂.total.map_comp]
    rfl

@[pp_dot]
noncomputable def resolutionNatTrans : Λ.resolutionFunctor ⋙ ι.mapCochainComplexMinus ⟶ 𝟭 _ where
  app := Λ.totalπ
  naturality {K L} f := by
    dsimp [resolutionFunctor, totalπ]
    erw [HomologicalComplex₂.mapTotalIso_inv_naturality_assoc]
    rw [totalπ'_naturality_assoc]
    erw [assoc ((HomologicalComplex₂.mapTotalIso ι _ (up ℤ)).inv), assoc]
    rw [HomologicalComplex₂.singleRow₀ObjTotal_hom_naturality]

lemma quasiIso_resolutionNatTrans_app (K : CochainComplex.Minus C) :
    Minus.quasiIso (Λ.resolutionNatTrans.app K) :=
  inferInstanceAs (QuasiIso (Λ.totalπ K))

end

end LeftResolutions

end CochainComplex

/-
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
