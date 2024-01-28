import Mathlib.Algebra.Homology.DerivedCategory.IsLE
import Mathlib.Algebra.Homology.Factorizations.Basic

open CategoryTheory Limits Category Preadditive ZeroObject

lemma HomologicalComplex.mono_of_mono_f {C ι : Type*} [Category C] {c : ComplexShape ι}
    [HasZeroMorphisms C]
    {K L : HomologicalComplex C c} (f : K ⟶ L) [hf : ∀ (n : ι), Mono (f.f n)] : Mono f where
  right_cancellation f₁ f₂ h := by
    ext n
    rw [← cancel_mono (f.f n), ← comp_f, ← comp_f, h]

noncomputable instance {C D : Type*} [Category C] [Category D] (F : C ⥤ D) [HasZeroMorphisms C]
    [HasZeroMorphisms D] [F.PreservesZeroMorphisms] [PreservesFiniteBiproducts F] :
    PreservesBinaryBiproducts F where
  preserves {X Y} := preservesBinaryBiproductOfPreservesBiproduct F X Y

variable {C : Type*} [Category C] [Abelian C] [EnoughInjectives C]
  {K L : CochainComplex C ℤ} (f : K ⟶ L)

namespace CochainComplex

namespace CM5b

variable (K L)

@[simps]
noncomputable def I : CochainComplex C ℤ where
  X n := Injective.under (K.X n)
  d _ _ := 0

instance (n : ℤ) : Injective ((I K).X n) := by
  simp only [I_X]
  infer_instance

instance (n : ℤ) [K.IsStrictlyGE n] : (I K).IsStrictlyGE n where
  isZero i hi := Injective.isZero_under _ (K.isZero_of_isStrictlyGE n i hi)

instance (n : ℤ) [K.IsStrictlyGE (n+1)] [L.IsStrictlyGE n] :
    (mappingCone (𝟙 (I K)) ⊞ L).IsStrictlyGE n where
  isZero i hi := by
    refine' IsZero.of_iso _ ((HomologicalComplex.eval C (ComplexShape.up ℤ) i).mapBiprod _ _)
    dsimp
    simp only [biprod.is_zero_iff, mappingCone.isZero_X_iff, I_X]
    refine' ⟨⟨_, _⟩, L.isZero_of_isStrictlyGE n i hi⟩
    all_goals
      apply (I K).isZero_of_isStrictlyGE (n + 1)
      linarith

noncomputable def p : mappingCone (𝟙 (I K)) ⊞ L ⟶ L := biprod.snd

variable {K L}

noncomputable def i : K ⟶ mappingCone (𝟙 (I K)) ⊞ L :=
  biprod.lift (mappingCone.lift _
    (HomComplex.Cocycle.mk (HomComplex.Cochain.mk (fun p q _ => K.d p q ≫ Injective.ι _)) 2
      (by linarith) (by
        ext p q hpq
        dsimp
        rw [HomComplex.δ_v 1 2 (by linarith) _ p q hpq (p+1) (p+1) (by linarith) rfl]
        simp))
    (HomComplex.Cochain.ofHoms (fun n => Injective.ι _)) (by aesop_cat)) f

lemma i_f_comp (n : ℤ) : (i f).f n ≫
    (biprod.fst : mappingCone (𝟙 (I K)) ⊞ L ⟶ _).f n ≫
      (mappingCone.snd (𝟙 (I K))).v n n (add_zero n) = Injective.ι (K.X n) := by
  dsimp [i]
  rw [← HomologicalComplex.comp_f_assoc, biprod.lift_fst,
    mappingCone.lift_f_snd_v, HomComplex.Cochain.ofHoms_v]

instance (n : ℤ) : Mono ((i f).f n) :=  mono_of_mono_fac (i_f_comp f n)

instance : Mono (i f) := HomologicalComplex.mono_of_mono_f _

@[reassoc (attr := simp)]
lemma fac : i f ≫ p K L = f := by simp [i, p]

variable (K L)

instance (n : ℤ) : Injective ((mappingCone (𝟙 (I K))).X n) :=
  Injective.of_iso (HomologicalComplex.homotopyCofiber.XIsoBiprod (𝟙 (I K)) n (n + 1) rfl).symm inferInstance

lemma degreewiseEpiWithInjectiveKernel_p :
    degreewiseEpiWithInjectiveKernel (p K L) := fun n => by
  rw [epiWithInjectiveKernel_iff]
  refine' ⟨(mappingCone (𝟙 (I K))).X n, inferInstance,
    (biprod.inl :_ ⟶ (mappingCone (𝟙 (I K))) ⊞ L).f n,
    (biprod.inr :_ ⟶ (mappingCone (𝟙 (I K))) ⊞ L).f n,
    (biprod.fst : (mappingCone (𝟙 (I K))) ⊞ L ⟶ _).f n,
    _, _, _, _, _⟩
  · dsimp [p]
    rw [← HomologicalComplex.comp_f, biprod.inl_snd, HomologicalComplex.zero_f]
  · rw [← HomologicalComplex.comp_f, biprod.inr_fst, HomologicalComplex.zero_f]
  · rw [← HomologicalComplex.comp_f, biprod.inl_fst, HomologicalComplex.id_f]
  · dsimp [p]
    rw [← HomologicalComplex.comp_f, biprod.inr_snd, HomologicalComplex.id_f]
  · dsimp [p]
    rw [← HomologicalComplex.id_f, ← biprod.total, HomologicalComplex.add_f_apply,
      HomologicalComplex.comp_f, HomologicalComplex.comp_f]

noncomputable def mappingConeHomotopyZero (M : CochainComplex C ℤ): Homotopy (𝟙 (mappingCone (𝟙 M))) 0 :=
  mappingCone.liftHomotopy _ _ _ (mappingCone.snd (𝟙 M)) 0 (by simp) (by simp)

noncomputable def homotopyEquiv : HomotopyEquiv (mappingCone (𝟙 (I K)) ⊞ L) L where
  hom := p K L
  inv := biprod.inr
  homotopyHomInvId := by
    let h₁ := ((mappingConeHomotopyZero (I K)).compRight
      (biprod.inl : _ ⟶ mappingCone (𝟙 (I K)) ⊞ L)).compLeft
        (biprod.fst : mappingCone (𝟙 (I K)) ⊞ L ⟶ _)
    let h₂ := Homotopy.add h₁ (Homotopy.refl (biprod.snd ≫ biprod.inr))
    exact Homotopy.trans (Homotopy.ofEq (by simp [p])) (h₂.symm.trans (Homotopy.ofEq (by simp [p])))
  homotopyInvHomId := Homotopy.ofEq (by simp [p])

instance quasiIso_i : QuasiIso (p K L) := (homotopyEquiv K L).toQuasiIso

end CM5b

lemma CM5b (n : ℤ) [K.IsStrictlyGE (n+1)] [L.IsStrictlyGE n] :
    ∃ (L' : CochainComplex C ℤ) (_hL' : L'.IsStrictlyGE n) (i : K ⟶ L') (p : L' ⟶ L)
      (_hi : Mono i) (_hp : degreewiseEpiWithInjectiveKernel p) (_hp' : QuasiIso p), i ≫ p = f :=
  ⟨_ , by infer_instance, CM5b.i f, CM5b.p K L, inferInstance,
    CM5b.degreewiseEpiWithInjectiveKernel_p K L, inferInstance, by simp⟩

end CochainComplex
