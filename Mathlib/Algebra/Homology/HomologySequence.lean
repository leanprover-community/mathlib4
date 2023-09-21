import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
import Mathlib.Algebra.Homology.ShortComplex.ShortComplexFour
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.HomologicalComplexLimits

open CategoryTheory Category Limits

def CategoryTheory.Limits.KernelFork.IsLimit.ofι'
    {C : Type*} [Category C] [HasZeroMorphisms C] {X Y K : C} {f : X ⟶ Y} (i : K ⟶ X) (w : i ≫ f = 0)
    (h : ∀ {A : C} (k : A ⟶ X) (_ : k ≫ f = 0), { l : A ⟶ K // l ≫ i = k}) [hi : Mono i] :
    IsLimit (KernelFork.ofι _ w) :=
  ofι _ _ (fun {A} k hk => (h k hk).1) (fun {A} k hk => (h k hk).2) (fun {A} k hk m hm => by
    rw [← cancel_mono i, (h k hk).2, hm])

def CategoryTheory.Limits.CokernelCofork.IsColimit.ofπ'
    {C : Type*} [Category C] [HasZeroMorphisms C] {X Y Q : C} {f : X ⟶ Y} (p : Y ⟶ Q) (w : f ≫ p = 0)
    (h : ∀ {A : C} (k : Y ⟶ A) (_ : f ≫ k = 0), { l : Q ⟶ A // p ≫ l = k}) [hp : Epi p] :
    IsColimit (CokernelCofork.ofπ _ w) :=
  ofπ _ _ (fun {A} k hk => (h k hk).1) (fun {A} k hk => (h k hk).2) (fun {A} k hk m hm => by
    rw [← cancel_epi p, (h k hk).2, hm])

variable {C ι : Type*} [Category C] [Abelian C] {c : ComplexShape ι}

variable {S S' : ShortComplex (HomologicalComplex C c)} (hS : S.ShortExact) (hS' : S'.ShortExact)
  (τ : S ⟶ S') (K L : HomologicalComplex C c) (φ : K ⟶ L)
  {i j : ι} (hij : c.Rel i j)

namespace HomologicalComplex

variable (i j)

noncomputable def opcyclesToCycles : K.opcycles i ⟶ K.cycles j :=
  K.liftCycles (K.fromOpcycles i j) _ rfl (by simp)

@[reassoc (attr := simp)]
lemma opcyclesToCycles_iCycles : K.opcyclesToCycles i j ≫ K.iCycles j = K.fromOpcycles i j := by
  dsimp only [opcyclesToCycles]
  simp

@[reassoc (attr := simp)]
lemma pOpcycles_opcyclesToCycles_iCycles :
    K.pOpcycles i ≫ K.opcyclesToCycles i j ≫ K.iCycles j = K.d i j := by
  simp [opcyclesToCycles]

@[reassoc (attr := simp)]
lemma pOpcycles_opcyclesToCycles :
    K.pOpcycles i ≫ K.opcyclesToCycles i j = K.toCycles i j := by
  simp only [← cancel_mono (K.iCycles j), assoc, opcyclesToCycles_iCycles,
    p_fromOpcycles, toCycles_i]

@[reassoc (attr := simp)]
lemma homologyι_opcyclesToCycles :
    K.homologyι i ≫ K.opcyclesToCycles i j = 0 := by
  simp only [← cancel_mono (K.iCycles j), assoc, opcyclesToCycles_iCycles,
    homologyι_comp_fromOpcycles, zero_comp]

@[reassoc (attr := simp)]
lemma opcyclesToCycles_homologyπ :
    K.opcyclesToCycles i j ≫ K.homologyπ j = 0 := by
  simp only [← cancel_epi (K.pOpcycles i),
    pOpcycles_opcyclesToCycles_assoc, toCycles_comp_homologyπ, comp_zero]

variable {K L}

@[reassoc (attr := simp)]
lemma opcyclesToCycles_naturality :
    opcyclesMap φ i ≫ opcyclesToCycles L i j = opcyclesToCycles K i j ≫ cyclesMap φ j := by
  simp only [← cancel_mono (L.iCycles j), ← cancel_epi (K.pOpcycles i),
    assoc, p_opcyclesMap_assoc, pOpcycles_opcyclesToCycles_iCycles, Hom.comm, cyclesMap_i,
    pOpcycles_opcyclesToCycles_iCycles_assoc]

variable (K)

@[simps]
noncomputable def shortComplex₄ : ShortComplex₄ C where
  f := K.homologyι i
  g := K.opcyclesToCycles i j
  h := K.homologyπ j

instance : Mono (K.shortComplex₄ i j).f := by
  dsimp
  infer_instance

instance : Epi (K.shortComplex₄ i j).h := by
  dsimp
  infer_instance

instance [Mono φ] (i : ι) : Mono (φ.f i) := by
  change Mono ((HomologicalComplex.eval C c i).map φ)
  infer_instance

instance [Epi φ] (i : ι) : Epi (φ.f i) := by
  change Epi ((HomologicalComplex.eval C c i).map φ)
  infer_instance

lemma shortComplex₄_exact : (K.shortComplex₄ i j).Exact where
  exact₂ := by
    let S := ShortComplex.mk _ _ (K.homologyι_comp_fromOpcycles i j)
    let φ : (K.shortComplex₄ i j).shortComplex₁ ⟶ S :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := K.iCycles j  }
    rw [ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ]
    exact S.exact_of_f_is_kernel (K.homologyIsKernel i j (c.next_eq' hij))
  exact₃ := by
    let S := ShortComplex.mk _ _ (K.toCycles_comp_homologyπ i j)
    let φ : S ⟶ (K.shortComplex₄ i j).shortComplex₂ :=
      { τ₁ := K.pOpcycles i
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _  }
    rw [← ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ]
    exact S.exact_of_g_is_cokernel (K.homologyIsCokernel i j (c.prev_eq' hij))

instance : Mono (K.shortComplex₄ i j).shortComplex₁.f := by
  dsimp
  infer_instance

instance : Epi (K.shortComplex₄ i j).shortComplex₂.g := by
  dsimp
  infer_instance

variable (C c)

@[simps]
noncomputable def natTransOpCyclesToCycles : opcyclesFunctor C c i ⟶ cyclesFunctor C c j where
  app K := K.opcyclesToCycles i j

attribute [local simp] homologyMap_comp opcyclesMap_comp cyclesMap_comp

@[simps]
noncomputable def shortComplex₄Functor : HomologicalComplex C c ⥤ ShortComplex₄ C where
  obj K := K.shortComplex₄ i j
  map {K₁ K₂} φ :=
    { τ₁ := homologyMap φ i
      τ₂ := opcyclesMap φ i
      τ₃ := cyclesMap φ j
      τ₄ := homologyMap φ j }

namespace HomologySequence

instance : (opcyclesFunctor C c i).PreservesZeroMorphisms where
instance : (cyclesFunctor C c i).PreservesZeroMorphisms where

variable {C c i j}

instance [Mono (φ.f j)] : Mono (cyclesMap φ j) :=
  mono_of_mono_fac (cyclesMap_i φ j)

attribute [local instance] epi_comp

instance [Epi (φ.f i)] : Epi (opcyclesMap φ i) :=
  epi_of_epi_fac (p_opcyclesMap φ i)

variable (i j)

def opcyclesRightExact :
    (ShortComplex.mk (opcyclesMap S.f j) (opcyclesMap S.g j) (by rw [← opcyclesMap_comp, S.zero, opcyclesMap_zero])).Exact := by
  have := hS.epi_g
  have hj := (hS.map_of_exact (HomologicalComplex.eval C c j)).gIsCokernel
  apply ShortComplex.exact_of_g_is_cokernel
  refine' CokernelCofork.IsColimit.ofπ' _ _  (fun {A} k hk => by
    dsimp at k hk ⊢
    have H := CokernelCofork.IsColimit.desc' hj (S.X₂.pOpcycles j ≫ k) (by
      dsimp
      rw [← p_opcyclesMap_assoc, hk, comp_zero])
    dsimp at H
    refine' ⟨S.X₃.descOpcycles H.1 _ rfl _, _⟩
    · rw [← cancel_epi (S.g.f (c.prev j)), comp_zero, Hom.comm_assoc, H.2,
        d_pOpcycles_assoc, zero_comp]
    · rw [← cancel_epi (S.X₂.pOpcycles j), opcyclesMap_comp_descOpcycles, p_descOpcycles, H.2])

def cyclesLeftExact :
    (ShortComplex.mk (cyclesMap S.f i) (cyclesMap S.g i) (by rw [← cyclesMap_comp, S.zero, cyclesMap_zero])).Exact := by
  have := hS.mono_f
  have hi := (hS.map_of_exact (HomologicalComplex.eval C c i)).fIsKernel
  apply ShortComplex.exact_of_f_is_kernel
  exact KernelFork.IsLimit.ofι' _ _ (fun {A} k hk => by
    dsimp at k hk ⊢
    have H := KernelFork.IsLimit.lift' hi (k ≫ S.X₂.iCycles i) (by
      dsimp
      rw [assoc, ← cyclesMap_i, reassoc_of% hk, zero_comp])
    dsimp at H
    refine' ⟨S.X₁.liftCycles H.1 _ rfl _, _⟩
    · rw [← cancel_mono (S.f.f _), assoc, zero_comp, ← Hom.comm, reassoc_of% H.2,
        iCycles_d, comp_zero]
    · rw [← cancel_mono (S.X₂.iCycles i), liftCycles_comp_cyclesMap, liftCycles_i, H.2])

@[simps]
noncomputable def snakeInput : ShortComplex.SnakeInput C where
  L₀ := (homologyFunctor C c i).mapShortComplex.obj S
  L₁ := (opcyclesFunctor C c i).mapShortComplex.obj S
  L₂ := (cyclesFunctor C c j).mapShortComplex.obj S
  L₃ := (homologyFunctor C c j).mapShortComplex.obj S
  v₀₁ := S.mapNatTrans (natTransHomologyι C c i)
  v₁₂ := S.mapNatTrans (natTransOpCyclesToCycles C c i j)
  v₂₃ := S.mapNatTrans (natTransHomologyπ C c j)
  w₀₂ := by ext <;> dsimp <;> simp
  w₁₃ := by ext <;> dsimp <;> simp
  h₀ := by
    apply ShortComplex.isLimitOfIsLimitπ
    all_goals
      refine' (KernelFork.isLimitMapConeEquiv _ _).symm _
      exact (HomologicalComplex.shortComplex₄_exact _ i j hij).exact₂.fIsKernel
  h₃ := by
    apply ShortComplex.isColimitOfIsColimitπ
    all_goals
      refine' (CokernelCofork.isColimitMapCoconeEquiv _ _).symm _
      exact (HomologicalComplex.shortComplex₄_exact _ i j hij).exact₃.gIsCokernel
  epi_L₁_g := by
    have := hS.epi_g
    dsimp
    infer_instance
  mono_L₂_f := by
    have := hS.mono_f
    dsimp
    infer_instance
  L₁_exact := opcyclesRightExact hS i
  L₂_exact := cyclesLeftExact hS j

@[simps]
noncomputable def snakeInputHom : snakeInput hS i j hij ⟶ snakeInput hS' i j hij where
  f₀ := (homologyFunctor C c i).mapShortComplex.map τ
  f₁ := (opcyclesFunctor C c i).mapShortComplex.map τ
  f₂ := (cyclesFunctor C c j).mapShortComplex.map τ
  f₃ := (homologyFunctor C c j).mapShortComplex.map τ
  comm₀₁ := by ext <;> dsimp <;> simp
  comm₁₂ := by ext <;> dsimp <;> simp
  comm₂₃ := by ext <;> dsimp <;> simp

end HomologySequence

end HomologicalComplex

namespace CategoryTheory

namespace ShortComplex

namespace ShortExact

open HomologicalComplex HomologySequence

variable (i j)

noncomputable def δ : S.X₃.homology i ⟶ S.X₁.homology j := (snakeInput hS i j hij).δ

@[reassoc (attr := simp)]
lemma δ_comp : hS.δ i j hij ≫ HomologicalComplex.homologyMap S.f j = 0 := (snakeInput hS i j hij).δ_L₃_f

@[reassoc (attr := simp)]
lemma comp_δ : HomologicalComplex.homologyMap S.g i ≫ hS.δ i j hij = 0 := (snakeInput hS i j hij).L₀_g_δ

lemma exact₁ : (ShortComplex.mk _ _ (δ_comp hS i j hij)).Exact :=
  (snakeInput hS i j hij).exact_L₂'

lemma exact₃ : (ShortComplex.mk _ _ (comp_δ hS i j hij)).Exact :=
  (snakeInput hS i j hij).exact_L₁'

lemma exact₂ : (ShortComplex.mk (HomologicalComplex.homologyMap S.f i) (HomologicalComplex.homologyMap S.g i)
    (by rw [← HomologicalComplex.homologyMap_comp, S.zero, HomologicalComplex.homologyMap_zero])).Exact := by
  by_cases c.Rel i (c.next i)
  · exact (snakeInput hS i _ h).ex₀
  · have : ∀ (K : HomologicalComplex C c), IsIso (K.homologyι i) :=
      fun K => ShortComplex.isIso_homologyι (K.sc i) (K.shape _ _ h)
    have e : S.map (HomologicalComplex.homologyFunctor C c i) ≅ S.map (HomologicalComplex.opcyclesFunctor C c i) :=
      ShortComplex.isoMk (asIso (S.X₁.homologyι i))
        (asIso (S.X₂.homologyι i)) (asIso (S.X₃.homologyι i)) (by aesop_cat) (by aesop_cat)
    exact ShortComplex.exact_of_iso e.symm (opcyclesRightExact hS i)

lemma δ_naturality : HomologicalComplex.homologyMap τ.τ₃ i ≫ hS'.δ i j hij =
    hS.δ i j hij ≫ HomologicalComplex.homologyMap τ.τ₁ j :=
  SnakeInput.naturality_δ (snakeInputHom hS hS' τ i j hij)

@[reassoc]
lemma comp_δ_eq {A : C} (x₃ : A ⟶ S.X₃.X i) (x₂ : A ⟶ S.X₂.X i) (y₁ : A ⟶ S.X₁.X j)
    (hx₃ : x₃ ≫ S.X₃.d i j = 0) (hx₂ : x₂ ≫ S.g.f i = x₃)
    (hy₁ : y₁ ≫ S.f.f j = x₂ ≫ S.X₂.d i j) :
    S.X₃.liftCycles x₃ j (c.next_eq' hij) hx₃ ≫ S.X₃.homologyπ i ≫ hS.δ i j hij =
      S.X₁.liftCycles y₁ _ rfl (by
        have := hS.mono_f
        rw [← cancel_mono (S.f.f _), assoc, ← Hom.comm, reassoc_of% hy₁, S.X₂.d_comp_d,
          comp_zero, zero_comp]) ≫ S.X₁.homologyπ j := by
  have eq := (snakeInput hS i j hij).comp_δ_eq
    (S.X₃.liftCycles x₃ j (c.next_eq' hij) hx₃ ≫ S.X₃.homologyπ i)
    (x₂ ≫ S.X₂.pOpcycles i) (S.X₁.liftCycles y₁ _ rfl (by
      have := hS.mono_f
      rw [← cancel_mono (S.f.f _), assoc, ← Hom.comm, reassoc_of% hy₁, S.X₂.d_comp_d,
        comp_zero, zero_comp])) (by simp [reassoc_of% hx₂]) (by
        rw [← cancel_mono (S.X₂.iCycles j)]
        simp [hy₁])
  simpa only [assoc] using eq

end ShortExact

end ShortComplex

end CategoryTheory
