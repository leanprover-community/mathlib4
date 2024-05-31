/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
# The homology sequence

If `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` is a short exact sequence in a category of complexes
`HomologicalComplex C c` in an abelian category (i.e. `S` is a short complex in
that category and satisfies `hS : S.ShortExact`), then whenever `i` and `j` are degrees
such that `hij : c.Rel i j`, then there is a long exact sequence :
`... ⟶ S.X₁.homology i ⟶ S.X₂.homology i ⟶ S.X₃.homology i ⟶ S.X₁.homology j ⟶ ...`.
The connecting homomorphism `S.X₃.homology i ⟶ S.X₁.homology j` is `hS.δ i j hij`, and
the exactness is asserted as lemmas `hS.homology_exact₁`, `hS.homology_exact₂` and
`hS.homology_exact₃`.

The proof is based on the snake lemma, similarly as it was originally done in
the Liquid Tensor Experiment.

## References

* https://stacks.math.columbia.edu/tag/0111

-/

open CategoryTheory Category Limits

namespace HomologicalComplex

section HasZeroMorphisms

variable {C ι : Type*} [Category C] [HasZeroMorphisms C] {c : ComplexShape ι}
  (K L : HomologicalComplex C c) (φ : K ⟶ L) (i j : ι)
  [K.HasHomology i] [K.HasHomology j] [L.HasHomology i] [L.HasHomology j]

/-- The morphism `K.opcycles i ⟶ K.cycles j` that is induced by `K.d i j`. -/
noncomputable def opcyclesToCycles [K.HasHomology i] [K.HasHomology j] :
    K.opcycles i ⟶ K.cycles j :=
  K.liftCycles (K.fromOpcycles i j) _ rfl (by simp)

@[reassoc (attr := simp)]
lemma opcyclesToCycles_iCycles : K.opcyclesToCycles i j ≫ K.iCycles j = K.fromOpcycles i j := by
  dsimp only [opcyclesToCycles]
  simp

@[reassoc]
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

variable (C c)

/-- The natural transformation `K.opcyclesToCycles i j : K.opcycles i ⟶ K.cycles j` for all
`K : HomologicalComplex C c`. -/
@[simps]
noncomputable def natTransOpCyclesToCycles [CategoryWithHomology C] :
    opcyclesFunctor C c i ⟶ cyclesFunctor C c j where
  app K := K.opcyclesToCycles i j

end HasZeroMorphisms

section Preadditive

variable {C ι : Type*} [Category C] [Preadditive C] {c : ComplexShape ι}
  (K : HomologicalComplex C c) (i j : ι) (hij : c.Rel i j)

namespace HomologySequence

/-- The diagram `K.homology i ⟶ K.opcycles i ⟶ K.cycles j ⟶ K.homology j`. -/
@[simp]
noncomputable def composableArrows₃ [K.HasHomology i] [K.HasHomology j] :
    ComposableArrows C 3 :=
  ComposableArrows.mk₃ (K.homologyι i) (K.opcyclesToCycles i j) (K.homologyπ j)

instance [K.HasHomology i] [K.HasHomology j] :
    Mono ((composableArrows₃ K i j).map' 0 1) := by
  dsimp
  infer_instance

-- Adaptation note: nightly-2024-03-11
-- We turn off simprocs here.
-- Ideally someone will investigate whether `simp` lemmas can be rearranged
-- so that this works without the `set_option`,
-- *or* come up with a proposal regarding finer control of disabling simprocs.
set_option simprocs false in
instance [K.HasHomology i] [K.HasHomology j] :
    Epi ((composableArrows₃ K i j).map' 2 3) := by
  dsimp
  infer_instance

/-- The diagram `K.homology i ⟶ K.opcycles i ⟶ K.cycles j ⟶ K.homology j` is exact
when `c.Rel i j`. -/
lemma composableArrows₃_exact [CategoryWithHomology C] :
    (composableArrows₃ K i j).Exact := by
  let S := ShortComplex.mk (K.homologyι i) (K.opcyclesToCycles i j) (by simp)
  let S' := ShortComplex.mk (K.homologyι i) (K.fromOpcycles i j) (by simp)
  let ι : S ⟶ S' :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := K.iCycles j }
  have hS : S.Exact := by
    rw [ShortComplex.exact_iff_of_epi_of_isIso_of_mono ι]
    exact S'.exact_of_f_is_kernel (K.homologyIsKernel i j (c.next_eq' hij))
  let T := ShortComplex.mk (K.opcyclesToCycles i j) (K.homologyπ j) (by simp)
  let T' := ShortComplex.mk (K.toCycles i j) (K.homologyπ j) (by simp)
  let π : T' ⟶ T :=
    { τ₁ := K.pOpcycles i
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _ }
  have hT : T.Exact := by
    rw [← ShortComplex.exact_iff_of_epi_of_isIso_of_mono π]
    exact T'.exact_of_g_is_cokernel (K.homologyIsCokernel i j (c.prev_eq' hij))
  apply ComposableArrows.exact_of_δ₀
  · exact hS.exact_toComposableArrows
  · exact hT.exact_toComposableArrows

variable (C)

attribute [local simp] homologyMap_comp cyclesMap_comp opcyclesMap_comp

-- Adaptation note: nightly-2024-03-11
-- We turn off simprocs here.
-- Ideally someone will investigate whether `simp` lemmas can be rearranged
-- so that this works without the `set_option`,
-- *or* come up with a proposal regarding finer control of disabling simprocs.
set_option simprocs false in
/-- The functor `HomologicalComplex C c ⥤ ComposableArrows C 3` that maps `K` to the
diagram `K.homology i ⟶ K.opcycles i ⟶ K.cycles j ⟶ K.homology j`. -/
@[simps]
noncomputable def composableArrows₃Functor [CategoryWithHomology C] :
    HomologicalComplex C c ⥤ ComposableArrows C 3 where
  obj K := composableArrows₃ K i j
  map {K L} φ := ComposableArrows.homMk₃ (homologyMap φ i) (opcyclesMap φ i) (cyclesMap φ j)
    (homologyMap φ j) (by aesop_cat) (by aesop_cat) (by aesop_cat)

end HomologySequence

end Preadditive

section Abelian

variable {C ι : Type*} [Category C] [Abelian C] {c : ComplexShape ι}

/-- If `X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` is an exact sequence of homological complexes, then
`X₁.opcycles i ⟶ X₂.opcycles i ⟶ X₃.opcycles i ⟶ 0` is exact. This lemma states
the exactness at `X₂.opcycles i`, while the fact that `X₂.opcycles i ⟶ X₃.opcycles i`
is an epi is an instance. -/
lemma opcycles_right_exact (S : ShortComplex (HomologicalComplex C c)) (hS : S.Exact) [Epi S.g]
    (i : ι) [S.X₁.HasHomology i] [S.X₂.HasHomology i] [S.X₃.HasHomology i] :
    (ShortComplex.mk (opcyclesMap S.f i) (opcyclesMap S.g i)
      (by rw [← opcyclesMap_comp, S.zero, opcyclesMap_zero])).Exact := by
  have : Epi (ShortComplex.map S (eval C c i)).g := by dsimp; infer_instance
  have hj := (hS.map (HomologicalComplex.eval C c i)).gIsCokernel
  apply ShortComplex.exact_of_g_is_cokernel
  refine CokernelCofork.IsColimit.ofπ' _ _  (fun {A} k hk => by
    dsimp at k hk ⊢
    have H := CokernelCofork.IsColimit.desc' hj (S.X₂.pOpcycles i ≫ k) (by
      dsimp
      rw [← p_opcyclesMap_assoc, hk, comp_zero])
    dsimp at H
    refine ⟨S.X₃.descOpcycles H.1 _ rfl ?_, ?_⟩
    · rw [← cancel_epi (S.g.f (c.prev i)), comp_zero, Hom.comm_assoc, H.2,
        d_pOpcycles_assoc, zero_comp]
    · rw [← cancel_epi (S.X₂.pOpcycles i), opcyclesMap_comp_descOpcycles, p_descOpcycles, H.2])

/-- If `0 ⟶ X₁ ⟶ X₂ ⟶ X₃` is an exact sequence of homological complex, then
`0 ⟶ X₁.cycles i ⟶ X₂.cycles i ⟶ X₃.cycles i` is exact. This lemma states
the exactness at `X₂.cycles i`, while the fact that `X₁.cycles i ⟶ X₂.cycles i`
is a mono is an instance. -/
lemma cycles_left_exact (S : ShortComplex (HomologicalComplex C c)) (hS : S.Exact) [Mono S.f]
    (i : ι) [S.X₁.HasHomology i] [S.X₂.HasHomology i] [S.X₃.HasHomology i] :
    (ShortComplex.mk (cyclesMap S.f i) (cyclesMap S.g i)
      (by rw [← cyclesMap_comp, S.zero, cyclesMap_zero])).Exact := by
  have : Mono (ShortComplex.map S (eval C c i)).f := by dsimp; infer_instance
  have hi := (hS.map (HomologicalComplex.eval C c i)).fIsKernel
  apply ShortComplex.exact_of_f_is_kernel
  exact KernelFork.IsLimit.ofι' _ _ (fun {A} k hk => by
    dsimp at k hk ⊢
    have H := KernelFork.IsLimit.lift' hi (k ≫ S.X₂.iCycles i) (by
      dsimp
      rw [assoc, ← cyclesMap_i, reassoc_of% hk, zero_comp])
    dsimp at H
    refine ⟨S.X₁.liftCycles H.1 _ rfl ?_, ?_⟩
    · rw [← cancel_mono (S.f.f _), assoc, zero_comp, ← Hom.comm, reassoc_of% H.2,
        iCycles_d, comp_zero]
    · rw [← cancel_mono (S.X₂.iCycles i), liftCycles_comp_cyclesMap, liftCycles_i, H.2])

variable  {S : ShortComplex (HomologicalComplex C c)}
  (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j)

namespace HomologySequence

/-- Given a short exact short complex `S : HomologicalComplex C c`, and degrees `i` and `j`
such that `c.Rel i j`, this is the snake diagram whose four lines are respectively
obtained by applying the functors `homologyFunctor C c i`, `opcyclesFunctor C c i`,
`cyclesFunctor C c j`, `homologyFunctor C c j` to `S`. Applying the snake lemma to this
gives the homology sequence of `S`. -/
@[simps]
noncomputable def snakeInput : ShortComplex.SnakeInput C where
  L₀ := (homologyFunctor C c i).mapShortComplex.obj S
  L₁ := (opcyclesFunctor C c i).mapShortComplex.obj S
  L₂ := (cyclesFunctor C c j).mapShortComplex.obj S
  L₃ := (homologyFunctor C c j).mapShortComplex.obj S
  v₀₁ := S.mapNatTrans (natTransHomologyι C c i)
  v₁₂ := S.mapNatTrans (natTransOpCyclesToCycles C c i j)
  v₂₃ := S.mapNatTrans (natTransHomologyπ C c j)
  h₀ := by
    apply ShortComplex.isLimitOfIsLimitπ
    all_goals
      exact (KernelFork.isLimitMapConeEquiv _ _).symm
        ((composableArrows₃_exact _ i j hij).exact 0).fIsKernel
  h₃ := by
    apply ShortComplex.isColimitOfIsColimitπ
    all_goals
      exact (CokernelCofork.isColimitMapCoconeEquiv _ _).symm
        ((composableArrows₃_exact _ i j hij).exact 1).gIsCokernel
  L₁_exact := by
    have := hS.epi_g
    exact opcycles_right_exact S hS.exact i
  L₂_exact := by
    have := hS.mono_f
    exact cycles_left_exact S hS.exact j
  epi_L₁_g := by
    have := hS.epi_g
    dsimp
    infer_instance
  mono_L₂_f := by
    have := hS.mono_f
    dsimp
    infer_instance

end HomologySequence

end Abelian

end HomologicalComplex

namespace CategoryTheory

open HomologicalComplex HomologySequence

variable {C ι : Type*} [Category C] [Abelian C] {c : ComplexShape ι}
  {S : ShortComplex (HomologicalComplex C c)}
  (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j)

namespace ShortComplex

namespace ShortExact

/-- The connecting homoomorphism `S.X₃.homology i ⟶ S.X₁.homology j` for a short exact
short complex `S`.  -/
noncomputable def δ : S.X₃.homology i ⟶ S.X₁.homology j := (snakeInput hS i j hij).δ

@[reassoc (attr := simp)]
lemma δ_comp : hS.δ i j hij ≫ HomologicalComplex.homologyMap S.f j = 0 :=
  (snakeInput hS i j hij).δ_L₃_f

@[reassoc (attr := simp)]
lemma comp_δ : HomologicalComplex.homologyMap S.g i ≫ hS.δ i j hij = 0 :=
  (snakeInput hS i j hij).L₀_g_δ

/-- Exactness of `S.X₃.homology i ⟶ S.X₁.homology j ⟶ S.X₂.homology j`. -/
lemma homology_exact₁ : (ShortComplex.mk _ _ (δ_comp hS i j hij)).Exact :=
  (snakeInput hS i j hij).L₂'_exact

/-- Exactness of `S.X₁.homology i ⟶ S.X₂.homology i ⟶ S.X₃.homology i`. -/
lemma homology_exact₂ : (ShortComplex.mk (HomologicalComplex.homologyMap S.f i)
    (HomologicalComplex.homologyMap S.g i) (by rw [← HomologicalComplex.homologyMap_comp,
      S.zero, HomologicalComplex.homologyMap_zero])).Exact := by
  by_cases h : c.Rel i (c.next i)
  · exact (snakeInput hS i _ h).L₀_exact
  · have := hS.epi_g
    have : ∀ (K : HomologicalComplex C c), IsIso (K.homologyι i) :=
      fun K => ShortComplex.isIso_homologyι (K.sc i) (K.shape _ _ h)
    have e : S.map (HomologicalComplex.homologyFunctor C c i) ≅
        S.map (HomologicalComplex.opcyclesFunctor C c i) :=
      ShortComplex.isoMk (asIso (S.X₁.homologyι i))
        (asIso (S.X₂.homologyι i)) (asIso (S.X₃.homologyι i)) (by aesop_cat) (by aesop_cat)
    exact ShortComplex.exact_of_iso e.symm (opcycles_right_exact S hS.exact i)

/-- Exactness of `S.X₂.homology i ⟶ S.X₃.homology i ⟶ S.X₁.homology j`. -/
lemma homology_exact₃ : (ShortComplex.mk _ _ (comp_δ hS i j hij)).Exact :=
  (snakeInput hS i j hij).L₁'_exact

lemma δ_eq' {A : C} (x₃ : A ⟶ S.X₃.homology i) (x₂ : A ⟶ S.X₂.opcycles i)
    (x₁ : A ⟶ S.X₁.cycles j)
    (h₂ : x₂ ≫ HomologicalComplex.opcyclesMap S.g i = x₃ ≫ S.X₃.homologyι i)
    (h₁ : x₁ ≫ HomologicalComplex.cyclesMap S.f j = x₂ ≫ S.X₂.opcyclesToCycles i j) :
    x₃ ≫ hS.δ i j hij = x₁ ≫ S.X₁.homologyπ j :=
  (snakeInput hS i j hij).δ_eq x₃ x₂ x₁ h₂ h₁

lemma δ_eq {A : C} (x₃ : A ⟶ S.X₃.X i) (hx₃ : x₃ ≫ S.X₃.d i j = 0)
    (x₂ : A ⟶ S.X₂.X i) (hx₂ : x₂ ≫ S.g.f i = x₃)
    (x₁ : A ⟶ S.X₁.X j) (hx₁ : x₁ ≫ S.f.f j = x₂ ≫ S.X₂.d i j)
    (k : ι) (hk : c.next j = k) :
    S.X₃.liftCycles x₃ j (c.next_eq' hij) hx₃ ≫ S.X₃.homologyπ i ≫ hS.δ i j hij =
      S.X₁.liftCycles x₁ k hk (by
        have := hS.mono_f
        rw [← cancel_mono (S.f.f k), assoc, ← S.f.comm, reassoc_of% hx₁,
          d_comp_d, comp_zero, zero_comp]) ≫ S.X₁.homologyπ j := by
  simpa only [assoc] using hS.δ_eq' i j hij (S.X₃.liftCycles x₃ j
    (c.next_eq' hij) hx₃ ≫ S.X₃.homologyπ i)
    (x₂ ≫ S.X₂.pOpcycles i) (S.X₁.liftCycles x₁ k hk _)
      (by simp only [assoc, HomologicalComplex.p_opcyclesMap,
        HomologicalComplex.homology_π_ι,
        HomologicalComplex.liftCycles_i_assoc, reassoc_of% hx₂])
      (by rw [← cancel_mono (S.X₂.iCycles j), HomologicalComplex.liftCycles_comp_cyclesMap,
        HomologicalComplex.liftCycles_i, assoc, assoc, opcyclesToCycles_iCycles,
        HomologicalComplex.p_fromOpcycles, hx₁])

end ShortExact

end ShortComplex

end CategoryTheory
