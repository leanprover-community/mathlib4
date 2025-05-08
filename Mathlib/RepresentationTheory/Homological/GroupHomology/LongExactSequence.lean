/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality

/-!
# Long exact sequence in group homology

Given a commutative ring `k` and a group `G`, this file shows that a short exact sequence of
`k`-linear `G`-representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` induces a short exact sequence of
complexes of inhomogeneous chains `0 ⟶ C(X₁) ⟶ C(X₂) ⟶ C(X₃) ⟶ 0`, where `Hₙ(C(Xᵢ))`
is the `n`th group homology of `Xᵢ`.

This allows us to specialize API about long exact sequences to group homology.

## Main definitions

* `groupHomology.δ hX i j hij`: the connecting homomorphism `Hᵢ(G, X₃) ⟶ Hⱼ(G, X₁)` associated
  to an exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of representations.

-/

universe u

namespace groupHomology

open CategoryTheory ShortComplex Finsupp

variable {k G : Type u} [CommRing k] [Group G] [DecidableEq G]
  {X : ShortComplex (Rep k G)} (hX : ShortExact X)

include hX

lemma map_chainsFunctor_shortExact :
    ShortExact (X.map (chainsFunctor k G)) :=
  letI := hX.2
  letI := hX.3
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => {
    exact := by
      have : LinearMap.range X.f.hom.hom = LinearMap.ker X.g.hom.hom :=
        (hX.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
      simp [moduleCat_exact_iff_range_eq_ker, ker_mapRange, range_mapRange_linearMap X.f.hom.hom
        (LinearMap.ker_eq_bot.2 ((ModuleCat.mono_iff_injective _).1 <|
        (forget₂ (Rep k G) (ModuleCat k)).map_mono X.f)), this]
    mono_f := chainsMap_id_f_map_mono X.f i
    epi_g := chainsMap_id_f_map_epi X.g i }

open HomologicalComplex.HomologySequence

/-- The short complex  `Hᵢ(G, X₃) ⟶ Hⱼ(G, X₁) ⟶ Hⱼ(G, X₂)` associated to an exact sequence
of representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`. -/
noncomputable abbrev mapShortComplex₁ {i j : ℕ} (hij : j + 1 = i) :=
  (snakeInput (map_chainsFunctor_shortExact hX) _ _ hij).L₂'

variable (X) in
/-- The short complex `Hᵢ(G, X₁) ⟶ Hᵢ(G, X₂) ⟶ Hᵢ(G, X₃)` associated to a short complex of
representations `X₁ ⟶ X₂ ⟶ X₃`. -/
noncomputable abbrev mapShortComplex₂ (i : ℕ) := X.map (functor k G i)

/-- The short complex `Hᵢ(G, X₂) ⟶ Hᵢ(G, X₃) ⟶ Hⱼ(G, X₁)` associated to an exact sequence of
representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`. -/
noncomputable abbrev mapShortComplex₃ {i j : ℕ} (hij : j + 1 = i) :=
  (snakeInput (map_chainsFunctor_shortExact hX) _ _ hij).L₁'

/-- Exactness of `Hᵢ(G, X₃) ⟶ Hⱼ(G, X₁) ⟶ Hⱼ(G, X₂)`. -/
lemma mapShortComplex₁_exact {i j : ℕ} (hij : j + 1 = i) :
    (mapShortComplex₁ hX hij).Exact :=
  (map_chainsFunctor_shortExact hX).homology_exact₁ i j hij

/-- Exactness of `Hᵢ(G, X₁) ⟶ Hᵢ(G, X₂) ⟶ Hᵢ(G, X₃)`. -/
lemma mapShortComplex₂_exact (i : ℕ) :
    (mapShortComplex₂ X i).Exact :=
  (map_chainsFunctor_shortExact hX).homology_exact₂ i

/--  Exactness of `Hᵢ(G, X₂) ⟶ Hᵢ(G, X₃) ⟶ Hⱼ(G, X₁)`. -/
lemma mapShortComplex₃_exact {i j : ℕ} (hij : j + 1 = i) :
    (mapShortComplex₃ hX hij).Exact :=
  (map_chainsFunctor_shortExact hX).homology_exact₃ i j hij

/-- The connecting homomorphism `Hᵢ(G, X₃) ⟶ Hⱼ(G, X₁)` associated to an exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of representations. -/
noncomputable abbrev δ (i j : ℕ) (hij : j + 1 = i) :
    groupHomology X.X₃ i ⟶ groupHomology X.X₁ j :=
  (map_chainsFunctor_shortExact hX).δ i j hij

theorem δ_apply (i j : ℕ) (hij : j + 1 = i)
    (z : (Fin i → G) →₀ X.X₃) (hz : (inhomogeneousChains X.X₃).d i j z = 0)
    (y : (Fin i → G) →₀ X.X₂) (hy : (chainsMap (MonoidHom.id G) X.g).f i y = z)
    (x : (Fin j → G) →₀ X.X₁)
    (hx : mapRange.linearMap X.f.hom.hom x = (inhomogeneousChains X.X₂).d i j y) :
    δ hX i j hij (groupHomologyπ X.X₃ i <|
      (moduleCatCyclesIso _).inv ⟨z, show ((inhomogeneousChains X.X₃).dFrom i).hom z = 0 by
        simp_all [(inhomogeneousChains X.X₃).dFrom_eq hij]⟩) = groupHomologyπ X.X₁ j
      ((moduleCatCyclesIso _).inv ⟨x, by
        convert (map_chainsFunctor_shortExact hX).δ_apply_aux i j y x
          (by simpa [chainsMap_f_id_eq_mapRange] using hx) ((ComplexShape.down ℕ).next j)⟩) := by
  convert (map_chainsFunctor_shortExact hX).δ_apply i j hij z
    hz y hy x (by simpa [chainsMap_f_id_eq_mapRange] using hx) ((ComplexShape.down ℕ).next j) rfl
  <;> rw [moduleCatCyclesIso_inv_apply]
  <;> rfl

section Limits

open Limits

instance : PreservesFiniteLimits (chainsFunctor k G) := by
  have := ((chainsFunctor k G).exact_tfae.out 0 3).1 fun X h => map_chainsFunctor_shortExact h
  exact this.1

instance : PreservesFiniteColimits (chainsFunctor k G) := by
  have := ((chainsFunctor k G).exact_tfae.out 0 3).1 fun X h => map_chainsFunctor_shortExact h
  exact this.2

instance (n : ℕ) : PreservesFiniteLimits (cyclesFunctor k G n) :=
  comp_preservesFiniteLimits _ _

instance (n : ℕ) : PreservesFiniteColimits (opcyclesFunctor k G n) :=
  comp_preservesFiniteColimits _ _

instance : PreservesFiniteLimits (oneCyclesFunctor k G) :=
  preservesFiniteLimits_of_natIso (isoOneCyclesFunctor k G)

instance : PreservesFiniteColimits (oneOpcyclesFunctor k G) :=
  preservesFiniteColimits_of_natIso (isoOneOpcyclesFunctor k G)

instance : PreservesFiniteLimits (twoCyclesFunctor k G) :=
  preservesFiniteLimits_of_natIso (isoTwoCyclesFunctor k G)

instance : PreservesFiniteColimits (twoOpcyclesFunctor k G) :=
  preservesFiniteColimits_of_natIso (isoTwoOpcyclesFunctor k G)

variable (k G)

/-- The projection `A ⟶ A_G` as a natural transformation. -/
@[simps]
noncomputable def coinvariantsMkNatTrans : Action.forget _ _ ⟶ Rep.coinvariantsFunctor k G where
  app X := (shortComplexH0 X).g
  naturality := by intros; rfl

instance : Epi (coinvariantsMkNatTrans k G) := by
  convert NatTrans.epi_of_epi_app _
  exact fun X => inferInstanceAs <| Epi (shortComplexH0 X).g

/-- The inclusion `Z₁(G, A) ⟶ H₁(G, A)` as a natural transformation. -/
@[simps]
noncomputable def H1πNatTrans : oneCyclesFunctor k G ⟶ H1Functor k G where
  app X := H1π X

/-- The inclusion `Z₂(G, A) ⟶ H₂(G, A)` as a natural transformation. -/
@[simps]
noncomputable def H2πNatTrans : twoCyclesFunctor k G ⟶ H2Functor k G where
  app X := H2π X

/-- The differential `d₀ : C₁(G, A)/B₁(G, A) ⟶ A` as a natural transformation. -/
@[simps]
noncomputable def dZeroNatTrans : oneOpcyclesFunctor k G ⟶ Action.forget _ G where
  app X := (shortComplexH1 X).moduleCatRightHomologyData.descQ (ModuleCat.ofHom <| dZero X)
    (shortComplexH1 X).zero
  naturality X Y φ := by
    simpa [← cancel_epi (moduleCatRightHomologyData _).p]
      using (mapShortComplexH1 (MonoidHom.id G) φ).comm₂₃

/-- The differential `d₁ : C₂(G, A)/B₂(G, A) ⟶ Z₁(G, A)` as a natural transformation. -/
@[simps]
noncomputable def dOneNatTrans : twoOpcyclesFunctor k G ⟶ oneCyclesFunctor k G where
  app X := (shortComplexH2 X).moduleCatRightHomologyData.descQ
      (shortComplexH1 X).moduleCatLeftHomologyData.f'
      (by ext x; exact Subtype.ext congr($(dOne_comp_dTwo X) x))
  naturality _ _ φ := by
    simp [← cancel_mono (moduleCatLeftHomologyData _).i,
      ← cancel_epi (moduleCatRightHomologyData _).p]

/-- The inclusion `H₁(G, A) ⟶ C₁(G, A)/B₁(G, A)` as a natural transformation. -/
@[simps]
noncomputable def H1ιNatTrans : H1Functor k G ⟶ oneOpcyclesFunctor k G where
  app X := leftRightHomologyComparison' (moduleCatLeftHomologyData _)
    (moduleCatRightHomologyData _) ≫ (moduleCatRightHomologyData _).ι
  naturality _ _ _ := by rw [← cancel_epi (H1π _)]; rfl

/-- The inclusion `H₂(G, A) ⟶ C₂(G, A)/B₂(G, A)` as a natural transformation. -/
@[simps]
noncomputable def H2ιNatTrans : H2Functor k G ⟶ twoOpcyclesFunctor k G where
  app X := leftRightHomologyComparison' (moduleCatLeftHomologyData _)
    (moduleCatRightHomologyData _) ≫ (moduleCatRightHomologyData _).ι
  naturality _ _ _ := by rw [← cancel_epi (H2π _)]; rfl

variable {k G} (X)

omit hX in
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma dZeroNatTrans_comp_coinvariantsMkNatTrans :
    dZeroNatTrans k G ≫ coinvariantsMkNatTrans k G = 0 := by
  ext X : 2
  exact (cancel_epi (moduleCatRightHomologyData _).p).1 (shortComplexH0 X).zero

noncomputable def isColimitCoinvariantsMkNatTrans :
    IsColimit (CokernelCofork.ofπ (coinvariantsMkNatTrans k G)
      dZeroNatTrans_comp_coinvariantsMkNatTrans) :=
  evaluationJointlyReflectsColimits _ fun _ => (CokernelCofork.isColimitMapCoconeEquiv _ _).symm <|
    isCokernelOfComp (shortComplexH1 _).moduleCatRightHomologyData.p
      (shortComplexH1 _).g (shortComplexH0_exact _).gIsCokernel
      (by simpa [← cancel_epi (shortComplexH1 _).moduleCatRightHomologyData.p, -zero]
        using (shortComplexH0 _).zero)
      (shortComplexH1 _).moduleCatRightHomologyData.p_g'

omit hX in
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma H1ιNatTrans_comp_dZeroNatTrans :
    H1ιNatTrans k G ≫ dZeroNatTrans k G = 0 := by
  ext X : 2
  rw [← cancel_epi (H1π _)]
  ext
  exact oneCycles.dZero_apply _

noncomputable def isLimitH1ιNatTrans :
    IsLimit (KernelFork.ofι (H1ιNatTrans k G) H1ιNatTrans_comp_dZeroNatTrans) :=
  evaluationJointlyReflectsLimits _ fun A =>
    (KernelFork.isLimitMapConeEquiv _ _).symm <| IsKernel.isoKernel _ _
      (shortComplexH1 A).moduleCatRightHomologyData.hι
      (shortComplexH1 A).moduleCatHomologyData.iso <| by
        simp [← cancel_epi (shortComplexH1 A).moduleCatLeftHomologyData.π,
          ← moduleCatHomologyData_left, ← moduleCatHomologyData_right]

omit hX in
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma dOneNatTrans_comp_H1πNatTrans :
    dOneNatTrans k G ≫ H1πNatTrans k G = 0 := by
  ext : 2
  simp [← cancel_epi (moduleCatRightHomologyData _).p]

noncomputable def isColimitH2πNatTrans :
    IsColimit (CokernelCofork.ofπ (H1πNatTrans k G) dOneNatTrans_comp_H1πNatTrans) :=
  evaluationJointlyReflectsColimits _ fun A => (CokernelCofork.isColimitMapCoconeEquiv _ _).symm <|
    isCokernelOfComp (shortComplexH2 A).moduleCatRightHomologyData.p
      (shortComplexH1 A).moduleCatLeftHomologyData.f'
      (shortComplexH1 A).moduleCatLeftHomologyData.hπ (by
        simp [← cancel_epi (shortComplexH2 A).moduleCatRightHomologyData.p]) <| by
        simp [← cancel_mono (shortComplexH2 A).moduleCatLeftHomologyData.i]

omit hX in
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma H2ιNatTrans_comp_dOneNatTrans :
    H2ιNatTrans k G ≫ dOneNatTrans k G = 0 := by
  ext : 2
  rw [← cancel_epi (H2π _), ← cancel_mono (shortComplexH1 _).moduleCatLeftHomologyData.i]
  ext
  exact twoCycles.dOne_apply _

noncomputable def isLimitH2ιNatTrans :
    IsLimit (KernelFork.ofι (H2ιNatTrans k G) H2ιNatTrans_comp_dOneNatTrans) :=
  evaluationJointlyReflectsLimits _ fun A =>
    (KernelFork.isLimitMapConeEquiv _ _).symm <| IsKernel.isoKernel _ _
      (isKernelOfComp (shortComplexH1 A).moduleCatLeftHomologyData.i
      (shortComplexH2 A).moduleCatRightHomologyData.g'
      (shortComplexH2 A).moduleCatRightHomologyData.hι (by
        simpa [← cancel_mono (shortComplexH1 A).moduleCatLeftHomologyData.i, LeftHomologyData.f',
          -RightHomologyData.wι, HomologyData.descQ_liftK
          (shortComplexH2 A).moduleCatRightHomologyData
          (shortComplexH1 A).moduleCatLeftHomologyData (shortComplexH1 A).f
          (shortComplexH2 A).zero] using (shortComplexH2 A).moduleCatRightHomologyData.wι) <| by
        simp [← cancel_epi (shortComplexH2 A).moduleCatRightHomologyData.p,
          shortComplexH1, shortComplexH2])
      (shortComplexH2 A).moduleCatHomologyData.iso <| by
        simp [← cancel_epi (shortComplexH1 A).moduleCatLeftHomologyData.π,
          ← moduleCatHomologyData_left, ← moduleCatHomologyData_right]

end Limits

/-- Given a short exact sequence of representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`, this is the
snake input associated to the commutative diagram
```
      C₁(G, X₁)/B₁(G, X₁) ⟶ C₁(G, X₂)/B₁(G, X₂) ⟶ C₁(G, X₃)/C₁(G, X₃) ⟶ 0
              ↓                       ↓                      ↓
0      ⟶     X₁          ⟶          X₂         ⟶         X₃          ⟶ 0
```
with exact rows.
-/
noncomputable abbrev snakeInput₀ : SnakeInput (ModuleCat k) :=
  CategoryTheory.ShortComplex.natTransSnakeInput
    (oneOpcyclesFunctor k G) (Action.forget _ _) hX (X.mapNatTrans <| dZeroNatTrans k G)
    (by rw [← mapNatTrans_comp, H1ιNatTrans_comp_dZeroNatTrans, mapNatTrans_zero])
    (X.isLimit_ofι_mapNatTrans _ _ H1ιNatTrans_comp_dZeroNatTrans isLimitH1ιNatTrans)
    (by rw [← mapNatTrans_comp, dZeroNatTrans_comp_coinvariantsMkNatTrans, mapNatTrans_zero])
    (X.isColimit_ofπ_mapNatTrans _ _ dZeroNatTrans_comp_coinvariantsMkNatTrans
      isColimitCoinvariantsMkNatTrans)

set_option maxHeartbeats 0 in
/-- Given a short exact sequence of representations `X := 0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`, the snake
input associated to its short exact sequence of inhomogeneous chains, in degrees 0, 1, is
isomorphic to the specialized, simpler snake input induced by the short complex morphism
`d₀: C₁(G, X)/B₁(G, X) ⟶ X`. -/
noncomputable def isoSnakeInput₀ :
    snakeInput (map_chainsFunctor_shortExact hX) 1 0 rfl ≅ snakeInput₀ hX :=
  SnakeInput.isoMk (X.mapNatIso <| isoH1Functor k G)
    (X.mapNatIso <| isoOneOpcyclesFunctor k G) (X.mapNatIso <| zeroCyclesFunctorIso k G)
    (X.mapNatIso <| isoCoinvariantsFunctor k G)
    (by ext : 1 <;> simp [← cancel_epi (groupHomologyπ _ 1)])
    (by ext : 1 <;> simp [← cancel_epi (HomologicalComplex.pOpcycles _ _),
      ← cancel_mono (moduleCatLeftHomologyData (shortComplexH1 _)).i, isoZeroCycles])
    (by ext : 1 <;> simp)

/-- The degree 0 connecting homomorphism `H₁(G, X₃) ⟶ X₁_G` associated to an exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of representations. Uses a simpler expression for `H₀` and `H₁` than
general `δ`. -/
noncomputable def δ₀ : H1 X.X₃ ⟶ H0 X.X₁ := (snakeInput₀ hX).δ

set_option maxHeartbeats 0 in
theorem δ₀_apply (z : oneCycles X.X₃) (y : G →₀ X.X₂)
    (hy : mapRange.linearMap X.g.hom.hom y = z) (x : X.X₁) (hx : X.f.hom x = dZero X.X₂ y) :
    δ₀ hX (H1π _ z) = H0π X.X₁ x :=
  (snakeInput₀ hX).δ_apply (H1π _ z)
    ((shortComplexH1 X.X₂).moduleCatRightHomologyData.p y) x
    sorry -- should just be simp now
    hx

open Limits

theorem epi_δ₀_of_isZero (h0 : IsZero (H0 X.X₂)) :
    Epi (δ₀ hX) := SnakeInput.epi_δ _ h0

/-- Given a short exact sequence of representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`, this is the
snake input associated to the commutative diagram
```
    C₂(G, X₁)/B₂(G, X₁) ⟶ C₂(G, X₂)/B₂(G, X₂) ⟶ C₂(G, X₃)/B₂(G, X₃) ⟶ 0
              ↓                     ↓                      ↓
0 ⟶      Z₂(G, X₁)     ⟶      Z₂(G, X₂)      ⟶       Z₂(G, X₃)
```
with exact rows.
-/
noncomputable abbrev snakeInput₁ : SnakeInput (ModuleCat k) :=
  CategoryTheory.ShortComplex.natTransSnakeInput
    (twoOpcyclesFunctor k G) (oneCyclesFunctor k G) hX (X.mapNatTrans <| dOneNatTrans k G)
    (ι := X.mapNatTrans <| H2ιNatTrans k G)
    (by rw [← mapNatTrans_comp, H2ιNatTrans_comp_dOneNatTrans, mapNatTrans_zero])
    (X.isLimit_ofι_mapNatTrans _ _ H2ιNatTrans_comp_dOneNatTrans isLimitH2ιNatTrans)
    (π := X.mapNatTrans <| H1πNatTrans k G)
    (by rw [← mapNatTrans_comp, dOneNatTrans_comp_H1πNatTrans, mapNatTrans_zero])
    (X.isColimit_ofπ_mapNatTrans _ _ dOneNatTrans_comp_H1πNatTrans isColimitH2πNatTrans)

set_option maxHeartbeats 0 in
/-- Given a short exact sequence of representations `X := 0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`, the snake
input associated to its short exact sequence of inhomogeneous chains, in degrees 1, 2, is
isomorphic to the specialized, simpler snake input induced by the short complex morphism
`d₁: C₂(G, X)/B₂(G, X) ⟶ Z₁(G, X)`. -/
noncomputable def isoSnakeInput₁ :
    snakeInput (map_chainsFunctor_shortExact hX) 2 1 rfl ≅ snakeInput₁ hX :=
  SnakeInput.isoMk (X.mapNatIso <| isoH2Functor k G) (X.mapNatIso <| isoTwoOpcyclesFunctor k G)
    (X.mapNatIso <| isoOneCyclesFunctor k G) (X.mapNatIso <| isoH1Functor k G)
    (by ext : 1 <;> simp [← cancel_epi (groupHomologyπ _ 2)])
    (by ext : 1 <;> simp [← cancel_epi (HomologicalComplex.pOpcycles _ _),
      ← cancel_mono (moduleCatLeftHomologyData (shortComplexH2 _)).i, isoOneCycles])
    (by ext : 1 <;> simp)

/-- The degree 1 connecting homomorphism `H₂(G, X₃) ⟶ H₁(G, X₁)` associated to an exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of representations. Uses a simpler expression for `H₁` and `H₂` than
general `δ`. -/
noncomputable def δ₁ : H2 X.X₃ ⟶ H1 X.X₁ := (snakeInput₁ hX).δ

theorem δ₁_apply_aux (y : G × G →₀ X.X₂) (x : G →₀ X.X₁)
    (hx : mapRange.linearMap X.f.hom.hom x = dOne X.X₂ y) :
    dZero X.X₁ x = 0 := by
  have h1 := (map_chainsFunctor_shortExact hX).δ_apply_aux 2 1 ((twoChainsIso X.X₂).inv y)
    ((oneChainsIso X.X₁).inv x)
  have h2 := congr($((CommSq.horiz_inv ⟨(shortComplexH1Iso X.X₂).hom.comm₁₂⟩).w) y)
  have h3 := congr($((Iso.eq_inv_comp _).2 (shortComplexH1Iso X.X₁).hom.comm₂₃) x)
  have h4 := congr($((CommSq.vert_inv (h := (oneChainsIso X.X₂))
    ⟨(chainsMap_f_1_comp_oneChainsIso (MonoidHom.id G) X.f)⟩).w) x)
  simp_all [shortComplexH1, fOne, MonoidHom.coe_id, -eq_comp_dZero]

theorem δ₁_apply  (z : twoCycles X.X₃) (y : G × G →₀ X.X₂)
    (hy : mapRange.linearMap X.g.hom.hom y = z) (x : G →₀ X.X₁)
    (hx : mapRange.linearMap X.f.hom.hom x = dOne X.X₂ y) :
    δ₁ hX (H2π X.X₃ z) = H1π X.X₁ ⟨x, δ₁_apply_aux hX y x hx⟩ :=
  (snakeInput₁ hX).δ_apply (H2π _ z)
    ((shortComplexH2 X.X₂).moduleCatRightHomologyData.p y) ⟨x, δ₁_apply_aux hX y x hx⟩
    sorry -- should just be simp now
    sorry

theorem epi_δ₁_of_isZero (h1 : IsZero (H1 X.X₂)) :
    Epi (δ₁ hX) := SnakeInput.epi_δ _ h1

variable (X) in
/-- The short complex `X₁_G ⟶ X₂_G ⟶ X₃_G` associated to a short complex of representations
`X₁ ⟶ X₂ ⟶ X₃`. -/
noncomputable abbrev H0ShortComplex₂ :=
  X.map (Rep.coinvariantsFunctor k G)

variable (X) in
/-- When `i = 0`, the general short complex `Hᵢ(G, X₁) ⟶ Hᵢ(G, X₂) ⟶ Hᵢ(G, X₃)` associated to a
short complex of representations agrees with our simpler expression of `X₁_G ⟶ X₂_G ⟶ X₃_G.` -/
noncomputable def isoH0ShortComplex₂ :
    mapShortComplex₂ X 0 ≅ H0ShortComplex₂ X :=
  X.mapNatIso (isoCoinvariantsFunctor k G)

theorem H0ShortComplex₂_exact :
    (H0ShortComplex₂ X).Exact := (snakeInput₀ hX).L₃_exact

/-- The short complex `H₁(G, X₃) ⟶ X₁_G ⟶ X₂_G` associated to an exact sequence of
representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`. -/
noncomputable abbrev H0ShortComplex₁ := (snakeInput₀ hX).L₂'

/-- When `i = 0`, the general short complex `Hᵢ₊₁(G, X₃) ⟶ Hᵢ(G, X₁) ⟶ Hᵢ(G, X₂)` associated to a
short exact sequence of representations agrees with our simpler expression for
`H₁(G, X₃) ⟶ X₁_G ⟶ X₂_G.` -/
noncomputable def isoH0ShortComplex₁ :
    mapShortComplex₁ hX (i := 1) rfl ≅ H0ShortComplex₁ hX :=
  SnakeInput.functorL₂'.mapIso (isoSnakeInput₀ hX)

theorem H0ShortComplex₁_exact :
    (H0ShortComplex₁ hX).Exact :=
  (snakeInput₀ hX).L₂'_exact

/-- The short complex  `H₁(G, X₂) ⟶ H₁(G, X₃) ⟶ X₁_G` associated to an exact sequence of
representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`. -/
noncomputable abbrev H1ShortComplex₃ := (snakeInput₀ hX).L₁'

/-- When `i = 0`, the general short complex `Hᵢ₊₁(G, X₂) ⟶ Hᵢ₊₁(G, X₃) ⟶ Hᵢ(G, X₁)` associated to
a short exact sequence of representations agrees with our simpler expression for
`H₁(G, X₂) ⟶ H₁(G, X₃) ⟶ X₁_G.` -/
noncomputable def isoH1ShortComplex₃ :
    mapShortComplex₃ hX (j := 0) rfl ≅ H1ShortComplex₃ hX :=
  SnakeInput.functorL₁'.mapIso (isoSnakeInput₀ hX)

theorem H1ShortComplex₃_exact :
    (H1ShortComplex₃ hX).Exact :=
  (snakeInput₀ hX).L₁'_exact

variable (X) in
/-- The short complex `H₁(G, X₁) ⟶ H₁(G, X₂) ⟶ H₁(G, X₃)` associated to a short complex of
representations `X₁ ⟶ X₂ ⟶ X₃`. -/
noncomputable abbrev H1ShortComplex₂ := X.map (H1Functor k G)

variable (X) in
/-- When `i = 1`, the general short complex `Hᵢ(G, X₁) ⟶ Hᵢ(G, X₂) ⟶ Hᵢ(G, X₃)` associated to
a short complex of representations agrees with our simpler expression for
`H₁(G, X₁) ⟶ H₁(G, X₂) ⟶ H₁(G, X₃).` -/
noncomputable def isoH1ShortComplex₂ :
    mapShortComplex₂ X 1 ≅ H1ShortComplex₂ X := X.mapNatIso (isoH1Functor k G)

theorem H1ShortComplex₂_exact :
    (H1ShortComplex₂ X).Exact := (snakeInput₁ hX).L₃_exact

/-- The short complex `H₂(G, X₃) ⟶ H₁(G, X₁) ⟶ H₁(G, X₂)` associated to an exact sequence of
representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`. -/
noncomputable abbrev H1ShortComplex₁ := (snakeInput₁ hX).L₂'

/-- When `i = 1`, the general short complex `Hᵢ₊₁(G, X₃) ⟶ Hᵢ(G, X₁) ⟶ Hᵢ(G, X₂)` associated to a
short exact sequence of representations agrees with our simpler expression for
`H₂(G, X₃) ⟶ H₁(G, X₁) ⟶ H₁(G, X₂).` -/
noncomputable def isoH1ShortComplex₁ :
    mapShortComplex₁ hX (i := 2) rfl ≅ H1ShortComplex₁ hX :=
  SnakeInput.functorL₂'.mapIso (isoSnakeInput₁ hX)

theorem H1ShortComplex₁_exact :
    (H1ShortComplex₁ hX).Exact :=
  (snakeInput₁ hX).L₂'_exact

/-- The short complex  `H₂(G, X₂) ⟶ H₂(G, X₃) ⟶ H₁(G, X₁)` associated to an exact sequence of
representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`. -/
noncomputable abbrev H2ShortComplex₃ := (snakeInput₁ hX).L₁'

/-- When `i = 1`, the general short complex `Hᵢ₊₁(G, X₂) ⟶ Hᵢ₊₁(G, X₃) ⟶ Hᵢ(G, X₁)` associated to
a short exact sequence of representations agrees with our simpler expression for
`H₂(G, X₂) ⟶ H₂(G, X₃) ⟶ H₁(G, X₁).` -/
noncomputable def isoH2ShortComplex₃ :
    mapShortComplex₃ hX (j := 1) rfl ≅ H2ShortComplex₃ hX :=
  SnakeInput.functorL₁'.mapIso (isoSnakeInput₁ hX)

theorem H2ShortComplex₃_exact :
    (H2ShortComplex₃ hX).Exact := (snakeInput₁ hX).L₁'_exact

end groupHomology
