/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Long exact sequence in group cohomology

Given a commutative ring `k` and a group `G`, this file shows that a short exact sequence of
`k`-linear `G`-representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` induces a short exact sequence of
complexes of inhomogeneous cochains `0 ⟶ C(X₁) ⟶ C(X₂) ⟶ C(X₃) ⟶ 0`, where `Hⁿ(C(Xᵢ))`
is the `n`th group cohomology of `Xᵢ`.

This allows us to specialize API about long exact sequences to group cohomology.

## Main definitions

* `groupCohomology.δ hX i j hij`: the connecting homomorphism `Hⁱ(G, X₃) ⟶ Hʲ(G, X₁)` associated
  to an exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of representations.

-/

universe u

namespace groupCohomology

open CategoryTheory ShortComplex

variable {k G : Type u} [CommRing k] [Group G] {X : ShortComplex (Rep k G)} (hX : ShortExact X)

include hX

lemma map_cochainsFunctor_shortExact :
    ShortExact (X.map (cochainsFunctor k G)) :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => {
    exact := by
      have : LinearMap.range X.f.hom.hom = LinearMap.ker X.g.hom.hom :=
        (hX.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
      simp [moduleCat_exact_iff_range_eq_ker, LinearMap.range_compLeft,
        LinearMap.ker_compLeft, this]
    mono_f := letI := hX.2; cochainsMap_id_f_map_mono X.f i
    epi_g := letI := hX.3; cochainsMap_id_f_map_epi X.g i }

open HomologicalComplex.HomologySequence

/-- The short complex `Hⁱ(G, X₃) ⟶ Hʲ(G, X₁) ⟶ Hʲ(G, X₂)` associated to an exact
sequence of representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`. -/
noncomputable abbrev mapShortComplex₁ {i j : ℕ} (hij : i + 1 = j) :=
  (snakeInput (map_cochainsFunctor_shortExact hX) _ _ hij).L₂'

variable (X) in
/-- The short complex `Hⁱ(G, X₁) ⟶ Hⁱ(G, X₂) ⟶ Hⁱ(G, X₃)` associated to a short complex of
representations `X₁ ⟶ X₂ ⟶ X₃`. -/
noncomputable abbrev mapShortComplex₂ (i : ℕ) := X.map (functor k G i)

/-- The short complex `Hⁱ(G, X₂) ⟶ Hⁱ(G, X₃) ⟶ Hʲ(G, X₁)`. -/
noncomputable abbrev mapShortComplex₃ {i j : ℕ} (hij : i + 1 = j) :=
  (snakeInput (map_cochainsFunctor_shortExact hX) _ _ hij).L₁'

/-- Exactness of `Hⁱ(G, X₃) ⟶ Hʲ(G, X₁) ⟶ Hʲ(G, X₂)`. -/
lemma mapShortComplex₁_exact {i j : ℕ} (hij : i + 1 = j) :
    (mapShortComplex₁ hX hij).Exact :=
  (map_cochainsFunctor_shortExact hX).homology_exact₁ i j hij

/-- Exactness of `Hⁱ(G, X₁) ⟶ Hⁱ(G, X₂) ⟶ Hⁱ(G, X₃)`. -/
lemma mapShortComplex₂_exact (i : ℕ) :
    (mapShortComplex₂ X i).Exact :=
  (map_cochainsFunctor_shortExact hX).homology_exact₂ i

/-- Exactness of `Hⁱ(G, X₂) ⟶ Hⁱ(G, X₃) ⟶ Hʲ(G, X₁)`. -/
lemma mapShortComplex₃_exact {i j : ℕ} (hij : i + 1 = j) :
    (mapShortComplex₃ hX hij).Exact :=
  (map_cochainsFunctor_shortExact hX).homology_exact₃ i j hij

/-- The connecting homomorphism `Hⁱ(G, X₃) ⟶ Hʲ(G, X₁)` associated to an exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of representations. -/
noncomputable abbrev δ (i j : ℕ) (hij : i + 1 = j) :
    groupCohomology X.X₃ i ⟶ groupCohomology X.X₁ j :=
  (map_cochainsFunctor_shortExact hX).δ i j hij

theorem δ_apply (i j : ℕ) (hij : i + 1 = j)
    (z : (Fin i → G) → X.X₃) (hz : (inhomogeneousCochains X.X₃).d i j z = 0)
    (y : (Fin i → G) → X.X₂) (hy : (cochainsMap (MonoidHom.id G) X.g).f i y = z)
    (x : (Fin j → G) → X.X₁) (hx : X.f.hom ∘ x = (inhomogeneousCochains X.X₂).d i j y) :
    δ hX i j hij (groupCohomologyπ X.X₃ i <| (moduleCatCyclesIso _).inv
      ⟨z, show ((inhomogeneousCochains X.X₃).dFrom i).hom z = 0 by
        simp_all [(inhomogeneousCochains X.X₃).dFrom_eq hij]⟩) = groupCohomologyπ X.X₁ j
      ((moduleCatCyclesIso _).inv ⟨x, by
        convert (map_cochainsFunctor_shortExact hX).δ_apply_aux i j y x
          (by simpa [cochainsMap_id_f_eq_compLeft] using hx) <| (ComplexShape.up ℕ).next j⟩) := by
  convert (map_cochainsFunctor_shortExact hX).δ_apply i j hij z
    hz y hy x (by simpa [cochainsMap_id_f_eq_compLeft] using hx) ((ComplexShape.up ℕ).next j) rfl
  <;> rw [moduleCatCyclesIso_inv_apply]
  <;> rfl

section Limits

open Limits

instance : PreservesFiniteLimits (cochainsFunctor k G) := by
  have := ((cochainsFunctor k G).exact_tfae.out 0 3).1 fun X h => map_cochainsFunctor_shortExact h
  exact this.1

instance : PreservesFiniteColimits (cochainsFunctor k G) := by
  have := ((cochainsFunctor k G).exact_tfae.out 0 3).1 fun X h => map_cochainsFunctor_shortExact h
  exact this.2

instance (n : ℕ) : PreservesFiniteLimits (cocyclesFunctor k G n) :=
  comp_preservesFiniteLimits _ _

instance (n : ℕ) : PreservesFiniteColimits (opcocyclesFunctor k G n) :=
  comp_preservesFiniteColimits _ _

instance : PreservesFiniteLimits (oneCocyclesFunctor k G) :=
  preservesFiniteLimits_of_natIso (isoOneCocyclesFunctor k G)

instance : PreservesFiniteColimits (oneOpcocyclesFunctor k G) :=
  preservesFiniteColimits_of_natIso (isoOneOpcocyclesFunctor k G)

instance : PreservesFiniteLimits (twoCocyclesFunctor k G) :=
  preservesFiniteLimits_of_natIso (isoTwoCocyclesFunctor k G)

instance : PreservesFiniteColimits (twoOpcocyclesFunctor k G) :=
  preservesFiniteColimits_of_natIso (isoTwoOpcocyclesFunctor k G)

variable (k G)

/-- The inclusion `Aᴳ ⟶ A` as a natural transformation. -/
@[simps]
noncomputable def invariantsSubtypeNatTrans : Rep.invariantsFunctor k G ⟶ Action.forget _ _ where
  app X := (shortComplexH0 X).f
  naturality := by intros; rfl

instance : Mono (invariantsSubtypeNatTrans k G) := by
  convert NatTrans.mono_of_mono_app _
  exact fun X => inferInstanceAs <| Mono (shortComplexH0 X).f

/-- The inclusion `Z¹(G, A) ⟶ H¹(G, A)` as natural transformation. -/
@[simps]
noncomputable def H1πNatTrans : oneCocyclesFunctor k G ⟶ H1Functor k G where
  app X := H1π X

/-- The inclusion `Z²(G, A) ⟶ H²(G, A)` as natural transformation. -/
@[simps]
noncomputable def H2πNatTrans : twoCocyclesFunctor k G ⟶ H2Functor k G where
  app X := H2π X

/-- The differential `d⁰ : A ⟶ Z¹(G, A)` as a natural transformation. -/
@[simps]
noncomputable def dZeroNatTrans : Action.forget _ _ ⟶ oneCocyclesFunctor k G where
  app X := (shortComplexH1 X).moduleCatLeftHomologyData.f'
  naturality X Y f := by
    simp only [← cancel_mono (moduleCatLeftHomologyData (shortComplexH1 Y)).i,
      Category.assoc, LeftHomologyData.f'_i, oneCocyclesFunctor_map,
      f'_cyclesMap', Action.forget_obj, Action.forget_map, mapShortComplexH1_τ₁]

/-- The differential `d¹ : C¹(G, A)/B¹(G, A) ⟶ Z²(G, A)` as a natural transformation. -/
@[simps]
noncomputable def dOneNatTrans : oneOpcocyclesFunctor k G ⟶ twoCocyclesFunctor k G where
  app X := (shortComplexH1 X).moduleCatRightHomologyData.descQ
    (shortComplexH2 X).moduleCatLeftHomologyData.f' <| by
      simpa [← cancel_mono (moduleCatLeftHomologyData (shortComplexH2 X)).i, -ShortComplex.zero]
        using (shortComplexH1 X).zero
  naturality _ _ _ := by
    simpa [← cancel_mono (moduleCatLeftHomologyData (shortComplexH2 _)).i,
      ← cancel_epi (moduleCatRightHomologyData _).p]
      using (mapShortComplexH1 (MonoidHom.id G) _).comm₂₃

/-- The inclusion `H¹(G, A) ⟶ C¹(G, A)/B¹(G, A)` as a natural transformation. -/
@[simps]
noncomputable def H1ιNatTrans : H1Functor k G ⟶ oneOpcocyclesFunctor k G where
  app X := leftRightHomologyComparison' (moduleCatLeftHomologyData _)
    (moduleCatRightHomologyData _) ≫ (moduleCatRightHomologyData _).ι
  naturality _ _ _ := by rw [← cancel_epi (H1π _)]; rfl

variable {k G} (X)

omit hX in
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma dZeroNatTrans_comp_H1πNatTrans :
    dZeroNatTrans k G ≫ H1πNatTrans k G = 0 := by
  ext X : 4
  exact (Submodule.Quotient.mk_eq_zero _).2 <| Set.mem_range_self _

noncomputable def isColimitH1πNatTrans :
    IsColimit (CokernelCofork.ofπ (H1πNatTrans k G) dZeroNatTrans_comp_H1πNatTrans) :=
  evaluationJointlyReflectsColimits _ fun _ => (CokernelCofork.isColimitMapCoconeEquiv _ _).symm <|
    ModuleCat.cokernelIsColimit _

omit hX in
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma invariantsSubtype_comp_dZero :
    invariantsSubtypeNatTrans k G ≫ dZeroNatTrans k G = 0 := by
  ext X : 2
  exact (cancel_mono (shortComplexH1 _).moduleCatLeftHomologyData.i).1 <|
    ModuleCat.hom_ext <| dZero_comp_subtype _

noncomputable def isLimitInvariantsSubtypeNatTrans :
    IsLimit (KernelFork.ofι (invariantsSubtypeNatTrans k G) invariantsSubtype_comp_dZero) :=
  evaluationJointlyReflectsLimits _ fun _ => (KernelFork.isLimitMapConeEquiv _ _).symm <|
    isKernelOfComp (shortComplexH1 _).moduleCatLeftHomologyData.i
      (shortComplexH1 _).f (shortComplexH0_exact _).fIsKernel
      (by simpa [← cancel_mono (shortComplexH1 _).moduleCatLeftHomologyData.i, -zero]
        using (shortComplexH0 _).zero)
      (shortComplexH1 _).moduleCatLeftHomologyData.f'_i

omit hX in
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma dOneNatTrans_comp_H2πNatTrans :
    dOneNatTrans k G ≫ H2πNatTrans k G = 0 := by
  ext : 2
  simp [← cancel_epi (moduleCatRightHomologyData (shortComplexH1 _)).p]

noncomputable def isColimitH2πNatTrans :
    IsColimit (CokernelCofork.ofπ (H2πNatTrans k G) dOneNatTrans_comp_H2πNatTrans) :=
  evaluationJointlyReflectsColimits _ fun A => (CokernelCofork.isColimitMapCoconeEquiv _ _).symm <|
    isCokernelOfComp (shortComplexH1 A).moduleCatRightHomologyData.p
      (shortComplexH2 A).moduleCatLeftHomologyData.f'
      (shortComplexH2 A).moduleCatLeftHomologyData.hπ (by
        simp [← cancel_epi (shortComplexH1 A).moduleCatRightHomologyData.p]) <| by
        simp [← cancel_mono (shortComplexH2 A).moduleCatLeftHomologyData.i]

omit hX in
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma H1ιNatTrans_comp_dOneNatTrans :
    H1ιNatTrans k G ≫ dOneNatTrans k G = 0 := by
  ext : 2
  rw [← cancel_epi (H1π _), ← cancel_mono (shortComplexH2 _).moduleCatLeftHomologyData.i]
  ext
  exact oneCocycles.dOne_apply _

noncomputable def isLimitH1ιNatTrans :
    IsLimit (KernelFork.ofι (H1ιNatTrans k G) H1ιNatTrans_comp_dOneNatTrans) :=
  evaluationJointlyReflectsLimits _ fun A =>
    (KernelFork.isLimitMapConeEquiv _ _).symm <| IsKernel.isoKernel _ _
      (isKernelOfComp (shortComplexH2 A).moduleCatLeftHomologyData.i
      (shortComplexH1 A).moduleCatRightHomologyData.g'
      (shortComplexH1 A).moduleCatRightHomologyData.hι (by
        simpa [← cancel_mono (shortComplexH2 A).moduleCatLeftHomologyData.i, LeftHomologyData.f',
          HomologyData.descQ_liftK (shortComplexH1 A).moduleCatRightHomologyData _
          (shortComplexH2 A).f (shortComplexH1 A).zero, -RightHomologyData.wι]
          using (shortComplexH1 A).moduleCatRightHomologyData.wι) <| by
        simp [← cancel_epi (shortComplexH1 A).moduleCatRightHomologyData.p,
          shortComplexH2, shortComplexH1])
      (shortComplexH1 A).moduleCatHomologyData.iso <| by
        simp [← cancel_epi (shortComplexH1 A).moduleCatLeftHomologyData.π,
          ← moduleCatHomologyData_left, ← moduleCatHomologyData_right]
suppress_compilation

omit hX in
lemma ker_shortComplexH1_f'_hom_eq_invariants (A : Rep k G) :
    LinearMap.ker (shortComplexH1 A).moduleCatLeftHomologyData.f'.hom = A.ρ.invariants := by
  show LinearMap.ker (LinearMap.codRestrict _ _ _) = _
  rw [LinearMap.ker_codRestrict]
  exact dZero_ker_eq_invariants _

end Limits

/-- Given a short exact sequence of representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`, this is the
snake input associated to the commutative diagram
```
        X₁     ⟶     X₂    ⟶    X₃ ⟶ 0
        ↓             ↓            ↓
0 ⟶ Z¹(G, X₁) ⟶ Z¹(G, X₂) ⟶ Z¹(G, X₃)
```
with exact rows.
-/
noncomputable abbrev snakeInput₀ : SnakeInput (ModuleCat k) :=
  CategoryTheory.ShortComplex.natTransSnakeInput
    (Action.forget _ _) (oneCocyclesFunctor k G) hX (X.mapNatTrans <| dZeroNatTrans k G)
    (by rw [← mapNatTrans_comp, invariantsSubtype_comp_dZero, mapNatTrans_zero])
    (X.isLimit_ofι_mapNatTrans _ _ invariantsSubtype_comp_dZero isLimitInvariantsSubtypeNatTrans)
    (by rw [← mapNatTrans_comp, dZeroNatTrans_comp_H1πNatTrans, mapNatTrans_zero])
    (X.isColimit_ofπ_mapNatTrans _ _ dZeroNatTrans_comp_H1πNatTrans isColimitH1πNatTrans)

set_option maxHeartbeats 0 in
/-- Given a short exact sequence of representations `X := 0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`, the snake
input associated to its short exact sequence of inhomogeneous cochains, in degrees 0, 1, is
isomorphic to the specialized, simpler snake input induced by the short complex morphism
`d⁰: X ⟶ Z¹(G, X)`. -/
noncomputable def isoSnakeInput₀ :
    snakeInput (map_cochainsFunctor_shortExact hX) 0 1 rfl ≅ snakeInput₀ hX :=
  SnakeInput.isoMk (X.mapNatIso <| isoInvariantsFunctor k G)
    (X.mapNatIso <| zeroOpcocyclesFunctorIso k G) (X.mapNatIso <| isoOneCocyclesFunctor k G)
    (X.mapNatIso <| isoH1Functor k G)
    (by ext : 1 <;> simp [← cancel_epi (groupCohomologyπ _ 0), shortComplexH0])
    (by ext : 1 <;> simp [← cancel_epi (HomologicalComplex.pOpcycles _ _),
      ← cancel_mono (moduleCatLeftHomologyData (shortComplexH1 _)).i, zeroOpcocyclesIso])
    (by ext : 1 <;> simp)

/-- The degree 0 connecting homomorphism `X₃ᴳ ⟶ H¹(G, X₁)` associated to an exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of representations. Uses a simpler expression for `H⁰` and `H¹` than
general `δ`. -/
noncomputable def δ₀ : H0 X.X₃ ⟶ H1 X.X₁ := (snakeInput₀ hX).δ

theorem δ₀_apply_aux (y : X.X₂) (x : G → X.X₁) (hx : X.f.hom ∘ x = dZero X.X₂ y) :
    dOne X.X₁ x = 0 := by
  apply Function.Injective.comp_left ((Rep.mono_iff_injective X.f).1 hX.2)
  have := congr($((mapShortComplexH1 (MonoidHom.id G) X.f).comm₂₃.symm) x)
  have := congr($(dOne_comp_dZero X.X₂) y)
  simp_all [shortComplexH1, LinearMap.compLeft]

theorem δ₀_apply (z : X.X₃) (hz : z ∈ X.X₃.ρ.invariants) (y : X.X₂) (hy : X.g.hom y = z)
    (x : G → X.X₁) (hx : X.f.hom ∘ x = dZero X.X₂ y) :
    δ₀ hX ⟨z, hz⟩ = H1π X.X₁ ⟨x, δ₀_apply_aux hX y x hx⟩ :=
  (snakeInput₀ hX).δ_apply ⟨z, hz⟩ y ⟨x, δ₀_apply_aux hX y x hx⟩ (by exact hy) (Subtype.ext hx)

open Limits

theorem epi_δ₀_of_isZero (h1 : IsZero (H1 X.X₂)) :
    Epi (δ₀ hX) := SnakeInput.epi_δ _ h1

/-- Given a short exact sequence of representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`, this is the
snake input associated to the commutative diagram
```
    C¹(G, X₁)/B¹(G, X₁) ⟶ C¹(G, X₂)/B¹(G, X₂) ⟶ C¹(G, X₃)/B¹(G, X₃) ⟶ 0
              ↓                     ↓                      ↓
0 ⟶      Z²(G, X₁)     ⟶      Z²(G, X₂)      ⟶       Z²(G, X₃)
```
with exact rows.
-/
noncomputable abbrev snakeInput₁ : SnakeInput (ModuleCat k) :=
  CategoryTheory.ShortComplex.natTransSnakeInput
    (oneOpcocyclesFunctor k G) (twoCocyclesFunctor k G) hX (X.mapNatTrans <| dOneNatTrans k G)
    (ι := X.mapNatTrans <| H1ιNatTrans k G)
    (by rw [← mapNatTrans_comp, H1ιNatTrans_comp_dOneNatTrans, mapNatTrans_zero])
    (X.isLimit_ofι_mapNatTrans _ _ H1ιNatTrans_comp_dOneNatTrans isLimitH1ιNatTrans)
    (π := X.mapNatTrans <| H2πNatTrans k G)
    (by rw [← mapNatTrans_comp, dOneNatTrans_comp_H2πNatTrans, mapNatTrans_zero])
    (X.isColimit_ofπ_mapNatTrans _ _ dOneNatTrans_comp_H2πNatTrans isColimitH2πNatTrans)

set_option maxHeartbeats 0 in
/-- Given a short exact sequence of representations `X := 0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`, the snake
input associated to its short exact sequence of inhomogeneous cochains, in degrees 1, 2, is
isomorphic to the specialized, simpler snake input induced by the short complex morphism
`d¹: C¹(G, X)/B¹(G, X) ⟶ Z²(G, X)`. -/
noncomputable def isoSnakeInput₁ :
    snakeInput (map_cochainsFunctor_shortExact hX) 1 2 rfl ≅ snakeInput₁ hX :=
  SnakeInput.isoMk (X.mapNatIso <| isoH1Functor k G) (X.mapNatIso <| isoOneOpcocyclesFunctor k G)
    (X.mapNatIso <| isoTwoCocyclesFunctor k G) (X.mapNatIso <| isoH2Functor k G)
    (by ext : 1 <;> simp [← cancel_epi (groupCohomologyπ _ 1)])
    (by ext : 1 <;> simp [← cancel_epi (HomologicalComplex.pOpcycles _ _),
      ← cancel_mono (moduleCatLeftHomologyData (shortComplexH2 _)).i, isoTwoCocycles])
    (by ext : 1 <;> simp)

/-- The degree 1 connecting homomorphism `H¹(G, X₃) ⟶ H²(G, X₁)` associated to an exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of representations. Uses a simpler expression for `H¹` and `H²` than
general `δ`. -/
noncomputable def δ₁ : H1 X.X₃ ⟶ H2 X.X₁ := (snakeInput₁ hX).δ

theorem δ₁_apply_aux (y : G → X.X₂) (x : G × G → X.X₁) (hx : X.f.hom ∘ x = dOne X.X₂ y) :
    dTwo X.X₁ x = 0 := by
  apply Function.Injective.comp_left ((Rep.mono_iff_injective X.f).1 hX.2)
  have := congr($((mapShortComplexH2 (MonoidHom.id G) X.f).comm₂₃.symm) x)
  have := congr($(dTwo_comp_dOne X.X₂) y)
  simp_all [shortComplexH2, LinearMap.compLeft]

theorem δ₁_apply (z : oneCocycles X.X₃) (y : G → X.X₂) (hy : X.g.hom ∘ y = z)
    (x : G × G → X.X₁) (hx : X.f.hom ∘ x = dOne X.X₂ y) :
    δ₁ hX (H1π X.X₃ z) = H2π X.X₁ ⟨x, δ₁_apply_aux hX y x hx⟩ :=
  (snakeInput₁ hX).δ_apply (H1π _ z) (Submodule.mkQ _ y) ⟨x, δ₁_apply_aux hX y x hx⟩
    congr(Submodule.Quotient.mk $hy) (Subtype.ext hx)

theorem epi_δ₁_of_isZero (h2 : IsZero (H2 X.X₂)) :
    Epi (δ₁ hX) := SnakeInput.epi_δ _ h2

variable (X) in
/-- The short complex `X₁ᴳ ⟶ X₂ᴳ ⟶ X₃ᴳ` associated to a short complex of representations. -/
noncomputable abbrev H0ShortComplex₂ := X.map (Rep.invariantsFunctor k G)

variable (X) in
/-- When `i = 0`, the general short complex `Hⁱ(G, X₁) ⟶ Hⁱ(G, X₂) ⟶ Hⁱ(G, X₃)` associated to a
short complex of representations agrees with our simpler expression of `X₁ᴳ ⟶ X₂ᴳ ⟶ X₃ᴳ.` -/
noncomputable def isoH0ShortComplex₂ :
    mapShortComplex₂ X 0 ≅ H0ShortComplex₂ X := X.mapNatIso (isoInvariantsFunctor k G)

theorem H0ShortComplex₂_exact : (H0ShortComplex₂ X).Exact := (snakeInput₀ hX).L₀_exact

/-- The short complex `X₂ᴳ ⟶ X₃ᴳ ⟶ H¹(G, X₁)` associated to a short exact sequence of
representations. -/
noncomputable abbrev H0ShortComplex₃ (H : ShortExact X) := (snakeInput₀ H).L₁'

/-- When `i = 0`, the general short complex `Hⁱ(G, X₂) ⟶ Hⁱ(G, X₃) ⟶ Hⁱ⁺¹(G, X₁)` associated to a
short exact sequence of representations agrees with our simpler expression for
`X₂ᴳ ⟶ X₃ᴳ ⟶ H¹(G, X₁).` -/
noncomputable def isoH0ShortComplex₃ (H : ShortExact X) :
    mapShortComplex₃ H (j := 1) rfl ≅ H0ShortComplex₃ H :=
  SnakeInput.functorL₁'.mapIso (isoSnakeInput₀ H)

theorem H0ShortComplex₃_exact :
    (H0ShortComplex₃ hX).Exact := (snakeInput₀ hX).L₁'_exact

/-- The short complex  `X₃ᴳ ⟶ H¹(G, X₁) ⟶ H¹(G, X₂)` associated to a short exact sequence of
representations. -/
noncomputable abbrev H1ShortComplex₁ := (snakeInput₀ hX).L₂'

/-- When `i = 0`, the general short complex `Hⁱ(G, X₃) ⟶ Hⁱ⁺¹(G, X₁) ⟶ Hⁱ⁺¹(G, X₂)` associated to
a short exact sequence of representations agrees with our simpler expression for
`X₃ᴳ ⟶ H¹(G, X₁) ⟶ H¹(G, X₂).` -/
noncomputable def isoH1ShortComplex₁ :
    mapShortComplex₁ hX (i := 0) rfl ≅ H1ShortComplex₁ hX :=
  SnakeInput.functorL₂'.mapIso (isoSnakeInput₀ hX)

theorem H1ShortComplex₁_exact :
    (H1ShortComplex₁ hX).Exact := (snakeInput₀ hX).L₂'_exact

variable (X) in
/-- The short complex  `H¹(G, X₁) ⟶ H¹(G, X₂) ⟶ H¹(G, X₃)` associated to a short complex of
representations. -/
noncomputable abbrev H1ShortComplex₂ := X.map (H1Functor k G)

variable (X) in
/-- When `i = 1`, the general short complex `Hⁱ(G, X₁) ⟶ Hⁱ(G, X₂) ⟶ Hⁱ(G, X₃)` associated to
a short complex of representations agrees with our simpler expression for
`H¹(G, X₁) ⟶ H¹(G, X₂) ⟶ H¹(G, X₃).` -/
noncomputable def isoH1ShortComplex₂ :
    mapShortComplex₂ X 1 ≅ H1ShortComplex₂ X := X.mapNatIso (isoH1Functor k G)

theorem H1ShortComplex₂_exact :
    (H1ShortComplex₂ X).Exact := (snakeInput₁ hX).L₀_exact

/-- The short complex  `H¹(G, X₂) ⟶ H¹(G, X₃) ⟶ H²(G, X₁)` associated to a short exact sequence of
representations. -/
noncomputable abbrev H1ShortComplex₃ := (snakeInput₁ hX).L₁'

/-- When `i = 1`, the general short complex `Hⁱ(G, X₂) ⟶ Hⁱ(G, X₃) ⟶ Hⁱ⁺¹(G, X₁)` associated to
a short exact sequence of representations agrees with our simpler expression for
`H¹(G, X₂) ⟶ H¹(G, X₃) ⟶ H²(G, X₁).` -/
noncomputable def isoH1ShortComplex₃ :
    mapShortComplex₃ hX (i := 1) rfl ≅ H1ShortComplex₃ hX :=
  SnakeInput.functorL₁'.mapIso (isoSnakeInput₁ hX)

theorem H1ShortComplex₃_exact :
    (H1ShortComplex₃ hX).Exact := (snakeInput₁ hX).L₁'_exact

/-- The short complex  `H¹(G, X₃) ⟶ H²(G, X₁) ⟶ H²(G, X₂)` associated to a short exact
sequence of representations. -/
noncomputable abbrev H2ShortComplex₁ := (snakeInput₁ hX).L₂'

/-- When `i = 1`, the general short complex `Hⁱ(G, X₃) ⟶ Hⁱ⁺¹(G, X₁) ⟶ Hⁱ⁺¹(G, X₂)` associated to
a short exact sequence of representations agrees with our simpler expression for
`H¹(G, X₃) ⟶ H²(G, X₁) ⟶ H²(G, X₂).` -/
noncomputable def isoH2ShortComplex₁ :
    mapShortComplex₁ hX (i := 1) rfl ≅ H2ShortComplex₁ hX :=
  SnakeInput.functorL₂'.mapIso (isoSnakeInput₁ hX)

theorem H2ShortComplex₁_exact :
    (H2ShortComplex₁ hX).Exact := (snakeInput₁ hX).L₂'_exact

end groupCohomology
