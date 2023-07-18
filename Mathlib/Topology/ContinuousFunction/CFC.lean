/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Analysis.NormedSpace.Star.Spectrum
import Mathlib.Topology.ContinuousFunction.Polynomial
import Mathlib.Topology.ContinuousFunction.StoneWeierstrass
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.MetricSpace.EMetricParacompact

/-! # Continuous Functional Calculus

This file develops an API for an abstract *continuous functional calculus*. A continuous functional
calculus for an element `a : A` in a topological `R`-algebra is a continuous extension of the
polynomial functional calculus (i.e., `Polynomial.aeval`) to continuous `R`-valued functions on
`spectrum R a`. More precisely, it is a continuous star algebra homomorphism
`cfc₁ : C(spectrum R a, R) →⋆ₐ[R] A` that sends `(X : R[X]).toContinuousMapOn (spectrum R a)` to
`a`, (or, if you prefer, the equivalent `(ContinuousMap.id R).restrict (spectrum R a)` is mapped to
`a`). This is the data contained in `CFCCoreClass` and in many cases (e.g., when `spectrum R a` is
compact and `R` is `ℝ≥0`, `ℝ`, or `ℂ`), this is sufficient to uniquely determine the continuous
functional calculus.

However, there are other properties enjoyed by the usual continuous functional calculus (i.e., for
normal elements in a C⋆-algebra), in particular, it is a closed embedding and the range of
`f : C(spectrum R a, R)` coincides with the spectrum of `cfc₁ R a f`. By the Stone-Weierstrass
theorem, when `R` is either `ℝ` or `ℂ` and `spectrum R a` is compact, the closed embedding condition
is sufficient to establish an equivalence `C(spectrum R a, R) ≃⋆ₐ[R] elementalStarAlgebra R a`.
The spectral mapping property is essential to establish the composition property (see `cfc₁_comp`)
of the continuous functional calculus. We encode these additional conditions in `CFCClass`. The
reason for the separation between `CFCCorecClass` and `CFCClass` is precisely to prove the
composition property.

We keep track of two homomorphisms `cfc₁ : C(spectrum R a, R) →⋆ₐ[R] A` and
`cfc₂ : C(R, R) →⋆ₐ[R] A`, and the latter is just given by composing the former with the natural
map `C(R, R) →⋆ₐ[R] C(spectrum R a, R)` given by precomposition with `Subtype.val`. We duplicate the
API for both for a few reasons. The former map is injective and, in certain relevant cases, every
element of `C(spectrum R a, R)` is a limit of polynomials by the Stone-Weierstrass theorem, both of
which are particularly useful. On the other hand, the composition property is much easier to use
for the latter (compare `cfc₁_comp` with `cfc₂_comp`, for example), and it avoids needing to
continually write `f.restrict (spectrum R a)` for `f : C(R, R)`, since we will usually have
continuous functions defined on the full type.



## Main definitions

* `CFCCoreClass`: a class for the (generally unique) continuous star algebra homomorphism from
  `C(spectrum R a, R)` to `A` sending the restriction of the identity to `a`.
* `CFCClass`: a stronger class than `CFCCoreClass` which further requires the homomorphism to be
  a closed embedding such that the spectrum of the image of `f : C(spectrum R a, R)` under this map
  is the range of `f`.
* `cfc₁ R a : C(spectrum R a, R) →⋆ₐ[R] A`: the morphism from `CFCCoreClass`
* `cfc₂ R a : C(R, R) →⋆ₐ[R] A`: this is `cfc₁` composed with the natural map
  `C(R, R) →⋆ₐ[R] C(spectrum R a, R)` given by precomposition with `Subtype.val`.
* `SpectrumRestricts a f`: this is a proposition stating that for `a : A` with `A` an `S`-algebra,
  and where `S` is an `R`-algebra with `f : S → R`, that (a) `f ∘ algebraMap R S = id` and
  (b) `(algebraMap R S ∘ f) x = x` for `x ∈ spectrum S a`.
* `cfcℝ a : C(ℝ, ℝ) →ₗ[ℝ] selfAdjoint A`: this is just `cfc₂` upgraded to a map into the subtype
  `selfAdjoint A` when `a : selfAdjoint A`. It is no longer multiplicative because `selfAdjoint A`
  doesn't have any multiplicative structure (unless `A` is commutative).

## Main theorems

* `cfc₁_comp`, `cfc₁₂_comp`, `cfc₂_comp`, `selfAdjoint.cfc₂_comp`, `selfAdjoint.cfc₂_comp_coe_mk`,
  `cfcℝ_comp`: various versions of the composition property of the continuous functional calculus.

## Implementation details




-/

open scoped Polynomial

open Polynomial

section prereqs

-- wtf? why is this not ported?
theorem Set.eqOn_singleton {α β : Type _} {f₁ f₂ : α → β} {a : α} :
    Set.EqOn f₁ f₂ {a} ↔ f₁ a = f₂ a := by
  simp [Set.EqOn]
#align set.eq_on_singleton Set.eqOn_singleton

/-- `Complex.re` as a bundled continuous map. -/
@[simps]
def ContinuousMap.complexRe : C(ℂ, ℝ) :=
  ContinuousMap.mk Complex.re Complex.continuous_re
#align continuous_map.complex_re ContinuousMap.complexRe

/-- `Complex.im` as a bundled continuous map. -/
@[simps]
def ContinuousMap.complexIm : C(ℂ, ℝ) :=
  ContinuousMap.mk Complex.im Complex.continuous_im
#align continuous_map.complex_im ContinuousMap.complexIm

instance ContinuousMap.trivialStar {X R : Type _} [TopologicalSpace X] [TopologicalSpace R] [Star R]
    [ContinuousStar R] [TrivialStar R] : TrivialStar C(X, R)
    where star_trivial _ := ContinuousMap.ext fun _ => star_trivial _
#align continuous_map.has_trivial_star ContinuousMap.trivialStar

instance {X Y : Type _} [TopologicalSpace X] [TopologicalSpace Y] [Add Y] [ContinuousAdd Y]
    [PartialOrder Y] [CovariantClass Y Y (· + ·) (· ≤ ·)] :
    CovariantClass C(X, Y) C(X, Y) (· + ·) (· ≤ ·) where
  elim _ _ _ h' x := add_le_add_left (h' x) _

instance IsScalarTower.complexToReal {M E : Type _} [AddCommGroup M] [Module ℂ M] [AddCommGroup E]
    [Module ℂ E] [SMul M E] [IsScalarTower ℂ M E] : IsScalarTower ℝ M E
    where smul_assoc x _ _ := (smul_assoc (x : ℂ) _ _ : _)
#align is_scalar_tower.complex_to_real IsScalarTower.complexToReal

-- this is not so crazy, we already have the `•` in `Module.complexToReal`
noncomputable instance Algebra.complexToReal {A : Type _} [Ring A] [Algebra ℂ A] : Algebra ℝ A :=
  instAlgebraRestrictScalarsInstSemiringRestrictScalars ℝ ℂ A
#align algebra.complex_to_real Algebra.complexToReal

@[simps]
def ContinuousMap.compStarAlgHom (X : Type _) {R B C : Type _} [TopologicalSpace X] [CommSemiring R]
    [Semiring B] [Algebra R B] [Star B] [TopologicalSpace B] [TopologicalSemiring B]
    [ContinuousStar B] [Semiring C] [Algebra R C] [Star C] [TopologicalSpace C]
    [TopologicalSemiring C] [ContinuousStar C] (φ : B →⋆ₐ[R] C) (hφ : Continuous φ) :
    C(X, B) →⋆ₐ[R] C(X, C) where
  toFun f := (⟨φ, hφ⟩ : C(B, C)).comp f
  map_one' := ContinuousMap.ext fun _ => map_one φ
  map_mul' f g := ContinuousMap.ext fun x => map_mul φ (f x) (g x)
  map_zero' := ContinuousMap.ext fun _ => map_zero φ
  map_add' f g := ContinuousMap.ext fun x => map_add φ (f x) (g x)
  commutes' r := ContinuousMap.ext fun _x => AlgHomClass.commutes φ r
  map_star' f := ContinuousMap.ext fun x => map_star φ (f x)

open scoped NNReal

instance : StarRing ℝ≥0 where
  star := id
  star_involutive _ := rfl
  star_mul := mul_comm
  star_add _ _ := rfl

instance : TrivialStar ℝ≥0 where star_trivial _ := rfl

instance : ContinuousStar ℝ≥0 where continuous_star := continuous_id

instance : StarModule ℝ≥0 ℝ
    where star_smul := by simp only [star_trivial, eq_self_iff_true, forall_const]

end prereqs

/-!
## Definitions
-/


/-- This class exists because under modest hypotheses, we can get a `subsingleton` instance for
this class. -/
@[ext]
class CFCCoreClass (R : Type _) {A : Type _} [CommSemiring R] [StarRing R] [TopologicalSpace R]
    [TopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A] [TopologicalSpace A]
    [Algebra R A] (a : A) where
  toStarAlgHom : C(spectrum R a, R) →⋆ₐ[R] A
  hom_continuous : Continuous toStarAlgHom
  hom_map_X : toStarAlgHom (toContinuousMapOnAlgHom (spectrum R a) X) = a
#align cfc_core_class CFCCoreClass

-- Question: do we want to make this a `uniform_embedding`?
/-- A `cfc_class R a` is a star algebra homomorphism from the continuous
`R`-valued functions defined on the spectrum of `a : A` into the algebra `A` which is in addiiton
continuous and extends the polynomial functional calculus. More precisely, this latter statement
is encapsulated in -/
@[ext]
class CFCClass (R : Type _) {A : Type _} [CommSemiring R] [StarRing R] [TopologicalSpace R]
    [TopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A] [TopologicalSpace A]
    [Algebra R A] (a : A) where
  toStarAlgHom : C(spectrum R a, R) →⋆ₐ[R] A
  hom_closedEmbedding : ClosedEmbedding toStarAlgHom
  hom_map_X : toStarAlgHom (toContinuousMapOnAlgHom (spectrum R a) X) = a
  hom_map_spectrum : ∀ f, spectrum R (toStarAlgHom f) = Set.range f
#align cfc_class CFCClass

-- see note [lower instance priority]
instance (priority := 100) CFCClass.toCFCCoreClass (R : Type _) {A : Type _} [CommSemiring R]
    [StarRing R] [TopologicalSpace R] [TopologicalSemiring R] [ContinuousStar R] [Ring A]
    [StarRing A] [TopologicalSpace A] [Algebra R A] (a : A) [CFCClass R a] : CFCCoreClass R a :=
  { (‹_› : CFCClass R a) with
    hom_continuous := (‹_› : CFCClass R a).hom_closedEmbedding.continuous }
#align cfc_class.to_cfc_core_class CFCClass.toCFCCoreClass

instance {𝕜 A : Type _} [IsROrC 𝕜] [Ring A] [StarRing A] [Algebra 𝕜 A] [TopologicalSpace A]
    [T2Space A] [StarModule 𝕜 A] {a : A} [CompactSpace (spectrum 𝕜 a)] :
    Subsingleton (CFCCoreClass 𝕜 a) :=
  Subsingleton.intro fun h₁ h₂ =>
    h₁.ext h₂ <|
      ContinuousMap.starAlgHom_ext_map_X h₁.hom_continuous h₂.hom_continuous <|
        h₁.hom_map_X.trans h₂.hom_map_X.symm

/-- The `star_alg_hom` underlying an instance of the continuous functional calculus. -/
def cfc₁ (R : Type _) {A : Type _} [CommSemiring R] [StarRing R] [TopologicalSpace R]
    [TopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A] [TopologicalSpace A]
    [Algebra R A] (a : A) [CFCCoreClass R a] : C(spectrum R a, R) →⋆ₐ[R] A :=
  CFCCoreClass.toStarAlgHom
#align cfc₁ cfc₁

section

-- needs explicit universes?
universe u v

/-- This is `cfc₁` composed with the natural star algebra homomorphism from `C(R, R)` into
`C(spectrum R a, R)` given by precompostion with the embedding of `spectrum R a` into `R`.

While `cfc₁` is necessary in order to have some of the key properties (e.g., uniqueness of the
continuous funcitonal calculus, injectivity, mapping into the `elemental_star_algebra`, etc.), it
is expected that this version will be more useful in practice. In particular, it will naturally
allow for iterated applications of the continuous functional calculus, and one can use existing
continuous functions with it, as opposed to continually needing to bundle some continuous function
into the type `C(spectrum R a, R)`.

Throughout the API, we duplicate lemmas for both versions. -/
def cfc₂ (R : Type u) {A : Type v} [CommSemiring R] [StarRing R] [TopologicalSpace R]
    [TopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A] [TopologicalSpace A]
    [Algebra R A] (a : A) [CFCCoreClass R a] : C(R, R) →⋆ₐ[R] A :=
  (cfc₁ R a).comp <|
    ContinuousMap.compStarAlgHom' R R <| (ContinuousMap.id R).restrict <| spectrum R a
#align cfc₂ cfc₂

end

/-!
## Basic properties
-/


theorem cfc₂_eq_of_eqOn {R A : Type _} [CommSemiring R] [StarRing R] [TopologicalSpace R]
    [TopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A] [TopologicalSpace A]
    [Algebra R A] (a : A) [CFCClass R a] {f g : C(R, R)} (h : (spectrum R a).EqOn f g) :
    cfc₂ R a f = cfc₂ R a g := by
  simp only [cfc₂, StarAlgHom.coe_comp, Function.comp]
  exact congr_arg _ (ContinuousMap.ext fun x => h x.prop)
#align cfc₂_eq_of_eq_on cfc₂_eq_of_eqOn

@[continuity]
theorem cfc₁_closedEmbedding (R : Type _) {A : Type _} [CommSemiring R] [StarRing R]
    [TopologicalSpace R] [TopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A]
    [TopologicalSpace A] [Algebra R A] (a : A) [CFCClass R a] :
    ClosedEmbedding (cfc₁ R a) :=
  CFCClass.hom_closedEmbedding
#align cfc₁_closed_embedding cfc₁_closedEmbedding

@[continuity]
theorem cfc₁_continuous (R : Type _) {A : Type _} [CommSemiring R] [StarRing R] [TopologicalSpace R]
    [TopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A] [TopologicalSpace A]
    [Algebra R A] (a : A) [CFCCoreClass R a] : Continuous (cfc₁ R a) :=
  CFCCoreClass.hom_continuous
#align cfc₁_continuous cfc₁_continuous

-- `cfc₂_closed_embedding`? Is it true in general? Maybe not without Tietze?
@[continuity]
theorem cfc₂_continuous (R : Type _) {A : Type _} [CommSemiring R] [StarRing R] [TopologicalSpace R]
    [TopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A] [TopologicalSpace A]
    [Algebra R A] (a : A) [CFCCoreClass R a] : Continuous (cfc₂ R a : C(R, R) →⋆ₐ[R] A) :=
  (cfc₁_continuous R a).comp <| ContinuousMap.continuous_comp_left _
#align cfc₂_continuous cfc₂_continuous

theorem X_toContinuousMap (R : Type _) [Semiring R] [TopologicalSpace R] [TopologicalSemiring R] :
    (X : R[X]).toContinuousMap = ContinuousMap.id R := by
  ext
  simp only [toContinuousMap_apply, eval_X, ContinuousMap.id_apply]
set_option linter.uppercaseLean3 false in
#align X_to_continuous_map X_toContinuousMap

@[simp]
theorem cfc₁_map_X (R : Type _) {A : Type _} [CommSemiring R] [StarRing R] [TopologicalSpace R]
    [TopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A] [TopologicalSpace A]
    [Algebra R A] (a : A) [CFCCoreClass R a] : cfc₁ R a (X.toContinuousMapOn <| spectrum R a) = a :=
  CFCCoreClass.hom_map_X
set_option linter.uppercaseLean3 false in
#align cfc₁_map_X cfc₁_map_X

@[simp]
theorem cfc₁_map_id (R : Type _) {A : Type _} [CommSemiring R] [StarRing R] [TopologicalSpace R]
    [TopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A] [TopologicalSpace A]
    [Algebra R A] (a : A) [CFCCoreClass R a] :
    cfc₁ R a ((ContinuousMap.id R).restrict <| spectrum R a) = a := by
  convert cfc₁_map_X R a
  rw [←X_toContinuousMap R]
  rfl
#align cfc₁_map_id cfc₁_map_id

@[simp]
theorem cfc₂_map_X {R A : Type _} [CommSemiring R] [StarRing R] [TopologicalSpace R]
    [TopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A] [TopologicalSpace A]
    [Algebra R A] (a : A) [CFCCoreClass R a] : cfc₂ R a (X : R[X]).toContinuousMap = a :=
  cfc₁_map_X R a
set_option linter.uppercaseLean3 false in
#align cfc₂_map_X cfc₂_map_X

@[simp]
theorem cfc₂_map_id (R : Type _) {A : Type _} [CommSemiring R] [StarRing R] [TopologicalSpace R]
    [TopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A] [TopologicalSpace A]
    [Algebra R A] (a : A) [CFCCoreClass R a] : cfc₂ R a (ContinuousMap.id R) = a :=
  cfc₁_map_id R a
#align cfc₂_map_id cfc₂_map_id

@[simp]
theorem cfc₁_map_C {R A : Type _} [CommSemiring R] [StarRing R] [TopologicalSpace R]
    [TopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A] [TopologicalSpace A]
    [Algebra R A] (a : A) [CFCCoreClass R a] (r : R) :
    cfc₁ R a ((C r).toContinuousMapOn <| spectrum R a) = algebraMap R A r :=
  ((cfc₁ R a).toAlgHom.comp (toContinuousMapOnAlgHom <| spectrum R a)).commutes' r
set_option linter.uppercaseLean3 false in
#align cfc₁_map_C cfc₁_map_C

@[simp]
theorem cfc₂_map_C {R A : Type _} [CommSemiring R] [StarRing R] [TopologicalSpace R]
    [TopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A] [TopologicalSpace A]
    [Algebra R A] (a : A) [CFCCoreClass R a] (r : R) :
    cfc₂ R a (C r).toContinuousMap = algebraMap R A r :=
  cfc₁_map_C a r
set_option linter.uppercaseLean3 false in
#align cfc₂_map_C cfc₂_map_C

/-- The continuous functional calculus extends the polynomial functional calculus. -/
theorem cfc₁_comp_toContinuousMapOnAlgHom (R : Type _) {A : Type _} [CommSemiring R] [StarRing R]
    [TopologicalSpace R] [TopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A]
    [TopologicalSpace A] [Algebra R A] (a : A) [CFCCoreClass R a] :
    (cfc₁ R a).toAlgHom.comp (toContinuousMapOnAlgHom <| spectrum R a) = aeval a := by
  simpa only [aeval_X_left, AlgHom.coe_comp, StarAlgHom.coe_toAlgHom, Function.comp_apply,
    toContinuousMapOnAlgHom_apply, cfc₁_map_X] using
    (aeval_algHom ((cfc₁ R a).toAlgHom.comp <| toContinuousMapOnAlgHom (spectrum R a)) X).symm
#align cfc₁_comp_to_continuous_map_on_alg_hom cfc₁_comp_toContinuousMapOnAlgHom

/-- The continuous functional calculus extends the polynomial functional calculus. -/
theorem cfc₁_map_polynomial {R A : Type _} [CommSemiring R] [StarRing R] [TopologicalSpace R]
    [TopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A] [TopologicalSpace A]
    [Algebra R A] (a : A) [CFCCoreClass R a] (p : R[X]) :
    cfc₁ R a (p.toContinuousMapOn <| spectrum R a) = (aeval a (R := R)) p :=
  FunLike.congr_fun (cfc₁_comp_toContinuousMapOnAlgHom R a) p
#align cfc₁_map_polynomial cfc₁_map_polynomial

/-- The continuous functional calculus extends the polynomial functional calculus. -/
theorem cfc₂_map_polynomial {R A : Type _} [CommSemiring R] [StarRing R] [TopologicalSpace R]
    [TopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A] [TopologicalSpace A]
    [Algebra R A] (a : A) [CFCCoreClass R a] (p : R[X]) :
    cfc₂ R a p.toContinuousMap = aeval (R := R) a p :=
  cfc₁_map_polynomial a p
#align cfc₂_map_polynomial cfc₂_map_polynomial

/-- The range of the continuous functional calculus is contained in the `elemental_star_algebra`
generated by the element. -/
theorem cfc₁_range_le (𝕜 : Type _) {A : Type _} [IsROrC 𝕜] [Ring A] [StarRing A]
    [TopologicalSpace A] [Algebra 𝕜 A] [StarModule 𝕜 A] [TopologicalRing A] [ContinuousStar A]
    (a : A) [CFCCoreClass 𝕜 a] [CompactSpace (spectrum 𝕜 a)] :
    (cfc₁ 𝕜 a).range ≤ elementalStarAlgebra 𝕜 a := by
  rw [StarAlgHom.range_eq_map_top, ← polynomialFunctions.starClosure_topologicalClosure]
  refine' (StarSubalgebra.map_topologicalClosure_le _ _ (cfc₁_continuous 𝕜 a)).trans _
  refine' StarSubalgebra.topologicalClosure_mono _
  rw [polynomialFunctions.starClosure_eq_adjoin_X, StarAlgHom.map_adjoin]
  refine' StarSubalgebra.adjoin_le _
  simp only [Set.image_singleton, Set.singleton_subset_iff, toContinuousMapOnAlgHom_apply,
    cfc₁_map_X]
  exact StarSubalgebra.self_mem_adjoin_singleton 𝕜 a
#align cfc₁_range_le cfc₁_range_le

/-- The range of the continuous functional calculus is contained in the `elemental_star_algebra`
generated by the element. -/
theorem cfc₁_mem_elementalStarAlgebra {𝕜 A : Type _} [IsROrC 𝕜] [Ring A] [StarRing A]
    [TopologicalSpace A] [Algebra 𝕜 A] [StarModule 𝕜 A] [TopologicalRing A] [ContinuousStar A]
    {a : A} [CFCCoreClass 𝕜 a] [CompactSpace (spectrum 𝕜 a)] (f : C(spectrum 𝕜 a, 𝕜)) :
    cfc₁ 𝕜 a f ∈ elementalStarAlgebra 𝕜 a :=
  cfc₁_range_le 𝕜 a ⟨f, rfl⟩
#align cfc₁_mem_elemental_star_algebra cfc₁_mem_elementalStarAlgebra

/-- The range of the continuous functional calculus is contained in the `elemental_star_algebra`
generated by the element. -/
theorem cfc₂_mem_elementalStarAlgebra {𝕜 A : Type _} [IsROrC 𝕜] [Ring A] [StarRing A]
    [TopologicalSpace A] [Algebra 𝕜 A] [StarModule 𝕜 A] [TopologicalRing A] [ContinuousStar A]
    (a : A) [CFCCoreClass 𝕜 a] [CompactSpace (spectrum 𝕜 a)] (f : C(𝕜, 𝕜)) :
    cfc₂ 𝕜 a f ∈ elementalStarAlgebra 𝕜 a :=
  cfc₁_mem_elementalStarAlgebra _
#align cfc₂_mem_elemental_star_algebra cfc₂_mem_elementalStarAlgebra

/-- The range of the continuous functional calculus is contained in the `elemental_star_algebra`
generated by the element. -/
theorem cfc₂_range_le (𝕜 : Type _) {A : Type _} [IsROrC 𝕜] [Ring A] [StarRing A]
    [TopologicalSpace A] [Algebra 𝕜 A] [StarModule 𝕜 A] [TopologicalRing A] [ContinuousStar A]
    (a : A) [CFCCoreClass 𝕜 a] [CompactSpace (spectrum 𝕜 a)] :
    (cfc₂ 𝕜 a).range ≤ elementalStarAlgebra 𝕜 a := by
  rintro _ ⟨f, rfl⟩
  exact cfc₂_mem_elementalStarAlgebra a f
#align cfc₂_range_le cfc₂_range_le

/-- Any images under the continuous functional calculus commute. -/
@[simp]
theorem cfc₁_commute {R A : Type _} [CommSemiring R] [StarRing R] [TopologicalSpace R]
    [TopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A] [TopologicalSpace A]
    [Algebra R A] {a : A} [CFCCoreClass R a] (f g : C(spectrum R a, R)) :
    Commute (cfc₁ R a f) (cfc₁ R a g) :=
  (Commute.all f g).map (cfc₁ R a)
#align cfc₁_commute cfc₁_commute

/-- Any images under the continuous functional calculus commute. -/
theorem cfc₂_commute {R A : Type _} [CommSemiring R] [StarRing R] [TopologicalSpace R]
    [TopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A] [TopologicalSpace A]
    [Algebra R A] (a : A) [CFCCoreClass R a] (f g : C(R, R)) : Commute (cfc₂ R a f) (cfc₂ R a g) :=
  cfc₁_commute _ _
#align cfc₂_commute cfc₂_commute

/-- Any image under the continuous functional calculus is normal. -/
instance cfc₁.isStarNormal {R A : Type _} [CommSemiring R] [StarRing R] [TopologicalSpace R]
    [TopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A] [TopologicalSpace A]
    [Algebra R A] {a : A} [CFCCoreClass R a] (f : C(spectrum R a, R)) :
    IsStarNormal (cfc₁ R a f) where
  star_comm_self := by simpa only [map_star] using cfc₁_commute (star f) f
#align cfc₁.is_star_normal cfc₁.isStarNormal

/-- Any image under the continuous functional calculus is normal. -/
instance IsStarNormal.cfc₂ {R A : Type _} [CommSemiring R] [StarRing R] [TopologicalSpace R]
    [TopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A] [TopologicalSpace A]
    [Algebra R A] (a : A) [CFCCoreClass R a] (f : C(R, R)) :
    IsStarNormal (cfc₂ R a f) where
  star_comm_self := by simpa only [map_star] using cfc₂_commute a (star f) f
#align is_star_normal.cfc₂ IsStarNormal.cfc₂

@[simp]
theorem cfc₁_injective (R : Type _) {A : Type _} [CommSemiring R] [StarRing R] [TopologicalSpace R]
    [TopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A] [TopologicalSpace A]
    [Algebra R A] (a : A) [CFCClass R a] :
    Function.Injective (cfc₁ R a) :=
  (cfc₁_closedEmbedding R a).inj
#align cfc₁_injective cfc₁_injective

theorem cfc₂_eq_iff_eqOn {R A : Type _} [CommSemiring R] [StarRing R] [TopologicalSpace R]
    [TopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A] [TopologicalSpace A]
    [Algebra R A] (a : A) [CFCClass R a] {f g : C(R, R)} :
    cfc₂ R a f = cfc₂ R a g ↔ (spectrum R a).EqOn f g := by
  refine' ⟨fun h => _, fun h => cfc₂_eq_of_eqOn a h⟩
  have := fun x hx => FunLike.congr_fun (cfc₁_injective R a h) ⟨x, hx⟩
  exact this
#align cfc₂_eq_iff_eq_on cfc₂_eq_iff_eqOn

/-- For an isometric continuous functional calculus for `a` over `is_R_or_C 𝕜`, the range is
precisely the `elemental_star_algebra` generated by `a`. -/
theorem cfc₁_range {𝕜 A : Type _} [IsROrC 𝕜] [NormedRing A] [StarRing A] [NormedAlgebra 𝕜 A]
    [StarModule 𝕜 A] [NormedStarGroup A] {a : A} [CompactSpace (spectrum 𝕜 a)] [CFCClass 𝕜 a] :
    (cfc₁ 𝕜 a).range = elementalStarAlgebra 𝕜 a := by
  rw [StarAlgHom.range_eq_map_top, ← polynomialFunctions.starClosure_topologicalClosure, ←
    StarSubalgebra.topologicalClosure_map _ _ (cfc₁_closedEmbedding 𝕜 a),
    polynomialFunctions.starClosure_eq_adjoin_X, StarAlgHom.map_adjoin]
  congr
  rw [Set.image_singleton, toContinuousMapOnAlgHom_apply, cfc₁_map_X]
#align cfc₁_range cfc₁_range

-- this is the only direct result where we need the `topology.tietze_extension`
-- and also `topology.metric_space.emetric_paracompact` for `normal_space` instance.
theorem cfc₂_range {𝕜 A : Type _} [IsROrC 𝕜] [NormedRing A] [StarRing A] [NormedAlgebra 𝕜 A]
    [StarModule 𝕜 A] [NormedStarGroup A] {a : A} [CompactSpace (spectrum 𝕜 a)] [CFCClass 𝕜 a] :
    (cfc₂ 𝕜 a).range = elementalStarAlgebra 𝕜 a := by
  refine' le_antisymm (cfc₂_range_le 𝕜 a) _
  rw [← cfc₁_range]
  rintro - ⟨f, rfl⟩
  have hspec := (isCompact_iff_compactSpace.mpr (‹_› : CompactSpace (spectrum 𝕜 a))).isClosed
  obtain ⟨f_re', hf_re⟩ :=
    (ContinuousMap.comp ⟨IsROrC.re, IsROrC.continuous_re⟩ f).exists_restrict_eq_of_closed hspec
  obtain ⟨f_im', hf_im⟩ :=
    (ContinuousMap.comp ⟨IsROrC.im, IsROrC.continuous_im⟩ f).exists_restrict_eq_of_closed hspec
  refine'
    ⟨(@IsROrC.ofRealClm 𝕜 _ : C(ℝ, 𝕜)).comp f_re' +
        @IsROrC.I 𝕜 _ • (@IsROrC.ofRealClm 𝕜 _ : C(ℝ, 𝕜)).comp f_im',
      _⟩
  simp only [AlgHom.toRingHom_eq_coe, map_add, RingHom.coe_coe, StarAlgHom.coe_toAlgHom]
  rw [cfc₂, StarAlgHom.coe_comp, Function.comp_apply, Function.comp_apply, ←map_add]
  congr!
  ext x
  apply IsROrC.ext <;>
    simp [ContinuousMap.compStarAlgHom', ContinuousMap.restrict, ContinuousMap.comp, (· ∘ ·),
      ContinuousMap.smul_apply IsROrC.I]
  · exact FunLike.congr_fun hf_re x
  · rw [← IsROrC.I_im' (f x)]
    congr! 1
    exact FunLike.congr_fun hf_im x
#align cfc₂_range cfc₂_range

/-- For an isometric continuous functional calculus for `a` over `is_R_or_C 𝕜`, the range is
precisely the `elemental_star_algebra` generated by `a`. -/
theorem cfc₁_exists_of_mem_elementalStarAlgebra {𝕜 A : Type _} [IsROrC 𝕜] [NormedRing A]
    [StarRing A] [NormedAlgebra 𝕜 A] [StarModule 𝕜 A] [NormedStarGroup A] {a : A}
    [CompactSpace (spectrum 𝕜 a)] [CFCClass 𝕜 a] {x : A} (hx : x ∈ elementalStarAlgebra 𝕜 a) :
    ∃ f : C(spectrum 𝕜 a, 𝕜), cfc₁ 𝕜 a f = x := by
  rwa [← cfc₁_range] at hx
#align cfc₁_exists_of_mem_elemental_star_algebra cfc₁_exists_of_mem_elementalStarAlgebra

theorem cfc₂_exists_of_mem_elementalStarAlgebra {𝕜 A : Type _} [IsROrC 𝕜] [NormedRing A]
    [StarRing A] [NormedAlgebra 𝕜 A] [StarModule 𝕜 A] [NormedStarGroup A] {a : A}
    [CompactSpace (spectrum 𝕜 a)] [CFCClass 𝕜 a] {x : A} (hx : x ∈ elementalStarAlgebra 𝕜 a) :
    ∃ f : C(𝕜, 𝕜), cfc₂ 𝕜 a f = x := by
  rwa [← cfc₂_range] at hx
#align cfc₂_exists_of_mem_elemental_star_algebra cfc₂_exists_of_mem_elementalStarAlgebra

theorem cfc₁_map_spectrum (R : Type _) {A : Type _} [CommSemiring R] [StarRing R]
    [TopologicalSpace R] [TopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A]
    [TopologicalSpace A] [Algebra R A] (a : A) [CFCClass R a] (f : C(spectrum R a, R)) :
    spectrum R (cfc₁ R a f) = Set.range f :=
  CFCClass.hom_map_spectrum f
#align cfc₁_map_spectrum cfc₁_map_spectrum

theorem cfc₂_map_spectrum {R A : Type _} [CommSemiring R] [StarRing R] [TopologicalSpace R]
    [TopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A] [TopologicalSpace A]
    [Algebra R A] (a : A) [CFCClass R a] (f : C(R, R)) :
    (spectrum R a).MapsTo f (spectrum R (cfc₂ R a f)) := by
  rw [cfc₂, StarAlgHom.coe_comp, Function.comp_apply, cfc₁_map_spectrum]
  exact fun x hx => ⟨⟨x, hx⟩, rfl⟩
#align cfc₂_map_spectrum cfc₂_map_spectrum

theorem cfc₂_map_spectrum' {R A : Type _} [CommSemiring R] [StarRing R] [TopologicalSpace R]
    [TopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A] [TopologicalSpace A]
    [Algebra R A] (a : A) [CFCClass R a] (f : C(R, R)) :
    spectrum R (cfc₂ R a f) = f '' spectrum R a := by
  rw [cfc₂, StarAlgHom.coe_comp, Function.comp_apply, cfc₁_map_spectrum]
  ext
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.prop, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
#align cfc₂_map_spectrum' cfc₂_map_spectrum'

lemma cfc₁_comp {R A : Type _} [CommSemiring R] [StarRing R] [TopologicalSpace R]
    [TopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A] [TopologicalSpace A]
    [Algebra R A] (a : A) [CFCClass R a] (f : C(spectrum R a, R)) [CFCCoreClass R (cfc₁ R a f)]
    [Subsingleton (CFCCoreClass R (cfc₁ R a f))] (g : C(spectrum R (cfc₁ R a f), R))
    (f' : C(spectrum R a, spectrum R (cfc₁ R a f))) (hff' : ∀ x, (f' x : R) = f x) :
    cfc₁ R a (g.comp f') = cfc₁ R (cfc₁ R a f) g := by
  let cfc₃ : C(spectrum R (cfc₁ R a f), R) →⋆ₐ[R] A := (cfc₁ R a).comp (f'.compStarAlgHom' R R)
  let this : CFCCoreClass R (cfc₁ R a f) :=
    { toStarAlgHom := cfc₃
      hom_continuous := CFCClass.hom_closedEmbedding.continuous.comp f'.continuous_comp_left
      hom_map_X := by
        simp only [cfc₂, StarAlgHom.coe_comp, Function.comp_apply]
        congr 1
        ext x
        simp [hff' x] }
  exact FunLike.congr_fun ((CFCCoreClass.ext_iff _ _).mp (Subsingleton.elim this _)) g

theorem cfc₁₂_comp {R A : Type _} [CommSemiring R] [StarRing R] [TopologicalSpace R]
    [TopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A] [TopologicalSpace A]
    [Algebra R A] (a : A) [CFCClass R a] (f : C(spectrum R a, R)) [CFCCoreClass R (cfc₁ R a f)]
    [Subsingleton (CFCCoreClass R (cfc₁ R a f))] (g : C(R, R)) :
    cfc₁ R a (g.comp f) = cfc₂ R (cfc₁ R a f) g :=
  let f' : C(spectrum R a, spectrum R (cfc₁ R a f)) :=
    ⟨fun r => ⟨f r, cfc₁_map_spectrum R a f ▸ Set.mem_range_self r (f := f)⟩,
      (map_continuous f).subtype_mk _⟩
  cfc₁_comp a f (g.restrict (spectrum R (cfc₁ R a f))) f' (fun _ => rfl)

theorem cfc₂_comp {R A : Type _} [CommSemiring R] [StarRing R] [TopologicalSpace R]
    [TopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A] [TopologicalSpace A]
    [Algebra R A] (a : A) [CFCClass R a] (f g : C(R, R)) [hf₁ : CFCCoreClass R (cfc₂ R a f)]
    [hf₂ : Subsingleton (CFCCoreClass R (cfc₂ R a f))] :
    cfc₂ R a (g.comp f) = cfc₂ R (cfc₂ R a f) g := by
  have : CFCCoreClass R (cfc₁ R a (f.restrict (spectrum R a))) := hf₁
  have : Subsingleton (CFCCoreClass R (cfc₁ R a (f.restrict (spectrum R a)))) := hf₂
  convert cfc₁₂_comp a (f.restrict (spectrum R a)) g
#align cfc₂_comp cfc₂_comp

/-!
## Restriction of the spectrum

Suppose that `A` is an `S`-algebra and `S` is an `R`-algebra. For `a : A`, what is the relationship
between `spectrum R a` and `spectrum S a`? Of course, these live in different places, and in general
the relationship is `spectrum R a = algebra_map R S ⁻¹' spectrum S a`. One might wonder under what
conditions one has `algebra_map R S '' spectrum R a = spectrum S a`. We provide a predicate here
called `spectrum_restricts` which takes an `a : A` and a function `f : S → R` and says that
`f ∘ algebra_map R S = id` and the restriction of `algebra_map R S ∘ f` to `spectrum S a` is the
identity. Of course, this forces `algebra_map R S` to be a ring embedding, and also this is
sufficient to guarantee `algebra_map R S '' spectrum R a = spectrum S a`.

This predicate is useful for restricting a continuous functional calculus over the ring `S` to one
over the ring `R`.
-/


theorem spectrum.algebraMap_mem_iff (R S : Type _) {A : Type _} [CommSemiring R] [CommSemiring S]
    [Ring A] [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] {a : A} {r : R} :
    algebraMap R S r ∈ spectrum S a ↔ r ∈ spectrum R a := by
  simp only [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]
#align spectrum.algebra_map_mem_iff spectrum.algebraMap_mem_iff

alias spectrum.algebraMap_mem_iff ↔ spectrum.of_algebraMap_mem spectrum.algebraMap_mem
#align spectrum.of_algebra_map_mem spectrum.of_algebraMap_mem
#align spectrum.algebra_map_mem spectrum.algebraMap_mem

theorem spectrum.preimage_algebraMap {R S A : Type _} [CommSemiring R] [CommSemiring S] [Ring A]
    [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] {a : A} :
    algebraMap R S ⁻¹' spectrum S a = spectrum R a :=
  Set.ext fun _ => spectrum.algebraMap_mem_iff _ _
#align spectrum.preimage_algebra_map spectrum.preimage_algebraMap

/-- Given an element `a : A` of an `S`-algebra, where `S` is itself an `R`-algebra, we say that
the spectrum of `a` restricts via a function `f : S → R` if `f` is a left inverse of
`algebra_map R S`, and `f` is a right inverse of `algebra_map R S` on `spectrum S a`.

This is the predicate which allows us to restrict a continuous functional calculus on over `S` to a
continuous functional calculus over `R`. -/
class SpectrumRestricts {R : Type _} {S : semiOutParam (Type _)} {A : Type _} [CommSemiring R]
    [CommSemiring S] [Ring A] [Algebra R S] [Algebra R A] [Algebra S A] (a : A) (f : S → R) :
    Prop where
  rightInvOn : (spectrum S a).RightInvOn f (algebraMap R S)
  left_inv : Function.LeftInverse f (algebraMap R S)
#align spectrum_restricts SpectrumRestricts

-- not an instance because reasons.
theorem spectrumRestricts_of_subset_range_algebraMap {R S : Type _} {A : Type _} [CommSemiring R]
    [CommSemiring S] [Ring A] [Algebra R S] [Algebra R A] [Algebra S A] (a : A) (f : S → R)
    (hf : Function.LeftInverse f (algebraMap R S)) (h : spectrum S a ⊆ Set.range (algebraMap R S)) :
    SpectrumRestricts a f where
  rightInvOn := fun s hs => by obtain ⟨r, rfl⟩ := h hs; rw [hf r]
  left_inv := hf
#align spectrum_restricts_of_subset_range_algebra_map spectrumRestricts_of_subset_range_algebraMap

theorem SpectrumRestricts.algebraMap_image {R S : Type _} {A : Type _} [CommSemiring R]
    [CommSemiring S] [Ring A] [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
    {a : A} {f : S → R} (h : SpectrumRestricts a f) :
    algebraMap R S '' spectrum R a = spectrum S a := by
  refine' Set.eq_of_subset_of_subset _ fun s hs => ⟨f s, _⟩
  simpa only [spectrum.preimage_algebraMap] using
    (spectrum S a).image_preimage_subset (algebraMap R S)
  exact ⟨spectrum.of_algebraMap_mem R S ((h.rightInvOn hs).symm ▸ hs), h.rightInvOn hs⟩
#align spectrum_restricts.algebra_map_image SpectrumRestricts.algebraMap_image

theorem SpectrumRestricts.image {R S : Type _} {A : Type _} [CommSemiring R] [CommSemiring S]
    [Ring A] [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] {a : A} {f : S → R}
    (h : SpectrumRestricts a f) : f '' spectrum S a = spectrum R a := by
  simp only [← h.algebraMap_image, Set.image_image, h.left_inv _, Set.image_id']
#align spectrum_restricts.image SpectrumRestricts.image

theorem SpectrumRestricts.isCompact {R S : Type _} {A : Type _} [CommSemiring R]
    [TopologicalSpace R] [CommSemiring S] [TopologicalSpace S] [Ring A] [Algebra R S] [Algebra R A]
    [Algebra S A] [IsScalarTower R S A] {a : A} {f : S → R} (hf : Continuous f)
    (h : SpectrumRestricts a f) (ha : IsCompact (spectrum S a)) : IsCompact (spectrum R a) :=
  h.image ▸ ha.image hf
#align spectrum_restricts.is_compact SpectrumRestricts.isCompact

-- not an instance because there is no good synthesization order
def SpectrumRestricts.compactSpace {R S : Type _} {A : Type _} [CommSemiring R]
    [TopologicalSpace R] [CommSemiring S] [TopologicalSpace S] [Ring A] [Algebra R S] [Algebra R A]
    [Algebra S A] [IsScalarTower R S A] {a : A} (f : C(S, R)) [h : SpectrumRestricts a f]
    [h' : CompactSpace (spectrum S a)] : CompactSpace (spectrum R a) :=
  isCompact_iff_compactSpace.mp <| h.isCompact (map_continuous f) <|
    isCompact_iff_compactSpace.mpr h'
#align spectrum_restricts.compact_space SpectrumRestricts.compactSpace

theorem SpectrumRestricts.apply_mem {R S : Type _} {A : Type _} [CommSemiring R] [CommSemiring S]
    [Ring A] [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] {a : A} {f : S → R}
    (h : SpectrumRestricts a f) {s : S} (hs : s ∈ spectrum S a) : f s ∈ spectrum R a :=
  h.image ▸ ⟨s, hs, rfl⟩
#align spectrum_restricts.apply_mem SpectrumRestricts.apply_mem

theorem SpectrumRestricts.subset_preimage {R S : Type _} {A : Type _} [CommSemiring R]
    [CommSemiring S] [Ring A] [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
    {a : A} {f : S → R} (h : SpectrumRestricts a f) : spectrum S a ⊆ f ⁻¹' spectrum R a :=
  h.image ▸ (spectrum S a).subset_preimage_image f
#align spectrum_restricts.subset_preimage SpectrumRestricts.subset_preimage

theorem IsSelfAdjoint.spectrumRestricts {A : Type _} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] [StarRing A] [CstarRing A] [StarModule ℂ A] {a : A} (ha : IsSelfAdjoint a) :
    SpectrumRestricts a ContinuousMap.complexRe where
  rightInvOn := fun _x hx => (ha.mem_spectrum_eq_re hx).symm
  left_inv := Complex.ofReal_re
#align is_self_adjoint.spectrum_restricts IsSelfAdjoint.spectrumRestricts

/-- `algebra_map R A` as a `star_alg_hom` when `A` is a star algebra over `R`. -/
@[simps]
def StarAlgHom.ofId (R : Type _) (A : Type _) [CommSemiring R] [StarRing R] [Semiring A]
    [Algebra R A] [StarSemigroup A] [StarModule R A] : R →⋆ₐ[R] A :=
  { Algebra.ofId R A with
    toFun := algebraMap R A
    map_star' := algebraMap_star_comm }
#align star_alg_hom.of_id StarAlgHom.ofId

/-!
### Restricting the continuous functional calculus to smaller rings

Suppose that `a : A` has a continuous functional calculus over some ring `S` (e.g., `ℂ`). Suppose
also that `R` is a subring of `S` and that the `S`-spectrum of `a` is contained in this subring `R`
(e..g, `R` is `ℝ` and `a` is self-adjoint). Then it is natural to want a continuous functional
calculus for `a` over the smaller ring `R` instead. In this section, we show that this can be done
assuming `spectrum_restricts a f` for a given continuous map `f : C(S, R)`. Each variant of the
continuous functional calculus can also be restricted, where only for
`continuous_functional_calculus_isometry_class` do we also requrie that `algebra_map R S` is an
isometry. In addition we show that if `spectrum_restricts a f`, then `spectrum_restricts (cfc₁ g) f`
for any `g : C(spectrum R a, R)`.

None of the definitions in this section are instances because they wouldn't fire due to the
`spectrum_restricts` hypothesis. However, they are all `reducible` so they are suitable for
transferring to your favorite applicable setting.
-/


section Univs

universe u v w

/-- If the spectrum of an element restricts to a smaller scalar ring, then a continuous functional
calculus over the larger scalar ring descends to the smaller one. -/
@[simps!]
def SpectrumRestricts.starAlgHom {R : Type u} {S : Type v} {A : Type w} [CommSemiring R]
    [StarRing R] [TopologicalSpace R] [TopologicalSemiring R] [ContinuousStar R] [CommSemiring S]
    [StarRing S] [TopologicalSpace S] [TopologicalSemiring S] [ContinuousStar S] [Ring A]
    [StarRing A] [TopologicalSpace A] [Algebra R S] [Algebra R A] [Algebra S A]
    [IsScalarTower R S A] [StarModule R S] [ContinuousSMul R S] {a : A}
    (φ : C(spectrum S a, S) →⋆ₐ[S] A) (f : C(S, R)) (h : SpectrumRestricts a f) :
    C(spectrum R a, R) →⋆ₐ[R] A :=
  (φ.restrictScalars R).comp <|
    (ContinuousMap.compStarAlgHom (spectrum S a) (StarAlgHom.ofId R S)
          (algebraMapClm R S).continuous).comp
      (ContinuousMap.compStarAlgHom' R R
        ⟨Subtype.map f h.subset_preimage,
          (map_continuous f).subtype_map fun x (hx : x ∈ spectrum S a) => h.subset_preimage hx⟩)
#align spectrum_restricts.star_alg_hom SpectrumRestricts.starAlgHom

/-- If the spectrum of an element restricts to a smaller scalar ring, then a continuous functional
calculus over the larger scalar ring descends to the smaller one. -/
@[reducible]
def SpectrumRestricts.cfcCore {R : Type u} {S : Type v} {A : Type w} [CommSemiring R] [StarRing R]
    [TopologicalSpace R] [TopologicalSemiring R] [ContinuousStar R] [CommSemiring S] [StarRing S]
    [TopologicalSpace S] [TopologicalSemiring S] [ContinuousStar S] [Ring A] [StarRing A]
    [TopologicalSpace A] [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
    [StarModule R S] [ContinuousSMul R S] {a : A} [CFCCoreClass S a] (f : C(S, R))
    (h : SpectrumRestricts a f) : CFCCoreClass R a where
  toStarAlgHom := h.starAlgHom (cfc₁ S a) f
  hom_continuous :=
    ((cfc₁_continuous S a).comp <| ContinuousMap.continuous_comp _).comp
      (ContinuousMap.continuous_comp_left _)
  hom_map_X := by
    simp only [SpectrumRestricts.starAlgHom_apply, Polynomial.toContinuousMapOnAlgHom_apply]
    convert cfc₁_map_X S a
    ext x
    simp only [Polynomial.eval_X, Subtype.map_coe, Polynomial.toContinuousMapOn_apply,
      ContinuousMap.coe_mk, ContinuousMap.comp_apply, Polynomial.toContinuousMap_apply,
      StarAlgHom.ofId_apply]
    exact h.rightInvOn x.prop
#align spectrum_restricts.cfc_core SpectrumRestricts.cfcCore

-- note: the hypotheses `[metric_space R] [metric_space S] [compact_space (spectrum S a)]
-- [complete_space R] (h_isom : isometry (algebra_map R S)) are probably too strong, but they make
-- the proof that it is a `closed_embedding` significantly easier, and they apply in the cases we
-- care about most.
/-- If the spectrum of an element restricts to a smaller scalar ring, then a continuous functional
calculus over the larger scalar ring descends to the smaller one. If the spectrum is preserved
over the larger ring, then it is over the smaller ring as well. -/
@[reducible]
def SpectrumRestricts.cfc {R : Type u} {S : Type v} {A : Type w} [CommSemiring R] [StarRing R]
    [MetricSpace R] [TopologicalSemiring R] [ContinuousStar R] [CommSemiring S] [StarRing S]
    [MetricSpace S] [TopologicalSemiring S] [ContinuousStar S] [Ring A] [StarRing A]
    [TopologicalSpace A] [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
    [StarModule R S] [ContinuousSMul R S] {a : A} [CFCClass S a] [CompactSpace (spectrum S a)]
    [CompleteSpace R] (f : C(S, R)) (h : SpectrumRestricts a f)
    (h_isom : Isometry (algebraMap R S)) : CFCClass R a :=
  { h.cfcCore f with
    hom_map_spectrum := fun g => by
      erw [SpectrumRestricts.starAlgHom_apply]
      simp only [← @spectrum.preimage_algebraMap R S, cfc₁_map_spectrum]
      ext x
      constructor
      · rintro ⟨y, hy⟩
        have := congr_arg f hy
        simp only [ContinuousMap.coe_mk, ContinuousMap.comp_apply, StarAlgHom.ofId_apply] at this
        rw [h.left_inv _, h.left_inv _] at this
        exact ⟨_, this⟩
      · rintro ⟨y, rfl⟩
        rw [Set.mem_preimage]
        refine' ⟨⟨algebraMap R S y, spectrum.algebraMap_mem R S y.prop⟩, _⟩
        simp only [ContinuousMap.coe_mk, ContinuousMap.comp_apply, StarAlgHom.ofId_apply]
        congr
        exact Subtype.ext (h.left_inv y)
    hom_closedEmbedding := by
      apply ClosedEmbedding.comp (cfc₁_closedEmbedding S a)
      simp only [AlgHom.coe_toRingHom, StarAlgHom.coe_toAlgHom, StarAlgHom.comp_apply,
        ContinuousMap.compStarAlgHom'_apply, ContinuousMap.compStarAlgHom_apply]
      have : CompactSpace (spectrum R a) := SpectrumRestricts.compactSpace f
      refine Isometry.closedEmbedding ?_
      simp only [isometry_iff_dist_eq]
      intro g₁ g₂
      refine' le_antisymm _ _
      · rw [ContinuousMap.dist_le dist_nonneg]
        intro x
        simp only [ContinuousMap.coe_mk, ContinuousMap.comp_apply, StarAlgHom.ofId_apply]
        rw [h_isom.dist_eq]
        exact ContinuousMap.dist_apply_le_dist _
      · rw [ContinuousMap.dist_le dist_nonneg]
        intro x
        obtain ⟨y, y_mem, hy⟩ := (h.image.symm ▸ x.prop : (x : R) ∈ f '' spectrum S a)
        lift y to spectrum S a using y_mem
        refine le_of_eq_of_le ?_ <| ContinuousMap.dist_apply_le_dist y
        simp only [ContinuousMap.coe_mk, ContinuousMap.comp_apply, StarAlgHom.ofId_apply]
        rw [h_isom.dist_eq]
        congr <;> exact Subtype.ext hy.symm }
#align spectrum_restricts.cfc SpectrumRestricts.cfc

/-- If the spectrum of `a` restricts from `S` to `R`, then so does `cfc₁ g` for any
`g : C(spectrum R a, R)`. You should use this lemma manually to prove the spectrum restriction
result for continuous functional calculi whenever you use one of the definitions above to create an
instance.

Tou can use this to prove that, for exmaple, the spectrum (in `ℂ`) of the image of a positive
operator is nonnegative. -/
theorem SpectrumRestricts.cfc_spectrumRestricts {R : Type u} {S : Type v} {A : Type w}
    [CommSemiring R] [StarRing R] [MetricSpace R] [TopologicalSemiring R] [ContinuousStar R]
    [CommSemiring S] [StarRing S] [MetricSpace S] [TopologicalSemiring S] [ContinuousStar S]
    [Ring A] [StarRing A] [TopologicalSpace A] [Algebra R S] [Algebra R A] [Algebra S A]
    [IsScalarTower R S A] [StarModule R S] [ContinuousSMul R S] {a : A} [CFCClass S a]
    [CompactSpace (spectrum S a)] [CompleteSpace R] (f : C(S, R)) (h : SpectrumRestricts a f)
    (g : C(spectrum R a, R)) :
    SpectrumRestricts (@cfc₁ _ _ _ _ _ _ _ _ _ _ _ _ (h.cfcCore f) g) f :=
  { rightInvOn := by
      letI := h.cfc f
      intro s hs
      erw [h.starAlgHom_apply, cfc₁_map_spectrum] at hs
      obtain ⟨x, hx⟩ := hs
      simp only [ContinuousMap.coe_mk, ContinuousMap.comp_apply, StarAlgHom.ofId_apply] at hx
      nth_rw 1 [← hx]
      rwa [h.left_inv]
    left_inv := h.left_inv }
#align spectrum_restricts.cfc_spectrum_restricts SpectrumRestricts.cfc_spectrumRestricts

end Univs

section ComplexToReal

noncomputable instance CfcCore.complexToReal {A : Type _} [Ring A] [StarRing A] [TopologicalSpace A]
    [Algebra ℂ A] {a : A} [CFCCoreClass ℂ a] [h : SpectrumRestricts a ContinuousMap.complexRe] :
    CFCCoreClass ℝ a :=
  h.cfcCore _
#align cfc_core.complex_to_real CfcCore.complexToReal

noncomputable instance Cfc.complexToReal {A : Type _} [Ring A] [StarRing A] [MetricSpace A]
    [Algebra ℂ A] {a : A} [CompactSpace (spectrum ℂ a)] [CFCClass ℂ a]
    [h : SpectrumRestricts a ContinuousMap.complexRe] : CFCClass ℝ a :=
  h.cfc _ (algebraMap_isometry ℝ ℂ)
#align cfc.complex_to_real Cfc.complexToReal

instance CfcSpectrumRestricts.complexToReal {A : Type _} [Ring A] [StarRing A] [TopologicalSpace A]
    [Algebra ℂ A] {a : A} [CFCClass ℂ a] [CompactSpace (spectrum ℂ a)]
    [h : SpectrumRestricts a ContinuousMap.complexRe] (g : C(spectrum ℝ a, ℝ)) :
    SpectrumRestricts (@cfc₁ _ _ _ _ _ _ _ _ _ _ _ _ (h.cfcCore ContinuousMap.complexRe) g)
      ContinuousMap.complexRe :=
  h.cfc_spectrumRestricts _ g
#align cfc_spectrum_restricts.complex_to_real CfcSpectrumRestricts.complexToReal

instance CfcSpectrumRestricts.complex_to_real' {A : Type _} [Ring A] [StarRing A]
    [TopologicalSpace A] [Algebra ℂ A] {a : A} [CFCClass ℂ a] [CompactSpace (spectrum ℂ a)]
    [h : SpectrumRestricts a ContinuousMap.complexRe] (g : C(ℝ, ℝ)) :
    SpectrumRestricts (@cfc₂ _ _ _ _ _ _ _ _ _ _ _ _ (h.cfcCore ContinuousMap.complexRe) g)
      ContinuousMap.complexRe := by
  rw [cfc₂, StarAlgHom.coe_comp, Function.comp_apply]
  infer_instance
#align cfc_spectrum_restricts.complex_to_real' CfcSpectrumRestricts.complex_to_real'

end ComplexToReal

section RealToNnreal

open scoped NNReal

/-- `to_nnreal` as a bundled continuous map. -/
noncomputable def ContinuousMap.toNnreal : C(ℝ, ℝ≥0) :=
  ⟨Real.toNNReal,
    (@continuous_induced_rng ℝ≥0 ℝ _ (↑) Real.toNNReal _ _).mpr
      (continuous_id'.max continuous_const)⟩
#align continuous_map.to_nnreal ContinuousMap.toNnreal

noncomputable instance CfcCore.realToNnreal {A : Type _} [Ring A] [StarRing A] [TopologicalSpace A]
    [Algebra ℝ A] {a : A} [CompactSpace (spectrum ℝ a)] [CFCCoreClass ℝ a]
    [h : SpectrumRestricts a ContinuousMap.toNnreal] : CFCCoreClass ℝ≥0 a :=
  h.cfcCore _
#align cfc_core.real_to_nnreal CfcCore.realToNnreal

noncomputable instance Cfc.realToNnreal {A : Type _} [Ring A] [StarRing A] [TopologicalSpace A]
    [Algebra ℝ A] {a : A} [CompactSpace (spectrum ℝ a)] [CFCClass ℝ a]
    [h : SpectrumRestricts a ContinuousMap.toNnreal] : CFCClass ℝ≥0 a :=
  h.cfc _ isometry_subtype_coe
#align cfc.real_to_nnreal Cfc.realToNnreal

instance CfcSpectrumRestricts.real_toNnreal {A : Type _} [Ring A] [StarRing A] [TopologicalSpace A]
    [Algebra ℝ A] {a : A} [CFCClass ℝ a] [CompactSpace (spectrum ℝ a)]
    [h : SpectrumRestricts a ContinuousMap.toNnreal] (g : C(spectrum ℝ≥0 a, ℝ≥0)) :
    SpectrumRestricts (@cfc₁ _ _ _ _ _ _ _ _ _ _ _ _ (h.cfcCore ContinuousMap.toNnreal) g)
      ContinuousMap.toNnreal :=
  h.cfc_spectrumRestricts _ g
#align cfc_spectrum_restricts.real_to_nnreal CfcSpectrumRestricts.real_toNnreal

instance CfcSpectrumRestricts.real_to_nnreal' {A : Type _} [Ring A] [StarRing A]
    [TopologicalSpace A] [Algebra ℝ A] {a : A} [CFCClass ℝ a] [CompactSpace (spectrum ℝ a)]
    [h : SpectrumRestricts a ContinuousMap.toNnreal] (g : C(ℝ≥0, ℝ≥0)) :
    SpectrumRestricts (@cfc₂ _ _ _ _ _ _ _ _ _ _ _ _ (h.cfcCore ContinuousMap.toNnreal) g)
      ContinuousMap.toNnreal := by
  rw [cfc₂, StarAlgHom.coe_comp, Function.comp_apply]
  infer_instance
#align cfc_spectrum_restricts.real_to_nnreal' CfcSpectrumRestricts.real_to_nnreal'

end RealToNnreal

-- this is the instance you would need to add in order to get things to work if you had an algebra
-- over `ℂ` instead of one over `ℝ` in what follows. Of course, for C⋆-algebras we already have
-- a proof of this (or rather, it follows easily), but for matrices you could provide it
-- separately.
/-
instance self_adjoint.spectrum_restricts {A : Type*} [ring A] [star_ring A] [topological_space A]
  [algebra ℂ A] {a : self_adjoint A} : spectrum_restricts (a : A) continuous_map.complex_re :=
sorry
-/
theorem cfc₂_real_isSelfAdjoint {A : Type _} [Ring A] [StarRing A] [TopologicalSpace A]
    [Algebra ℝ A] (a : A) [CFCClass ℝ a] (f : C(ℝ, ℝ)) : IsSelfAdjoint (cfc₂ ℝ a f) :=
  show star _ = _ by rw [← map_star, star_trivial]
#align cfc₂_real_is_self_adjoint cfc₂_real_isSelfAdjoint

-- composition still works as long as we have propositinal equality of the intermediate elements.
theorem selfAdjoint.cfc₂_comp {A : Type _} [Ring A] [StarRing A] [TopologicalSpace A] [Algebra ℝ A]
    (a b : selfAdjoint A) (f g : C(ℝ, ℝ)) [CFCClass ℝ (a : A)]
    [Subsingleton (CFCCoreClass ℝ (cfc₂ ℝ (a : A) f))]
    -- alternatively: [compact_space (spectrum ℝ (cfc₂ (a : A) f))] [t2_space A]
    [h' : CFCClass ℝ (b : A)]
    (h : cfc₂ ℝ (a : A) f = b) : cfc₂ ℝ (a : A) (g.comp f) = cfc₂ ℝ (b : A) g := by
  let : CFCClass ℝ (cfc₂ ℝ (a : A) f)
  exact cast (by rw [h]) h'
  rw [_root_.cfc₂_comp (a : A) f g]
  congr 3
  simp only [cast_heq]
#align self_adjoint.cfc₂_comp selfAdjoint.cfc₂_comp

theorem selfAdjoint.cfc₂_comp_coe_mk {A : Type _} [Ring A] [StarRing A] [TopologicalSpace A]
    [Algebra ℝ A] (a : selfAdjoint A) (f g : C(ℝ, ℝ)) [∀ b : selfAdjoint A, CFCClass ℝ (b : A)]
    [Subsingleton (CFCCoreClass ℝ (cfc₂ ℝ (a : A) f))]
    -- alternatively: [compact_space (spectrum ℝ (cfc₂ (a : A) f))] [t2_space A]
    (h := cfc₂_real_isSelfAdjoint (a : A) f) :
    cfc₂ ℝ (a : A) (g.comp f) = cfc₂ ℝ ((⟨cfc₂ ℝ (a : A) f, h⟩ : selfAdjoint A) : A) g :=
  selfAdjoint.cfc₂_comp a _ f g rfl
#align self_adjoint.cfc₂_comp_coe_mk selfAdjoint.cfc₂_comp_coe_mk

@[simps]
def cfcℝ {A : Type _} [Ring A] [StarRing A] [TopologicalSpace A] [Algebra ℝ A] [StarModule ℝ A]
    (a : selfAdjoint A) [CFCClass ℝ (a : A)] : C(ℝ, ℝ) →L[ℝ] selfAdjoint A where
  toFun f := ⟨cfc₂ ℝ (a : A) f, cfc₂_real_isSelfAdjoint (a : A) f⟩
  map_add' f g := Subtype.ext <| by
    simp only [Subtype.coe_mk, AddSubgroup.coe_add, map_add (cfc₂ ℝ (a : A))]
  map_smul' r f :=
    Subtype.ext <| by simp only [map_smul, RingHom.id_apply, selfAdjoint.val_smul, Subtype.coe_mk]
  cont := continuous_induced_rng.mpr (cfc₂_continuous ℝ (a : A))
#align cfcℝ cfcℝ

theorem cfcℝ_comp {A : Type _} [Ring A] [StarRing A] [TopologicalSpace A] [Algebra ℝ A]
    [StarModule ℝ A] (a : selfAdjoint A) (f g : C(ℝ, ℝ)) [∀ b : selfAdjoint A, CFCClass ℝ (b : A)]
    [h : ∀ b : selfAdjoint A, Subsingleton (CFCCoreClass ℝ (b : A))] :
    cfcℝ a (g.comp f) = cfcℝ (cfcℝ a f) g := by
  ext
  simp only [cfcℝ_apply_coe]
  have : Subsingleton (CFCCoreClass ℝ (cfc₂ ℝ (a : A) f))
  simpa only using h ⟨cfc₂ ℝ (a : A) f, cfc₂_real_isSelfAdjoint (a : A) f⟩
  refine' selfAdjoint.cfc₂_comp _ _ _ _ rfl
#align cfcℝ_comp cfcℝ_comp

section Selfadjoint

variable {A : Type _} [Ring A] [StarRing A] [TopologicalSpace A] [Algebra ℝ A] [StarModule ℝ A]
  [∀ b : selfAdjoint A, CFCClass ℝ (b : A)]
  [∀ b : selfAdjoint A, Subsingleton (CFCCoreClass ℝ (b : A))]

theorem coe_cfcℝ_commute (a : selfAdjoint A) (f g : C(ℝ, ℝ)) : Commute (cfcℝ a f : A) (cfcℝ a g) :=
  by simpa only [cfcℝ_apply_coe] using cfc₂_commute (a : A) f g
#align coe_cfcℝ_commute coe_cfcℝ_commute

theorem cfcℝ_map_X (a : selfAdjoint A) : cfcℝ a X.toContinuousMap = a :=
  Subtype.ext (by rw [cfcℝ_apply_coe, cfc₂_map_X])
set_option linter.uppercaseLean3 false in
#align cfcℝ_map_X cfcℝ_map_X

theorem cfcℝ_map_id (a : selfAdjoint A) : cfcℝ a (ContinuousMap.id ℝ) = a := by
  rw [← X_toContinuousMap, cfcℝ_map_X]
#align cfcℝ_map_id cfcℝ_map_id

theorem cfcℝ_X_pow (a : selfAdjoint A) (n : ℕ) : cfcℝ a (X.toContinuousMap ^ n) = a ^ n := by
  ext
  rw [cfcℝ_apply_coe, ← toContinuousMapAlgHom_apply, map_pow, toContinuousMapAlgHom_apply,
    cfc₂_map_X, selfAdjoint.val_pow]
set_option linter.uppercaseLean3 false in
#align cfcℝ_X_pow cfcℝ_X_pow

theorem cfcℝ_pow_comm (a : selfAdjoint A) (n : ℕ) (f : C(ℝ, ℝ)) :
    cfcℝ (a ^ n) f = cfcℝ a (f.comp (X ^ n : ℝ[X]).toContinuousMap) := by
  rw [← toContinuousMapAlgHom_apply, map_pow, cfcℝ_comp, ← cfcℝ_X_pow]; rfl
#align cfcℝ_pow_comm cfcℝ_pow_comm

theorem cfcℝ_smul_comm (a : selfAdjoint A) (r : ℝ) (f : C(ℝ, ℝ)) :
    cfcℝ (r • a) f = cfcℝ a (f.comp (r • ContinuousMap.id ℝ)) := by
  rw [cfcℝ_comp, map_smul, cfcℝ_map_id]
#align cfcℝ_smul_comm cfcℝ_smul_comm

theorem cfcℝ_one (f : C(ℝ, ℝ)) : cfcℝ (1 : selfAdjoint A) f = f 1 • (1 : selfAdjoint A) := by
  ext
  rw [cfcℝ_apply_coe, selfAdjoint.val_smul]
  conv_rhs =>
    rw [selfAdjoint.val_one]
  have := map_one (cfc₂ ℝ ((1 : selfAdjoint A) : A) : C(ℝ, ℝ) →⋆ₐ[ℝ] A)
  rw [← this, ← map_smul]
  refine' cfc₂_eq_of_eqOn _ _
  simp only [ContinuousMap.coe_smul, ContinuousMap.coe_one, selfAdjoint.val_one]
  nontriviality A
  rw [spectrum.one_eq, Set.eqOn_singleton]
  simp [ContinuousMap.smul_apply (f 1)]
#align cfcℝ_one cfcℝ_one

theorem cfcℝ_neg_comm (a : selfAdjoint A) (f : C(ℝ, ℝ)) :
    cfcℝ (-a) f = cfcℝ a (f.comp (-ContinuousMap.id ℝ)) := by rw [cfcℝ_comp, map_neg, cfcℝ_map_id]
#align cfcℝ_neg_comm cfcℝ_neg_comm

/-
We should not actually define the positive parts and negative parts like this because then it won't
work for non-unital algebras. We first need to develop the non-unital cfc.

These are included here for the moment as a proof of concept, but are intended to be removed before
this PR is merged.
-/

noncomputable instance selfAdjoint.hasPosPart : PosPart (selfAdjoint A) where
  pos a := cfcℝ a (ContinuousMap.id ℝ ⊔ 0)
#align self_adjoint.has_pos_part selfAdjoint.hasPosPart

theorem selfAdjoint.pos_part_def (a : selfAdjoint A) : a⁺ = cfcℝ a (ContinuousMap.id ℝ ⊔ 0) :=
  rfl
#align self_adjoint.pos_part_def selfAdjoint.pos_part_def

theorem selfAdjoint.coe_pos_part (a : selfAdjoint A) :
    (↑(a⁺) : A) = cfc₂ ℝ (a : A) (ContinuousMap.id ℝ ⊔ 0) :=
  rfl
#align self_adjoint.coe_pos_part selfAdjoint.coe_pos_part

noncomputable instance selfAdjoint.hasNegPart : NegPart (selfAdjoint A)
    where neg a := cfcℝ a (-ContinuousMap.id ℝ ⊔ 0)
#align self_adjoint.has_neg_part selfAdjoint.hasNegPart

theorem selfAdjoint.neg_part_def (a : selfAdjoint A) : a⁻ = cfcℝ a (-ContinuousMap.id ℝ ⊔ 0) :=
  rfl
#align self_adjoint.neg_part_def selfAdjoint.neg_part_def

theorem selfAdjoint.coe_neg_part (a : selfAdjoint A) :
    (↑(a⁻) : A) = cfc₂ ℝ (a : A) (-ContinuousMap.id ℝ ⊔ 0) :=
  rfl
#align self_adjoint.coe_neg_part selfAdjoint.coe_neg_part

theorem selfAdjoint.neg_part_neg (a : selfAdjoint A) : (-a)⁻ = a⁺ := by
  rw [selfAdjoint.neg_part_def, selfAdjoint.pos_part_def, cfcℝ_neg_comm]
  congr
  ext x
  simp only [ContinuousMap.comp_apply, ContinuousMap.neg_apply, ContinuousMap.id_apply,
    ContinuousMap.sup_apply, neg_neg, ContinuousMap.zero_apply]
#align self_adjoint.neg_part_neg selfAdjoint.neg_part_neg

theorem selfAdjoint.pos_part_neg (a : selfAdjoint A) : (-a)⁺ = a⁻ := by
  simpa only [neg_neg] using (selfAdjoint.neg_part_neg (-a)).symm
#align self_adjoint.pos_part_neg selfAdjoint.pos_part_neg

theorem selfAdjoint.pos_part_sub_neg_part (a : selfAdjoint A) : a⁺ - a⁻ = a := by
  simp only [selfAdjoint.neg_part_def, selfAdjoint.pos_part_def, ← map_sub]
  simp only [sub_eq_add_neg, neg_sup_eq_neg_inf_neg, neg_neg, neg_zero]
  rw [add_comm, inf_add_sup, add_zero, cfcℝ_map_id]
#align self_adjoint.pos_part_sub_neg_part selfAdjoint.pos_part_sub_neg_part

theorem selfAdjoint.pos_part_mul_neg_part (a : selfAdjoint A) : (↑(a⁺) : A) * ↑(a⁻) = 0 := by
  simp only [selfAdjoint.pos_part_def, selfAdjoint.neg_part_def, cfcℝ_apply_coe, ← map_mul]
  convert map_zero (cfc₂ ℝ (a : A))
  ext x
  simp only [ContinuousMap.mul_apply, ContinuousMap.sup_apply, ContinuousMap.id_apply,
    ContinuousMap.zero_apply, ContinuousMap.neg_apply, mul_eq_zero, max_eq_right_iff,
    Right.neg_nonpos_iff]
  exact le_total _ _
#align self_adjoint.pos_part_mul_neg_part selfAdjoint.pos_part_mul_neg_part

-- it is essential to use coercions here because `self_adjoint A` can't have a `has_mul` instance
theorem selfAdjoint.neg_part_mul_pos_part (a : selfAdjoint A) : (↑(a⁻) : A) * ↑(a⁺) = 0 := by
  convert selfAdjoint.pos_part_mul_neg_part a using 1; exact coe_cfcℝ_commute _ _ _
#align self_adjoint.neg_part_mul_pos_part selfAdjoint.neg_part_mul_pos_part

end Selfadjoint
