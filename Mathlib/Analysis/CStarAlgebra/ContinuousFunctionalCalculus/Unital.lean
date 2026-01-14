/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
import Mathlib.Algebra.Algebra.StrictPositivity
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Algebra.Star.Real
import Mathlib.Topology.ContinuousMap.StarOrdered

/-!
# The continuous functional calculus

This file defines a generic API for the *continuous functional calculus* which is suitable in a wide
range of settings.

A continuous functional calculus for an element `a : A` in a topological `R`-algebra is a continuous
extension of the polynomial functional calculus (i.e., `Polynomial.aeval`) to continuous `R`-valued
functions on `spectrum R a`. More precisely, it is a continuous star algebra homomorphism
`C(spectrum R a, R) →⋆ₐ[R] A` that sends `(ContinuousMap.id R).restrict (spectrum R a)` to
`a`. In all cases of interest (e.g., when `spectrum R a` is compact and `R` is `ℝ≥0`, `ℝ`, or `ℂ`),
this is sufficient to uniquely determine the continuous functional calculus which is encoded in the
`ContinuousMap.UniqueHom` class.

Although these properties suffice to uniquely determine the continuous functional calculus, we
choose to bundle more information into the class itself. Namely, we include that the star algebra
homomorphism is a closed embedding, and also that the spectrum of the image of
`f : C(spectrum R a, R)` under this morphism is the range of `f`. In addition, the class specifies
a collection of continuous functional calculi for elements satisfying a given predicate
`p : A → Prop`, and we require that this predicate is preserved by the functional calculus.

Although `cfcHom : p a → C(spectrum R a, R) →*ₐ[R] A` is a necessity for getting the full power
out of the continuous functional calculus, this declaration will generally not be accessed directly
by the user. One reason for this is that `cfcHom` requires a proof of `p a` (indeed, if the
spectrum is empty, there cannot exist a star algebra homomorphism like this). Instead, we provide
the completely unbundled `cfc : (R → R) → A → A` which operates on bare functions and provides junk
values when either `a` does not satisfy the property `p`, or else when the function which is the
argument to `cfc` is not continuous on the spectrum of `a`.

This completely unbundled approach may give up some conveniences, but it allows for tremendous
freedom. In particular, `cfc f a` makes sense for *any* `a : A` and `f : R → R`. This is quite
useful in a variety of settings, but perhaps the most important is the following.
Besides being a star algebra homomorphism sending the identity to `a`, the key property enjoyed
by the continuous functional calculus is the *composition property*, which guarantees that
`cfc (g ∘ f) a = cfc g (cfc f a)` under suitable hypotheses on `a`, `f` and `g`. Note that this
theorem is nearly impossible to state nicely in terms of `cfcHom` (see `cfcHom_comp`). An
additional advantage of the unbundled approach is that expressions like `fun x : R ↦ x⁻¹` are valid
arguments to `cfc`, and a bundled continuous counterpart can only make sense when the spectrum of
`a` does not contain zero and when we have an `⁻¹` operation on the domain.

A reader familiar with C⋆-algebra theory may be somewhat surprised at the level of abstraction here.
For instance, why not require `A` to be an actual C⋆-algebra? Why define separate continuous
functional calculi for `R := ℂ`, `ℝ` or `ℝ≥0` instead of simply using the continuous functional
calculus for normal elements? The reason for both can be explained with a simple example,
`A := Matrix n n ℝ`. In Mathlib, matrices are not equipped with a norm (nor even a metric), and so
requiring `A` to be a C⋆-algebra is far too stringent. Likewise, `A` is not a `ℂ`-algebra, and so
it is impossible to consider the `ℂ`-spectrum of `a : Matrix n n ℝ`.

There is another, more practical reason to define separate continuous functional calculi for
different scalar rings. It gives us the ability to use functions defined on these types, and the
algebra of functions on them. For example, for `R := ℝ` it is quite natural to consider the
functions `(·⁺ : ℝ → ℝ)` and `(·⁻ : ℝ → ℝ)` because the functions `ℝ → ℝ` form a lattice ordered
group. If `a : A` is selfadjoint, and we define `a⁺ := cfc (·⁺ : ℝ → ℝ) a`, and likewise for `a⁻`,
then the properties `a⁺ * a⁻ = 0 = a⁻ * a⁺` and `a = a⁺ - a⁻` are trivial consequences of the
corresponding facts for functions. In contrast, if we had to do this using functions on `ℂ`, the
proofs of these facts would be much more cumbersome.

## Example

The canonical example of the continuous functional calculus is when `A := Matrix n n ℂ`, `R := ℂ`
and `p := IsStarNormal`. In this case, `spectrum ℂ a` consists of the eigenvalues of the normal
matrix `a : Matrix n n ℂ`, and, because this set is discrete, any function is continuous on the
spectrum. The continuous functional calculus allows us to make sense of expressions like `log a`
(`:= cfc log a`), and when `0 ∉ spectrum ℂ a`, we get the nice property `exp (log a) = a`, which
arises from the composition property `cfc exp (cfc log a) = cfc (exp ∘ log) a = cfc id a = a`, since
`exp ∘ log = id` *on the spectrum of `a`*. Of course, there are other ways to make sense of `exp`
and `log` for matrices (power series), and these agree with the continuous functional calculus.
In fact, given `f : C(spectrum ℂ a, ℂ)`, `cfc f a` amounts to diagonalizing `a` (possible since `a`
is normal), and applying `f` to the resulting diagonal entries. That is, if `a = u * d * star u`
with `u` a unitary matrix and `d` diagonal, then `cfc f a = u * d.map f * star u`.

In addition, if `a : Matrix n n ℂ` is positive semidefinite, then the `ℂ`-spectrum of `a` is
contained in (the range of the coercion of) `ℝ≥0`. In this case, we get a continuous functional
calculus with `R := ℝ≥0`. From this we can define `√a := cfc a NNReal.sqrt`, which is also
positive semidefinite (because `cfc` preserves the predicate), and this is truly a square root since
```
√a * √a = cfc NNReal.sqrt a * cfc NNReal.sqrt a =
  cfc (NNReal.sqrt ^ 2) a = cfc id a = a
```
The composition property allows us to show that, in fact, this is the *unique* positive semidefinite
square root of `a` because, if `b` is any positive semidefinite square root, then
```
b = cfc id b = cfc (NNReal.sqrt ∘ (· ^ 2)) b =
  cfc NNReal.sqrt (cfc b (· ^ 2)) = cfc NNReal.sqrt a = √a
```

## Main declarations

+ `ContinuousFunctionalCalculus R A (p : A → Prop)`: a class stating that every `a : A` satisfying
  `p a` has a star algebra homomorphism from the continuous `R`-valued functions on the
  `R`-spectrum of `a` into the algebra `A`. This map is a closed embedding, and satisfies the
  **spectral mapping theorem**.
+ `cfcHom : p a → C(spectrum R a, R) →⋆ₐ[R] A`: the underlying star algebra homomorphism for an
  element satisfying property `p`.
+ `cfc : (R → R) → A → A`: an unbundled version of `cfcHom` which takes the junk value `0` when
  `cfcHom` is not defined.
+ `cfcUnits`: builds a unit from `cfc f a` when `f` is nonzero and continuous on the
  spectrum of `a`.

## Main theorems

+ `cfc_comp : cfc (x ↦ g (f x)) a = cfc g (cfc f a)`
+ `cfc_polynomial`: the continuous functional calculus extends the polynomial functional calculus.

## Implementation details

Instead of defining a class depending on a term `a : A`, we register it for an `outParam` predicate
`p : A → Prop`, and then any element of `A` satisfying this predicate has the associated star
algebra homomorphism with the specified properties. In so doing we avoid a common pitfall:
dependence of the class on a term. This avoids annoying situations where `a b : A` are
propositionally equal, but not definitionally so, and hence Lean would not be able to automatically
identify the continuous functional calculi associated to these elements. In order to guarantee
the necessary properties, we require that the continuous functional calculus preserves this
predicate. That is, `p a → p (cfc f a)` for any function `f` continuous on the spectrum of `a`.

As stated above, the unbundled approach to `cfc` has its advantages. For instance, given an
expression `cfc f a`, the user is free to rewrite either `a` or `f` as desired with no possibility
of the expression ceasing to be defined. However, this unbundling also has some potential downsides.
In particular, by unbundling, proof requirements are deferred until the user calls the lemmas, most
of which have hypotheses both of `p a` and of `ContinuousOn f (spectrum R a)`.

In order to minimize burden to the user, we provide `autoParams` in terms of two tactics. Goals
related to continuity are dispatched by (a small wrapper around) `fun_prop`. As for goals involving
the predicate `p`, it should be noted that these will only ever be of the form `IsStarNormal a`,
`IsSelfAdjoint a` or `0 ≤ a`. For the moment we provide a rudimentary tactic to deal with these
goals, but it can be modified to become more sophisticated as the need arises.
-/

open Topology ContinuousMap

section Basic

/-- A star `R`-algebra `A` has a *continuous functional calculus* for elements satisfying the
property `p : A → Prop` if

+ for every such element `a : A` there is a star algebra homomorphism
  `cfcHom : C(spectrum R a, R) →⋆ₐ[R] A` sending the (restriction of) the identity map to `a`.
+ `cfcHom` is a closed embedding for which the spectrum of the image of function `f` is its range.
+ `cfcHom` preserves the property `p`.
+ `p 0` is true, which ensures among other things that `p ≠ fun _ ↦ False`.

The property `p` is marked as an `outParam` so that the user need not specify it. In practice,

+ for `R := ℂ`, we choose `p := IsStarNormal`,
+ for `R := ℝ`, we choose `p := IsSelfAdjoint`,
+ for `R := ℝ≥0`, we choose `p := (0 ≤ ·)`.

Instead of directly providing the data we opt instead for a `Prop` class. In all relevant cases,
the continuous functional calculus is uniquely determined, and utilizing this approach
prevents diamonds or problems arising from multiple instances. -/
class ContinuousFunctionalCalculus (R A : Type*) (p : outParam (A → Prop))
    [CommSemiring R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R]
    [Ring A] [StarRing A] [TopologicalSpace A] [Algebra R A] : Prop where
  predicate_zero : p 0
  [compactSpace_spectrum (a : A) : CompactSpace (spectrum R a)]
  spectrum_nonempty [Nontrivial A] (a : A) (ha : p a) : (spectrum R a).Nonempty
  exists_cfc_of_predicate : ∀ a, p a → ∃ φ : C(spectrum R a, R) →⋆ₐ[R] A,
    IsClosedEmbedding φ ∧ φ ((ContinuousMap.id R).restrict <| spectrum R a) = a ∧
      (∀ f, spectrum R (φ f) = Set.range f) ∧ ∀ f, p (φ f)

-- this instance should not be activated everywhere but it is useful when developing generic API
-- for the continuous functional calculus
scoped[ContinuousFunctionalCalculus]
attribute [instance] ContinuousFunctionalCalculus.compactSpace_spectrum

/-- A class guaranteeing that the continuous functional calculus is uniquely determined by the
properties that it is a continuous star algebra homomorphism mapping the (restriction of) the
identity to `a`. This is the necessary tool used to establish `cfcHom_comp` and the more common
variant `cfc_comp`.

This class has instances, which can be found in
`Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unique.lean`, in each of the common
cases `ℂ`, `ℝ` and `ℝ≥0` as a consequence of the Stone-Weierstrass theorem.

This class is separate from `ContinuousFunctionalCalculus` primarily because we will later use
`SpectrumRestricts` to derive an instance of `ContinuousFunctionalCalculus` on a scalar subring
from one on a larger ring (i.e., to go from a continuous functional calculus over `ℂ` for normal
elements to one over `ℝ` for selfadjoint elements), and proving this additional property is
preserved would be burdensome or impossible. -/
class ContinuousMap.UniqueHom (R A : Type*) [CommSemiring R] [StarRing R]
    [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A]
    [TopologicalSpace A] [Algebra R A] : Prop where
  eq_of_continuous_of_map_id (s : Set R) [CompactSpace s]
    (φ ψ : C(s, R) →⋆ₐ[R] A) (hφ : Continuous φ) (hψ : Continuous ψ)
    (h : φ (.restrict s <| .id R) = ψ (.restrict s <| .id R)) :
    φ = ψ

variable {R A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R] [MetricSpace R]
variable [IsTopologicalSemiring R] [ContinuousStar R] [TopologicalSpace A] [Ring A] [StarRing A]
variable [Algebra R A] [instCFC : ContinuousFunctionalCalculus R A p]

include instCFC in
lemma ContinuousFunctionalCalculus.isCompact_spectrum (a : A) :
    IsCompact (spectrum R a) :=
  isCompact_iff_compactSpace.mpr inferInstance

lemma StarAlgHom.ext_continuousMap [UniqueHom R A]
    (a : A) [CompactSpace (spectrum R a)] (φ ψ : C(spectrum R a, R) →⋆ₐ[R] A)
    (hφ : Continuous φ) (hψ : Continuous ψ)
    (h : φ (.restrict (spectrum R a) <| .id R) = ψ (.restrict (spectrum R a) <| .id R)) :
    φ = ψ :=
  UniqueHom.eq_of_continuous_of_map_id (spectrum R a) φ ψ hφ hψ h

section cfcHom

variable {a : A} (ha : p a)

-- Note: since `spectrum R a` is closed, we may always extend `f : C(spectrum R a, R)` to a function
-- of type `C(R, R)` by the Tietze extension theorem (assuming `R` is either `ℝ`, `ℂ` or `ℝ≥0`).

/-- The star algebra homomorphism underlying a instance of the continuous functional calculus;
a version for continuous functions on the spectrum.

In this case, the user must supply the fact that `a` satisfies the predicate `p`, for otherwise it
may be the case that no star algebra homomorphism exists. For instance if `R := ℝ` and `a` is an
element whose spectrum (in `ℂ`) is disjoint from `ℝ`, then `spectrum ℝ a = ∅` and so there can be
no star algebra homomorphism between these spaces.

While `ContinuousFunctionalCalculus` is stated in terms of these homomorphisms, in practice the
user should instead prefer `cfc` over `cfcHom`.
-/
noncomputable def cfcHom : C(spectrum R a, R) →⋆ₐ[R] A :=
  (ContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose

lemma cfcHom_isClosedEmbedding :
    IsClosedEmbedding <| (cfcHom ha : C(spectrum R a, R) →⋆ₐ[R] A) :=
  (ContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.1

@[fun_prop]
lemma cfcHom_continuous : Continuous (cfcHom ha : C(spectrum R a, R) →⋆ₐ[R] A) :=
  cfcHom_isClosedEmbedding ha |>.continuous

lemma cfcHom_id :
    cfcHom ha ((ContinuousMap.id R).restrict <| spectrum R a) = a :=
  (ContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.2.1

/-- The **spectral mapping theorem** for the continuous functional calculus. -/
lemma cfcHom_map_spectrum (f : C(spectrum R a, R)) :
    spectrum R (cfcHom ha f) = Set.range f :=
  (ContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.2.2.1 f

lemma cfcHom_predicate (f : C(spectrum R a, R)) :
    p (cfcHom ha f) :=
  (ContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.2.2.2 f

open scoped ContinuousFunctionalCalculus in
lemma cfcHom_eq_of_continuous_of_map_id [UniqueHom R A]
    (φ : C(spectrum R a, R) →⋆ₐ[R] A) (hφ₁ : Continuous φ)
    (hφ₂ : φ (.restrict (spectrum R a) <| .id R) = a) : cfcHom ha = φ :=
  (cfcHom ha).ext_continuousMap a φ (cfcHom_isClosedEmbedding ha).continuous hφ₁ <| by
    rw [cfcHom_id ha, hφ₂]

theorem cfcHom_comp [UniqueHom R A] (f : C(spectrum R a, R))
    (f' : C(spectrum R a, spectrum R (cfcHom ha f)))
    (hff' : ∀ x, f x = f' x) (g : C(spectrum R (cfcHom ha f), R)) :
    cfcHom ha (g.comp f') = cfcHom (cfcHom_predicate ha f) g := by
  let φ : C(spectrum R (cfcHom ha f), R) →⋆ₐ[R] A :=
    (cfcHom ha).comp <| ContinuousMap.compStarAlgHom' R R f'
  suffices cfcHom (cfcHom_predicate ha f) = φ from DFunLike.congr_fun this.symm g
  refine cfcHom_eq_of_continuous_of_map_id (cfcHom_predicate ha f) φ ?_ ?_
  · exact (cfcHom_isClosedEmbedding ha).continuous.comp f'.continuous_precomp
  · simp only [φ, StarAlgHom.comp_apply, ContinuousMap.compStarAlgHom'_apply]
    congr
    ext x
    simp [hff']

end cfcHom

section cfcL

/-- `cfcHom` bundled as a continuous linear map. -/
@[simps apply]
noncomputable def cfcL {a : A} (ha : p a) : C(spectrum R a, R) →L[R] A :=
  { cfcHom ha with
    toFun := cfcHom ha
    map_smul' := map_smul _
    cont := (cfcHom_isClosedEmbedding ha).continuous }

end cfcL

section CFC

open scoped Classical in
/-- This is the *continuous functional calculus* of an element `a : A` applied to bare functions.
When either `a` does not satisfy the predicate `p` (i.e., `a` is not `IsStarNormal`,
`IsSelfAdjoint`, or `0 ≤ a` when `R` is `ℂ`, `ℝ`, or `ℝ≥0`, respectively), or when `f : R → R` is
not continuous on the spectrum of `a`, then `cfc f a` returns the junk value `0`.

This is the primary declaration intended for widespread use of the continuous functional calculus,
and all the API applies to this declaration. For more information, see the module documentation
for `Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital`. -/
noncomputable irreducible_def cfc (f : R → R) (a : A) : A :=
  if h : p a ∧ ContinuousOn f (spectrum R a)
    then cfcHom h.1 ⟨_, h.2.restrict⟩
    else 0

variable (f g : R → R) (a : A) (ha : p a := by cfc_tac)
variable (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
variable (hg : ContinuousOn g (spectrum R a) := by cfc_cont_tac)

lemma cfc_apply : cfc f a = cfcHom (a := a) ha ⟨_, hf.restrict⟩ := by
  rw [cfc_def, dif_pos ⟨ha, hf⟩]

lemma cfc_apply_pi {ι : Type*} (f : ι → R → R) (a : A) (ha : p a := by cfc_tac)
    (hf : ∀ i, ContinuousOn (f i) (spectrum R a) := by cfc_cont_tac) :
    (fun i => cfc (f i) a) = (fun i => cfcHom (a := a) ha ⟨_, (hf i).restrict⟩) := by
  ext i
  simp only [cfc_apply (f i) a ha (hf i)]

lemma cfc_apply_of_not_and {f : R → R} (a : A) (ha : ¬ (p a ∧ ContinuousOn f (spectrum R a))) :
    cfc f a = 0 := by
  rw [cfc_def, dif_neg ha]

lemma cfc_apply_of_not_predicate {f : R → R} (a : A) (ha : ¬ p a) :
    cfc f a = 0 := by
  rw [cfc_def, dif_neg (not_and_of_not_left _ ha)]

lemma cfc_apply_of_not_continuousOn {f : R → R} (a : A) (hf : ¬ ContinuousOn f (spectrum R a)) :
    cfc f a = 0 := by
  rw [cfc_def, dif_neg (not_and_of_not_right _ hf)]

lemma cfcHom_eq_cfc_extend {a : A} (g : R → R) (ha : p a) (f : C(spectrum R a, R)) :
    cfcHom ha f = cfc (Function.extend Subtype.val f g) a := by
  have h : f = (spectrum R a).restrict (Function.extend Subtype.val f g) := by
    ext; simp
  have hg : ContinuousOn (Function.extend Subtype.val f g) (spectrum R a) :=
    continuousOn_iff_continuous_restrict.mpr <| h ▸ map_continuous f
  rw [cfc_apply ..]
  congr!

lemma cfc_eq_cfcL {a : A} {f : R → R} (ha : p a) (hf : ContinuousOn f (spectrum R a)) :
    cfc f a = cfcL ha ⟨_, hf.restrict⟩ := by
  rw [cfc_def, dif_pos ⟨ha, hf⟩, cfcL_apply]

/-- A version of `cfc_apply` in terms of `ContinuousMap.mkD` -/
lemma cfc_apply_mkD :
    cfc f a = cfcHom (a := a) ha (mkD ((spectrum R a).restrict f) 0) := by
  by_cases hf : ContinuousOn f (spectrum R a)
  · rw [cfc_apply f a, mkD_of_continuousOn hf]
  · rw [cfc_apply_of_not_continuousOn a hf, mkD_of_not_continuousOn hf,
      map_zero]

/-- A version of `cfc_eq_cfcL` in terms of `ContinuousMapZero.mkD` -/
lemma cfc_eq_cfcL_mkD :
    cfc f a = cfcL (a := a) ha (mkD ((spectrum R a).restrict f) 0) :=
  cfc_apply_mkD _ _

lemma cfc_cases (P : A → Prop) (a : A) (f : R → R) (h₀ : P 0)
    (haf : (hf : ContinuousOn f (spectrum R a)) → (ha : p a) → P (cfcHom ha ⟨_, hf.restrict⟩)) :
    P (cfc f a) := by
  by_cases h : p a ∧ ContinuousOn f (spectrum R a)
  · rw [cfc_apply f a h.1 h.2]
    exact haf h.2 h.1
  · simp only [not_and_or] at h
    obtain (h | h) := h
    · rwa [cfc_apply_of_not_predicate _ h]
    · rwa [cfc_apply_of_not_continuousOn _ h]

lemma cfc_commute_cfc (f g : R → R) (a : A) : Commute (cfc f a) (cfc g a) := by
  refine cfc_cases (fun x ↦ Commute x (cfc g a)) a f (by simp) fun hf ha ↦ ?_
  refine cfc_cases (fun x ↦ Commute _ x) a g (by simp) fun hg _ ↦ ?_
  exact Commute.all _ _ |>.map _

variable (R) in
lemma cfc_id (ha : p a := by cfc_tac) : cfc (id : R → R) a = a :=
  cfc_apply (id : R → R) a ▸ cfcHom_id (p := p) ha

variable (R) in
lemma cfc_id' (ha : p a := by cfc_tac) : cfc (fun x : R ↦ x) a = a := cfc_id R a

/-- The **spectral mapping theorem** for the continuous functional calculus. -/
lemma cfc_map_spectrum (ha : p a := by cfc_tac)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) :
    spectrum R (cfc f a) = f '' spectrum R a := by
  simp [cfc_apply f a, cfcHom_map_spectrum (p := p)]

lemma cfc_const (r : R) (a : A) (ha : p a := by cfc_tac) :
    cfc (fun _ ↦ r) a = algebraMap R A r := by
  rw [cfc_apply (fun _ : R ↦ r) a, ← AlgHomClass.commutes (cfcHom ha (p := p)) r]
  congr

variable (R) in
include R in
lemma cfc_predicate_zero : p 0 :=
  ContinuousFunctionalCalculus.predicate_zero (R := R)

lemma cfc_predicate (f : R → R) (a : A) : p (cfc f a) :=
  cfc_cases p a f (cfc_predicate_zero R) fun _ _ ↦ cfcHom_predicate ..

lemma cfc_predicate_algebraMap (r : R) : p (algebraMap R A r) :=
  cfc_const r (0 : A) (cfc_predicate_zero R) ▸ cfc_predicate (fun _ ↦ r) 0

variable (R) in
include R in
lemma cfc_predicate_one : p 1 :=
  map_one (algebraMap R A) ▸ cfc_predicate_algebraMap (1 : R)

lemma cfc_congr {f g : R → R} {a : A} (hfg : (spectrum R a).EqOn f g) :
    cfc f a = cfc g a := by
  by_cases h : p a ∧ ContinuousOn g (spectrum R a)
  · rw [cfc_apply (ha := h.1) (hf := h.2.congr hfg), cfc_apply (ha := h.1) (hf := h.2)]
    congr 2
    exact Set.restrict_eq_iff.mpr hfg
  · obtain (ha | hg) := not_and_or.mp h
    · simp [cfc_apply_of_not_predicate a ha]
    · rw [cfc_apply_of_not_continuousOn a hg, cfc_apply_of_not_continuousOn]
      exact fun hf ↦ hg (hf.congr hfg.symm)

lemma eqOn_of_cfc_eq_cfc {f g : R → R} {a : A} (h : cfc f a = cfc g a)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (hg : ContinuousOn g (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    (spectrum R a).EqOn f g := by
  rw [cfc_apply f a, cfc_apply g a] at h
  have := (cfcHom_isClosedEmbedding (show p a from ha) (R := R)).injective h
  intro x hx
  congrm($(this) ⟨x, hx⟩)

variable {a f g} in
include ha hf hg in
lemma cfc_eq_cfc_iff_eqOn : cfc f a = cfc g a ↔ (spectrum R a).EqOn f g :=
  ⟨eqOn_of_cfc_eq_cfc, cfc_congr⟩

variable (R)

include ha in
lemma cfc_one : cfc (1 : R → R) a = 1 :=
  cfc_apply (1 : R → R) a ▸ map_one (cfcHom (show p a from ha))

include ha in
lemma cfc_const_one : cfc (fun _ : R ↦ 1) a = 1 := cfc_one R a

@[simp]
lemma cfc_zero : cfc (0 : R → R) a = 0 := by
  by_cases ha : p a
  · exact cfc_apply (0 : R → R) a ▸ map_zero (cfcHom ha)
  · rw [cfc_apply_of_not_predicate a ha]

@[simp]
lemma cfc_const_zero : cfc (fun _ : R ↦ 0) a = 0 :=
  cfc_zero R a

variable {R}

lemma cfc_mul (f g : R → R) (a : A) (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (hg : ContinuousOn g (spectrum R a) := by cfc_cont_tac) :
    cfc (fun x ↦ f x * g x) a = cfc f a * cfc g a := by
  by_cases ha : p a
  · rw [cfc_apply f a, cfc_apply g a, ← map_mul, cfc_apply _ a]
    congr
  · simp [cfc_apply_of_not_predicate a ha]

lemma cfc_pow (f : R → R) (n : ℕ) (a : A)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc (fun x ↦ (f x) ^ n) a = cfc f a ^ n := by
  rw [cfc_apply f a, ← map_pow, cfc_apply _ a]
  congr

lemma cfc_add (f g : R → R) (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (hg : ContinuousOn g (spectrum R a) := by cfc_cont_tac) :
    cfc (fun x ↦ f x + g x) a = cfc f a + cfc g a := by
  by_cases ha : p a
  · rw [cfc_apply f a, cfc_apply g a, ← map_add, cfc_apply _ a]
    congr
  · simp [cfc_apply_of_not_predicate a ha]

lemma cfc_const_add (r : R) (f : R → R) (a : A)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc (fun x => r + f x) a = algebraMap R A r + cfc f a := by
  have : (fun z => r + f z) = (fun z => (fun _ => r) z + f z) := by ext; simp
  rw [this, cfc_add a _ _ (continuousOn_const (c := r)) hf, cfc_const r a ha]

lemma cfc_add_const (r : R) (f : R → R) (a : A)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc (fun x => f x + r) a = cfc f a + algebraMap R A r := by
  rw [add_comm (cfc f a)]
  conv_lhs => simp only [add_comm]
  exact cfc_const_add r f a hf ha

open Finset in
lemma cfc_sum {ι : Type*} (f : ι → R → R) (a : A) (s : Finset ι)
    (hf : ∀ i ∈ s, ContinuousOn (f i) (spectrum R a) := by cfc_cont_tac) :
    cfc (∑ i ∈ s, f i)  a = ∑ i ∈ s, cfc (f i) a := by
  by_cases ha : p a
  · have hsum : s.sum f = fun z => ∑ i ∈ s, f i z := by ext; simp
    have hf' : ContinuousOn (∑ i : s, f i) (spectrum R a) := by
      rw [sum_coe_sort s, hsum]
      exact continuousOn_finset_sum s fun i hi => hf i hi
    rw [← sum_coe_sort s, ← sum_coe_sort s]
    rw [cfc_apply_pi _ a ha (fun ⟨i, hi⟩ => hf i hi), ← map_sum, cfc_apply _ a ha hf']
    congr 1
    ext
    simp
  · simp [cfc_apply_of_not_predicate a ha]

open Finset in
lemma cfc_sum_univ {ι : Type*} [Fintype ι] (f : ι → R → R) (a : A)
    (hf : ∀ i, ContinuousOn (f i) (spectrum R a) := by cfc_cont_tac) :
    cfc (∑ i, f i) a = ∑ i, cfc (f i) a :=
  cfc_sum f a _ fun i _ ↦ hf i

lemma cfc_smul {S : Type*} [SMul S R] [ContinuousConstSMul S R]
    [SMulZeroClass S A] [IsScalarTower S R A] [IsScalarTower S R (R → R)]
    (s : S) (f : R → R) (a : A) (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) :
    cfc (fun x ↦ s • f x) a = s • cfc f a := by
  by_cases ha : p a
  · rw [cfc_apply f a, cfc_apply _ a]
    simp_rw [← Pi.smul_def, ← smul_one_smul R s _]
    rw [← map_smul]
    congr
  · simp [cfc_apply_of_not_predicate a ha]

lemma cfc_const_mul (r : R) (f : R → R) (a : A)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) :
    cfc (fun x ↦ r * f x) a = r • cfc f a :=
  cfc_smul r f a

lemma cfc_star (f : R → R) (a : A) : cfc (fun x ↦ star (f x)) a = star (cfc f a) := by
  by_cases h : p a ∧ ContinuousOn f (spectrum R a)
  · obtain ⟨ha, hf⟩ := h
    rw [cfc_apply f a, ← map_star, cfc_apply _ a]
    congr
  · obtain (ha | hf) := not_and_or.mp h
    · simp [cfc_apply_of_not_predicate a ha]
    · rw [cfc_apply_of_not_continuousOn a hf, cfc_apply_of_not_continuousOn, star_zero]
      exact fun hf_star ↦ hf <| by simpa using hf_star.star

lemma cfc_pow_id (a : A) (n : ℕ) (ha : p a := by cfc_tac) : cfc (· ^ n : R → R) a = a ^ n := by
  rw [cfc_pow .., cfc_id' ..]

lemma cfc_smul_id {S : Type*} [SMul S R] [ContinuousConstSMul S R]
    [SMulZeroClass S A] [IsScalarTower S R A] [IsScalarTower S R (R → R)]
    (s : S) (a : A) (ha : p a := by cfc_tac) : cfc (s • · : R → R) a = s • a := by
  rw [cfc_smul .., cfc_id' ..]

lemma cfc_const_mul_id (r : R) (a : A) (ha : p a := by cfc_tac) : cfc (r * ·) a = r • a :=
  cfc_smul_id r a

include ha in
lemma cfc_star_id : cfc (star · : R → R) a = star a := by
  rw [cfc_star .., cfc_id' ..]

variable (R) in
theorem range_cfc_eq_range_cfcHom [StarModule R A] {a : A} (ha : p a) :
    Set.range (cfc (R := R) · a) = (cfcHom ha (R := R)).range := by
  ext
  constructor
  all_goals rintro ⟨f, rfl⟩
  · exact cfc_cases _ a f (zero_mem _) fun hf ha ↦ ⟨_, rfl⟩
  · exact ⟨Subtype.val.extend f 0, cfcHom_eq_cfc_extend _ ha _ |>.symm⟩

section Polynomial
open Polynomial

lemma cfc_eval_X (ha : p a := by cfc_tac) : cfc (X : R[X]).eval a = a := by
  simpa using cfc_id R a

lemma cfc_eval_C (r : R) (a : A) (ha : p a := by cfc_tac) :
    cfc (C r).eval a = algebraMap R A r := by
  simp [cfc_const r a]

lemma cfc_map_polynomial (q : R[X]) (f : R → R) (a : A) (ha : p a := by cfc_tac)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) :
    cfc (fun x ↦ q.eval (f x)) a = aeval (cfc f a) q := by
  induction q using Polynomial.induction_on with
  | C r => simp [cfc_const r a]
  | add q₁ q₂ hq₁ hq₂ =>
    simp only [eval_add, map_add, ← hq₁, ← hq₂, cfc_add a (q₁.eval <| f ·) (q₂.eval <| f ·)]
  | monomial n r _ =>
    simp only [eval_mul, eval_C, eval_X_pow, map_mul, aeval_C, map_pow, aeval_X]
    rw [cfc_const_mul .., cfc_pow _ (n + 1) _, ← smul_eq_mul, algebraMap_smul]

lemma cfc_polynomial (q : R[X]) (a : A) (ha : p a := by cfc_tac) :
    cfc q.eval a = aeval a q := by
  rw [cfc_map_polynomial .., cfc_id' ..]

end Polynomial

section Comp

variable [UniqueHom R A]

lemma cfc_comp (g f : R → R) (a : A) (ha : p a := by cfc_tac)
    (hg : ContinuousOn g (f '' spectrum R a) := by cfc_cont_tac)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) :
    cfc (g ∘ f) a = cfc g (cfc f a) := by
  have := hg.comp hf <| (spectrum R a).mapsTo_image f
  have sp_eq : spectrum R (cfcHom (show p a from ha) (ContinuousMap.mk _ hf.restrict)) =
      f '' (spectrum R a) := by
    rw [cfcHom_map_spectrum (by exact ha) _]
    ext
    simp
  rw [cfc_apply .., cfc_apply f a,
    cfc_apply _ _ (cfcHom_predicate (show p a from ha) _) (by convert hg), ← cfcHom_comp _ _]
  swap
  · exact ContinuousMap.mk _ <| hf.restrict.codRestrict fun x ↦ by rw [sp_eq]; use x.1; simp
  · congr
  · exact fun _ ↦ rfl

lemma cfc_comp' (g f : R → R) (a : A) (hg : ContinuousOn g (f '' spectrum R a) := by cfc_cont_tac)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc (g <| f ·) a = cfc g (cfc f a) :=
  cfc_comp g f a

lemma cfc_comp_pow (f : R → R) (n : ℕ) (a : A)
    (hf : ContinuousOn f ((· ^ n) '' (spectrum R a)) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc (f <| · ^ n) a = cfc f (a ^ n) := by
  rw [cfc_comp' .., cfc_pow_id ..]

lemma cfc_comp_smul {S : Type*} [SMul S R] [ContinuousConstSMul S R] [SMulZeroClass S A]
    [IsScalarTower S R A] [IsScalarTower S R (R → R)] (s : S) (f : R → R) (a : A)
    (hf : ContinuousOn f ((s • ·) '' (spectrum R a)) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc (f <| s • ·) a = cfc f (s • a) := by
  rw [cfc_comp' .., cfc_smul_id ..]

lemma cfc_comp_const_mul (r : R) (f : R → R) (a : A)
    (hf : ContinuousOn f ((r * ·) '' (spectrum R a)) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc (f <| r * ·) a = cfc f (r • a) := by
  rw [cfc_comp' .., cfc_const_mul_id ..]

lemma cfc_comp_star (f : R → R) (a : A)
    (hf : ContinuousOn f (star '' (spectrum R a)) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc (f <| star ·) a = cfc f (star a) := by
  rw [cfc_comp' .., cfc_star_id ..]

open Polynomial in
lemma cfc_comp_polynomial (q : R[X]) (f : R → R) (a : A)
    (hf : ContinuousOn f (q.eval '' (spectrum R a)) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc (f <| q.eval ·) a = cfc f (aeval a q) := by
  rw [cfc_comp' .., cfc_polynomial ..]

end Comp

lemma CFC.eq_algebraMap_of_spectrum_subset_singleton (r : R) (h_spec : spectrum R a ⊆ {r})
    (ha : p a := by cfc_tac) : a = algebraMap R A r := by
  simpa [cfc_id R a, cfc_const r a] using
    cfc_congr (f := id) (g := fun _ : R ↦ r) (a := a) fun x hx ↦ by simpa using h_spec hx

lemma CFC.eq_zero_of_spectrum_subset_zero (h_spec : spectrum R a ⊆ {0}) (ha : p a := by cfc_tac) :
    a = 0 := by
  simpa using eq_algebraMap_of_spectrum_subset_singleton a 0 h_spec

lemma CFC.eq_one_of_spectrum_subset_one (h_spec : spectrum R a ⊆ {1}) (ha : p a := by cfc_tac) :
    a = 1 := by
  simpa using eq_algebraMap_of_spectrum_subset_singleton a 1 h_spec

include instCFC in
lemma CFC.spectrum_algebraMap_subset (r : R) : spectrum R (algebraMap R A r) ⊆ {r} := by
  rw [← cfc_const r 0 (cfc_predicate_zero R),
    cfc_map_spectrum (fun _ ↦ r) 0 (cfc_predicate_zero R)]
  rintro - ⟨x, -, rfl⟩
  simp

include instCFC in
lemma CFC.spectrum_algebraMap_eq [Nontrivial A] (r : R) :
    spectrum R (algebraMap R A r) = {r} := by
  have hp : p 0 := cfc_predicate_zero R
  rw [← cfc_const r 0 hp, cfc_map_spectrum (fun _ => r) 0 hp]
  exact Set.Nonempty.image_const (⟨0, spectrum.zero_mem (R := R) not_isUnit_zero⟩) _

include instCFC in
lemma CFC.spectrum_zero_eq [Nontrivial A] :
    spectrum R (0 : A) = {0} := by
  have : (0 : A) = algebraMap R A 0 := Eq.symm (RingHom.map_zero (algebraMap R A))
  rw [this, spectrum_algebraMap_eq]

include instCFC in
lemma CFC.spectrum_one_eq [Nontrivial A] :
    spectrum R (1 : A) = {1} := by
  have : (1 : A) = algebraMap R A 1 := Eq.symm (RingHom.map_one (algebraMap R A))
  rw [this, spectrum_algebraMap_eq]

@[simp]
lemma cfc_algebraMap (r : R) (f : R → R) : cfc f (algebraMap R A r) = algebraMap R A (f r) := by
  have h₁ : ContinuousOn f (spectrum R (algebraMap R A r)) :=
  continuousOn_singleton _ _ |>.mono <| CFC.spectrum_algebraMap_subset r
  rw [cfc_apply f (algebraMap R A r) (cfc_predicate_algebraMap r),
    ← AlgHomClass.commutes (cfcHom (p := p) (cfc_predicate_algebraMap r)) (f r)]
  congr
  ext ⟨x, hx⟩
  apply CFC.spectrum_algebraMap_subset r at hx
  simp_all

@[simp] lemma cfc_apply_zero {f : R → R} : cfc f (0 : A) = algebraMap R A (f 0) := by
  simpa using cfc_algebraMap (A := A) 0 f

@[simp] lemma cfc_apply_one {f : R → R} : cfc f (1 : A) = algebraMap R A (f 1) := by
  simpa using cfc_algebraMap (A := A) 1 f

@[simp]
instance IsStarNormal.cfc_map (f : R → R) (a : A) : IsStarNormal (cfc f a) where
  star_comm_self := by
    rw [Commute, SemiconjBy]
    by_cases h : ContinuousOn f (spectrum R a)
    · rw [← cfc_star, ← cfc_mul .., ← cfc_mul ..]
      congr! 2
      exact mul_comm _ _
    · simp [cfc_apply_of_not_continuousOn a h]

-- The following two lemmas are just `cfc_predicate`, but specific enough for the `@[simp]` tag.
@[simp]
protected lemma IsSelfAdjoint.cfc [ContinuousFunctionalCalculus R A IsSelfAdjoint]
    {f : R → R} {a : A} : IsSelfAdjoint (cfc f a) :=
  cfc_predicate _ _

@[simp]
lemma cfc_nonneg_of_predicate [LE A]
    [ContinuousFunctionalCalculus R A (0 ≤ ·)] {f : R → R} {a : A} : 0 ≤ cfc f a :=
  cfc_predicate _ _

variable (R) in
/-- In an `R`-algebra with a continuous functional calculus, every element satisfying the predicate
has nonempty `R`-spectrum. -/
lemma CFC.spectrum_nonempty [Nontrivial A] (a : A) (ha : p a := by cfc_tac) :
    (spectrum R a).Nonempty := by
  by_contra! h
  apply one_ne_zero (α := A)
  rw [← cfc_one R a, ← cfc_zero R a]
  exact cfc_congr fun x hx ↦ by simp_all

end CFC

end Basic

section Inv

variable {R A : Type*} {p : A → Prop} [Semifield R] [StarRing R] [MetricSpace R]
variable [IsTopologicalSemiring R] [ContinuousStar R] [TopologicalSpace A]
variable [Ring A] [StarRing A] [Algebra R A] [ContinuousFunctionalCalculus R A p]

lemma isUnit_cfc_iff (f : R → R) (a : A) (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) : IsUnit (cfc f a) ↔ ∀ x ∈ spectrum R a, f x ≠ 0 := by
  rw [← spectrum.zero_notMem_iff R, cfc_map_spectrum ..]
  simp

alias ⟨_, isUnit_cfc⟩ := isUnit_cfc_iff

variable [ContinuousInv₀ R] (f : R → R) (a : A)

/-- Bundle `cfc f a` into a unit given a proof that `f` is nonzero on the spectrum of `a`. -/
@[simps]
noncomputable def cfcUnits (hf' : ∀ x ∈ spectrum R a, f x ≠ 0)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) : Aˣ where
  val := cfc f a
  inv := cfc (fun x ↦ (f x)⁻¹) a
  val_inv := by
    rw [← cfc_mul .., ← cfc_one R a]
    exact cfc_congr fun _ _ ↦ by aesop
  inv_val := by
    rw [← cfc_mul .., ← cfc_one R a]
    exact cfc_congr fun _ _ ↦ by aesop

lemma cfcUnits_pow (hf' : ∀ x ∈ spectrum R a, f x ≠ 0) (n : ℕ)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    (cfcUnits f a hf') ^ n =
      cfcUnits _ _ (forall₂_imp (fun _ _ ↦ pow_ne_zero n) hf') (hf := hf.pow n) := by
  ext
  cases n with
  | zero => simp [cfc_const_one R a]
  | succ n => simp [cfc_pow f _ a]

lemma cfc_inv (hf' : ∀ x ∈ spectrum R a, f x ≠ 0)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc (fun x ↦ (f x) ⁻¹) a = Ring.inverse (cfc f a) := by
  rw [← val_inv_cfcUnits f a hf', ← val_cfcUnits f a hf', Ring.inverse_unit]

lemma cfc_inv_id (a : Aˣ) (ha : p a := by cfc_tac) :
    cfc (fun x ↦ x⁻¹ : R → R) (a : A) = a⁻¹ := by
  rw [← Ring.inverse_unit]
  convert cfc_inv (id : R → R) (a : A) ?_
  · exact (cfc_id R (a : A)).symm
  · rintro x hx rfl
    exact spectrum.zero_notMem R a.isUnit hx

lemma cfc_map_div (f g : R → R) (a : A) (hg' : ∀ x ∈ spectrum R a, g x ≠ 0)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (hg : ContinuousOn g (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc (fun x ↦ f x / g x) a = cfc f a * Ring.inverse (cfc g a) := by
  simp only [div_eq_mul_inv]
  rw [cfc_mul .., cfc_inv g a hg']

section ContinuousOnInvSpectrum
-- TODO: this section should probably be moved to another file altogether

variable {R A : Type*} [Semifield R] [Ring A] [TopologicalSpace R] [ContinuousInv₀ R]
variable [Algebra R A]

@[fun_prop]
lemma Units.continuousOn_inv₀_spectrum (a : Aˣ) : ContinuousOn (· ⁻¹) (spectrum R (a : A)) :=
  continuousOn_inv₀.mono <| by
    simpa only [Set.subset_compl_singleton_iff] using spectrum.zero_notMem R a.isUnit

@[fun_prop]
lemma Units.continuousOn_zpow₀_spectrum [ContinuousMul R] (a : Aˣ) (n : ℤ) :
    ContinuousOn (· ^ n) (spectrum R (a : A)) :=
  (continuousOn_zpow₀ n).mono <| by
    simpa only [Set.subset_compl_singleton_iff] using spectrum.zero_notMem R a.isUnit

end ContinuousOnInvSpectrum

lemma cfcUnits_zpow (hf' : ∀ x ∈ spectrum R a, f x ≠ 0) (n : ℤ)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    (cfcUnits f a hf') ^ n =
      cfcUnits (f ^ n) a (forall₂_imp (fun _ _ ↦ zpow_ne_zero n) hf')
        (hf.zpow₀ n (forall₂_imp (fun _ _ ↦ Or.inl) hf')) := by
  cases n with
  | ofNat _ => simpa using cfcUnits_pow f a hf' _
  | negSucc n =>
    simp only [zpow_negSucc, ← inv_pow]
    ext
    exact cfc_pow (hf := hf.inv₀ hf') .. |>.symm

lemma cfc_zpow (a : Aˣ) (n : ℤ) (ha : p a := by cfc_tac) :
    cfc (fun x : R ↦ x ^ n) (a : A) = ↑(a ^ n) := by
  cases n with
  | ofNat n => simpa using cfc_pow_id (a : A) n
  | negSucc n =>
    simp only [zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val]
    have := cfc_pow (fun x ↦ x⁻¹ : R → R) (n + 1) (a : A)
    exact this.trans <| congr($(cfc_inv_id a) ^ (n + 1))

variable [UniqueHom R A]

lemma cfc_comp_inv (f : R → R) (a : Aˣ)
    (hf : ContinuousOn f ((·⁻¹) '' (spectrum R (a : A))) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) :
    cfc (fun x ↦ f x⁻¹) (a : A) = cfc f (↑a⁻¹ : A) := by
  rw [cfc_comp' .., cfc_inv_id _]

lemma cfc_comp_zpow (f : R → R) (n : ℤ) (a : Aˣ)
    (hf : ContinuousOn f ((· ^ n) '' (spectrum R (a : A))) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) :
    cfc (fun x ↦ f (x ^ n)) (a : A) = cfc f (↑(a ^ n) : A) := by
  rw [cfc_comp' .., cfc_zpow a]

end Inv

section Neg

variable {R A : Type*} {p : A → Prop} [CommRing R] [StarRing R] [MetricSpace R]
variable [IsTopologicalRing R] [ContinuousStar R] [TopologicalSpace A]
variable [Ring A] [StarRing A] [Algebra R A] [ContinuousFunctionalCalculus R A p]
variable (f g : R → R) (a : A) (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
variable (hg : ContinuousOn g (spectrum R a) := by cfc_cont_tac)

include hf hg in
lemma cfc_sub : cfc (fun x ↦ f x - g x) a = cfc f a - cfc g a := by
  by_cases ha : p a
  · rw [cfc_apply f a, cfc_apply g a, ← map_sub, cfc_apply ..]
    congr
  · simp [cfc_apply_of_not_predicate a ha]

lemma cfc_neg : cfc (fun x ↦ - (f x)) a = - (cfc f a) := by
  by_cases h : p a ∧ ContinuousOn f (spectrum R a)
  · obtain ⟨ha, hf⟩ := h
    rw [cfc_apply f a, ← map_neg, cfc_apply ..]
    congr
  · obtain (ha | hf) := not_and_or.mp h
    · simp [cfc_apply_of_not_predicate a ha]
    · rw [cfc_apply_of_not_continuousOn a hf, cfc_apply_of_not_continuousOn, neg_zero]
      exact fun hf_neg ↦ hf <| by simpa using hf_neg.neg

lemma cfc_neg_id (ha : p a := by cfc_tac) : cfc (- · : R → R) a = -a := by
  rw [cfc_neg _ a, cfc_id' R a]

variable [UniqueHom R A]

lemma cfc_comp_neg (hf : ContinuousOn f ((-·) '' (spectrum R (a : A))) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) : cfc (f <| - ·) a = cfc f (-a) := by
  rw [cfc_comp' .., cfc_neg_id _]

end Neg

section Order

section Semiring

variable {R A : Type*} {p : A → Prop} [CommSemiring R] [PartialOrder R] [StarRing R] [MetricSpace R]
variable [IsTopologicalSemiring R] [ContinuousStar R] [ContinuousSqrt R] [StarOrderedRing R]
variable [TopologicalSpace A] [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A]
variable [Algebra R A] [instCFC : ContinuousFunctionalCalculus R A p]

lemma cfcHom_mono {a : A} (ha : p a) {f g : C(spectrum R a, R)} (hfg : f ≤ g) :
    cfcHom ha f ≤ cfcHom ha g :=
  OrderHomClass.mono (cfcHom ha) hfg

lemma cfcHom_nonneg_iff [NonnegSpectrumClass R A] {a : A} (ha : p a) {f : C(spectrum R a, R)} :
    0 ≤ cfcHom ha f ↔ 0 ≤ f := by
  constructor
  · exact fun hf x ↦ (cfcHom_map_spectrum ha (R := R) _ ▸ spectrum_nonneg_of_nonneg hf) ⟨x, rfl⟩
  · simpa using (cfcHom_mono ha (f := 0) (g := f) ·)

lemma cfcHom_isStrictlyPositive_iff [NonnegSpectrumClass R A] {a : A} (ha : p a)
    {f : C(spectrum R a, R)} : IsStrictlyPositive (cfcHom ha f) ↔ ∀ x, 0 < f x := by
  refine ⟨fun hf x => hf.spectrum_pos <| cfcHom_map_spectrum (R := R) ha _ ▸ Set.mem_range_self x,
    fun h => ⟨cfcHom_nonneg_iff _ |>.mpr fun x => le_of_lt (h x), ?_⟩⟩
  apply spectrum.isUnit_of_zero_notMem (R := R)
  grind [cfcHom_map_spectrum, ne_of_lt]

lemma cfc_mono {f g : R → R} {a : A} (h : ∀ x ∈ spectrum R a, f x ≤ g x)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (hg : ContinuousOn g (spectrum R a) := by cfc_cont_tac) :
    cfc f a ≤ cfc g a := by
  by_cases ha : p a
  · rw [cfc_apply f a, cfc_apply g a]
    exact cfcHom_mono ha fun x ↦ h x.1 x.2
  · simp only [cfc_apply_of_not_predicate _ ha, le_rfl]

lemma cfc_nonneg_iff [NonnegSpectrumClass R A] (f : R → R) (a : A)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) : 0 ≤ cfc f a ↔ ∀ x ∈ spectrum R a, 0 ≤ f x := by
  rw [cfc_apply .., cfcHom_nonneg_iff, ContinuousMap.le_def]
  simp

lemma StarOrderedRing.nonneg_iff_spectrum_nonneg [NonnegSpectrumClass R A] (a : A)
    (ha : p a := by cfc_tac) : 0 ≤ a ↔ ∀ x ∈ spectrum R a, 0 ≤ x := by
  have := cfc_nonneg_iff (id : R → R) a (by fun_prop) ha
  simpa [cfc_id _ a ha] using this

lemma cfc_isStrictlyPositive_iff [NonnegSpectrumClass R A] (f : R → R) (a : A)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) : IsStrictlyPositive (cfc f a) ↔ ∀ x ∈ spectrum R a, 0 < f x := by
  rw [cfc_apply .., cfcHom_isStrictlyPositive_iff]
  simp

lemma StarOrderedRing.isStrictlyPositive_iff_spectrum_pos [NonnegSpectrumClass R A] (a : A)
    (ha : p a := by cfc_tac) : IsStrictlyPositive a ↔ ∀ x ∈ spectrum R a, 0 < x := by
  have := cfc_isStrictlyPositive_iff (id : R → R) a (by fun_prop) ha
  simpa [cfc_id _ a ha] using this

lemma cfc_nonneg {f : R → R} {a : A} (h : ∀ x ∈ spectrum R a, 0 ≤ f x) :
    0 ≤ cfc f a := by
  by_cases hf : ContinuousOn f (spectrum R a)
  · simpa using cfc_mono h
  · simp only [cfc_apply_of_not_continuousOn _ hf, le_rfl]

lemma cfc_nonpos (f : R → R) (a : A) (h : ∀ x ∈ spectrum R a, f x ≤ 0) :
    cfc f a ≤ 0 := by
  by_cases hf : ContinuousOn f (spectrum R a)
  · simpa using cfc_mono h
  · simp only [cfc_apply_of_not_continuousOn _ hf, le_rfl]

lemma cfc_le_algebraMap (f : R → R) (r : R) (a : A) (h : ∀ x ∈ spectrum R a, f x ≤ r)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc f a ≤ algebraMap R A r :=
  cfc_const r a ▸ cfc_mono h

lemma algebraMap_le_cfc (f : R → R) (r : R) (a : A) (h : ∀ x ∈ spectrum R a, r ≤ f x)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    algebraMap R A r ≤ cfc f a :=
  cfc_const r a ▸ cfc_mono h

lemma le_algebraMap_of_spectrum_le {r : R} {a : A} (h : ∀ x ∈ spectrum R a, x ≤ r)
    (ha : p a := by cfc_tac) : a ≤ algebraMap R A r := by
  rw [← cfc_id R a]
  exact cfc_le_algebraMap id r a h

lemma algebraMap_le_of_le_spectrum {r : R} {a : A} (h : ∀ x ∈ spectrum R a, r ≤ x)
    (ha : p a := by cfc_tac) : algebraMap R A r ≤ a := by
  rw [← cfc_id R a]
  exact algebraMap_le_cfc id r a h

lemma cfc_le_one (f : R → R) (a : A) (h : ∀ x ∈ spectrum R a, f x ≤ 1) : cfc f a ≤ 1 := by
  apply cfc_cases (· ≤ 1) _ _ (by simp) fun hf ha ↦ ?_
  rw [← map_one (cfcHom ha (R := R))]
  apply cfcHom_mono ha
  simpa [ContinuousMap.le_def] using h

lemma one_le_cfc (f : R → R) (a : A) (h : ∀ x ∈ spectrum R a, 1 ≤ f x)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    1 ≤ cfc f a := by
  simpa using algebraMap_le_cfc f 1 a h

lemma CFC.le_one {a : A} (h : ∀ x ∈ spectrum R a, x ≤ 1) (ha : p a := by cfc_tac) :
    a ≤ 1 := by
  simpa using le_algebraMap_of_spectrum_le h

lemma CFC.one_le {a : A} (h : ∀ x ∈ spectrum R a, 1 ≤ x) (ha : p a := by cfc_tac) :
    1 ≤ a := by
  simpa using algebraMap_le_of_le_spectrum h

end Semiring

section NNReal

open scoped NNReal

variable {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A] [PartialOrder A]
  [Algebra ℝ≥0 A] [ContinuousFunctionalCalculus ℝ≥0 A (0 ≤ ·)]

lemma CFC.inv_nonneg_of_nonneg (a : Aˣ) (ha : (0 : A) ≤ a := by cfc_tac) : (0 : A) ≤ a⁻¹ :=
  cfc_inv_id (R := ℝ≥0) a ▸ cfc_predicate _ (a : A)

lemma CFC.inv_nonneg (a : Aˣ) : (0 : A) ≤ a⁻¹ ↔ (0 : A) ≤ a :=
  ⟨fun _ ↦ inv_inv a ▸ inv_nonneg_of_nonneg a⁻¹, fun _ ↦ inv_nonneg_of_nonneg a⟩

end NNReal

section Ring

variable {R A : Type*} {p : A → Prop} [CommRing R] [PartialOrder R] [StarRing R] [MetricSpace R]
variable [IsTopologicalRing R] [ContinuousStar R] [ContinuousSqrt R] [StarOrderedRing R]
variable [TopologicalSpace A] [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A]
variable [Algebra R A] [instCFC : ContinuousFunctionalCalculus R A p]
variable [NonnegSpectrumClass R A]

lemma cfcHom_le_iff {a : A} (ha : p a) {f g : C(spectrum R a, R)} :
    cfcHom ha f ≤ cfcHom ha g ↔ f ≤ g := by
  rw [← sub_nonneg, ← map_sub, cfcHom_nonneg_iff, sub_nonneg]

lemma cfc_le_iff (f g : R → R) (a : A) (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (hg : ContinuousOn g (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc f a ≤ cfc g a ↔ ∀ x ∈ spectrum R a, f x ≤ g x := by
  rw [cfc_apply f a, cfc_apply g a, cfcHom_le_iff (show p a from ha), ContinuousMap.le_def]
  simp

lemma cfc_nonpos_iff (f : R → R) (a : A) (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) : cfc f a ≤ 0 ↔ ∀ x ∈ spectrum R a, f x ≤ 0 := by
  simp_rw [← neg_nonneg, ← cfc_neg]
  exact cfc_nonneg_iff (fun x ↦ -f x) a

lemma cfc_le_algebraMap_iff (f : R → R) (r : R) (a : A)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc f a ≤ algebraMap R A r ↔ ∀ x ∈ spectrum R a, f x ≤ r := by
  rw [← cfc_const r a, cfc_le_iff ..]

lemma algebraMap_le_cfc_iff (f : R → R) (r : R) (a : A)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    algebraMap R A r ≤ cfc f a ↔ ∀ x ∈ spectrum R a, r ≤ f x := by
  rw [← cfc_const r a, cfc_le_iff ..]

lemma le_algebraMap_iff_spectrum_le {r : R} {a : A} (ha : p a := by cfc_tac) :
    a ≤ algebraMap R A r ↔ ∀ x ∈ spectrum R a, x ≤ r := by
  nth_rw 1 [← cfc_id R a]
  exact cfc_le_algebraMap_iff id r a

lemma algebraMap_le_iff_le_spectrum {r : R} {a : A} (ha : p a := by cfc_tac) :
    algebraMap R A r ≤ a ↔ ∀ x ∈ spectrum R a, r ≤ x:= by
  nth_rw 1 [← cfc_id R a]
  exact algebraMap_le_cfc_iff id r a

lemma cfc_le_one_iff (f : R → R) (a : A)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    cfc f a ≤ 1 ↔ ∀ x ∈ spectrum R a, f x ≤ 1 := by
  simpa using cfc_le_algebraMap_iff f 1 a

lemma one_le_cfc_iff (f : R → R) (a : A)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    1 ≤ cfc f a ↔ ∀ x ∈ spectrum R a, 1 ≤ f x := by
  simpa using algebraMap_le_cfc_iff f 1 a

lemma CFC.le_one_iff (a : A) (ha : p a := by cfc_tac) :
    a ≤ 1 ↔ ∀ x ∈ spectrum R a, x ≤ 1 := by
  simpa using le_algebraMap_iff_spectrum_le (r := (1 : R)) (a := a)

lemma CFC.one_le_iff (a : A) (ha : p a := by cfc_tac) :
    1 ≤ a ↔ ∀ x ∈ spectrum R a, 1 ≤ x := by
  simpa using algebraMap_le_iff_le_spectrum (r := (1 : R)) (a := a)

end Ring

end Order

/-! ### `cfcHom` on a superset of the spectrum -/

section Superset

variable {R A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R]
    [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A]
    [TopologicalSpace A] [Algebra R A] [instCFC : ContinuousFunctionalCalculus R A p]

/-- The composition of `cfcHom` with the natural embedding `C(s, R) → C(spectrum R a, R)`
whenever `spectrum R a ⊆ s`.

This is sometimes necessary in order to consider the same continuous functions applied to multiple
distinct elements, with the added constraint that `cfc` does not suffice. This can occur, for
example, if it is necessary to use uniqueness of this continuous functional calculus. -/
@[simps!]
noncomputable def cfcHomSuperset {a : A} (ha : p a) {s : Set R} (hs : spectrum R a ⊆ s) :
    C(s, R) →⋆ₐ[R] A :=
  cfcHom ha |>.comp <| ContinuousMap.compStarAlgHom' R R <| ⟨_, continuous_id.subtype_map hs⟩

lemma cfcHomSuperset_continuous {a : A} (ha : p a) {s : Set R} (hs : spectrum R a ⊆ s) :
    Continuous (cfcHomSuperset ha hs) :=
  (cfcHom_continuous ha).comp <| ContinuousMap.continuous_precomp _

lemma cfcHomSuperset_id {a : A} (ha : p a) {s : Set R} (hs : spectrum R a ⊆ s) :
    cfcHomSuperset ha hs (.restrict s <| .id R) = a :=
  cfcHom_id ha

end Superset
