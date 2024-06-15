/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Algebra.Algebra.Quasispectrum
import Mathlib.Topology.ContinuousFunction.Compact
import Mathlib.Topology.ContinuousFunction.ContinuousMapZero
import Mathlib.Topology.ContinuousFunction.FunctionalCalculus
import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# The continuous functional calculus for non-unital algebras

This file defines a generic API for the *continuous functional calculus* in *non-unital* algebras
which is suitable in a wide range of settings. The design is intended to match as closely as
possible that for unital algebras in `Mathlib.Topology.ContinuousFunction.FunctionalCalculus`.
Changes to either file should be mirrored in its counterpart whenever possible. The underlying
reasons for the design decisions in the unital case apply equally in the non-unital case. See the
module documentation in that file for more information.

A continuous functional calculus for an element `a : A` in a non-unital topological `R`-algebra is
a continuous extension of the polynomial functional calculus (i.e., `Polynomial.aeval`) for
polynomials with no constant term to continuous `R`-valued functions on `quasispectrum R a` which
vanish at zero. More precisely, it is a continuous star algebra homomorphism
`C(quasispectrum R a, R)₀ →⋆ₙₐ[R] A` that sends `(ContinuousMap.id R).restrict (quasispectrum R a)`
to `a`. In all cases of interest (e.g., when `quasispectrum R a` is compact and `R` is `ℝ≥0`, `ℝ`,
or `ℂ`), this is sufficient to uniquely determine the continuous functional calculus which is
encoded in the `UniqueNonUnitalContinuousFunctionalCalculus` class.

## Main declarations

+ `NonUnitalContinuousFunctionalCalculus R (p : A → Prop)`: a class stating that every `a : A`
  satisfying `p a` has a non-unital star algebra homomorphism from the continuous `R`-valued
  functions on the `R`-quasispectrum of `a` vanishing at zero into the algebra `A`. This map is a
  closed embedding, and satisfies the **spectral mapping theorem**.
+ `cfcₙHom : p a → C(quasispectrum R a, R)₀ →⋆ₐ[R] A`: the underlying non-unital star algebra
  homomorphism for an element satisfying property `p`.
+ `cfcₙ : (R → R) → A → A`: an unbundled version of `cfcₙHom` which takes the junk value `0` when
  `cfcₙHom` is not defined.

## Main theorems

+ `cfcₙ_comp : cfcₙ (x ↦ g (f x)) a = cfcₙ g (cfcₙ f a)`

-/
local notation "σₙ" => quasispectrum

open scoped ContinuousMapZero

/-- A non-unital star `R`-algebra `A` has a *continuous functional calculus* for elements
satisfying the property `p : A → Prop` if

+ for every such element `a : A` there is a non-unital star algebra homomorphism
  `cfcₙHom : C(quasispectrum R a, R)₀ →⋆ₙₐ[R] A` sending the (restriction of) the identity map
  to `a`.
+ `cfcₙHom` is a closed embedding for which the quasispectrum of the image of function `f` is its
  range.
+ `cfcₙHom` preserves the property `p`.

The property `p` is marked as an `outParam` so that the user need not specify it. In practice,

+ for `R := ℂ`, we choose `p := IsStarNormal`,
+ for `R := ℝ`, we choose `p := IsSelfAdjoint`,
+ for `R := ℝ≥0`, we choose `p := (0 ≤ ·)`.

Instead of directly providing the data we opt instead for a `Prop` class. In all relevant cases,
the continuous functional calculus is uniquely determined, and utilizing this approach
prevents diamonds or problems arising from multiple instances. -/
class NonUnitalContinuousFunctionalCalculus (R : Type*) {A : Type*} (p : outParam (A → Prop))
    [CommSemiring R] [Nontrivial R] [StarRing R] [MetricSpace R] [TopologicalSemiring R]
    [ContinuousStar R] [NonUnitalRing A] [StarRing A] [TopologicalSpace A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] : Prop where
  exists_cfc_of_predicate : ∀ a, p a → ∃ φ : C(σₙ R a, R)₀ →⋆ₙₐ[R] A,
    ClosedEmbedding φ ∧ φ ⟨(ContinuousMap.id R).restrict <| σₙ R a, rfl⟩ = a ∧
      (∀ f, σₙ R (φ f) = Set.range f) ∧ ∀ f, p (φ f)

-- TODO: try to unify with the unital version. The `ℝ≥0` case makes it tricky.
/-- A class guaranteeing that the non-unital continuous functional calculus is uniquely determined
by the properties that it is a continuous non-unital star algebra homomorphism mapping the
(restriction of) the identity to `a`. This is the necessary tool used to establish `cfcₙHom_comp`
and the more common variant `cfcₙ_comp`.

This class will have instances in each of the common cases `ℂ`, `ℝ` and `ℝ≥0` as a consequence of
the Stone-Weierstrass theorem. -/
class UniqueNonUnitalContinuousFunctionalCalculus (R A : Type*) [CommSemiring R] [StarRing R]
    [MetricSpace R] [TopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A] [StarRing A]
    [TopologicalSpace A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] : Prop where
  eq_of_continuous_of_map_id (s : Set R) [CompactSpace s] [Zero s] (h0 : (0 : s) = (0 : R))
    (φ ψ : C(s, R)₀ →⋆ₙₐ[R] A) (hφ : Continuous φ) (hψ : Continuous ψ)
    (h : φ (⟨.restrict s <| .id R, h0⟩) = ψ (⟨.restrict s <| .id R, h0⟩)) :
    φ = ψ
  compactSpace_quasispectrum (a : A) : CompactSpace (σₙ R a)

section Main

variable {R A : Type*} {p : A → Prop} [CommSemiring R] [Nontrivial R] [StarRing R] [MetricSpace R]
variable [TopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A] [StarRing A]
variable [TopologicalSpace A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
variable [NonUnitalContinuousFunctionalCalculus R p]

lemma NonUnitalStarAlgHom.ext_continuousMap [UniqueNonUnitalContinuousFunctionalCalculus R A]
    (a : A) (φ ψ : C(σₙ R a, R)₀ →⋆ₙₐ[R] A) (hφ : Continuous φ) (hψ : Continuous ψ)
    (h : φ ⟨.restrict (σₙ R a) <| .id R, rfl⟩ = ψ ⟨.restrict (σₙ R a) <| .id R, rfl⟩) :
    φ = ψ :=
  have := UniqueNonUnitalContinuousFunctionalCalculus.compactSpace_quasispectrum (R := R) a
  UniqueNonUnitalContinuousFunctionalCalculus.eq_of_continuous_of_map_id _ (by simp) φ ψ hφ hψ h

section cfcₙHom

variable {a : A} (ha : p a)

/-- The non-unital star algebra homomorphism underlying a instance of the continuous functional
calculus for non-unital algebras; a version for continuous functions on the quasispectrum.

In this case, the user must supply the fact that `a` satisfies the predicate `p`.

While `NonUnitalContinuousFunctionalCalculus` is stated in terms of these homomorphisms, in practice
the user should instead prefer `cfcₙ` over `cfcₙHom`.
-/
noncomputable def cfcₙHom : C(σₙ R a, R)₀ →⋆ₙₐ[R] A :=
  (NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose

lemma cfcₙHom_closedEmbedding :
    ClosedEmbedding <| (cfcₙHom ha : C(σₙ R a, R)₀ →⋆ₙₐ[R] A) :=
  (NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.1

lemma cfcₙHom_id :
    cfcₙHom ha ⟨(ContinuousMap.id R).restrict <| σₙ R a, rfl⟩ = a :=
  (NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.2.1

/-- The **spectral mapping theorem** for the non-unital continuous functional calculus. -/
lemma cfcₙHom_map_quasispectrum (f : C(σₙ R a, R)₀) :
    σₙ R (cfcₙHom ha f) = Set.range f :=
  (NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.2.2.1 f

lemma cfcₙHom_predicate (f : C(σₙ R a, R)₀) :
    p (cfcₙHom ha f) :=
  (NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.2.2.2 f

lemma cfcₙHom_eq_of_continuous_of_map_id [UniqueNonUnitalContinuousFunctionalCalculus R A]
    (φ : C(σₙ R a, R)₀ →⋆ₙₐ[R] A) (hφ₁ : Continuous φ)
    (hφ₂ : φ ⟨.restrict (σₙ R a) <| .id R, rfl⟩ = a) : cfcₙHom ha = φ :=
  (cfcₙHom ha).ext_continuousMap a φ (cfcₙHom_closedEmbedding ha).continuous hφ₁ <| by
    rw [cfcₙHom_id ha, hφ₂]

theorem cfcₙHom_comp [UniqueNonUnitalContinuousFunctionalCalculus R A] (f : C(σₙ R a, R)₀)
    (f' : C(σₙ R a, σₙ R (cfcₙHom ha f))₀)
    (hff' : ∀ x, f x = f' x) (g : C(σₙ R (cfcₙHom ha f), R)₀) :
    cfcₙHom ha (g.comp f') = cfcₙHom (cfcₙHom_predicate ha f) g := by
  let ψ : C(σₙ R (cfcₙHom ha f), R)₀ →⋆ₙₐ[R] C(σₙ R a, R)₀ :=
    { toFun := (ContinuousMapZero.comp · f')
      map_smul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_star' := fun _ ↦ rfl }
  let φ : C(σₙ R (cfcₙHom ha f), R)₀ →⋆ₙₐ[R] A := (cfcₙHom ha).comp ψ
  suffices cfcₙHom (cfcₙHom_predicate ha f) = φ from DFunLike.congr_fun this.symm g
  refine cfcₙHom_eq_of_continuous_of_map_id (cfcₙHom_predicate ha f) φ ?_ ?_
  · refine (cfcₙHom_closedEmbedding ha).continuous.comp <| continuous_induced_rng.mpr ?_
    exact f'.toContinuousMap.continuous_comp_left.comp continuous_induced_dom
  · simp only [φ, ψ, NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgHom.coe_mk',
      NonUnitalAlgHom.coe_mk]
    congr
    ext x
    simp [hff']

end cfcₙHom


section CFCn

open Classical in
/-- This is the *continuous functional calculus* of an element `a : A` in a non-unital algebra
applied to bare functions.  When either `a` does not satisfy the predicate `p` (i.e., `a` is not
`IsStarNormal`, `IsSelfAdjoint`, or `0 ≤ a` when `R` is `ℂ`, `ℝ`, or `ℝ≥0`, respectively), or when
`f : R → R` is not continuous on the quasispectrum of `a` or `f 0 ≠ 0`, then `cfcₙ f a` returns the
junk value `0`.

This is the primary declaration intended for widespread use of the continuous functional calculus
for non-unital algebras, and all the API applies to this declaration. For more information, see the
module documentation for `Topology.ContinuousFunction.FunctionalCalculus`. -/
noncomputable irreducible_def cfcₙ (f : R → R) (a : A) : A :=
  if h : p a ∧ ContinuousOn f (σₙ R a) ∧ f 0 = 0
    then cfcₙHom h.1 ⟨⟨_, h.2.1.restrict⟩, h.2.2⟩
    else 0

/-- A tactic used to automatically discharge goals relating to the continuous functional calculus,
specifically concerning whether `f 0 = 0`. -/
syntax (name := cfcZeroTac) "cfc_zero_tac" : tactic
macro_rules
  | `(tactic| cfc_zero_tac) => `(tactic| try (first | aesop | assumption))

variable (f g : R → R) (a : A)
variable (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
variable (hg : ContinuousOn g (σₙ R a) := by cfc_cont_tac) (hg0 : g 0 = 0 := by cfc_zero_tac)
variable (ha : p a := by cfc_tac)

lemma cfcₙ_apply : cfcₙ f a = cfcₙHom (a := a) ha ⟨⟨_, hf.restrict⟩, hf0⟩ := by
  rw [cfcₙ_def, dif_pos ⟨ha, hf, hf0⟩]

lemma cfcₙ_apply_of_not_and_and {f : R → R} (a : A)
    (ha : ¬ (p a ∧ ContinuousOn f (σₙ R a) ∧ f 0 = 0)) :
    cfcₙ f a = 0 := by
  rw [cfcₙ_def, dif_neg ha]

lemma cfcₙ_apply_of_not_predicate {f : R → R} (a : A) (ha : ¬ p a) :
    cfcₙ f a = 0 := by
  rw [cfcₙ_def, dif_neg (not_and_of_not_left _ ha)]

lemma cfcₙ_apply_of_not_continuousOn {f : R → R} (a : A) (hf : ¬ ContinuousOn f (σₙ R a)) :
    cfcₙ f a = 0 := by
  rw [cfcₙ_def, dif_neg (not_and_of_not_right _ (not_and_of_not_left _ hf))]

lemma cfcₙ_apply_of_not_map_zero {f : R → R} (a : A) (hf : ¬ f 0 = 0) :
    cfcₙ f a = 0 := by
  rw [cfcₙ_def, dif_neg (not_and_of_not_right _ (not_and_of_not_right _ hf))]

lemma cfcₙHom_eq_cfcₙ_extend {a : A} (g : R → R) (ha : p a) (f : C(σₙ R a, R)₀) :
    cfcₙHom ha f = cfcₙ (Function.extend Subtype.val f g) a := by
  have h : f = (σₙ R a).restrict (Function.extend Subtype.val f g) := by
    ext; simp [Subtype.val_injective.extend_apply]
  have hg : ContinuousOn (Function.extend Subtype.val f g) (σₙ R a) :=
    continuousOn_iff_continuous_restrict.mpr <| h ▸ map_continuous f
  have hg0 : (Function.extend Subtype.val f g) 0 = 0 := by
    rw [← quasispectrum.coe_zero (R := R) a, Subtype.val_injective.extend_apply]
    exact map_zero f
  rw [cfcₙ_apply ..]
  congr!

lemma cfcₙ_cases (P : A → Prop) (a : A) (f : R → R) (h₀ : P 0)
    (haf : ∀ (hf : ContinuousOn f (σₙ R a)) h0 ha, P (cfcₙHom ha ⟨⟨_, hf.restrict⟩, h0⟩)) :
    P (cfcₙ f a) := by
  by_cases h : ContinuousOn f (σₙ R a) ∧ f 0 = 0 ∧ p a
  · rw [cfcₙ_apply f a h.1 h.2.1 h.2.2]
    exact haf h.1 h.2.1 h.2.2
  · simp only [not_and_or] at h
    obtain (h | h | h) := h
    · rwa [cfcₙ_apply_of_not_continuousOn _ h]
    · rwa [cfcₙ_apply_of_not_map_zero _ h]
    · rwa [cfcₙ_apply_of_not_predicate _ h]

variable (R) in
lemma cfcₙ_id : cfcₙ (id : R → R) a = a :=
  cfcₙ_apply (id : R → R) a ▸ cfcₙHom_id (p := p) ha

variable (R) in
lemma cfcₙ_id' : cfcₙ (fun x : R ↦ x) a = a := cfcₙ_id R a

/-- The **spectral mapping theorem** for the non-unital continuous functional calculus. -/
lemma cfcₙ_map_quasispectrum : σₙ R (cfcₙ f a) = f '' σₙ R a := by
  simp [cfcₙ_apply f a, cfcₙHom_map_quasispectrum (p := p)]

lemma cfcₙ_predicate : p (cfcₙ f a) :=
  cfcₙ_apply f a ▸ cfcₙHom_predicate (A := A) ha _

lemma cfcₙ_congr {f g : R → R} {a : A} (hfg : (σₙ R a).EqOn f g) :
    cfcₙ f a = cfcₙ g a := by
  by_cases h : p a ∧ ContinuousOn g (σₙ R a) ∧ g 0 = 0
  · rw [cfcₙ_apply f a (h.2.1.congr hfg) (hfg (quasispectrum.zero_mem R a) ▸ h.2.2) h.1,
      cfcₙ_apply g a h.2.1 h.2.2 h.1]
    congr
    exact Set.restrict_eq_iff.mpr hfg
  · simp only [not_and_or] at h
    obtain (ha | hg | h0) := h
    · simp [cfcₙ_apply_of_not_predicate a ha]
    · rw [cfcₙ_apply_of_not_continuousOn a hg, cfcₙ_apply_of_not_continuousOn]
      exact fun hf ↦ hg (hf.congr hfg.symm)
    · rw [cfcₙ_apply_of_not_map_zero a h0, cfcₙ_apply_of_not_map_zero]
      exact fun hf ↦ h0 (hfg (quasispectrum.zero_mem R a) ▸ hf)

lemma eqOn_of_cfcₙ_eq_cfcₙ {f g : R → R} {a : A} (h : cfcₙ f a = cfcₙ g a) (ha : p a := by cfc_tac)
    (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (hg : ContinuousOn g (σₙ R a) := by cfc_cont_tac) (hg0 : g 0 = 0 := by cfc_zero_tac) :
    (σₙ R a).EqOn f g := by
  rw [cfcₙ_apply f a, cfcₙ_apply g a] at h
  have := (cfcₙHom_closedEmbedding (show p a from ha) (R := R)).inj h
  intro x hx
  congrm($(this) ⟨x, hx⟩)

lemma cfcₙ_eq_cfcₙ_iff_eqOn {f g : R → R} {a : A} (ha : p a := by cfc_tac)
    (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (hg : ContinuousOn g (σₙ R a) := by cfc_cont_tac) (hg0 : g 0 = 0 := by cfc_zero_tac) :
    cfcₙ f a = cfcₙ g a ↔ (σₙ R a).EqOn f g :=
  ⟨eqOn_of_cfcₙ_eq_cfcₙ, cfcₙ_congr⟩

variable (R)

@[simp]
lemma cfcₙ_zero : cfcₙ (0 : R → R) a = 0 := by
  by_cases ha : p a
  · exact cfcₙ_apply (0 : R → R) a ▸ map_zero (cfcₙHom ha)
  · rw [cfcₙ_apply_of_not_predicate a ha]

@[simp]
lemma cfcₙ_const_zero : cfcₙ (fun _ : R ↦ 0) a = 0 := cfcₙ_zero R a

variable {R}

lemma cfcₙ_mul : cfcₙ (fun x ↦ f x * g x) a = cfcₙ f a * cfcₙ g a := by
  by_cases ha : p a
  · rw [cfcₙ_apply f a, cfcₙ_apply g a, ← map_mul, cfcₙ_apply _ a]
    congr
  · simp [cfcₙ_apply_of_not_predicate a ha]

lemma cfcₙ_add : cfcₙ (fun x ↦ f x + g x) a = cfcₙ f a + cfcₙ g a := by
  by_cases ha : p a
  · rw [cfcₙ_apply f a, cfcₙ_apply g a, cfcₙ_apply _ a]
    simp_rw [← map_add]
    congr
  · simp [cfcₙ_apply_of_not_predicate a ha]

lemma cfcₙ_smul {S : Type*} [SMulZeroClass S R] [ContinuousConstSMul S R]
    [SMulZeroClass S A] [IsScalarTower S R A] [IsScalarTower S R (R → R)]
    (s : S) (f : R → R) (a : A) (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac)
    (h0 : f 0 = 0 := by cfc_zero_tac) :
    cfcₙ (fun x ↦ s • f x) a = s • cfcₙ f a := by
  by_cases ha : p a
  · rw [cfcₙ_apply f a, cfcₙ_apply _ a]
    simp_rw [← Pi.smul_def, ← smul_one_smul R s _]
    rw [← map_smul]
    congr
  · simp [cfcₙ_apply_of_not_predicate a ha]

lemma cfcₙ_const_mul (r : R) (f : R → R) (a : A) (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac)
    (h0 : f 0 = 0 := by cfc_zero_tac) :
    cfcₙ (fun x ↦ r * f x) a = r • cfcₙ f a :=
  cfcₙ_smul r f a

lemma cfcₙ_star : cfcₙ (fun x ↦ star (f x)) a = star (cfcₙ f a) := by
  by_cases h : p a ∧ ContinuousOn f (σₙ R a) ∧ f 0 = 0
  · obtain ⟨ha, hf, h0⟩ := h
    rw [cfcₙ_apply f a, ← map_star, cfcₙ_apply _ a]
    congr
  · simp only [not_and_or] at h
    obtain (ha | hf | h0) := h
    · simp [cfcₙ_apply_of_not_predicate a ha]
    · rw [cfcₙ_apply_of_not_continuousOn a hf, cfcₙ_apply_of_not_continuousOn, star_zero]
      exact fun hf_star ↦ hf <| by simpa using hf_star.star
    · rw [cfcₙ_apply_of_not_map_zero a h0, cfcₙ_apply_of_not_map_zero, star_zero]
      exact fun hf0 ↦ h0 <| by simpa using congr(star $(hf0))

lemma cfcₙ_smul_id {S : Type*} [SMulZeroClass S R] [ContinuousConstSMul S R]
    [SMulZeroClass S A] [IsScalarTower S R A] [IsScalarTower S R (R → R)]
    (s : S) (a : A) (ha : p a := by cfc_tac) : cfcₙ (s • · : R → R) a = s • a := by
  rw [cfcₙ_smul s _ a, cfcₙ_id' R a]

lemma cfcₙ_const_mul_id (r : R) (a : A) (ha : p a := by cfc_tac) : cfcₙ (r * ·) a = r • a :=
  cfcₙ_smul_id r a

lemma cfcₙ_star_id : cfcₙ (star · : R → R) a = star a := by
  rw [cfcₙ_star _ a, cfcₙ_id' R a]

variable [UniqueNonUnitalContinuousFunctionalCalculus R A]

lemma cfcₙ_comp (g f : R → R) (a : A)
    (hg : ContinuousOn g (f '' σₙ R a) := by cfc_cont_tac) (hg0 : g 0 = 0 := by cfc_zero_tac)
    (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (ha : p a := by cfc_tac) :
    cfcₙ (g ∘ f) a = cfcₙ g (cfcₙ f a) := by
  have := hg.comp hf <| (σₙ R a).mapsTo_image f
  have sp_eq :
      σₙ R (cfcₙHom (show p a from ha) ⟨ContinuousMap.mk _ hf.restrict, hf0⟩) = f '' (σₙ R a) := by
    rw [cfcₙHom_map_quasispectrum (by exact ha) _]
    ext
    simp
  rw [cfcₙ_apply .., cfcₙ_apply f a,
    cfcₙ_apply _ (by convert hg) (ha := cfcₙHom_predicate (show p a from ha) _) ,
    ← cfcₙHom_comp _ _]
  swap
  · exact ⟨.mk _ <| hf.restrict.codRestrict fun x ↦ by rw [sp_eq]; use x.1; simp, Subtype.ext hf0⟩
  · congr
  · exact fun _ ↦ rfl

lemma cfcₙ_comp' (g f : R → R) (a : A)
    (hg : ContinuousOn g (f '' σₙ R a) := by cfc_cont_tac) (hg0 : g 0 = 0 := by cfc_zero_tac)
    (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (ha : p a := by cfc_tac) :
    cfcₙ (g <| f ·) a = cfcₙ g (cfcₙ f a) :=
  cfcₙ_comp g f a

lemma cfcₙ_comp_smul {S : Type*} [SMulZeroClass S R] [ContinuousConstSMul S R]
    [SMulZeroClass S A] [IsScalarTower S R A] [IsScalarTower S R (R → R)]
    (s : S) (f : R → R) (a : A) (hf : ContinuousOn f ((s • ·) '' (σₙ R a)) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) (ha : p a := by cfc_tac) :
    cfcₙ (f <| s • ·) a = cfcₙ f (s • a) := by
  rw [cfcₙ_comp' f (s • ·) a, cfcₙ_smul_id s a]

lemma cfcₙ_comp_const_mul (r : R) (f : R → R) (a : A)
    (hf : ContinuousOn f ((r * ·) '' (σₙ R a)) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) (ha : p a := by cfc_tac) :
    cfcₙ (f <| r * ·) a = cfcₙ f (r • a) := by
  rw [cfcₙ_comp' f (r * ·) a, cfcₙ_const_mul_id r a]

lemma cfcₙ_comp_star (hf : ContinuousOn f (star '' (σₙ R a)) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) (ha : p a := by cfc_tac) :
    cfcₙ (f <| star ·) a = cfcₙ f (star a) := by
  rw [cfcₙ_comp' f star a, cfcₙ_star_id a]

lemma eq_zero_of_quasispectrum_eq_zero (h_spec : σₙ R a ⊆ {0}) (ha : p a := by cfc_tac) :
    a = 0 := by
  simpa [cfcₙ_id R a] using cfcₙ_congr (a := a) (f := id) (g := fun _ : R ↦ 0) fun x ↦ by simp_all

end CFCn

end Main

section Neg

variable {R A : Type*} {p : A → Prop} [CommRing R] [Nontrivial R] [StarRing R] [MetricSpace R]
variable [TopologicalRing R] [ContinuousStar R] [TopologicalSpace A] [NonUnitalRing A] [StarRing A]
variable [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
variable [NonUnitalContinuousFunctionalCalculus R p]
variable (f g : R → R) (a : A)
variable (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
variable (hg : ContinuousOn g (σₙ R a) := by cfc_cont_tac) (hg0 : g 0 = 0 := by cfc_zero_tac)

lemma cfcₙ_sub : cfcₙ (fun x ↦ f x - g x) a = cfcₙ f a - cfcₙ g a := by
  by_cases ha : p a
  · rw [cfcₙ_apply f a, cfcₙ_apply g a, ← map_sub, cfcₙ_apply ..]
    congr
  · simp [cfcₙ_apply_of_not_predicate a ha]

lemma cfcₙ_neg : cfcₙ (fun x ↦ - (f x)) a = - (cfcₙ f a) := by
  by_cases h : p a ∧ ContinuousOn f (σₙ R a) ∧ f 0 = 0
  · obtain ⟨ha, hf, h0⟩ := h
    rw [cfcₙ_apply f a, ← map_neg, cfcₙ_apply ..]
    congr
  · simp only [not_and_or] at h
    obtain (ha | hf | h0) := h
    · simp [cfcₙ_apply_of_not_predicate a ha]
    · rw [cfcₙ_apply_of_not_continuousOn a hf, cfcₙ_apply_of_not_continuousOn, neg_zero]
      exact fun hf_neg ↦ hf <| by simpa using hf_neg.neg
    · rw [cfcₙ_apply_of_not_map_zero a h0, cfcₙ_apply_of_not_map_zero, neg_zero]
      exact (h0 <| neg_eq_zero.mp ·)

lemma cfcₙ_neg_id (ha : p a := by cfc_tac) :
    cfcₙ (- · : R → R) a = -a := by
  rw [cfcₙ_neg .., cfcₙ_id' R a]

variable [UniqueNonUnitalContinuousFunctionalCalculus R A]

lemma cfcₙ_comp_neg (hf : ContinuousOn f ((- ·) '' (σₙ R a)) := by cfc_cont_tac)
    (h0 : f 0 = 0 := by cfc_zero_tac) (ha : p a := by cfc_tac) :
    cfcₙ (f <| - ·) a = cfcₙ f (-a) := by
  rw [cfcₙ_comp' .., cfcₙ_neg_id _]

end Neg

section Order

section Semiring

variable {R A : Type*} {p : A → Prop} [OrderedCommSemiring R] [Nontrivial R]
variable [StarRing R] [StarOrderedRing R] [MetricSpace R] [TopologicalSemiring R] [ContinuousStar R]
variable [∀ (α) [Zero α] [TopologicalSpace α], StarOrderedRing C(α, R)₀]
variable [TopologicalSpace A] [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A]
variable [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]
variable [NonUnitalContinuousFunctionalCalculus R p] [NonnegSpectrumClass R A]

lemma cfcₙHom_mono {a : A} (ha : p a) {f g : C(σₙ R a, R)₀} (hfg : f ≤ g) :
    cfcₙHom ha f ≤ cfcₙHom ha g :=
  OrderHomClass.mono (cfcₙHom ha) hfg

lemma cfcₙHom_nonneg_iff {a : A} (ha : p a) {f : C(σₙ R a, R)₀} :
    0 ≤ cfcₙHom ha f ↔ 0 ≤ f := by
  constructor
  · exact fun hf x ↦
      (cfcₙHom_map_quasispectrum ha (R := R) _ ▸ quasispectrum_nonneg_of_nonneg (cfcₙHom ha f) hf)
      _ ⟨x, rfl⟩
  · simpa using (cfcₙHom_mono ha (f := 0) (g := f) ·)

lemma cfcₙ_mono {f g : R → R} {a : A} (h : ∀ x ∈ σₙ R a, f x ≤ g x)
    (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac)
    (hg : ContinuousOn g (σₙ R a) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) (hg0 : g 0 = 0 := by cfc_zero_tac) :
    cfcₙ f a ≤ cfcₙ g a := by
  by_cases ha : p a
  · rw [cfcₙ_apply f a, cfcₙ_apply g a]
    exact cfcₙHom_mono ha fun x ↦ h x.1 x.2
  · simp only [cfcₙ_apply_of_not_predicate _ ha, le_rfl]

lemma cfcₙ_nonneg_iff (f : R → R) (a : A) (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac)
    (h0 : f 0 = 0 := by cfc_zero_tac) (ha : p a := by cfc_tac) :
    0 ≤ cfcₙ f a ↔ ∀ x ∈ σₙ R a, 0 ≤ f x := by
  rw [cfcₙ_apply .., cfcₙHom_nonneg_iff, ContinuousMapZero.le_def]
  simp only [ContinuousMapZero.coe_mk, ContinuousMap.coe_mk, Set.restrict_apply, Subtype.forall]
  congr!

lemma cfcₙ_nonneg {f : R → R} {a : A} (h : ∀ x ∈ σₙ R a, 0 ≤ f x) :
    0 ≤ cfcₙ f a := by
  by_cases hf : ContinuousOn f (σₙ R a) ∧ f 0 = 0
  · obtain ⟨h₁, h₂⟩ := hf
    simpa using cfcₙ_mono h
  · simp only [not_and_or] at hf
    obtain (hf | hf) := hf
    · simp only [cfcₙ_apply_of_not_continuousOn _ hf, le_rfl]
    · simp only [cfcₙ_apply_of_not_map_zero _ hf, le_rfl]

lemma cfcₙ_nonpos (f : R → R) (a : A) (h : ∀ x ∈ σₙ R a, f x ≤ 0) :
    cfcₙ f a ≤ 0 := by
  by_cases hf : ContinuousOn f (σₙ R a) ∧ f 0 = 0
  · obtain ⟨h₁, h₂⟩ := hf
    simpa using cfcₙ_mono h
  · simp only [not_and_or] at hf
    obtain (hf | hf) := hf
    · simp only [cfcₙ_apply_of_not_continuousOn _ hf, le_rfl]
    · simp only [cfcₙ_apply_of_not_map_zero _ hf, le_rfl]

end Semiring

section Ring

variable {R A : Type*} {p : A → Prop} [OrderedCommRing R] [Nontrivial R]
variable [StarRing R] [StarOrderedRing R] [MetricSpace R] [TopologicalRing R] [ContinuousStar R]
variable [∀ (α) [Zero α] [TopologicalSpace α], StarOrderedRing C(α, R)₀]
variable [TopologicalSpace A] [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A]
variable [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]
variable [NonUnitalContinuousFunctionalCalculus R p] [NonnegSpectrumClass R A]

lemma cfcₙHom_le_iff {a : A} (ha : p a) {f g : C(σₙ R a, R)₀} :
    cfcₙHom ha f ≤ cfcₙHom ha g ↔ f ≤ g := by
  rw [← sub_nonneg, ← map_sub, cfcₙHom_nonneg_iff, sub_nonneg]

lemma cfcₙ_le_iff (f g : R → R) (a : A) (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac)
    (hg : ContinuousOn g (σₙ R a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (hg0 : g 0 = 0 := by cfc_zero_tac) (ha : p a := by cfc_tac) :
    cfcₙ f a ≤ cfcₙ g a ↔ ∀ x ∈ σₙ R a, f x ≤ g x := by
  rw [cfcₙ_apply f a, cfcₙ_apply g a, cfcₙHom_le_iff (show p a from ha), ContinuousMapZero.le_def]
  simp

lemma cfcₙ_nonpos_iff (f : R → R) (a : A) (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac)
    (h0 : f 0 = 0 := by cfc_zero_tac) (ha : p a := by cfc_tac) :
    cfcₙ f a ≤ 0 ↔ ∀ x ∈ σₙ R a, f x ≤ 0 := by
  simp_rw [← neg_nonneg, ← cfcₙ_neg]
  exact cfcₙ_nonneg_iff (fun x ↦ -f x) a

end Ring

end Order

/-! ### Obtain a non-unital continuous functional calculus from a unital one -/

section UnitalToNonUnital

open ContinuousMapZero Set Uniformity ContinuousMap

variable {R A : Type*} {p : A → Prop} [Field R] [StarRing R] [MetricSpace R] [CompleteSpace R]
variable [TopologicalRing R] [ContinuousStar R] [Ring A] [StarRing A] [TopologicalSpace A]
variable [Algebra R A] [ContinuousFunctionalCalculus R p]
variable [h_cpct : ∀ a : A, CompactSpace (spectrum R a)]

instance ContinuousFunctionalCalculus.toNonUnital : NonUnitalContinuousFunctionalCalculus R p where
  exists_cfc_of_predicate a ha := by
    have h_cpct' : CompactSpace (quasispectrum R a) := by
      specialize h_cpct a
      simp_rw [← isCompact_iff_compactSpace, quasispectrum_eq_spectrum_union_zero] at h_cpct ⊢
      exact h_cpct.union isCompact_singleton
    let e := ContinuousMapZero.toContinuousMapHom (X := quasispectrum R a) (R := R)
    let f : C(spectrum R a, quasispectrum R a) :=
      ⟨_, continuous_inclusion <| spectrum_subset_quasispectrum R a⟩
    let ψ := ContinuousMap.compStarAlgHom' R R f
    let ψ' := (cfcHom ha (R := R) : C(spectrum R a, R) →⋆ₙₐ[R] A).comp <|
      (ψ : C(quasispectrum R a, R) →⋆ₙₐ[R] C(spectrum R a, R)).comp e
    refine ⟨ψ', ?closedEmbedding, ?map_id, ?map_spectrum, ?predicate⟩
    case closedEmbedding =>
      refine (cfcHom_closedEmbedding ha).comp <|
        (UniformInducing.uniformEmbedding ⟨?_⟩).toClosedEmbedding
      have := uniformSpace_eq_inf_precomp_of_cover (β := R) f (0 : C(Unit, σₙ R a))
        (map_continuous f).isProperMap (map_continuous 0).isProperMap <| by
          simp only [← Subtype.val_injective.image_injective.eq_iff, f, ContinuousMap.coe_mk,
            ContinuousMap.coe_zero, range_zero, image_union, image_singleton,
            quasispectrum.coe_zero, ← range_comp, val_comp_inclusion, image_univ, Subtype.range_coe,
            quasispectrum_eq_spectrum_union_zero]
      simp_rw [ContinuousMapZero.instUniformSpace, this, uniformity_comap,
        @inf_uniformity _ (.comap _ _) (.comap _ _), uniformity_comap, Filter.comap_inf,
        Filter.comap_comap]
      refine .symm <| inf_eq_left.mpr <| le_top.trans <| eq_top_iff.mp ?_
      have : ∀ U ∈ 𝓤 (C(Unit, R)), (0, 0) ∈ U := fun U hU ↦ refl_mem_uniformity hU
      convert Filter.comap_const_of_mem this with ⟨u, v⟩ <;>
      ext ⟨x, rfl⟩ <;> [exact map_zero u; exact map_zero v]
    case map_id => exact cfcHom_id ha
    case map_spectrum =>
      intro f
      simp only [ψ']
      rw [quasispectrum_eq_spectrum_union_zero]
      simp only [NonUnitalStarAlgHom.comp_assoc, NonUnitalStarAlgHom.comp_apply,
        NonUnitalStarAlgHom.coe_coe]
      rw [cfcHom_map_spectrum ha]
      ext x
      constructor
      · rintro (⟨x, rfl⟩ | rfl)
        · exact ⟨⟨x.1, spectrum_subset_quasispectrum R a x.2⟩, rfl⟩
        · exact ⟨0, map_zero f⟩
      · rintro ⟨x, rfl⟩
        have hx := x.2
        simp_rw [quasispectrum_eq_spectrum_union_zero R a] at hx
        obtain (hx | hx) := hx
        · exact Or.inl ⟨⟨x.1, hx⟩, rfl⟩
        · apply Or.inr
          simp only [Set.mem_singleton_iff] at hx ⊢
          rw [show x = 0 from Subtype.val_injective hx, map_zero]
    case predicate => exact fun f ↦ cfcHom_predicate ha _

end UnitalToNonUnital
