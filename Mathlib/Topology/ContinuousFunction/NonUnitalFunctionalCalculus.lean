/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Algebra.Algebra.Quasispectrum
import Mathlib.Topology.ContinuousFunction.ContinuousMapZero
import Mathlib.Topology.ContinuousFunction.FunctionalCalculus

/-!
# The continuous functional calculus for non-unital algebras

This file defines a generic API for the *continuous functional calculus* in *non-unital* algebras
which is suitable in a wide range of settings. The design is intended to match as closely as
possible that for unital algebras in `Topology.ContinuousFunction.FunctionalCalculus`. Changes to
either file should be mirrored in its counterpart whenever possible. The underlying reasons for the
design decisions in the unital case apply equally in the non-unital case. See the module
documentation in that file for more information.

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
+ `cfcₙ : A → (R → R) → A`: an unbundled version of `cfcₙHom` which takes the junk value `0` when
  `cfcₙHom` is not defined.

## Main theorems

+ `cfcₙ_comp : cfcₙ a (x ↦ g (f x)) = cfcₙ (cfcₙ a f) g`

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
    [Semifield R] [StarRing R] [MetricSpace R] [TopologicalSemiring R] [ContinuousStar R]
    [NonUnitalRing A] [StarRing A] [TopologicalSpace A] [Module R A] [IsScalarTower R A A]
    [SMulCommClass R A A] : Prop where
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
class UniqueNonUnitalContinuousFunctionalCalculus (R A : Type*) [Semifield R] [StarRing R]
    [MetricSpace R] [TopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A] [StarRing A]
    [TopologicalSpace A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] : Prop where
  eq_of_continuous_of_map_id (s : Set R) [CompactSpace s] [Zero s] (h0 : (0 : s) = (0 : R))
    (φ ψ : C(s, R)₀ →⋆ₙₐ[R] A) (hφ : Continuous φ) (hψ : Continuous ψ)
    (h : φ (⟨.restrict s <| .id R, h0⟩) = ψ (⟨.restrict s <| .id R, h0⟩)) :
    φ = ψ
  compactSpace_quasispectrum (a : A) : CompactSpace (σₙ R a)

variable {R A : Type*} {p : A → Prop} [Semifield R] [StarRing R] [MetricSpace R]
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
`f : R → R` is not continuous on the quasispectrum of `a` or `f 0 ≠ 0`, then `cfc a f` returns the
junk value `0`.

This is the primary declaration intended for widespread use of the continuous functional calculus
for non-unital algebras, and all the API applies to this declaration. For more information, see the
module documentation for `Topology.ContinuousFunction.FunctionalCalculus`. -/
noncomputable irreducible_def cfcₙ (a : A) (f : R → R) : A :=
  if h : p a ∧ ContinuousOn f (σₙ R a) ∧ f 0 = 0
    then cfcₙHom h.1 ⟨⟨_, h.2.1.restrict⟩, h.2.2⟩
    else 0

variable (a : A)


/-- A tactic used to automatically discharge goals relating to the continuous functional calculus,
specifically concerning whether `f 0 = 0`. -/
syntax (name := cfcZeroTac) "cfc_zero_tac" : tactic
macro_rules
  | `(tactic| cfc_zero_tac) => `(tactic| try (first | aesop | assumption))

lemma cfcₙ_apply (f : R → R) (ha : p a := by cfc_tac)
    (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac) (h0 : f 0 = 0 := by cfc_zero_tac) :
    cfcₙ a f = cfcₙHom (a := a) ha ⟨⟨_, hf.restrict⟩, h0⟩ := by
  rw [cfcₙ_def, dif_pos ⟨ha, hf, h0⟩]

lemma cfcₙ_apply_of_not_and_and {f : R → R} (ha : ¬ (p a ∧ ContinuousOn f (σₙ R a) ∧ f 0 = 0)) :
    cfcₙ a f = 0 := by
  rw [cfcₙ_def, dif_neg ha]

lemma cfcₙ_apply_of_not_predicate {f : R → R} (ha : ¬ p a) :
    cfcₙ a f = 0 := by
  rw [cfcₙ_def, dif_neg (not_and_of_not_left _ ha)]

lemma cfcₙ_apply_of_not_continuousOn {f : R → R} (hf : ¬ ContinuousOn f (σₙ R a)) :
    cfcₙ a f = 0 := by
  rw [cfcₙ_def, dif_neg (not_and_of_not_right _ (not_and_of_not_left _ hf))]

lemma cfcₙ_apply_of_not_map_zero {f : R → R} (hf : ¬ f 0 = 0) :
    cfcₙ a f = 0 := by
  rw [cfcₙ_def, dif_neg (not_and_of_not_right _ (not_and_of_not_right _ hf))]

variable (R) in
lemma cfcₙ_id (ha : p a := by cfc_tac) : cfcₙ a (id : R → R) = a :=
  cfcₙ_apply a (id : R → R) ▸ cfcₙHom_id (p := p) ha

variable (R) in
lemma cfcₙ_id' (ha : p a := by cfc_tac) : cfcₙ a (fun x : R ↦ x) = a :=
  cfcₙ_id R a

/-- The **spectral mapping theorem** for the non-unital continuous functional calculus. -/
lemma cfc_map_quasispectrum (f : R → R) (ha : p a := by cfc_tac)
    (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac) (h0 : f 0 = 0 := by cfc_zero_tac) :
    σₙ R (cfcₙ a f) = f '' σₙ R a := by
  simp [cfcₙ_apply a f, cfcₙHom_map_quasispectrum (p := p)]

lemma cfcₙ_predicate (f : R → R) (ha : p a := by cfc_tac)
    (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac) (h0 : f 0 = 0 := by cfc_zero_tac) :
    p (cfcₙ a f) :=
  cfcₙ_apply a f ▸ cfcₙHom_predicate (A := A) ha _

lemma cfcₙ_congr {f g : R → R} (hfg : (σₙ R a).EqOn f g) :
    cfcₙ a f = cfcₙ a g := by
  by_cases h : p a ∧ ContinuousOn g (σₙ R a) ∧ g 0 = 0
  · rw [cfcₙ_apply a f h.1 (h.2.1.congr hfg) (hfg (quasispectrum.zero_mem R a) ▸ h.2.2),
      cfcₙ_apply a g h.1 h.2.1 h.2.2]
    congr
    exact Set.restrict_eq_iff.mpr hfg
  · simp only [not_and_or] at h
    obtain (ha | hg | h0) := h
    · simp [cfcₙ_apply_of_not_predicate a ha]
    · rw [cfcₙ_apply_of_not_continuousOn a hg, cfcₙ_apply_of_not_continuousOn]
      exact fun hf ↦ hg (hf.congr hfg.symm)
    · rw [cfcₙ_apply_of_not_map_zero a h0, cfcₙ_apply_of_not_map_zero]
      exact fun hf ↦ h0 (hfg (quasispectrum.zero_mem R a) ▸ hf)

lemma eqOn_of_cfcₙ_eq_cfcₙ {f g : R → R} (h : cfcₙ a f = cfcₙ a g) (ha : p a := by cfc_tac)
    (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (hg : ContinuousOn g (σₙ R a) := by cfc_cont_tac) (hg0 : g 0 = 0 := by cfc_zero_tac) :
    (σₙ R a).EqOn f g := by
  rw [cfcₙ_apply a f, cfcₙ_apply a g] at h
  have := (cfcₙHom_closedEmbedding (show p a from ha) (R := R)).inj h
  intro x hx
  congrm($(this) ⟨x, hx⟩)

lemma cfcₙ_eq_cfcₙ_iff_eqOn {f g : R → R} (ha : p a := by cfc_tac)
    (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (hg : ContinuousOn g (σₙ R a) := by cfc_cont_tac) (hg0 : g 0 = 0 := by cfc_zero_tac) :
    cfcₙ a f = cfcₙ a g ↔ (σₙ R a).EqOn f g :=
  ⟨eqOn_of_cfcₙ_eq_cfcₙ a, cfcₙ_congr a⟩

variable (R)

@[simp]
lemma cfcₙ_zero : cfcₙ a (0 : R → R) = 0 := by
  by_cases ha : p a
  · exact cfcₙ_apply a (0 : R → R) ▸ map_zero (cfcₙHom ha)
  · rw [cfcₙ_apply_of_not_predicate a ha]

@[simp]
lemma cfcₙ_const_zero : cfcₙ a (fun _ : R ↦ 0) = 0 :=
  cfcₙ_zero R a

variable {R}

lemma cfcₙ_mul (f g : R → R)
    (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (hg : ContinuousOn g (σₙ R a) := by cfc_cont_tac) (hg0 : g 0 = 0 := by cfc_zero_tac) :
    cfcₙ a (fun x ↦ f x * g x) = cfcₙ a f * cfcₙ a g := by
  by_cases ha : p a
  · rw [cfcₙ_apply a f, cfcₙ_apply a g, ← map_mul, cfcₙ_apply a _]
    congr
  · simp [cfcₙ_apply_of_not_predicate a ha]

lemma cfcₙ_add (f g : R → R)
    (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (hg : ContinuousOn g (σₙ R a) := by cfc_cont_tac) (hg0 : g 0 = 0 := by cfc_zero_tac) :
    cfcₙ a (fun x ↦ f x + g x) = cfcₙ a f + cfcₙ a g := by
  by_cases ha : p a
  · rw [cfcₙ_apply a f, cfcₙ_apply a g, cfcₙ_apply a _]
    simp_rw [← map_add]
    congr
  · simp [cfcₙ_apply_of_not_predicate a ha]

lemma cfcₙ_smul {S : Type*} [SMulZeroClass S R] [ContinuousConstSMul S R]
    [SMulZeroClass S A] [IsScalarTower S R A] [IsScalarTower S R (R → R)]
    (s : S) (f : R → R) (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac)
    (h0 : f 0 = 0 := by cfc_zero_tac) :
    cfcₙ a (fun x ↦ s • f x) = s • cfcₙ a f := by
  by_cases ha : p a
  · rw [cfcₙ_apply a f, cfcₙ_apply a _]
    simp_rw [← Pi.smul_def, ← smul_one_smul R s _]
    rw [← map_smul]
    congr
  · simp [cfcₙ_apply_of_not_predicate a ha]

lemma cfcₙ_const_mul (r : R) (f : R → R) (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac)
    (h0 : f 0 = 0 := by cfc_zero_tac) :
    cfcₙ a (fun x ↦ r * f x) = r • cfcₙ a f :=
  cfcₙ_smul a r f

lemma cfcₙ_star (f : R → R) : cfcₙ a (fun x ↦ star (f x)) = star (cfcₙ a f) := by
  by_cases h : p a ∧ ContinuousOn f (σₙ R a) ∧ f 0 = 0
  · obtain ⟨ha, hf, h0⟩ := h
    rw [cfcₙ_apply a f, ← map_star, cfcₙ_apply a _]
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
    (s : S) (ha : p a := by cfc_tac) : cfcₙ a (s • · : R → R) = s • a := by
  rw [cfcₙ_smul a s _, cfcₙ_id' R a]

lemma cfcₙ_const_mul_id (r : R) (ha : p a := by cfc_tac) : cfcₙ a (r * ·) = r • a :=
  cfcₙ_smul_id a r

lemma cfcₙ_star_id (ha : p a := by cfc_tac) : cfcₙ a (star · : R → R) = star a := by
  rw [cfcₙ_star a _, cfcₙ_id' R a]

variable [UniqueNonUnitalContinuousFunctionalCalculus R A]

lemma cfcₙ_comp (g f : R → R) (ha : p a := by cfc_tac)
    (hg : ContinuousOn g (f '' σₙ R a) := by cfc_cont_tac) (hg0 : g 0 = 0 := by cfc_zero_tac)
    (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac) :
    cfcₙ a (g ∘ f) = cfcₙ (cfcₙ a f) g := by
  have := hg.comp hf <| (σₙ R a).mapsTo_image f
  have sp_eq :
      σₙ R (cfcₙHom (show p a from ha) ⟨ContinuousMap.mk _ hf.restrict, hf0⟩) = f '' (σₙ R a) := by
    rw [cfcₙHom_map_quasispectrum (by exact ha) _]
    ext
    simp
  rw [cfcₙ_apply .., cfcₙ_apply a f,
    cfcₙ_apply _ _ (cfcₙHom_predicate (show p a from ha) _) (by convert hg), ← cfcₙHom_comp _ _]
  swap
  · exact ⟨.mk _ <| hf.restrict.codRestrict fun x ↦ by rw [sp_eq]; use x.1; simp, Subtype.ext hf0⟩
  · congr
  · exact fun _ ↦ rfl

lemma cfcₙ_comp' (g f : R → R) (ha : p a := by cfc_tac)
    (hg : ContinuousOn g (f '' σₙ R a) := by cfc_cont_tac) (hg0 : g 0 = 0 := by cfc_zero_tac)
    (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac) :
    cfcₙ a (g <| f ·) = cfcₙ (cfcₙ a f) g :=
  cfcₙ_comp a g f

lemma cfcₙ_comp_smul {S : Type*} [SMulZeroClass S R] [ContinuousConstSMul S R]
    [SMulZeroClass S A] [IsScalarTower S R A] [IsScalarTower S R (R → R)]
    (s : S) (f : R → R) (ha : p a := by cfc_tac)
    (hf : ContinuousOn f ((s • ·) '' (σₙ R a)) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) :
    cfcₙ a (f <| s • ·) = cfcₙ (s • a) f := by
  rw [cfcₙ_comp' a f (s • ·), cfcₙ_smul_id a s]

lemma cfcₙ_comp_const_mul (r : R) (f : R → R) (ha : p a := by cfc_tac)
    (hf : ContinuousOn f ((r * ·) '' (σₙ R a)) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) :
    cfcₙ a (f <| r * ·) = cfcₙ (r • a) f := by
  rw [cfcₙ_comp' a f (r * ·), cfcₙ_const_mul_id a r]

lemma cfcₙ_comp_star (f : R → R) (ha : p a := by cfc_tac)
    (hf : ContinuousOn f (star '' (σₙ R a)) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) :
    cfcₙ a (f <| star ·) = cfcₙ (star a) f := by
  rw [cfcₙ_comp' a f star, cfcₙ_star_id a]

lemma eq_zero_of_quasispectrum_eq_zero (h_spec : σₙ R a ⊆ {0}) (ha : p a := by cfc_tac) :
    a = 0 := by
  simpa [cfcₙ_id R a] using cfcₙ_congr a (f := id) (g := fun _ : R ↦ 0) fun x ↦ by simp_all

end CFCn
section Neg

variable {R A : Type*} {p : A → Prop} [Field R] [StarRing R] [MetricSpace R]
variable [TopologicalRing R] [ContinuousStar R] [TopologicalSpace A] [NonUnitalRing A] [StarRing A]
variable [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
variable [NonUnitalContinuousFunctionalCalculus R p]

lemma cfcₙ_sub (a : A) (f g : R → R)
    (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (hg : ContinuousOn g (σₙ R a) := by cfc_cont_tac) (hg0 : g 0 = 0 := by cfc_zero_tac) :
    cfcₙ a (fun x ↦ f x - g x) = cfcₙ a f - cfcₙ a g := by
  by_cases ha : p a
  · rw [cfcₙ_apply a f, cfcₙ_apply a g, ← map_sub, cfcₙ_apply ..]
    congr
  · simp [cfcₙ_apply_of_not_predicate a ha]

lemma cfcₙ_neg (a : A) (f : R → R) : cfcₙ a (fun x ↦ - (f x)) = - (cfcₙ a f) := by
  by_cases h : p a ∧ ContinuousOn f (σₙ R a) ∧ f 0 = 0
  · obtain ⟨ha, hf, h0⟩ := h
    rw [cfcₙ_apply a f, ← map_neg, cfcₙ_apply ..]
    congr
  · simp only [not_and_or] at h
    obtain (ha | hf | h0) := h
    · simp [cfcₙ_apply_of_not_predicate a ha]
    · rw [cfcₙ_apply_of_not_continuousOn a hf, cfcₙ_apply_of_not_continuousOn, neg_zero]
      exact fun hf_neg ↦ hf <| by simpa using hf_neg.neg
    · rw [cfcₙ_apply_of_not_map_zero a h0, cfcₙ_apply_of_not_map_zero, neg_zero]
      exact (h0 <| neg_eq_zero.mp ·)

lemma cfcₙ_neg_id (a : A) (ha : p a := by cfc_tac) :
    cfcₙ (a : A) (- · : R → R) = -a := by
  rw [cfcₙ_neg a _, cfcₙ_id' R a]

variable [UniqueNonUnitalContinuousFunctionalCalculus R A]

lemma cfcₙ_comp_neg (a : A) (f : R → R) (ha : p a := by cfc_tac)
    (hf : ContinuousOn f ((- ·) '' (σₙ R (a : A))) := by cfc_cont_tac)
    (h0 : f 0 = 0 := by cfc_zero_tac) :
    cfcₙ (a : A) (f <| - ·) = cfcₙ (-a) f := by
  rw [cfcₙ_comp' .., cfcₙ_neg_id _]

end Neg
