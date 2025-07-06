/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.Elaborators

/-!
# Covariant derivatives

TODO: add a more complete doc-string

-/

open Bundle Filter Function Topology

open scoped Bundle Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

section

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 0 M]

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  -- `F` model fiber
  (n : WithTop ℕ∞)
  (V : M → Type*) [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  -- `V` vector bundle

section prerequisites

def bar (a : 𝕜) : TangentSpace 𝓘(𝕜) a ≃L[𝕜] 𝕜 where
  toFun v := v
  invFun v := v
  map_add' := by simp
  map_smul' := by simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']

@[simp]
theorem Bundle.Trivial.mdifferentiableAt_iff (σ : (x : E) → Trivial E E' x) (e : E) :
    MDifferentiableAt% (T% σ) e ↔
    DifferentiableAt 𝕜 σ e := by
  simp [mdifferentiableAt_totalSpace, mdifferentiableAt_iff_differentiableAt]

attribute [simp] mdifferentiableAt_iff_differentiableAt

-- XXX: make a better version of fderiv_const_smul'', with field coefficients instead!
theorem fderiv_section_smul {𝕜 E E' : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    (σ : (x : E) → Trivial E E' x) (a : 𝕜) (x : E) :
    fderiv 𝕜 (a • σ) x = a • fderiv 𝕜 σ x := by
  obtain (rfl | ha) := eq_or_ne a 0
  · simp
  · have : Invertible a := invertibleOfNonzero ha
    exact fderiv_const_smul'' ..

lemma FiberBundle.trivializationAt.baseSet_mem_nhds {B : Type*} (F : Type*)
    [TopologicalSpace B] [TopologicalSpace F]
    (E : B → Type*) [TopologicalSpace (TotalSpace F E)] [(b : B) → TopologicalSpace (E b)]
    [FiberBundle F E] (b : B) : (trivializationAt F E b |>.baseSet) ∈ 𝓝 b :=
  (trivializationAt F E b).open_baseSet.eventually_mem (FiberBundle.mem_baseSet_trivializationAt' b)

omit [IsManifold I 0 M] [∀ (x : M), IsTopologicalAddGroup (V x)] [(x : M) → Module 𝕜 (V x)]
     [(x : M) → AddCommGroup (V x)]
     [∀ (x : M), ContinuousSMul 𝕜 (V x)] [VectorBundle 𝕜 F V] in
variable {I F V x} in
/-- If two sections `σ` and `σ'` are equal on a neighbourhood `s` of `x`,
if one is differentiable at `x` then so is the other.
Issue: EventuallyEq does not work for dependent functions. -/
lemma mdifferentiableAt_dependent_congr {σ σ' : Π x : M, V x} {s : Set M} (hs : s ∈ nhds x)
    (hσ₁ : MDifferentiableAt% (T% σ) x)
    (hσ₂ : ∀ x ∈ s, σ x = σ' x) :
    MDifferentiableAt% (T% σ') x := by
  apply MDifferentiableAt.congr_of_eventuallyEq hσ₁
  -- TODO: split off a lemma?
  apply Set.EqOn.eventuallyEq_of_mem _ hs
  intro x hx
  simp [hσ₂, hx]

omit [IsManifold I 0 M] [∀ (x : M), IsTopologicalAddGroup (V x)] [(x : M) → Module 𝕜 (V x)]
     [∀ (x : M), ContinuousSMul 𝕜 (V x)] [VectorBundle 𝕜 F V] [(x : M) → AddCommGroup (V x)] in
variable {I F V x} in
/-- If two sections `σ` and `σ'` are equal on a neighbourhood `s` of `x`,
one is differentiable at `x` iff the other is. -/
lemma mfderiv_dependent_congr_iff {σ σ' : Π x : M, V x} {s : Set M} (hs : s ∈ nhds x)
    (hσ : ∀ x ∈ s, σ x = σ' x) :
    MDifferentiableAt% (T% σ) x  ↔
    MDifferentiableAt% (T% σ') x :=
  ⟨fun h ↦ mdifferentiableAt_dependent_congr hs h hσ,
   fun h ↦ mdifferentiableAt_dependent_congr hs h (fun x hx ↦ (hσ x hx).symm)⟩

end prerequisites

@[ext]
structure CovariantDerivative where
  toFun : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)
  addX : ∀ (X X' : Π x : M, TangentSpace I x) (σ : Π x : M, V x),
    toFun (X + X') σ = toFun X σ + toFun X' σ
  smulX : ∀ (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (f : M → 𝕜),
    toFun (f • X) σ = f • toFun X σ
  addσ : ∀ (X : Π x : M, TangentSpace I x) (σ σ' : Π x : M, V x) (x : M),
    MDifferentiableAt% (T% σ) x → MDifferentiableAt% (T% σ') x
    → toFun X (σ + σ') x = toFun X σ x + toFun X σ' x
  leibniz : ∀ (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (f : M → 𝕜) (x : M),
    MDifferentiableAt% (T% σ) x → MDifferentiableAt% f x
    → toFun X (f • σ) x = (f • toFun X σ) x + (bar _ <| mfderiv I 𝓘(𝕜) f x (X x)) • σ x
  smul_const_σ : ∀ (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (a : 𝕜),
    toFun X (a • σ) = a • toFun X σ

variable {I} in
structure IsCovariantDerivativeOn
    (f : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)) (s : Set M) : Prop where
  -- All the same axioms as CovariantDerivative, but restricted to the set s.
  addX : ∀ (X X' : Π x : M, TangentSpace I x) (σ : Π x : M, V x),
    ∀ x ∈ s, f (X + X') σ x = f X σ x + f X' σ x
  smulX : ∀ (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (g : M → 𝕜),
    ∀ x ∈ s, f (g • X) σ x = g x • f X σ x
  addσ : ∀ (X : Π x : M, TangentSpace I x) {σ σ' : Π x : M, V x}, ∀ x ∈ s,
    MDifferentiableAt% (T% σ) x → MDifferentiableAt% (T% σ') x
    → f X (σ + σ') x = f X σ x + f X σ' x
  leibniz : ∀ (X : Π x : M, TangentSpace I x) {σ : Π x : M, V x} {g : M → 𝕜}, ∀ x ∈ s,
    MDifferentiableAt% (T% σ) x → MDifferentiableAt% g x
    → f X (g • σ) x = (g • f X σ) x + (bar _ <| mfderiv I 𝓘(𝕜) g x (X x)) • σ x
  smul_const_σ : ∀ (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (a : 𝕜), ∀ x ∈ s,
    f X (a • σ) x = a • f X σ x

variable {I F V}

omit [IsManifold I 0 M] [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)]
  [VectorBundle 𝕜 F V] in
lemma IsCovariantDerivativeOn.mono
    {f : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)} {s t : Set M}
    (hf : IsCovariantDerivativeOn F V f t) (hst : s ⊆ t) : IsCovariantDerivativeOn F V f s where
  addX X X' σ x hx := hf.addX X X' σ x (hst hx)
  smulX X σ f x hx := hf.smulX X σ f x (hst hx)
  addσ X {_σ _σ'} x hx hσ hσ' := hf.addσ X x (hst hx) hσ hσ'
  leibniz X {_ _} _ hx hσ hf' := hf.leibniz X _ (hst hx) hσ hf'
  smul_const_σ X σ a x hx := hf.smul_const_σ X σ a x (hst hx)

omit [IsManifold I 0 M] [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)]
  [VectorBundle 𝕜 F V] in
lemma IsCovariantDerivativeOn.iUnion {ι : Type*}
    {f : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)} {s : ι → Set M}
    (hf : ∀ i, IsCovariantDerivativeOn F V f (s i)) : IsCovariantDerivativeOn F V f (⋃ i, s i) where
  addX X X' σ x hx := by
    obtain ⟨si, ⟨i, rfl⟩, hxsi⟩ := hx
    exact (hf i).addX _ _ _ _ hxsi
  smulX X σ f x hx := by
    obtain ⟨si, ⟨i, rfl⟩, hxsi⟩ := hx
    exact (hf i).smulX _ _ _ _ hxsi
  addσ X σ σ' x hx hσ hσ' := by
    obtain ⟨si, ⟨i, rfl⟩, hxsi⟩ := hx
    exact (hf i).addσ _ _ hxsi hσ hσ'
  leibniz X σ f x hx hσ hf' := by
    obtain ⟨si, ⟨i, rfl⟩, hxsi⟩ := hx
    exact (hf i).leibniz _ _ hxsi hσ hf'
  smul_const_σ X σ a x hx := by
    obtain ⟨si, ⟨i, rfl⟩, hxsi⟩ := hx
    exact (hf i).smul_const_σ _ _ _ _ hxsi

namespace CovariantDerivative

attribute [coe] toFun

/-- Coercion of a `CovariantDerivative` to function -/
instance : CoeFun (CovariantDerivative I F V)
    fun _ ↦ (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x) :=
  ⟨fun e ↦ e.toFun⟩

omit [IsManifold I 0 M] [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)]
  [VectorBundle 𝕜 F V] in
lemma isCovariantDerivativeOn_univ (cov : CovariantDerivative I F V) :
    IsCovariantDerivativeOn F V cov Set.univ where
  addX X X' σ x _ := by simp [cov.addX]
  smulX X σ f x _ := by simp [cov.smulX]
  addσ X σ σ' x _ hσ hσ' := cov.addσ _ _ _ _ hσ hσ'
  leibniz X σ f x _ hσ hf := cov.leibniz X _ _ _ hσ hf
  smul_const_σ X σ a x _ := by simp [cov.smul_const_σ X σ a]

omit [IsManifold I 0 M] [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)]
  [VectorBundle 𝕜 F V] in
lemma isCovariantDerivativeOn (cov : CovariantDerivative I F V) {s : Set M} :
    IsCovariantDerivativeOn F V cov s := by
  apply (cov.isCovariantDerivativeOn_univ).mono (fun ⦃a⦄ a ↦ trivial)

/-- If `f : Vec(M) × Γ(E) → Vec(M)` is a covariant on `Set.univ`, it is a covariant derivative. -/
def of_isCovariantDerivativeOn_univ
    {f : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    (hf : IsCovariantDerivativeOn F V f Set.univ) : CovariantDerivative I F V where
  toFun := f
  addX X X' σ := by ext; simp [hf.addX X X' σ]
  smulX X σ g := by ext; simp [hf.smulX X σ]
  addσ X σ σ' x hσ hf' := hf.addσ _ _ trivial hσ hf'
  leibniz X σ f x hσ hf' := hf.leibniz X x trivial hσ hf'
  smul_const_σ X σ a := by ext; simp [hf.smul_const_σ X σ a]

omit [IsManifold I 0 M] [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)]
  [VectorBundle 𝕜 F V] in
@[simp]
lemma of_isCovariantDerivativeOn_univ_coe
    {f : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    (hf : IsCovariantDerivativeOn F V f Set.univ) :
    of_isCovariantDerivativeOn_univ hf = f := rfl

omit [IsManifold I 0 M] [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)]
  [VectorBundle 𝕜 F V] in
/-- If `f : Vec(M) × Γ(E) → Vec(M)` is a covariant derivative on each set in an open cover,
it is a covariant derivative. -/
def of_isCovariantDerivativeOn_of_open_cover {ι : Type*} {s : ι → Set M}
    {f : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    (hf : ∀ i, IsCovariantDerivativeOn F V f (s i)) (hs : ⋃ i, s i = Set.univ) :
    CovariantDerivative I F V :=
  of_isCovariantDerivativeOn_univ (hs ▸ IsCovariantDerivativeOn.iUnion hf)

omit [IsManifold I 0 M] [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)]
  [VectorBundle 𝕜 F V] in
@[simp]
lemma of_isCovariantDerivativeOn_of_open_cover_coe {ι : Type*} {s : ι → Set M}
    {f : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    (hf : ∀ i, IsCovariantDerivativeOn F V f (s i)) (hs : ⋃ i, s i = Set.univ) :
    of_isCovariantDerivativeOn_of_open_cover hf hs = f := rfl

-- TODO: generalise all the lemmas below to IsCovariantDerivativeOn

/--
A covariant derivative ∇ is called of class `C^k` iff,
whenever `X` is a `C^k` section and `σ` a `C^{k+1}` section, the result `∇ X σ` is a `C^k` section.
This is a class so typeclass inference can deduce this automatically.
-/
class _root_.IsCkConnection (cov : CovariantDerivative I F V) (k : ℕ∞) [IsManifold I 1 M] where
  regularity : ∀ {X : Π x : M, TangentSpace I x} {σ : Π x : M, V x},
    ContMDiff I (I.prod 𝓘(𝕜, F)) (k + 1) (T% σ) → ContMDiff I (I.prod 𝓘(𝕜, E)) k (T% X) →
    ContMDiff I (I.prod 𝓘(𝕜, F)) k (T% (cov X σ))

-- future: if g is a C^k metric on a manifold M, the corresponding Levi-Civita connection
-- is of class C^k (up to off-by-one errors)

omit [IsManifold I 0 M] [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)]
  [VectorBundle 𝕜 F V] in
@[simp]
lemma zeroX (cov : CovariantDerivative I F V) (σ : Π x : M, V x) : cov 0 σ = 0 := by
  have := cov.addX (0 : (x : M) → TangentSpace I x) (0 : (x : M) → TangentSpace I x) σ
  simpa using this

omit [IsManifold I 0 M] [∀ (x : M), IsTopologicalAddGroup (V x)]
     [∀ (x : M), ContinuousSMul 𝕜 (V x)] in
@[simp]
lemma zeroσ (cov : CovariantDerivative I F V) (X : Π x : M, TangentSpace I x) : cov X 0 = 0 := by
  ext x
  have : MDifferentiableAt% (T% fun x ↦ (0 : V x)) x := by
    exact (contMDiff_zeroSection 𝕜 V).mdifferentiableAt le_rfl
  have := cov.addσ X (0 : (x : M) → V x) (0 : (x : M) → V x) x this this
  simpa using this

omit [IsManifold I 0 M] [∀ (x : M), IsTopologicalAddGroup (V x)]
  [∀ (x : M), ContinuousSMul 𝕜 (V x)] [VectorBundle 𝕜 F V] in
/-- If `σ` and `σ'` are equal sections of `E`, they have equal covariant derivatives. -/
lemma congr_σ (cov : CovariantDerivative I F V)
    (X : Π x : M, TangentSpace I x) {σ σ' : Π x : M, V x} (hσ : ∀ x, σ x = σ' x) (x : M) :
    cov X σ x = cov X σ' x := by
  simp [funext hσ]

omit [IsManifold I 0 M] [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)]
  [VectorBundle 𝕜 F V] in
lemma sum_X (cov : CovariantDerivative I F V)
    {ι : Type*} {s : Finset ι} {X : ι → Π x : M, TangentSpace I x} {σ : Π x : M, V x} :
    cov (∑ i ∈ s, X i) σ = ∑ i ∈ s, cov (X i) σ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha h => simp [Finset.sum_insert ha, ← h, cov.addX]

/-- A convex combination of covariant derivatives is a covariant derivative. -/
@[simps]
def convexCombination (cov cov' : CovariantDerivative I F V) (f : M → 𝕜) :
    CovariantDerivative I F V where
  toFun X s := (f • (cov X s)) + (1 - f) • (cov' X s)
  addX X X' σ := by simp only [cov.addX, cov'.addX]; module
  smulX X σ f := by simp only [cov.smulX, cov'.smulX]; module
  addσ X σ σ' x hσ hσ' := by
    simp [cov.addσ X σ σ' x hσ hσ', cov'.addσ X σ σ' x hσ hσ']
    module
  smul_const_σ X {σ a} /-hσ-/ := by
    simp [cov.smul_const_σ, cov'.smul_const_σ]
    module
  leibniz X σ f x hσ hf := by
    simp [cov.leibniz X σ f x hσ hf, cov'.leibniz X σ f x hσ hf]
    module

/-- A finite convex combination of covariant derivatives is a covariant derivative. -/
def convexCombination' {ι : Type*} {s : Finset ι} [Nonempty s]
    (cov : ι → CovariantDerivative I F V) {f : ι → M → 𝕜} (hf : ∑ i ∈ s, f i = 1) :
    CovariantDerivative I F V where
  toFun X t := ∑ i ∈ s, (f i) • (cov i) X t
  addX X X' σ := by
    rw [← Finset.sum_add_distrib]
    congr
    ext i
    simp [(cov i).addX]
  smulX X σ g := by
    rw [Finset.smul_sum]
    congr
    ext i
    simp [(cov i).smulX]
    module
  addσ X σ σ' x hσ hσ' := by
    -- XXX: is this nicer using induction?
    classical
    induction s using Finset.induction with
    | empty => simp
    | insert a s has h =>
      simp [Finset.sum_insert has]
      sorry
  smul_const_σ X {σ a} /-hσ-/ := by
    rw [Finset.smul_sum]
    congr
    ext i x
    simp [(cov i).smul_const_σ]
    module
  leibniz X σ g x hσ hf := by
    calc (∑ i ∈ s, f i • (cov i) X (g • σ)) x
      _ = ∑ i ∈ s, ((g • (f i • (cov i) X σ)) x
            + f i x • (bar (g x)) ((mfderiv I 𝓘(𝕜, 𝕜) g x) (X x)) • σ x) :=
        sorry -- rewrite using (cov i).leibniz
      _ = ∑ i ∈ s, ((g • (f i • (cov i) X σ)) x
        + ∑ i ∈ s, f i x • (bar (g x)) ((mfderiv I 𝓘(𝕜, 𝕜) g x) (X x)) • σ x) := by
        rw [Finset.sum_add_distrib]
        simp; sorry
      _ = (g • ∑ i ∈ s, f i • (cov i) X σ) x + (bar (g x)) ((mfderiv I 𝓘(𝕜, 𝕜) g x) (X x)) • σ x :=
        -- use hf and pull out g...
        sorry

omit [IsManifold I 0 M]
  [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)] in
/-- A convex combination of two `C^k` connections is a `C^k` connection. -/
lemma convexCombination_isRegular [IsManifold I 1 M] (cov cov' : CovariantDerivative I F V)
    {f : M → 𝕜} {n : ℕ∞} (hf : ContMDiff I 𝓘(𝕜) n f)
    (hcov : IsCkConnection cov n) (hcov' : IsCkConnection cov' n) :
    IsCkConnection (convexCombination cov cov' f) n where
  regularity {X σ} hX hσ := by
    apply contMDiff_add_section
    · exact contMDiff_smul_section hf <| hcov.regularity hX hσ
    · exact contMDiff_smul_section (contMDiff_const.sub hf) <| hcov'.regularity hX hσ

omit [IsManifold I 0 M]
  [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)] in
/-- A convex combination of finitely many `C^k` connections is a `C^k` connection. -/
lemma convexCombination'_isRegular [IsManifold I 1 M] {ι : Type*} {s : Finset ι} [Nonempty s]
    (cov : ι → CovariantDerivative I F V) {f : ι → M → 𝕜} (hf : ∑ i ∈ s, f i = 1) {n : ℕ∞}
    (hf' : ∀ i ∈ s, ContMDiff I 𝓘(𝕜) n (f i))
    (hcov : ∀ i ∈ s, IsCkConnection (cov i) n) :
    IsCkConnection (convexCombination' cov hf) n where
  regularity {X σ} hX hσ := by
    unfold convexCombination'
    dsimp
    have ms (i) (hi : i ∈ s) : ContMDiff I (I.prod 𝓘(𝕜, F)) n
        (T% (f i • (cov i) X σ)) := by
      apply contMDiff_smul_section (hf' i hi)
      exact IsCkConnection.regularity hX hσ (self := hcov i hi)
    simp only [Finset.sum_apply, Pi.smul_apply']
    exact contMDiff_finsum_section (t := fun i ↦ f i • (cov i) X σ) ms

-- Future: prove a version with a locally finite sum, and deduce that C^k connections always
-- exist (using a partition of unity argument)

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']

variable (E E') in
/-- The trivial connection on a trivial bundle, given by the directional derivative -/
@[simps]
noncomputable def trivial : CovariantDerivative 𝓘(𝕜, E) E'
  (Bundle.Trivial E E') where
  toFun X s := fun x ↦ fderiv 𝕜 s x (X x)
  addX X X' σ := by ext; simp
  smulX X σ c' := by ext; simp
  addσ X σ σ' e hσ hσ' := by
    rw [Bundle.Trivial.mdifferentiableAt_iff] at hσ hσ'
    rw [fderiv_add hσ hσ']
    rfl
  smul_const_σ X σ a := by ext; simp [fderiv_section_smul σ a]
  leibniz X σ f x hσ hf := by
    have : fderiv 𝕜 (f • σ) x = f x • fderiv 𝕜 σ x + (fderiv 𝕜 f x).smulRight (σ x) :=
      fderiv_smul (by simp_all) (by simp_all)
    simp [this, bar]
    rfl

-- TODO: does it make sense to speak of analytic connections? if so, change the definition of
-- regularity and use ∞ from `open scoped ContDiff` instead.

/-- The trivial connection on the trivial bundle is smooth -/
lemma trivial_isSmooth : IsCkConnection (𝕜 := 𝕜) (trivial E E') (⊤ : ℕ∞) where
  regularity {X σ} hX hσ := by
    -- except for local trivialisations, contDiff_infty_iff_fderiv covers this well
    simp only [trivial]
    -- use a local trivialisation
    intro x
    specialize hX x
    -- TODO: use contMDiffOn instead, to get something like
    -- have hX' : ContMDiffOn 𝓘(𝕜, E) (𝓘(𝕜, E).prod 𝓘(𝕜, E')) (∞ + 1)
    --  (T% σ) (trivializationAt x).baseSet := hX.contMDiffOn
    -- then want a version contMDiffOn_totalSpace
    rw [contMDiffAt_totalSpace] at hX ⊢
    simp only [Trivial.fiberBundle_trivializationAt', Trivial.trivialization_apply]
    refine ⟨contMDiff_id _, ?_⟩
    obtain ⟨h₁, h₂⟩ := hX
    -- ... hopefully telling me
    -- have h₂scifi : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E') ∞
    --   (fun x ↦ σ x) (trivializationAt _).baseSet_ := sorry
    simp at h₂
    -- now use ContMDiffOn.congr and contDiff_infty_iff_fderiv,
    -- or perhaps a contMDiffOn version of this lemma?
    sorry

open scoped Classical in
@[simps]
noncomputable def of_endomorphism (A : E → E →L[𝕜] E' →L[𝕜] E') :
    CovariantDerivative 𝓘(𝕜, E) E' (Bundle.Trivial E E') where
  toFun X σ := fun x ↦ fderiv 𝕜 σ x (X x) + A x (X x) (σ x)
  addX X X' σ := by
    ext x
    by_cases h : DifferentiableAt 𝕜 σ x
    · simp [map_add]; abel
    · simp [fderiv_zero_of_not_differentiableAt h]
  smulX X σ c' := by ext; simp
  addσ X σ σ' e hσ hσ' := by
    rw [Bundle.Trivial.mdifferentiableAt_iff] at hσ hσ'
    simp [fderiv_add hσ hσ']
    abel
  smul_const_σ X σ a := by ext; simp [fderiv_section_smul σ a]
  leibniz X σ f x hσ hf := by
    rw [Bundle.Trivial.mdifferentiableAt_iff] at hσ
    rw [mdifferentiableAt_iff_differentiableAt] at hf
    -- have h : DifferentiableAt 𝕜 (f • σ) x := hf.smul hσ
    have : fderiv 𝕜 (f • σ) x = f x • fderiv 𝕜 σ x + (fderiv 𝕜 f x).smulRight (σ x) :=
      fderiv_smul (by simp_all) (by simp_all)
    simp [this, bar]
    module

-- TODO: prove something about the regularity of this connection

section real

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {x : M}

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  -- `F` model fiber
  (n : WithTop ℕ∞)
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  -- `V` vector bundle

/- the following lemmas are subsubmed by tensoriality_criterion
  XXX should they be extracted as separate lemmas (stated twice)?
omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul ℝ (V x)]
  [VectorBundle ℝ F V] in
/-- If `X` and `X'` agree in a neighbourhood of `p`, then `∇_X σ` and `∇_X' σ` agree at `p`. -/
lemma congr_X_of_eventuallyEq (cov : CovariantDerivative I F V) [T2Space M]
    {X X' : Π x : M, TangentSpace I x} {σ : Π x : M, V x} {x : M} {s : Set M} (hs : s ∈ nhds x)
    (hσσ' : ∀ x ∈ s, X x = X' x) :
    cov X σ x = cov X' σ x := by
  -- Choose a smooth bump function ψ with support around `x` contained in `s`
  obtain ⟨ψ, _, hψ⟩ := (SmoothBumpFunction.nhds_basis_support (I := I) hs).mem_iff.1 hs
  -- Observe that `ψ • X = ψ • X'` as dependent functions.
  have (x : M) : ((ψ : M → ℝ) • X) x = ((ψ : M → ℝ) • X') x := by
    by_cases h : x ∈ s
    · simp [hσσ' x h]
    · simp [notMem_support.mp fun a ↦ h (hψ a)]
  -- Then, it's a chain of (dependent) equalities.
  calc cov X σ x
    _ = cov ((ψ : M → ℝ) • X) σ x := by simp [cov.smulX]
    _ = cov ((ψ : M → ℝ) • X') σ x := by rw [funext this]
    _ = cov X' σ x := by simp [cov.smulX]

omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul ℝ (V x)]
  [VectorBundle ℝ F V] in
lemma congr_X_at_aux (cov : CovariantDerivative I F V) [T2Space M] [IsManifold I ∞ M]
    (X : Π x : M, TangentSpace I x) {σ : Π x : M, V x} {x : M}
    (hX : X x = 0) : cov X σ x = 0 := by
  -- Consider the local frame {Xⁱ} on TangentSpace I x induced by chartAt H x.
  -- To do so, choose a basis of TangentSpace I x = E.
  let n : ℕ := Module.finrank ℝ E
  let b : Basis (Fin n) ℝ E := Module.finBasis ℝ E
  let e := trivializationAt E (TangentSpace I) x
  let Xi (i : Fin n) := b.localFrame e i
  -- Write X in coordinates: X = ∑ i, a i • Xi i near `x`.
  let a := fun i ↦ b.localFrame_repr e i X
  have : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have aux : ∀ᶠ (x' : M) in 𝓝 x, X x' = ∑ i, a i x' • Xi i x' := b.localFrame_repr_spec this X
  have (i : Fin n) : a i x = 0 := b.localFrame_repr_apply_zero_at hX i
  calc cov X σ x
    _ = cov (∑ i, a i • Xi i) σ x := cov.congr_X_of_eventuallyEq aux (by simp)
    _ = ∑ i, cov (a i • Xi i) σ x := by rw [cov.sum_X]; simp
    _ = ∑ i, a i x • cov (Xi i) σ x := by
      congr; ext i; simp [cov.smulX (Xi i) σ (a i)]
    _ = 0 := by simp [this] -/

omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul ℝ (V x)] in
/-- `cov X σ x` only depends on `X` via `X x` -/
lemma congr_X_at (cov : CovariantDerivative I F V) [T2Space M] [IsManifold I ∞ M]
    (X X' : Π x : M, TangentSpace I x) {σ : Π x : M, V x} {x : M} (hXX' : X x = X' x) :
    cov X σ x = cov X' σ x := by
  apply tensoriality_criterion' (E := E) (I := I) E (TangentSpace I) F V hXX'
  · intro f X
    rw [cov.smulX]
    rfl
  · intro X X'
    rw [cov.addX]
    rfl

/- TODO: are these lemmas still useful after the general tensoriality lemma?
are they worth extracting separately?
omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul ℝ (V x)]
  [VectorBundle ℝ F V] in
lemma congr_σ_smoothBumpFunction (cov : CovariantDerivative I F V) [T2Space M] [IsManifold I ∞ M]
    (X : Π x : M, TangentSpace I x) {σ : Π x : M, V x}
    (hσ : MDifferentiableAt% (T% σ) x)
    (f : SmoothBumpFunction I x) :
    cov X ((f : M → ℝ) • σ) x = cov X σ x := by
  rw [cov.leibniz _ _ _ _ hσ]
  swap; · apply f.contMDiff.mdifferentiable (by norm_num)
  calc _
    _ = cov X σ x + 0 := ?_
    _ = cov X σ x := by rw [add_zero]
  simp [f.eq_one, f.eventuallyEq_one.mfderiv_eq]
  rw [show mfderiv I 𝓘(ℝ, ℝ) 1 x = 0 by apply mfderiv_const]
  left
  rfl

omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul ℝ (V x)]
  [VectorBundle ℝ F V] in
lemma congr_σ_of_eventuallyEq
    (cov : CovariantDerivative I F V) [T2Space M] [IsManifold I ∞ M]
    (X : Π x : M, TangentSpace I x) {σ σ' : Π x : M, V x} {x : M} {s : Set M} (hs : s ∈ nhds x)
    (hσ : MDifferentiableAt% (T% σ) x)
    (hσσ' : ∀ x ∈ s, σ x = σ' x) :
    cov X σ x = cov X σ' x := by
  -- Choose a smooth bump function ψ with support around `x` contained in `s`
  obtain ⟨ψ, _, hψ⟩ := (SmoothBumpFunction.nhds_basis_support (I := I) hs).mem_iff.1 hs
  -- Observe that `ψ • σ = ψ • σ'` as dependent functions.
  have (x : M) : ((ψ : M → ℝ) • σ) x = ((ψ : M → ℝ) • σ') x := by
    by_cases h : x ∈ s
    · simp [hσσ' x h]
    · simp [notMem_support.mp fun a ↦ h (hψ a)]
  -- Then, it's a chain of (dependent) equalities.
  calc cov X σ x
    _ = cov X ((ψ : M → ℝ) • σ) x := by rw [cov.congr_σ_smoothBumpFunction _ hσ]
    _ = cov X ((ψ : M → ℝ) • σ') x := cov.congr_σ _ _ (by simp [this])
    _ = cov X σ' x := by
      simp [cov.congr_σ_smoothBumpFunction, mdifferentiableAt_dependent_congr hs hσ hσσ']
-/

-- TODO: prove that `cov X σ x` depends on σ only via σ(X) and the 1-jet of σ at x

/-- The difference of two covariant derivatives, as a function `Γ(TM) × Γ(E) → Γ(E)`.
Future lemmas will upgrade this to a map `TM ⊕ E → E`. -/
def differenceAux (cov cov' : CovariantDerivative I F V) :
    (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x) :=
  fun X σ ↦ cov X σ - cov' X σ

omit [FiniteDimensional ℝ E] [∀ (x : M), IsTopologicalAddGroup (V x)]
  [∀ (x : M), ContinuousSMul ℝ (V x)] [VectorBundle ℝ F V] in
@[simp]
lemma differenceAux_apply (cov cov' : CovariantDerivative I F V)
    (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) :
    differenceAux cov cov' X σ = cov X σ - cov' X σ := rfl

omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul ℝ (V x)]
  [VectorBundle ℝ F V] [FiniteDimensional ℝ E] in
lemma differenceAux_smul_eq (cov cov' : CovariantDerivative I F V)
    (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (f : M → ℝ) {x : M}
    (hσ : MDifferentiableAt% (T% σ) x)
    (hf : MDifferentiableAt% f x) :
    differenceAux cov cov' X ((f : M → ℝ) • σ) x = f x • differenceAux cov cov' X σ x:=
  calc _
    _ = cov X ((f : M → ℝ) • σ) x - cov' X ((f : M → ℝ) • σ) x := rfl
    _ = (f x • cov X σ x +  (bar _ <| mfderiv I 𝓘(ℝ) f x (X x)) • σ x)
        - (f x • cov' X σ x +  (bar _ <| mfderiv I 𝓘(ℝ) f x (X x)) • σ x) := by
      simp [cov.leibniz X _ _ _ hσ hf, cov'.leibniz X _ _ _ hσ hf]
    _ = f x • cov X σ x - f x • cov' X σ x := by simp
    _ = f x • (cov X σ x - cov' X σ x) := by simp [smul_sub]
    _ = _ := rfl

omit [FiniteDimensional ℝ E] [∀ (x : M), IsTopologicalAddGroup (V x)]
    [∀ (x : M), ContinuousSMul ℝ (V x)] [VectorBundle ℝ F V] in
lemma differenceAux_smul_eq' (cov cov' : CovariantDerivative I F V)
    (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (f : M → ℝ) (x : M) :
    differenceAux cov cov' (f • X) σ x = f x • differenceAux cov cov' X σ x := by
  simp [differenceAux, cov.smulX, cov'.smulX, smul_sub]

omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul ℝ (V x)] in
/-- The value of `differenceAux cov cov' X σ` at `x₀` depends only on `X x₀` and `σ x₀`. -/
lemma differenceAux_tensorial (cov cov' : CovariantDerivative I F V) [T2Space M] [IsManifold I ∞ M]
    [FiniteDimensional ℝ F] [ContMDiffVectorBundle 1 F V I]
    {X X' : Π x : M, TangentSpace I x} {σ σ' : Π x : M, V x} {x₀ : M}
    (hσ : MDifferentiableAt% (T% σ) x₀)
    (hσ' : MDifferentiableAt% (T% σ') x₀)
    (hXX' : X x₀ = X' x₀) (hσσ' : σ x₀ = σ' x₀) :
    differenceAux cov cov' X σ x₀ = differenceAux cov cov' X' σ' x₀ := by
  trans cov.differenceAux cov' X' σ x₀
  · let φ : (Π x : M, TangentSpace I x) → (Π x, V x) := fun X ↦ cov.differenceAux cov' X σ
    change φ X x₀ = φ X' x₀
    apply tensoriality_criterion' (E := E) (I := I) E (TangentSpace I) F V hXX'
    · intro f X
      apply differenceAux_smul_eq'
    · intro X X'
      unfold φ CovariantDerivative.differenceAux
      rw [cov.addX, cov'.addX]
      simp
      abel
  · let φ : (Π x : M, V x) → (Π x, V x) := fun σ ↦ cov.differenceAux cov' X' σ
    change φ σ x₀ = φ σ' x₀
    apply tensoriality_criterion (E := E) (I := I) F V F V hσ hσ' hσσ'
    · intro f σ x hf
      exact differenceAux_smul_eq cov cov' X' σ f hf x
    · intro σ σ' hσ hσ'
      unfold φ CovariantDerivative.differenceAux
      simp
      rw [cov.addσ, cov'.addσ] <;> try assumption
      abel

-- TODO: either change `localFrame` to make sure it is everywhere smooth
-- or introduce a cut-off here. First option is probaly better.
-- TODO: comment why we chose the second option in the end, and adapt the definition accordingly
-- new definition: smooth a bump function, then smul with localExtensionOn
variable (I F) in
/-- Extend a vector `v ∈ V x` to a section of the bundle `V`, whose value at `x` is `v`.
The details of the extension are mostly unspecified: for covariant derivatives, the value of
`s` at points other than `x` will not matter (except for shorter proofs).
Thus, we choose `s` to be somewhat nice: our chosen construction is linear in `v`.
-/
noncomputable def extend [FiniteDimensional ℝ F] [T2Space M] {x : M} (v : V x) :
    (x' : M) → V x' :=
  letI b := Basis.ofVectorSpace ℝ F
  letI t := trivializationAt F V x
  -- Choose a smooth bump function ψ near `x`, supported within t.baseSet
  -- and return ψ • V₀ instead.
  letI ht := t.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x)
  let ψ := Classical.choose <| (SmoothBumpFunction.nhds_basis_support (I := I) ht).mem_iff.1 ht
  ψ.toFun • localExtensionOn b t x v

omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul ℝ (V x)] in
-- NB. These two lemmas don't hold for *any* choice of extension of `v`, but they hold for
-- *well-chosen* extensions (such as ours).
-- so, one may argue this is mathematically wrong, but it encodes the "choice some extension
-- with this and that property" nicely
-- a different proof would be to argue only the value at a point matters for cov
@[simp]
lemma extend_add [FiniteDimensional ℝ F] [T2Space M] {x : M} (v v' : V x) :
    extend I F (v + v') = extend I F v + extend I F v' := by
  simp [extend, localExtensionOn_add]

omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul ℝ (V x)] in
@[simp]
lemma extend_smul [FiniteDimensional ℝ F] [T2Space M] {a : ℝ} (v  : V x) :
  extend I F (a • v) = a • extend I F v := by simp [extend, localExtensionOn_smul]; module

omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul ℝ (V x)] in
@[simp] lemma extend_apply_self [FiniteDimensional ℝ F] [T2Space M] {x : M} (v : V x) :
    extend I F v x = v := by
  simpa [extend] using
    localExtensionOn_apply_self _ _ (FiberBundle.mem_baseSet_trivializationAt' x) v

omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul ℝ (V x)] in
/-- If `ψ: M → ℝ` a smooth bump function and `s` is a section of a smooth vector bundle `V → M`,
the scalar product `ψ s` is `C^n` if `s` is `C^n` on an open set containing `tsupport ψ`.
This is a vector bundle analogue of `contMDiff_of_tsupport`: the total space of `V` has no zero,
but we only consider sections of the form `ψ s`. -/
lemma _root_.contMDiff_section_of_smul_smoothBumpFunction [T2Space M] [IsManifold I ∞ M]
    {s : Π (x : M), V x} {ψ : SmoothBumpFunction I x} {t : Set M}
    (hs : ContMDiffOn I (I.prod 𝓘(ℝ, F)) n (T% s) t)
    (ht : IsOpen t) (ht' : tsupport ψ ⊆ t) (hn : n ≤ ∞) :
    ContMDiff I (I.prod 𝓘(ℝ, F)) n (T% fun x ↦ (ψ x • s x)) := by
  apply contMDiff_of_contMDiffOn_union_of_isOpen
      (contMDiffOn_smul_section (ψ.contMDiff.of_le hn).contMDiffOn hs) ?_ ?_ ht
      (isOpen_compl_iff.mpr <| isClosed_tsupport ψ)
  · apply ((contMDiff_zeroSection _ _).contMDiffOn (s := (tsupport ψ)ᶜ)).congr
    intro y hy
    simp [image_eq_zero_of_notMem_tsupport hy, zeroSection]
  · exact Set.compl_subset_iff_union.mp <| Set.compl_subset_compl.mpr ht'

-- unused, but might be nice to have
omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul ℝ (V x)] in
/-- If `ψ: M → ℝ` a smooth bump function and `s` is a section of a smooth vector bundle `V → M`,
the scalar product `ψ s` is `C^n` if `s` is `C^n` at each `x ∈ tsupport ψ`.
This is a vector bundle analogue of `contMDiff_of_tsupport`: the total space of `V` has no zero,
but we only consider sections of the form `ψ s`. -/
lemma _root_.contMDiff_section_of_smul_smoothBumpFunction' [T2Space M] [IsManifold I ∞ M]
    {s : Π (x : M), V x} {ψ : SmoothBumpFunction I x} (hn : n ≤ ∞)
    (hs : ∀ x ∈ tsupport ψ,
      ContMDiffAt I (I.prod 𝓘(ℝ, F)) n (T% fun x ↦ (ψ x • s x)) x) :
    ContMDiff I (I.prod 𝓘(ℝ, F)) n (T% fun x ↦ (ψ x • s x)) := by
  -- apply contMDiff_of_smul_smoothBumpFunction (s := s) (hn := hn) --?_ ?_ ?_ ?_
  sorry

omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul ℝ (V x)] in
lemma contMDiff_extend [IsManifold I ∞ M] [FiniteDimensional ℝ F] [T2Space M]
    [ContMDiffVectorBundle ∞ F V I] {x : M} (σ₀ : V x) :
    ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% extend I F σ₀) := by
  letI t := trivializationAt F V x
  letI ht := t.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x)
  have hx : x ∈ t.baseSet := by exact FiberBundle.mem_baseSet_trivializationAt' x
  let ψ := Classical.choose <| (SmoothBumpFunction.nhds_basis_support (I := I) ht).mem_iff.1 ht
  -- XXX: extract ψ and hψ as helper declarations, perhaps private to prevent API leakage?
  let hψ :=
    Classical.choose_spec <| (SmoothBumpFunction.nhds_basis_support (I := I) ht).mem_iff.1 ht
  apply _root_.contMDiff_section_of_smul_smoothBumpFunction _ ?_ t.open_baseSet hψ.1 le_rfl
  apply contMDiffOn_localExtensionOn _ hx

omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul ℝ (V x)] in
lemma mdifferentiable_extend [IsManifold I ∞ M] [FiniteDimensional ℝ F] [T2Space M]
    [ContMDiffVectorBundle ∞ F V I] {x : M} (σ₀ : V x) :
    MDifferentiable% (T% extend I F σ₀) :=
  contMDiff_extend σ₀ |>.mdifferentiable (by simp)

/-- The difference of two covariant derivatives, as a tensorial map -/
noncomputable def difference
    [FiniteDimensional ℝ F] [T2Space M] [FiniteDimensional ℝ E] [IsManifold I 1 M]
    (cov cov' : CovariantDerivative I F V) :
    Π x : M, TangentSpace I x → V x → V x :=
  fun x X₀ σ₀ ↦ differenceAux cov cov' (extend I E X₀) (extend I F σ₀) x

-- -- Note: we conciously register this lemma in unapplied form,
-- -- but differenceAux_apply: this means the applied form should simplify down all the way,
-- -- but hopefully a mere term difference not.
-- omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul ℝ (V x)] in
-- @[simp]
-- lemma difference_toFun [FiniteDimensional ℝ F] [FiniteDimensional ℝ E] [IsManifold I 1 M]
--     (cov cov' : CovariantDerivative I F V) :
--     cov.difference cov' = fun x X₀ σ₀ ↦ differenceAux cov cov' (extend E X₀)
--       (extend F σ₀) x := rfl

-- show? the map differenceAux to difference is injective

omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul ℝ (V x)] in
@[simp]
lemma difference_apply [FiniteDimensional ℝ F] [IsManifold I 1 M] [T2Space M]
    (cov cov' : CovariantDerivative I F V) (x : M) (X₀ : TangentSpace I x) (σ₀ : V x) :
    difference cov cov' x X₀ σ₀ =
      cov (extend I E X₀) (extend I F σ₀) x - cov' (extend I E X₀) (extend I F σ₀) x := rfl

-- The classification of real connections over a trivial bundle
section classification

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

theorem contDiff_extend {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] (x : E) (y : E') :
    ContDiff ℝ ∞ (extend 𝓘(ℝ, E) E' y (x := x)) := by
  rw [contDiff_iff_contDiffAt]
  intro x'
  rw [← contMDiffAt_iff_contDiffAt]
  simpa [contMDiffAt_section] using contMDiff_extend (V := Trivial E E') y x'

@[simps]
noncomputable def endomorph_of_trivial_aux [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    (cov : CovariantDerivative 𝓘(ℝ, E) E' (Bundle.Trivial E E')) (x X : E) : E' →ₗ[ℝ] E' where
  toFun := difference cov (CovariantDerivative.trivial E E') x X
  map_add' y y' := by
    have A : fderiv ℝ ((extend 𝓘(ℝ, E) E' y  (x := x)) + extend 𝓘(ℝ, E) E' y' (x := x)) x =
        fderiv ℝ (extend 𝓘(ℝ, E) E' y (x := x)) x + fderiv ℝ (extend 𝓘(ℝ, E) E' y' (x := x)) x := by
      rw [fderiv_add] <;> exact (contDiff_extend x _).contDiffAt.differentiableAt (by simp)
    have B : cov (extend 𝓘(ℝ, E) E X (x := x))
        (extend 𝓘(ℝ, E) E' y (x := x) + extend 𝓘(ℝ, E) E' y' (x := x)) x =
      cov (extend 𝓘(ℝ, E) E X (x := x)) (extend 𝓘(ℝ, E) E' y (x := x)) x +
        cov (extend 𝓘(ℝ, E) E X (x := x)) (extend 𝓘(ℝ, E) E' y' (x := x)) x := by
      apply cov.addσ
      · exact (contMDiff_extend _ _).mdifferentiableAt (n := ∞) (hn := by norm_num)
      · apply (contMDiff_extend _ _).mdifferentiableAt (n := ∞) (hn := by norm_num)
    simp [A, B]
    module
  map_smul' a v := by
    simp [fderiv_section_smul, cov.smul_const_σ]
    module

@[simps!]
noncomputable def endomorph_of_trivial_aux' [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    (cov : CovariantDerivative 𝓘(ℝ, E) E' (Bundle.Trivial E E')) (x X : E) : E' →L[ℝ] E' where
  toLinearMap := cov.endomorph_of_trivial_aux x X
  cont := LinearMap.continuous_of_finiteDimensional _

-- Not marked simp, as unfolding this is not always desirable.
noncomputable def endomorph_of_trivial_aux'' [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    (cov : CovariantDerivative 𝓘(ℝ, E) E' (Bundle.Trivial E E')) (x : E) : E →ₗ[ℝ] E' →L[ℝ] E' where
  toFun X := cov.endomorph_of_trivial_aux' x X
  map_add' X Y := by
    ext Z
    simp [cov.addX (extend 𝓘(ℝ, E) E X (x := x))
      (extend 𝓘(ℝ, E) E Y (x := x)) (extend 𝓘(ℝ, E) E' Z (x := x))]
    module
  map_smul' t X := by
    ext Z
    simp only [endomorph_of_trivial_aux'_apply, extend_smul, map_smul, RingHom.id_apply,
      ContinuousLinearMap.coe_smul', Pi.smul_apply]
    -- The following lines should ideally mold into the simp call above.
    trans t • (cov (extend 𝓘(ℝ, E) E X (x := x)) (extend 𝓘(ℝ, E) E' Z (x := x)) x)
      - t • (fderiv ℝ (extend 𝓘(ℝ, E)  E' Z (x := x)) x) X
    swap; · module
    let h := cov.smulX (extend 𝓘(ℝ, E) E X (x := x)) (extend 𝓘(ℝ, E) E' Z (x := x)) (fun x ↦ t)
    simpa using congr_fun h x

@[simps!]
noncomputable def endomorph_of_trivial_aux''' [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    (cov : CovariantDerivative 𝓘(ℝ, E) E' (Bundle.Trivial E E')) (x : E) : E →L[ℝ] E' →L[ℝ] E' where
  toLinearMap := cov.endomorph_of_trivial_aux'' x
  cont := LinearMap.continuous_of_finiteDimensional _

/-- Classification of covariant derivatives over a trivial vector bundle: every connection
is of the form `D + A`, where `D` is the trivial covariant derivative, and `A` a zeroth-order term

For technical reasons, this is only almost true: the left hand sides agree for all `X`, `σ` and `x`
such that `σ` is differentiable at `x`. (Since the literature mostly considers smooth connections,
this is not an issue for mathematical practice at all.)
The reason is because of the construction of a covariant derivative from a zero-order term `A`:
`of_endomorphism A X₀ σ₀` is defined by turning the tangent vectors `X₀` and `σ₀` at `x`
into vector fields near `x` --- which are smooth by construction. Thus, if `σ` is not differentiable
at `x`, `of_endomorphism A` at `x` uses a smooth extension of `σ x`, with different results.
-/
lemma exists_endomorph [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    (cov : CovariantDerivative 𝓘(ℝ, E) E' (Bundle.Trivial E E')) :
    ∃ (A : E → E →L[ℝ] E' →L[ℝ] E'),
    ∀ X : (x : E) → TangentSpace 𝓘(ℝ, E) x, ∀ σ : (x : E) → Trivial E E' x, ∀ x : E,
    MDifferentiableAt% (T% σ) x →
    cov X σ x = (CovariantDerivative.of_endomorphism A) X σ x := by
  use cov.endomorph_of_trivial_aux'''
  intro X σ x hσ
  -- TODO: this is unfolding too much; need to fix this manually below...
  -- think about a better design that actually works...
  simp only [of_endomorphism_toFun, endomorph_of_trivial_aux'''_apply_apply]
  rw [← CovariantDerivative.trivial_toFun]
  have h₁ : cov X σ x - (trivial E E') X σ x = cov.difference (trivial E E') x (X x) (σ x) := by
    -- Do not unfold differenceAux: we use the tensoriality of differenceAux.
    rw [difference]
    apply differenceAux_tensorial cov (trivial E E') hσ ?_
      (extend_apply_self (X x)).symm (extend_apply_self (σ x)).symm
    exact ((contMDiff_extend _).contMDiffAt).mdifferentiableAt (by norm_num)
  have h₂ : cov.difference (trivial E E') x (X x) (σ x) =
      cov (extend 𝓘(ℝ, E) E (X x)) (extend 𝓘(ℝ, E) E' (σ x)) x
        - (fderiv ℝ (extend 𝓘(ℝ, E) E' (σ x) (x := x)) x) (X x) := by
    simp
  rw [← h₂, ← h₁]
  module

end classification

section horiz

def proj (cov : CovariantDerivative I F V) (e : TotalSpace F V) :
    TangentSpace (I.prod 𝓘(ℝ, F)) e →L[ℝ] V e.proj := by
  sorry

noncomputable def horiz (cov : CovariantDerivative I F V) (e : TotalSpace F V) :
    Submodule ℝ (TangentSpace (I.prod 𝓘(ℝ, F)) e) :=
  LinearMap.ker (cov.proj e)

noncomputable def _root_.Bundle.vert (e : TotalSpace F V) :
    Submodule ℝ (TangentSpace (I.prod 𝓘(ℝ, F)) e) :=
  LinearMap.ker (mfderiv (I.prod 𝓘(ℝ, F)) I Bundle.TotalSpace.proj e)

lemma horiz_vert_direct_sum (cov : CovariantDerivative I F V) (e : TotalSpace F V) :
    IsCompl (cov.horiz e) (vert e) := by
  sorry

variable [IsManifold I 1 M]
variable {cov : CovariantDerivative I F V}

lemma proj_mderiv {X : Π x : M, TangentSpace I x} {σ : Π x : M, V x} (x : M)
    (hX : MDifferentiableAt% (T% X) x)
    (hσ : MDifferentiableAt% (T% σ) x) :
    cov X σ x = cov.proj (σ x)
      (mfderiv I (I.prod 𝓘(ℝ, F)) (T% σ) x (X x)) := by
  sorry

end horiz

section torsion

variable [h : IsManifold I ∞ M]

-- The torsion tensor of a covariant derivative on the tangent bundle `TM`.
variable {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}

omit [FiniteDimensional ℝ E]

variable (cov) in
noncomputable def torsion :
    (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x) :=
  fun X Y ↦ cov X Y - cov Y X - VectorField.mlieBracket I X Y

variable {X X' Y : Π x : M, TangentSpace I x}

variable (X) in
lemma torsion_self : torsion cov X X = 0 := by
  simp [torsion]

variable (X Y) in
lemma torsion_antisymm : torsion cov X Y = - torsion cov Y X := by
  simp only [torsion]
  rw [VectorField.mlieBracket_swap]
  module

variable (X) in
@[simp]
lemma torsion_zero : torsion cov 0 X = 0 := by
  ext x
  simp [torsion]

variable (X) in
@[simp]
lemma torsion_zero' : torsion cov X 0 = 0 := by rw [torsion_antisymm, torsion_zero]; simp

variable (Y) in
lemma torsion_add_left_apply [CompleteSpace E] {x : M}
    (hX : MDifferentiableAt% (T% X) x)
    (hX' : MDifferentiableAt% (T% X') x) :
    torsion cov (X + X') Y x = torsion cov X Y x + torsion cov X' Y x := by
  simp [torsion, cov.addX]
  rw [cov.addσ _ X X' _ hX hX', VectorField.mlieBracket_add_left hX hX']
  module

variable (Y) in
lemma torsion_add_left [CompleteSpace E]
    (hX : MDifferentiable% (T% X))
    (hX' : MDifferentiable% (T% X')) :
    torsion cov (X + X') Y = torsion cov X Y + torsion cov X' Y := by
  ext x
  exact cov.torsion_add_left_apply _ (hX x) (hX' x)

lemma torsion_add_right_apply [CompleteSpace E] {x : M}
    (hX : MDifferentiableAt% (T% X) x)
    (hX' : MDifferentiableAt% (T% X') x) :
    torsion cov Y (X + X') x = torsion cov Y X x + torsion cov Y X' x := by
  rw [torsion_antisymm, Pi.neg_apply,
    cov.torsion_add_left_apply _ hX hX', torsion_antisymm Y, torsion_antisymm Y]
  simp; abel

lemma torsion_add_right [CompleteSpace E]
    (hX : MDifferentiable% (T% X))
    (hX' : MDifferentiable% (T% X')) :
    torsion cov Y (X + X') = torsion cov Y X + torsion cov Y X' := by
  rw [torsion_antisymm, torsion_add_left _ hX hX', torsion_antisymm X, torsion_antisymm X']; module

variable (Y) in
lemma torsion_smul_left_apply [CompleteSpace E] {f : M → ℝ} {x : M} (hf : MDifferentiableAt% f x)
    (hX : MDifferentiableAt% (T% X) x) :
    torsion cov (f • X) Y x = f x • torsion cov X Y x := by
  simp only [torsion, cov.smulX, Pi.sub_apply, Pi.smul_apply']
  rw [cov.leibniz Y X f x hX hf, VectorField.mlieBracket_smul_left hf hX]
  simp [bar, smul_sub]
  abel

variable (Y) in
lemma torsion_smul_left [CompleteSpace E] {f : M → ℝ} (hf : MDifferentiable% f)
    (hX : MDifferentiable% (T% X)) :
    torsion cov (f • X) Y = f • torsion cov X Y := by
  ext x
  exact cov.torsion_smul_left_apply _ (hf x) (hX x)

variable (X) in
lemma torsion_smul_right_apply [CompleteSpace E] {f : M → ℝ} {x : M} (hf : MDifferentiableAt% f x)
    (hX : MDifferentiableAt% (T% Y) x) :
    torsion cov X (f • Y) x = f x • torsion cov X Y x := by
  rw [torsion_antisymm, Pi.neg_apply, torsion_smul_left_apply X hf hX, torsion_antisymm X]
  simp

variable (X) in
lemma torsion_smul_right [CompleteSpace E] {f : M → ℝ} (hf : MDifferentiable% f)
    (hY : MDifferentiable% (T% Y)) :
    torsion cov X (f • Y) = f • torsion cov X Y := by
  ext x
  apply cov.torsion_smul_right_apply _ (hf x) (hY x)

omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul ℝ (V x)] in
/-- The torsion of a covariant derivative is tensorial:
the value of `torsion cov X Y` at `x₀` depends only on `X x₀` and `Y x₀`. -/
def torsion_tensorial [T2Space M] [IsManifold I ∞ M]
    [FiniteDimensional ℝ F] [ContMDiffVectorBundle 1 F V I]
    {X X' Y Y' : Π x : M, TangentSpace I x} {x₀ : M}
    (hX : MDifferentiableAt% (T% X) x₀) (hX' : MDifferentiableAt% (T% X') x₀)
    (hY : MDifferentiableAt% (T% Y) x₀) (hY' : MDifferentiableAt% (T% Y') x₀)
    (hXX' : X x₀ = X' x₀) (hYY' : Y x₀ = Y' x₀) :
    (torsion cov X Y) x₀ = (torsion cov X' Y') x₀ := by
  apply tensoriality_criterion₂ I E (TangentSpace I) E (TangentSpace I) hX hX' hY hY' hXX' hYY'
  · intro f σ τ hf hσ
    exact cov.torsion_smul_left_apply _ hf hσ
  · intro σ σ' τ hσ hσ'
    exact cov.torsion_add_left_apply _ hσ hσ'
  · intros f σ σ' hf hσ'
    exact cov.torsion_smul_right_apply _ hf hσ'
  · intro σ τ τ' hτ hτ'
    exact cov.torsion_add_right_apply hτ hτ'

variable (cov) in
/-- A covariant derivation is called **torsion-free** iff its torsion tensor vanishes. -/
def IsTorsionFree : Prop := torsion cov = 0

lemma isTorsionFree_def : IsTorsionFree cov ↔ torsion cov = 0 := by simp [IsTorsionFree]

-- This should be obvious, I'm doing something wrong.
lemma isTorsionFree_iff : IsTorsionFree cov ↔
    ∀ X Y, cov X Y - cov Y X = VectorField.mlieBracket I X Y := by
  simp [IsTorsionFree]
  constructor
  · intro h
    intro X Y
    have : torsion cov X Y = 0 := sorry
    rw [torsion] at this
    sorry
  · intro h
    ext X Y x
    specialize h X Y
    apply congr_fun
    simp_all [torsion]

-- lemma the trivial connection on a normed space is torsion-free
-- lemma trivial.isTorsionFree : IsTorsionFree (TangentBundle 𝓘(ℝ, E) E) := sorry

-- lemma: tangent bundle of E is trivial -> there exists a single trivialisation with baseSet univ
-- make a new abbrev Bundle.Trivial.globalFrame --- which is localFrame for the std basis of F,
--    w.r.t. to this trivialisation
-- add lemmas: globalFrame is contMDiff globally

-- proof of above lemma: write sections s and t in the global frame above
-- by linearity (proven above), suffices to consider s = s^i and t = s^j (two sections in the frame)
-- compute: their Lie bracket is zero
-- compute: the other two terms cancel, done

end torsion

end real

end CovariantDerivative

end
