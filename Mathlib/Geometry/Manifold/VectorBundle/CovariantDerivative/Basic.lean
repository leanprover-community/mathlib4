/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang, Heather Macbeth
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
public import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
public import Mathlib.Geometry.Manifold.MfDerivSMul
public import Mathlib.Geometry.Manifold.VectorBundle.Delaborators

/-!
# Covariant derivatives

TODO: add a more complete doc-string

In the whole file `M` is manifold over any nontrivially normed field `𝕜` and `V` is
a vector bundle over `M` with model fiber `F`.
-/

open Bundle Filter Module Topology Set NormedSpace
open scoped Bundle Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

@[expose] public section -- TODO: think if we want to expose all definitions!

/-!
## Local unbundled theory

-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V]

/-- A function from sections of a vector bundle $V$ over a manifold $M$ to sections of $Hom(TM, E)$
is a covariant derivative over a set $s$ in $M$ if it is additive and satisfies the Leibniz when
applied to sections that are differentiable at a point of $s$. -/
structure IsCovariantDerivativeOn
    (cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x))
    (s : Set M := Set.univ) : Prop where
  add {σ σ' : Π x : M, V x} {x}
    (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x) (hx : x ∈ s := by trivial) :
    cov (σ + σ') x = cov σ x + cov σ' x
  leibniz {σ : Π x : M, V x} {g : M → 𝕜} {x}
    (hσ : MDiffAt (T% σ) x) (hg : MDiffAt g x) (hx : x ∈ s := by trivial) :
    cov (g • σ) x = g x • cov σ x
     + .toSpanSingleton 𝕜 (σ x) ∘L (fromTangentSpace <| g x).toContinuousLinearMap ∘L (mfderiv% g x)

/--
A covariant derivative ∇ is called of class `C^k` iff,
whenever `X` is a `C^k` section and `σ` a `C^{k+1}` section, the result `∇ X σ` is a `C^k` section.
This is a class so typeclass inference can deduce this automatically.
-/
class ContMDiffCovariantDerivativeOn [IsManifold I 1 M] [VectorBundle 𝕜 F V] (k : ℕ∞)
    (cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x))
    (u : Set M) where
  contMDiff : ∀ {σ : Π x : M, V x}, CMDiff[u] (k + 1) (T% σ) →
    letI cov (x : M) : TotalSpace (E →L[𝕜] F) fun x ↦ TangentSpace I x →L[𝕜] V x := ⟨x, cov σ x⟩
    ContMDiffOn I (I.prod 𝓘(𝕜, E →L[𝕜] F)) k cov u
    -- TODO elaborators are not working here. We want to use `T% (cov σ)` and CMDiff[u] k f

variable {F}

namespace IsCovariantDerivativeOn

-- TODO: prove that `cov X σ x` depends on σ only via σ(X) and the 1-jet of σ at x
-- this should be easy using the projection formula in `CovariantDerivative.Ehresmann`.
-- In the mean time we use the following weaker result (which is convenient to apply anyway).

/-- Given a covariant derivative `cov` on a neighborhood `s` of a point `x`, if sections `σ` and
  `σ'` agree at `x` and are differentiable there, then `cov σ x = cov σ x'`. -/
lemma congr_of_eqOn
    {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
    {s : Set M} (hcov : IsCovariantDerivativeOn F cov s)
    {σ σ' : Π x : M, V x} {x : M}
    (hσ : MDiffAt (T% σ) x)
    (hσ' : MDiffAt (T% σ') x)
    (hxs : s ∈ 𝓝 x)
    (hσσ' : ∀ x ∈ s, σ x = σ' x) :
    cov σ x = cov σ' x := by
  classical
  have hxs' : x ∈ s := mem_of_mem_nhds hxs
  let ψ (x' : M) : 𝕜 := if x' ∈ s then 1 else 0
  have hψx : ψ x = 1 := by simp [ψ, hxs']
  -- Observe that `ψ • σ = ψ • σ'` as dependent functions.
  have H (x' : M) : ((ψ : M → 𝕜) • σ) x' = ((ψ : M → 𝕜) • σ') x' := by
    dsimp [ψ]
    split_ifs with hx's
    · simpa using hσσ' _ hx's
    · simp
  have hψ' : HasMFDerivAt I 𝓘(𝕜) ψ x 0 := by
    have : HasMFDerivAt I 𝓘(𝕜, 𝕜) (fun (_x : M) ↦ (1 : 𝕜)) x 0 := hasMFDerivAt_const ..
    refine this.congr_of_eventuallyEq ?_
    apply Filter.eventuallyEq_of_mem hxs
    intro t ht
    simp [ψ, ht]
  have := hcov.leibniz hσ hψ'.mdifferentiableAt
  -- Then, it's a chain of (dependent) equalities.
  calc cov σ x
    _ = cov ((ψ : M → 𝕜) • σ) x := by
          rw [hcov.leibniz hσ hψ'.mdifferentiableAt, hψx, hψ'.mfderiv]
          erw [ContinuousLinearMap.comp_zero]
          simp
    _ = cov ((ψ : M → 𝕜) • σ') x := by rw [funext H]
    _ = cov σ' x := by
          rw [hcov.leibniz hσ' hψ'.mdifferentiableAt, hψx, hψ'.mfderiv]
          erw [ContinuousLinearMap.comp_zero]
          simp

section changing_set
/-! ### Changing set

In this section, we change `s` in `IsCovariantDerivativeOn F cov s`, proving the condition is
monotone and local.
-/

lemma mono
    {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)} {s t : Set M}
    (hcov : IsCovariantDerivativeOn F cov t) (hst : s ⊆ t) : IsCovariantDerivativeOn F cov s where
  add {_σ _σ' _x} hσ hσ' hx := hcov.add hσ hσ' (hst hx)
  leibniz {_σ _cov _x} hσ hcov' hx := hcov.leibniz hσ hcov' (hst hx)

lemma iUnion {ι : Type*} {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
    {s : ι → Set M} (hcov : ∀ i, IsCovariantDerivativeOn F cov (s i)) :
    IsCovariantDerivativeOn F cov (⋃ i, s i) where
  add {_σ _σ' _x} hσ hσ' hx := by
    obtain ⟨si, ⟨i, rfl⟩, hxsi⟩ := hx
    exact (hcov i).add hσ hσ'
  leibniz {σ f x} hσ hf' hx := by
    obtain ⟨si, ⟨i, rfl⟩, hxsi⟩ := hx
    exact (hcov i).leibniz hσ hf'

end changing_set


section computational_properties
/-! ### Computation properties -/

variable {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)} {s : Set M}

@[simp]
lemma zero [VectorBundle 𝕜 F V] (hcov : IsCovariantDerivativeOn F cov s)
    {x} (hx : x ∈ s := by trivial) :
    cov 0 x = 0 := by
  simpa using (hcov.add (mdifferentiableAt_zeroSection ..)
    (mdifferentiableAt_zeroSection ..) : cov (0 + 0) x = _)

theorem smul_const (hcov : IsCovariantDerivativeOn F cov s)
    {σ : Π x : M, V x} {x} (a : 𝕜)
    (hσ : MDiffAt (T% σ) x) (hx : x ∈ s := by trivial) :
    cov (a • σ) x = a • cov σ x := by
  simpa using hcov.leibniz (g := fun _ ↦ a) hσ mdifferentiableAt_const

end computational_properties

section operations

/-! ### Operations

In this section we prove that:

* affine combinations of covariant derivatives are covariant derivatives
* adding a one form taking values into endomorphisms of the vector bundle to a covariant
  derivative gives a covariant derivative. See `add_on_form`.
* subtracting two covariant derivatives on some set gives a one form taking values into
  endomorphisms of the vector bundle. See `difference`.

Note: morally this means covariant derivatives form an affine space over the vector space of
one-forms taking values in endomorphisms of the bundle, but we don’t package it that way yet.
-/
variable {s : Set M} {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}

/-- An affine combination of covariant derivatives is a covariant derivative. -/
@[simps]
def affineCombination (hcov : IsCovariantDerivativeOn F cov s)
    {cov' : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
    (hcov' : IsCovariantDerivativeOn F cov' s) (g : M → 𝕜) :
    IsCovariantDerivativeOn F (fun σ ↦ (g • (cov σ)) + (1 - g) • (cov' σ)) s where
  add {_σ _σ' x} hσ hσ' hx := by
    simp [hcov.add hσ hσ', hcov'.add hσ hσ']
    module
  leibniz {σ φ x} hσ hφ hx := by
    simp [hcov.leibniz hσ hφ, hcov'.leibniz hσ hφ]
    module

/-- An affine combination of two `C^k` connections is a `C^k` connection. -/
lemma _root_.ContMDiffCovariantDerivativeOn.affineCombination [IsManifold I 1 M]
    [VectorBundle 𝕜 F V]
    {cov cov' : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
    {u: Set M} {f : M → 𝕜} {n : ℕ∞} (hf : CMDiff[u] n f)
    (Hcov : ContMDiffCovariantDerivativeOn (F := F) n cov u)
    (Hcov' : ContMDiffCovariantDerivativeOn (F := F) n cov' u) :
    ContMDiffCovariantDerivativeOn F n (fun σ ↦ (f • (cov σ)) + (1 - f) • (cov' σ)) u where
  contMDiff hσ := by
    apply ContMDiffOn.add_section
    · exact hf.smul_section <| Hcov.contMDiff hσ
    · exact (contMDiffOn_const.sub hf).smul_section <| Hcov'.contMDiff hσ

/-- A finite affine combination of covariant derivatives is a covariant derivative. -/
def affineCombination' {ι : Type*} {s : Finset ι} [Nonempty s]
    {u : Set M} {cov : ι → (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
    (h : ∀ i, IsCovariantDerivativeOn F (cov i) u) {f : ι → M → 𝕜} (hf : ∑ i ∈ s, f i = 1) :
    IsCovariantDerivativeOn F (fun σ x ↦ ∑ i ∈ s, (f i x) • (cov i) σ x) u where
  add {_σ _σ' _x} hσ hσ' hx := by
    rw [← Finset.sum_add_distrib]
    congr
    ext i
    rw [← smul_add, (h i).add hσ hσ' hx]
  leibniz {σ g x} hσ hg hx := by
    set B := (ContinuousLinearMap.toSpanSingleton 𝕜 (σ x) ∘L
      ((fromTangentSpace (g x)).toContinuousLinearMap ∘L (mfderiv% g x)))
    calc ∑ i ∈ s, f i x • cov i (g • σ) x
      _ = ∑ i ∈ s, (g x • f i x • cov i σ x + f i x • B) := by
          congr! 1 with i hi
          rw [(h i).leibniz hσ hg]
          module
      _ = g x • ∑ i ∈ s, f i x • cov i σ x + (∑ i ∈ s, f i) x • B := by
          rw [Finset.sum_add_distrib, Finset.smul_sum, Finset.sum_apply, Finset.sum_smul]
      _ = g x • ∑ i ∈ s, f i x • cov i σ x + B := by rw [hf]; simp

/-- An affine combination of finitely many `C^k` connections on `u` is a `C^k` connection on `u`. -/
lemma _root_.ContMDiffCovariantDerivativeOn.affineCombination' [IsManifold I 1 M] {n : ℕ∞}
    [VectorBundle 𝕜 F V] {ι : Type*} {s : Finset ι} {u : Set M}
    {cov : ι → (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
    (hcov : ∀ i ∈ s, ContMDiffCovariantDerivativeOn F n (cov i) u)
    {f : ι → M → 𝕜} (hf : ∀ i ∈ s, CMDiff[u] n (f i)) :
    ContMDiffCovariantDerivativeOn F n (fun σ x ↦ ∑ i ∈ s, (f i x) • (cov i) σ x) u where
  contMDiff {σ} hσ := by
    simpa using ContMDiffOn.sum_section
      (fun i hi ↦ (hf i hi).smul_section <| (hcov i hi).contMDiff hσ)

/-- Adding a one form taking values into endomorphisms of the vector bundle to a covariant
  derivative gives a covariant derivative. -/
lemma add_one_form (hcov : IsCovariantDerivativeOn F cov s)
    (A : Π x : M, V x →L[𝕜] TangentSpace I x →L[𝕜] V x) :
    IsCovariantDerivativeOn F (fun σ x ↦ cov σ x + A x (σ x)) s where
  add {_σ _σ' _x} hσ hσ' hx := by
    simp [hcov.add hσ hσ']
    abel
  leibniz {σ g x} hσ hg hx := by
    simp [hcov.leibniz hσ hg]
    module

section difference

/-- The difference of two covariant derivatives, as a function `Γ(TM) × Γ(V) → Γ(V)`.
Future lemmas will upgrade this to a one-forme taking values in endomorphisms of `V`. -/
noncomputable def differenceAux
    (cov cov' : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)) :
    (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x) :=
  fun σ ↦ cov σ - cov' σ

-- We need more assumptions to use the tensoriality criterion in order to build the difference
-- operation.
variable [CompleteSpace 𝕜]
    [IsManifold I 1 M]
    [FiniteDimensional 𝕜 F]
    [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]

variable
    {cov' : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
    {s : Set M}
    (hcov : IsCovariantDerivativeOn F cov s)
    (hcov' : IsCovariantDerivativeOn F cov' s)

open scoped Classical in
/-- The difference of two covariant derivatives, as a tensorial map. -/
noncomputable def difference (x : M) : V x →L[𝕜] TangentSpace I x →L[𝕜] V x :=
  if hxs : x ∈ s then
    mkTensorAt I F (differenceAux cov cov') x
      (fun f σ hf hσ ↦ by simp [differenceAux, hcov.leibniz hσ hf, hcov'.leibniz hσ hf]; module)
      (fun σ σ' hσ hσ' ↦ by simp [differenceAux, hcov.add hσ hσ', hcov'.add hσ hσ']; abel)
  else
    0

@[simp]
lemma difference_apply {x : M} (hx : x ∈ s := by trivial) {σ : Π x, V x} (hσ : MDiffAt (T% σ) x) :
    difference hcov hcov' x (σ x) = cov σ x - cov' σ x := by
  simp only [difference, hx, reduceDIte]
  rw [mkTensorAt_apply _ _ _ hσ]
  rfl

end difference

end operations

end IsCovariantDerivativeOn

/-! ## Bundled global covariant derivatives -/

variable (I F V) in
/--
Bundled global covariant derivative on a vector bundle.
Caution: the argument order is slightly tricky: `cov Y x (X x)` corresponds to `∇ X Y x` on paper.
-/
@[ext]
structure CovariantDerivative where
  toFun : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)
  isCovariantDerivativeOnUniv : IsCovariantDerivativeOn F toFun Set.univ

namespace CovariantDerivative

attribute [coe] toFun

/-- Coercion of a `CovariantDerivative` to function -/
instance : CoeFun (CovariantDerivative I F V)
    fun _ ↦ (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x) :=
  ⟨fun e ↦ e.toFun⟩

lemma isCovariantDerivativeOn (cov : CovariantDerivative I F V) {s : Set M} :
    IsCovariantDerivativeOn F cov s :=
  cov.isCovariantDerivativeOnUniv.mono (fun _ _ ↦ trivial)

@[simp]
lemma zero [VectorBundle 𝕜 F V] (cov : CovariantDerivative I F V) : cov 0 = 0 := by
  ext1 x
  simp [cov.isCovariantDerivativeOnUniv.zero]

/-- If `f : Vec(M) × Γ(V) → Vec(M)` is a covariant derivative on each set in an open cover,
it is a covariant derivative. -/
def of_isCovariantDerivativeOn_of_open_cover {ι : Type*} {s : ι → Set M}
    {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
    (hcov : ∀ i, IsCovariantDerivativeOn F cov (s i)) (hs : ⋃ i, s i = Set.univ) :
    CovariantDerivative I F V :=
  ⟨cov, hs ▸ IsCovariantDerivativeOn.iUnion hcov⟩

@[simp]
lemma of_isCovariantDerivativeOn_of_open_cover_coe {ι : Type*} {s : ι → Set M}
    {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
    (hcov : ∀ i, IsCovariantDerivativeOn F cov (s i)) (hs : ⋃ i, s i = Set.univ) :
    of_isCovariantDerivativeOn_of_open_cover hcov hs = cov := rfl

/--
A covariant derivative ∇ is called of class `C^k` iff,
whenever `X` is a `C^k` section and `σ` a `C^{k+1}` section, the result `∇ X σ` is a `C^k` section.
This is a class so typeclass inference can deduce this automatically.
-/
class ContMDiffCovariantDerivative [IsManifold I 1 M] [VectorBundle 𝕜 F V]
    (cov : CovariantDerivative I F V) (k : ℕ∞) where
  contMDiff : ContMDiffCovariantDerivativeOn F k cov.toFun Set.univ

@[simp]
lemma contMDiffCovariantDerivativeOn_univ_iff [IsManifold I 1 M] [VectorBundle 𝕜 F V]
    {cov : CovariantDerivative I F V} {k : ℕ∞} :
    ContMDiffCovariantDerivativeOn F k cov.toFun Set.univ ↔ ContMDiffCovariantDerivative cov k :=
  ⟨fun h ↦ ⟨h⟩, fun h ↦ h.contMDiff⟩

section operations

/-! ### Operations

In this section we prove that:

* affine combinations of covariant derivatives are covariant derivatives
* adding a one form taking values into endomorphisms of the vector bundle to a covariant
  derivative gives a covariant derivative. See `add_on_form`.
* subtracting two covariant derivatives on some set gives a one form taking values into
  endomorphisms of the vector bundle. See `difference`.

Note: morally this means covariant derivatives form an affine space over the vector space of
one-forms taking values in endomorphisms of the bundle, but we don’t package it that way yet.
-/

/-- An affine combination of covariant derivatives is a covariant derivative. -/
@[simps]
def affineCombination (cov cov' : CovariantDerivative I F V) (g : M → 𝕜) :
    CovariantDerivative I F V where
  toFun := fun σ ↦ (g • (cov σ)) + (1 - g) • (cov' σ)
  isCovariantDerivativeOnUniv :=
    cov.isCovariantDerivativeOn.affineCombination cov'.isCovariantDerivativeOn _

/-- A finite affine combination of covariant derivatives is a covariant derivative. -/
def affineCombination' {ι : Type*} {s : Finset ι} [Nonempty s]
    (cov : ι → CovariantDerivative I F V) {f : ι → M → 𝕜} (hf : ∑ i ∈ s, f i = 1) :
    CovariantDerivative I F V where
  toFun t x := ∑ i ∈ s, (f i x) • (cov i) t x
  isCovariantDerivativeOnUniv := IsCovariantDerivativeOn.affineCombination'
    (fun i ↦ (cov i).isCovariantDerivativeOn) hf

/-- An affine combination of two `C^k` connections is a `C^k` connection. -/
lemma ContMDiffCovariantDerivative.affineCombination [IsManifold I 1 M] [VectorBundle 𝕜 F V]
  (cov cov' : CovariantDerivative I F V)
    {f : M → 𝕜} {n : ℕ∞} (hf : ContMDiff I 𝓘(𝕜) n f)
    (hcov : ContMDiffCovariantDerivative cov n) (hcov' : ContMDiffCovariantDerivative cov' n) :
    ContMDiffCovariantDerivative (affineCombination cov cov' f) n where
  contMDiff :=
    ContMDiffCovariantDerivativeOn.affineCombination hf.contMDiffOn hcov.contMDiff hcov'.contMDiff

/-- An affine combination of finitely many `C^k` connections is a `C^k` connection. -/
lemma ContMDiffCovariantDerivative.affineCombination' [IsManifold I 1 M] [VectorBundle 𝕜 F V]
    {ι : Type*} {s : Finset ι} [Nonempty s]
    (cov : ι → CovariantDerivative I F V) {f : ι → M → 𝕜} (hf : ∑ i ∈ s, f i = 1) {n : ℕ∞}
    (hf' : ∀ i ∈ s, ContMDiff I 𝓘(𝕜) n (f i))
    (hcov : ∀ i ∈ s, ContMDiffCovariantDerivative (cov i) n) :
    ContMDiffCovariantDerivative (affineCombination' cov hf) n where
  contMDiff :=
    ContMDiffCovariantDerivativeOn.affineCombination'
      (fun i hi ↦ (hcov i hi).contMDiff) (fun i hi ↦ (hf' i hi).contMDiffOn)

-- TODO: prove a version with a locally finite sum, and deduce that C^k connections always
-- exist (using a partition of unity argument)

/-- Adding a one form taking values into endomorphisms of the vector bundle to a covariant
  derivative gives a covariant derivative. -/
def add_one_form (cov : CovariantDerivative I F V)
    (A : Π (x : M), V x →L[𝕜] TangentSpace I x →L[𝕜] V x) : CovariantDerivative I F V where
  toFun := fun σ x ↦ cov σ x + (A x) (σ x)
  isCovariantDerivativeOnUniv := cov.isCovariantDerivativeOnUniv.add_one_form A

section difference

-- We need more assumptions to use the tensoriality criterion in order to build the difference
-- operation.
variable [CompleteSpace 𝕜]
    [IsManifold I 1 M]
    [FiniteDimensional 𝕜 F]
    [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]

noncomputable def difference (cov cov' : CovariantDerivative I F V) :
    Π (x : M), V x →L[𝕜] TangentSpace I x →L[𝕜] V x :=
  cov.isCovariantDerivativeOnUniv.difference cov'.isCovariantDerivativeOnUniv

end difference
end operations

end CovariantDerivative
