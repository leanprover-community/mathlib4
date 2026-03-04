/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
public import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
public import Mathlib.Geometry.Manifold.MfDerivSMul

/-!
# Covariant derivatives

TODO: add a more complete doc-string

-/

open Bundle Filter Module Topology Set
open scoped Bundle Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

@[expose] public section -- TODO: think if we want to expose all definitions!

section any_field
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] -- [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  -- `F` model fiber
  (n : WithTop ℕ∞)
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V] --[VectorBundle 𝕜 F V]
  -- `V` vector bundle

structure IsCovariantDerivativeOn [IsManifold I 1 M]
    (f : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x))
    (s : Set M := Set.univ) : Prop where
  -- All the same axioms as CovariantDerivative, but restricted to the set s.
  addσ {σ σ' : Π x : M, V x} {x}
    (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x)
    (hx : x ∈ s := by trivial) :
    f (σ + σ') x = f σ x + f σ' x
  leibniz {σ : Π x : M, V x} {g : M → 𝕜} {x}
    (hσ : MDiffAt (T% σ) x) (hg : MDiffAt g x) (hx : x ∈ s := by trivial):
    f (g • σ) x = g x • f σ x
      + .toSpanSingleton 𝕜 (σ x) ∘L
        (((bar (g x)).toContinuousLinearMap ∘L (mfderiv I 𝓘(𝕜) g x)))

/--
A covariant derivative ∇ is called of class `C^k` iff,
whenever `X` is a `C^k` section and `σ` a `C^{k+1}` section, the result `∇ X σ` is a `C^k` section.
This is a class so typeclass inference can deduce this automatically.
-/
class ContMDiffCovariantDerivativeOn [IsManifold I 1 M] [VectorBundle 𝕜 F V] (k : ℕ∞)
    (cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x))
    (u : Set M) where
  contMDiff : ∀ {σ : Π x : M, V x}, CMDiff[u] (k + 1) (T% σ) →
    let f (x : M) : TotalSpace (E →L[𝕜] F) fun x ↦ TangentSpace I x →L[𝕜] V x := ⟨x, cov σ x⟩
    ContMDiffOn I (I.prod 𝓘(𝕜, E →L[𝕜] F)) k f u
    -- elaborators not working here, TODO investigate
    -- ContMDiffOn I (I.prod 𝓘(𝕜, E →L[𝕜] F)) k (T% (cov σ)) u
    -- CMDiff[u] k f

variable {F}

namespace IsCovariantDerivativeOn

variable [IsManifold I 1 M]

variable (E) in
/-- If `E` is the trivial vector space, [HM: i.e. the manifold is zero-dimensional??]
the axioms of a covariant derivative are vacuous. -/
lemma of_subsingleton [hE : Subsingleton E] [TopologicalSpace (TotalSpace E V)] [FiberBundle E V]
    (f : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)) :
    IsCovariantDerivativeOn E f Set.univ := by
  have (Y) (x) : f Y x = 0 := by
    have : Subsingleton (TangentSpace I x) := inferInstanceAs (Subsingleton E)
    exact Subsingleton.eq_zero _
  exact {
    addσ {σ σ' x} hσ hσ' hx := by simp [this]
    leibniz {σ g x} hσ hg hx := by
      have H : (mfderiv I 𝓘(𝕜, 𝕜) g x) = 0 :=
        have : Subsingleton (TangentSpace I x) := inferInstanceAs (Subsingleton E)
        Subsingleton.eq_zero _
      simp [this, H] }

section changing_set
/-! Changing set

In this changing we change `s` in `IsCovariantDerivativeOn F f s`.

-/
lemma mono
    {f : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)} {s t : Set M}
    (hf : IsCovariantDerivativeOn F f t) (hst : s ⊆ t) : IsCovariantDerivativeOn F f s where
  addσ {_σ _σ' _x} hσ hσ' hx := hf.addσ hσ hσ' (hst hx)
  leibniz {_σ _f _x} hσ hf' hx := hf.leibniz hσ hf' (hst hx)

lemma iUnion {ι : Type*}
    {f : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)} {s : ι → Set M}
    (hf : ∀ i, IsCovariantDerivativeOn F f (s i)) : IsCovariantDerivativeOn F f (⋃ i, s i) where
  addσ {_σ _σ' _x} hσ hσ' hx := by
    obtain ⟨si, ⟨i, rfl⟩, hxsi⟩ := hx
    exact (hf i).addσ hσ hσ'
  leibniz {σ f x} hσ hf' hx := by
    obtain ⟨si, ⟨i, rfl⟩, hxsi⟩ := hx
    exact (hf i).leibniz hσ hf'

end changing_set

/- Congruence properties -/
section

lemma congr {f g : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)} {s : Set M}
    (hf : IsCovariantDerivativeOn F f s)
    -- Is this too strong? Will see!
    (hfg : ∀ {σ : Π x : M, V x}, ∀ {x}, x ∈ s → f σ x = g σ x) :
    IsCovariantDerivativeOn F g s where
  addσ hσ hσ' hx := by simp [← hfg hx, hf.addσ hσ hσ']
  leibniz hσ hf' hx := by simp [← hfg hx, hf.leibniz hσ hf']

end

section computational_properties

variable {f : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)} {s : Set M}

@[simp]
lemma zeroσ [VectorBundle 𝕜 F V] (hf : IsCovariantDerivativeOn F f s)
    {x} (hx : x ∈ s := by trivial) :
    f 0 x = 0 := by
  simpa using (hf.addσ (mdifferentiableAt_zeroSection ..)
    (mdifferentiableAt_zeroSection ..) : f (0 + 0) x = _)

theorem smul_const_σ (hf : IsCovariantDerivativeOn F f s)
    {σ : Π x : M, V x} {x} (a : 𝕜)
    (hσ : MDiffAt (T% σ) x) (hx : x ∈ s := by trivial) :
    f (a • σ) x = a • f σ x := by
  simpa using hf.leibniz (g := fun _ ↦ a) hσ mdifferentiableAt_const

end computational_properties

section operations

variable {s : Set M}
    {f : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}

/-- An affine combination of covariant derivatives is a covariant derivative. -/
@[simps]
def affineCombination
    {f' : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
    (hf : IsCovariantDerivativeOn F f s) (hf' : IsCovariantDerivativeOn F f' s) (g : M → 𝕜) :
    IsCovariantDerivativeOn F (fun σ ↦ (g • (f σ)) + (1 - g) • (f' σ)) s where
  addσ {_σ _σ' x} hσ hσ' hx := by
    simp [hf.addσ hσ hσ', hf'.addσ hσ hσ']
    module
  leibniz {σ φ x} hσ hφ hx := by
    simp [hf.leibniz hσ hφ, hf'.leibniz hσ hφ]
    module

/-- An affine combination of two `C^k` connections is a `C^k` connection. -/
lemma _root_.ContMDiffCovariantDerivativeOn.affineCombination
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
  addσ {_σ _σ' _x} hσ hσ' hx := by
    rw [← Finset.sum_add_distrib]
    congr
    ext i
    rw [← smul_add, (h i).addσ hσ hσ' hx]
  leibniz {σ g x} hσ hg hx := by
    set B := (ContinuousLinearMap.toSpanSingleton 𝕜 (σ x) ∘L
            ((bar (g x)).toContinuousLinearMap ∘L (mfderiv I 𝓘(𝕜, 𝕜) g x)))
    calc ∑ i ∈ s, f i x • cov i (g • σ) x
      _ = ∑ i ∈ s, (g x • f i x • cov i σ x + f i x • B) := by
          congr! 1 with i hi
          rw [(h i).leibniz hσ hg]
          module
      _ = g x • ∑ i ∈ s, f i x • cov i σ x + (∑ i ∈ s, f i) x • B := by
          rw [Finset.sum_add_distrib, Finset.smul_sum, Finset.sum_apply, Finset.sum_smul]
      _ = g x • ∑ i ∈ s, f i x • cov i σ x + B := by rw [hf]; simp

/-- An affine combination of finitely many `C^k` connections on `u` is a `C^k` connection on `u`. -/
lemma _root_.ContMDiffCovariantDerivativeOn.affineCombination' {n : ℕ∞}
    [VectorBundle 𝕜 F V] {ι : Type*} {s : Finset ι} {u : Set M}
    {cov : ι → (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
    (hcov : ∀ i ∈ s, ContMDiffCovariantDerivativeOn F n (cov i) u)
    {f : ι → M → 𝕜} (hf : ∀ i ∈ s, CMDiff[u] n (f i)) :
    ContMDiffCovariantDerivativeOn F n (fun σ x ↦ ∑ i ∈ s, (f i x) • (cov i) σ x) u where
  contMDiff {σ} hσ := by
    simpa using ContMDiffOn.sum_section
      (fun i hi ↦ (hf i hi).smul_section <| (hcov i hi).contMDiff hσ)

variable {s : Set M}
    {f : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}

omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)] in
lemma add_one_form [∀ (x : M), IsTopologicalAddGroup (V x)]
    [∀ (x : M), ContinuousSMul 𝕜 (V x)] (hf : IsCovariantDerivativeOn F f s)
    (A : Π x : M, V x →L[𝕜] TangentSpace I x →L[𝕜] V x) :
    IsCovariantDerivativeOn F (fun σ x ↦ f σ x + A x (σ x)) s where
  addσ {_σ _σ' _x} hσ hσ' hx := by
    simp [hf.addσ hσ hσ']
    abel
  leibniz {σ g x} hσ hg hx := by
    simp [hf.leibniz hσ hg]
    module

end operations

end IsCovariantDerivativeOn

/-! Bundled global covariant derivatives -/

variable (I F V) in
@[ext]
structure CovariantDerivative [IsManifold I 1 M] where
  toFun : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)
  isCovariantDerivativeOn : IsCovariantDerivativeOn F toFun Set.univ

namespace CovariantDerivative

attribute [coe] toFun

variable [IsManifold I 1 M]

/-- Coercion of a `CovariantDerivative` to function -/
instance : CoeFun (CovariantDerivative I F V)
    fun _ ↦ (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x) :=
  ⟨fun e ↦ e.toFun⟩

instance (cov : CovariantDerivative I F V) {s : Set M} :
    IsCovariantDerivativeOn F cov s := by
  apply cov.isCovariantDerivativeOn.mono (fun ⦃a⦄ a ↦ trivial)

/-- If `f : Vec(M) × Γ(E) → Vec(M)` is a covariant derivative on each set in an open cover,
it is a covariant derivative. -/
def of_isCovariantDerivativeOn_of_open_cover {ι : Type*} {s : ι → Set M}
    {f : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
    (hf : ∀ i, IsCovariantDerivativeOn F f (s i)) (hs : ⋃ i, s i = Set.univ) :
    CovariantDerivative I F V :=
  ⟨f, hs ▸ IsCovariantDerivativeOn.iUnion hf⟩

@[simp]
lemma of_isCovariantDerivativeOn_of_open_cover_coe {ι : Type*} {s : ι → Set M}
    {f : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
    (hf : ∀ i, IsCovariantDerivativeOn F f (s i)) (hs : ⋃ i, s i = Set.univ) :
    of_isCovariantDerivativeOn_of_open_cover hf hs = f := rfl


/--
A covariant derivative ∇ is called of class `C^k` iff,
whenever `X` is a `C^k` section and `σ` a `C^{k+1}` section, the result `∇ X σ` is a `C^k` section.
This is a class so typeclass inference can deduce this automatically.
-/
class ContMDiffCovariantDerivative [VectorBundle 𝕜 F V] (cov : CovariantDerivative I F V)
    (k : ℕ∞) where
  contMDiff : ContMDiffCovariantDerivativeOn F k cov.toFun Set.univ

@[simp]
lemma contMDiffCovariantDerivativeOn_univ_iff [VectorBundle 𝕜 F V] {cov : CovariantDerivative I F V}
    {k : ℕ∞} :
    ContMDiffCovariantDerivativeOn F k cov.toFun Set.univ ↔ ContMDiffCovariantDerivative cov k :=
  ⟨fun h ↦ ⟨h⟩, fun h ↦ h.contMDiff⟩

-- future: if g is a C^k metric on a manifold M, the corresponding Levi-Civita connection
-- is of class C^k (up to off-by-one errors)

section computational_properties

@[simp]
lemma zeroσ [VectorBundle 𝕜 F V] (cov : CovariantDerivative I F V) : cov 0 = 0 := by
  ext1 x
  simp [cov.isCovariantDerivativeOn.zeroσ]

end computational_properties

section operations

/-- An affine combination of covariant derivatives is a covariant derivative. -/
@[simps]
def affineCombination (cov cov' : CovariantDerivative I F V) (g : M → 𝕜) :
    CovariantDerivative I F V where
  toFun := fun σ ↦ (g • (cov σ)) + (1 - g) • (cov' σ)
  isCovariantDerivativeOn :=
    cov.isCovariantDerivativeOn.affineCombination cov'.isCovariantDerivativeOn _

/-- A finite affine combination of covariant derivatives is a covariant derivative. -/
def affineCombination' {ι : Type*} {s : Finset ι} [Nonempty s]
    (cov : ι → CovariantDerivative I F V) {f : ι → M → 𝕜} (hf : ∑ i ∈ s, f i = 1) :
    CovariantDerivative I F V where
  toFun t x := ∑ i ∈ s, (f i x) • (cov i) t x
  isCovariantDerivativeOn := IsCovariantDerivativeOn.affineCombination'
    (fun i ↦ (cov i).isCovariantDerivativeOn) hf

/-- An affine combination of two `C^k` connections is a `C^k` connection. -/
lemma ContMDiffCovariantDerivative.affineCombination [VectorBundle 𝕜 F V]
  (cov cov' : CovariantDerivative I F V)
    {f : M → 𝕜} {n : ℕ∞} (hf : ContMDiff I 𝓘(𝕜) n f)
    (hcov : ContMDiffCovariantDerivative cov n) (hcov' : ContMDiffCovariantDerivative cov' n) :
    ContMDiffCovariantDerivative (affineCombination cov cov' f) n where
  contMDiff :=
    ContMDiffCovariantDerivativeOn.affineCombination hf.contMDiffOn hcov.contMDiff hcov'.contMDiff

/-- An affine combination of finitely many `C^k` connections is a `C^k` connection. -/
lemma ContMDiffCovariantDerivative.affineCombination' [VectorBundle 𝕜 F V]
    {ι : Type*} {s : Finset ι} [Nonempty s]
    (cov : ι → CovariantDerivative I F V) {f : ι → M → 𝕜} (hf : ∑ i ∈ s, f i = 1) {n : ℕ∞}
    (hf' : ∀ i ∈ s, ContMDiff I 𝓘(𝕜) n (f i))
    (hcov : ∀ i ∈ s, ContMDiffCovariantDerivative (cov i) n) :
    ContMDiffCovariantDerivative (affineCombination' cov hf) n where
  contMDiff :=
    ContMDiffCovariantDerivativeOn.affineCombination'
      (fun i hi ↦ (hcov i hi).contMDiff) (fun i hi ↦ (hf' i hi).contMDiffOn)

-- Future: prove a version with a locally finite sum, and deduce that C^k connections always
-- exist (using a partition of unity argument)

end operations

end CovariantDerivative
end any_field

section real

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {x : M}

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  -- `F` model fiber
  (n : WithTop ℕ∞)
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)] [FiberBundle F V]
  -- `V` vector bundle

namespace IsCovariantDerivativeOn

-- TODO can probably work for `IsManifold I 1 M`,
-- by weakening the conditions for the `extend` construction
theorem ext [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M]
    {P P' : (Π x : M, TangentSpace I x →L[ℝ] V x)} {x}
    (H : ∀ {X : Π x : M, TangentSpace I x}, MDiffAt (T% X) x → P x (X x) = P' x (X x)) :
    P x = P' x := by
  ext X₀
  rw [← extend_apply_self (I := I) (F := E) X₀]
  exact H (mdifferentiable_extend ..)

/-- `cov X σ x` only depends on `X` via `X x` -/
lemma congr_X_at
    {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[ℝ] V x)}
    {X X' : Π x : M, TangentSpace I x}
    {σ : Π x : M, V x} {x : M}
    (hXX' : X x = X' x) :
    cov σ x (X x) = cov σ x (X' x) := by
  rw [hXX']

lemma congr_σ_smoothBumpFunction [T2Space M] [IsManifold I ∞ M]
    [FiniteDimensional ℝ E]
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
    {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[ℝ] V x)}
    {u : Set M} (hcov : IsCovariantDerivativeOn F cov u)
    {σ : Π x : M, V x}
    (hσ : MDiffAt (T% σ) x)
    (f : SmoothBumpFunction I x)
    (hx : x ∈ u) :
    cov ((f : M → ℝ) • σ) x = cov σ x := by
  have hf : MDiffAt f x := f.contMDiffAt.mdifferentiableAt (by simp)
  rw [hcov.leibniz hσ hf hx, f.eq_one, f.eventuallyEq_one.mfderiv_eq]
  rw [show mfderiv I 𝓘(ℝ, ℝ) 1 x = 0 by apply mfderiv_const]
  simp

lemma congr_σ_of_eqOn [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M] [VectorBundle ℝ F V]
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
    {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[ℝ] V x)}
    {s : Set M} (hcov : IsCovariantDerivativeOn F cov s)
    {σ σ' : Π x : M, V x}
    (hσ : MDiffAt (T% σ) x)
    (hσ' : MDiffAt (T% σ') x)
    (hxs : s ∈ 𝓝 x)
    (hσσ' : ∀ x ∈ s, σ x = σ' x) :
    cov σ x = cov σ' x := by
  -- Choose a smooth bump function ψ with support around `x` contained in `s`
  obtain ⟨ψ, _, hψ⟩ := (SmoothBumpFunction.nhds_basis_support (I := I) hxs).mem_iff.1 hxs
  -- Observe that `ψ • σ = ψ • σ'` as dependent functions.
  have (x : M) : ((ψ : M → ℝ) • σ) x = ((ψ : M → ℝ) • σ') x := by
    by_cases h : x ∈ s
    · simp [hσσ' x h]
    · simp [Function.notMem_support.mp fun a ↦ h (hψ a)]
  -- Then, it's a chain of (dependent) equalities.
  calc cov σ x
    _ = cov ((ψ : M → ℝ) • σ) x := by
          rw [hcov.congr_σ_smoothBumpFunction hσ ψ (mem_of_mem_nhds hxs)]
    _ = cov ((ψ : M → ℝ) • σ') x := by rw [funext this]
    _ = cov σ' x := by
          rw [hcov.congr_σ_smoothBumpFunction hσ' ψ (mem_of_mem_nhds hxs)]

-- TODO: prove that `cov X σ x` depends on σ only via σ(X) and the 1-jet of σ at x
-- this should be easy using the projection formula below.

/-- The difference of two covariant derivatives, as a function `Γ(TM) × Γ(E) → Γ(E)`.
Future lemmas will upgrade this to a map `TM ⊕ E → E`. -/
noncomputable def differenceAux
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
    (cov cov' : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[ℝ] V x)) :
    (Π x : M, V x) → (Π x : M, TangentSpace I x →L[ℝ] V x) :=
  fun σ ↦ cov σ - cov' σ

variable [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]

open Classical in
/-- The difference of two covariant derivatives, as a tensorial map -/
noncomputable def difference [∀ x, FiniteDimensional ℝ (V x)] [∀ x, T2Space (V x)]
    [FiniteDimensional ℝ F] [T2Space M] [FiniteDimensional ℝ E] [IsManifold I ∞ M]
    [FiniteDimensional ℝ E] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
    {cov cov' : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[ℝ] V x)}
    {s : Set M}
    (hcov : IsCovariantDerivativeOn F cov s)
    (hcov' : IsCovariantDerivativeOn F cov' s)
    (x : M) : V x →L[ℝ] TangentSpace I x →L[ℝ] V x :=
  if hxs : x ∈ s then
    mkTensorAt I F (E →L[ℝ] F) (differenceAux cov cov') x
      (fun f σ hf hσ ↦ by simp [differenceAux, hcov.leibniz hσ hf, hcov'.leibniz hσ hf]; module)
      (fun σ σ' hσ hσ' ↦ by simp [differenceAux, hcov.addσ hσ hσ', hcov'.addσ hσ hσ']; abel)
  else
    0

-- do we need this?
lemma difference_def [∀ x, FiniteDimensional ℝ (V x)] [∀ x, T2Space (V x)]
    [FiniteDimensional ℝ F] [T2Space M] [IsManifold I ∞ M] [FiniteDimensional ℝ E]
    [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
    {cov cov' : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[ℝ] V x)}
    {s : Set M} {x : M}
    (hcov : IsCovariantDerivativeOn F cov s)
    (hcov' : IsCovariantDerivativeOn F cov' s)
    (hx : x ∈ s := by trivial) (σ₀ : V x) :
    difference hcov hcov' x σ₀ =
      cov (extend I F σ₀) x - cov' (extend I F σ₀) x := by
  simp only [difference, hx, reduceDIte]
  rfl

@[simp]
lemma difference_apply [∀ x, FiniteDimensional ℝ (V x)] [∀ x, T2Space (V x)]
    [FiniteDimensional ℝ F] [T2Space M] [IsManifold I ∞ M] [FiniteDimensional ℝ E]
    [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
    {cov cov' : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[ℝ] V x)}
    {s : Set M} {x : M}
    (hcov : IsCovariantDerivativeOn F cov s)
    (hcov' : IsCovariantDerivativeOn F cov' s)
    (hx : x ∈ s := by trivial) {σ : Π x, V x}
    (hσ : MDiffAt (T% σ) x) :
    difference hcov hcov' x (σ x) =
      cov σ x - cov' σ x := by
  simp only [difference, hx, reduceDIte]
  rw [mkTensorAt_apply _ _ _ _ hσ]
  rfl

end IsCovariantDerivativeOn
