/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Mathlib.Geometry.Manifold.BumpFunction
public import Mathlib.Geometry.Manifold.Notation
public import Mathlib.Geometry.Manifold.VectorBundle.Misc
public import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
public import Mathlib.Geometry.Manifold.VectorField.LieBracket
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Prelim

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
      + ContinuousLinearMap.toSpanSingleton 𝕜 (σ x) ∘L
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

section trivial_bundle

variable (I M F) in
@[simps]
noncomputable def trivial [IsManifold I 1 M] :
    IsCovariantDerivativeOn F (V := Trivial M F)
      (fun s x ↦ mfderiv I 𝓘(𝕜, F) s x) univ where
  addσ {σ σ' x} hσ hσ' hx := by
    rw [mdifferentiableAt_section] at hσ hσ'
    -- TODO: specialize mdifferentiableAt_section to trivial bundles?
    change MDifferentiableAt I 𝓘(𝕜, F) σ x at hσ
    change MDifferentiableAt I 𝓘(𝕜, F) σ' x at hσ'
    rw [mfderiv_add hσ hσ']
  leibniz {σ f x} hσ hf hx := by
    rw [mdifferentiableAt_section] at hσ
    ext1 X₀
    exact mfderiv_smul hσ hf X₀

lemma of_endomorphism (A : (x : M) → F →L[𝕜] TangentSpace I x →L[𝕜] F) :
    IsCovariantDerivativeOn F
      (fun (s : M → F) x ↦
        letI d : TangentSpace I x →L[𝕜] F := mfderiv I 𝓘(𝕜, F) s x
        d + A x (s x)) univ :=
  trivial I M F |>.add_one_form A

end trivial_bundle

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

section trivial_bundle

variable (I M F) in
@[simps]
noncomputable def trivial [IsManifold I 1 M] : CovariantDerivative I F (Trivial M F) where
  toFun s x := mfderiv I 𝓘(𝕜, F) s x
  isCovariantDerivativeOn := -- TODO use previous work
  { addσ {σ σ' x} hσ hσ' hx := by
      rw [mdifferentiableAt_section] at hσ hσ'
      -- TODO: specialize mdifferentiableAt_section to trivial bundles?
      change MDifferentiableAt I 𝓘(𝕜, F) σ x at hσ
      change MDifferentiableAt I 𝓘(𝕜, F) σ' x at hσ'
      rw [mfderiv_add hσ hσ']
    leibniz {σ f x} hσ hf hx := by
      rw [mdifferentiableAt_section] at hσ
      ext1 X₀
      exact mfderiv_smul hσ hf X₀ }

end trivial_bundle

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']


-- TODO: does it make sense to speak of analytic connections? if so, change the definition of
-- regularity and use ∞ from `open scoped ContDiff` instead.

/-- The trivial connection on the trivial bundle is smooth -/
lemma trivial_isSmooth : ContMDiffCovariantDerivative (𝕜 := 𝕜) (trivial 𝓘(𝕜, E) E E') (⊤ : ℕ∞) where
  contMDiff := by -- {X σ} hX hσ
    sorry /-
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
    sorry -/

noncomputable def of_endomorphism (A : E → E' →L[𝕜] E →L[𝕜] E') :
    CovariantDerivative 𝓘(𝕜, E) E' (Trivial E E') where
  toFun σ := fun x ↦ fderiv 𝕜 σ x + A x (σ x)
  isCovariantDerivativeOn := by
    convert IsCovariantDerivativeOn.of_endomorphism (I := 𝓘(𝕜, E)) A
    ext f x v
    rw [mfderiv_eq_fderiv]
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

-- The classification of real connections over a trivial bundle
section classification

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [T2Space M] [IsManifold I ∞ M]

/-- Classification of covariant derivatives over a trivial vector bundle: every connection
is of the form `D + A`, where `D` is the trivial covariant derivative, and `A` a zeroth-order term
-/
lemma exists_one_form {cov : (M → F) → (Π x : M, TangentSpace I x →L[ℝ] F)}
    {s : Set M} (hcov : IsCovariantDerivativeOn F cov s) :
    ∃ (A : (x : M) → F →L[ℝ] TangentSpace I x →L[ℝ] F),
    ∀ σ : M → F, ∀ x ∈ s, MDiffAt (T% σ) x →
    letI d : TangentSpace I x →L[ℝ] F := mfderiv I 𝓘(ℝ, F) σ x
    cov σ x = d + A x (σ x) := by
  use hcov.difference (trivial I M F |>.mono <| subset_univ s)
  intro σ x hx hσ
  rw [hcov.difference_apply _ (by trivial) hσ]
  module

noncomputable def one_form {cov : (M → F) → (Π x : M, TangentSpace I x →L[ℝ] F)}
    {s : Set M} (hcov : IsCovariantDerivativeOn F cov s) :
    Π x : M, F →L[ℝ] TangentSpace I x →L[ℝ] F :=
  hcov.exists_one_form.choose

lemma eq_one_form {cov : (M → F) → (Π x : M, TangentSpace I x →L[ℝ] F)}
    {s : Set M} (hcov : IsCovariantDerivativeOn F cov s)
    {σ : M → F}
    {x : M} (hσ : MDiffAt (T% σ) x) (hx : x ∈ s := by trivial) :
    letI d : TangentSpace I x →L[ℝ] F := mfderiv I 𝓘(ℝ, F) σ x
    cov σ x = d + hcov.one_form x (σ x) :=
  hcov.exists_one_form.choose_spec σ x hx hσ

lemma _root_.CovariantDerivative.exists_one_form
    (cov : CovariantDerivative I F (Bundle.Trivial M F)) :
    ∃ (A : (x : M) → F →L[ℝ] TangentSpace I x →L[ℝ] F),
    ∀ σ : M → F, ∀ x, MDiffAt (T% σ) x →
    letI d : TangentSpace I x →L[ℝ] F := mfderiv I 𝓘(ℝ, F) σ x
    cov σ x = d + A x (σ x) := by
  simpa using cov.isCovariantDerivativeOn.exists_one_form

end classification

section projection_trivial_bundle

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [T2Space M] [IsManifold I ∞ M]

local notation "TM" => TangentSpace I

variable {cov : (M → F) → (Π x : M, TangentSpace I x →L[ℝ] F)} {s : Set M}

noncomputable
def projection (hcov : IsCovariantDerivativeOn F cov s) (x : M) (f : F) : (TM x) × F →L[ℝ] F :=
  .snd ℝ (TM x) F + (hcov.one_form x f ∘L .fst ℝ (TM x) F)

@[simp]
lemma projection_apply (hcov : IsCovariantDerivativeOn F cov s) (x : M) (f : F) (v : TM x) (w : F) :
  hcov.projection x f (v, w) = w + hcov.one_form x f v := rfl

lemma cov_eq_proj (hcov : IsCovariantDerivativeOn F cov s) (σ : M → F)
    {x : M} (X₀ : TM x) (hσ : MDiffAt (T% σ) x) (hx : x ∈ s := by trivial) :
    cov σ x X₀ = hcov.projection x (σ x) (X₀, mfderiv I 𝓘(ℝ, F) σ x X₀) := by
  simpa using congr($(hcov.eq_one_form hσ) X₀)

noncomputable def horiz (hcov : IsCovariantDerivativeOn F cov s) (x : M) (f : F) :
    Submodule ℝ (TM x × F) :=
  (hcov.projection x f).ker

lemma horiz_vert_direct_sum (hcov : IsCovariantDerivativeOn F cov s) (x : M) (f : F) :
    IsCompl (hcov.horiz x f) (.prod ⊥ ⊤) := by
  refine IsCompl.of_eq ?_ ?_
  · refine (Submodule.eq_bot_iff _).mpr ?_
    rintro ⟨u, w⟩ ⟨huw, hu, hw⟩
    simp_all [horiz]
  · apply Submodule.sup_eq_top_iff _ _ |>.2
    intro u
    use u - (0, hcov.projection x f u), ?_, (0, hcov.projection x f u), ?_, ?_
    all_goals simp [horiz]

set_option backward.isDefEq.respectTransparency false in
lemma mem_horiz_iff_exists (hcov : IsCovariantDerivativeOn F cov s) {x : M} {f : F}
    {u : TM x} {v : F} (hx : x ∈ s := by trivial) : (u, v) ∈ hcov.horiz x f ↔
    ∃ σ : M → F, MDiffAt (T% σ) x ∧
                 σ x = f ∧
                 mfderiv I 𝓘(ℝ, F) σ x u = v ∧
                 cov σ x u = 0 := by
  constructor
  · intro huv
    simp only [horiz, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, projection_apply] at huv
    let w : TangentSpace 𝓘(ℝ, F) f := v
    by_cases hu : u = 0
    · subst hu
      replace huv : v = 0 := by simpa using huv
      subst huv
      use fun x ↦ f
      simp [mdifferentiableAt_section,  mdifferentiableAt_const]
    rcases map_of_one_jet_spec u w (by tauto) with ⟨h, h', h''⟩
    use map_of_one_jet u w, ?_, h, h''
    · rw [hcov.eq_one_form]
      · simp only [w, h]
        convert huv
        convert ContinuousLinearMap.add_apply (M₁ := TangentSpace I x) (M₂ := F) _
          (hcov.one_form x f) u
        exact h''.symm
      · rwa [mdifferentiableAt_section]
    · rwa [mdifferentiableAt_section]
  · rintro ⟨σ, σ_diff, rfl, rfl, covσ⟩
    simp only [horiz, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, projection_apply, ← covσ]
    rw [hcov.eq_one_form σ_diff]
    rfl

end projection_trivial_bundle

end IsCovariantDerivativeOn

namespace Bundle.Trivialization

section to_trivialization

variable (e : Trivialization F (π F V)) [VectorBundle ℝ F V] [MemTrivializationAtlas e]
  [IsManifold I 1 M]

noncomputable
def pushCovDer
    (cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[ℝ] V x)) :
    (M → F) → (Π x : M, TangentSpace I x →L[ℝ] F) :=
  fun σ x ↦ e.continuousLinearMapAt ℝ x ∘L (cov (fun x' ↦ e.symm x' <| σ x') x)

set_option backward.isDefEq.respectTransparency false in
lemma pushCovDer_ofSect [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [T2Space M] [IsManifold I ∞ M]
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
    [ContMDiffVectorBundle 1 F V I]
    {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[ℝ] V x)}
    (hcov : IsCovariantDerivativeOn F cov e.baseSet)
    {X₀ : TangentSpace I x} {σ : Π x : M, V x} {x : M}
    (hσ : MDiffAt T%σ x)
    (hx : x ∈ e.baseSet := by assumption) :
    (e.pushCovDer cov) (fun x ↦ (e (σ x)).2) x X₀ = (e (cov σ x X₀)).2 := by
  have : cov (fun x' ↦ e.symm x' (e (T% σ x')).2) x = cov σ x := by
    apply hcov.congr_σ_of_eqOn _ hσ (e.baseSet_mem_nhds hx)
    · exact fun y hy ↦ symm_apply_apply_mk e hy (σ y) --FIXME extract as lemma?
    · rw [(e.symm_apply_apply_mk_eventuallyEq hx σ).mdifferentiableAt_iff]
      exact hσ
  unfold pushCovDer
  rw [this]
  simp [coe_linearMapAt, hx]


variable {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[ℝ] V x)}
    -- {s : Set M} (hcov : IsCovariantDerivativeOn F cov s)

lemma pushCovDer_isCovariantDerivativeOn
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
    [ContMDiffVectorBundle 1 F V I]
    {u : Set M} (hu : u ⊆ e.baseSet)
    (hcov : IsCovariantDerivativeOn F cov u) :
    IsCovariantDerivativeOn F (e.pushCovDer cov) u where
  addσ {σ σ' x} hσ hσ' hx := by
    set s := (fun x' ↦ e.symm x' (σ x'))
    have hs : MDiffAt (T% s) x :=
      e.mdifferentiableAt_section_of_function (hu hx) <| mdifferentiableAt_section_trivial_iff.1 hσ
    set s' := (fun x' ↦ e.symm x' (σ' x'))
    have hs' : MDiffAt (T% s') x :=
      e.mdifferentiableAt_section_of_function (hu hx) <| mdifferentiableAt_section_trivial_iff.1
      hσ'
    unfold pushCovDer
    rw [← ContinuousLinearMap.comp_add, ← hcov.addσ hs hs' hx]
    congr
    ext y
    simp [e.symm_map_add ℝ, s, s']
  leibniz {σ g x} hσ hg hx := by
    set s := (fun x' ↦ e.symm x' (σ x'))
    have hs : MDiffAt (T% s) x :=
      e.mdifferentiableAt_section_of_function (hu hx) <| mdifferentiableAt_section_trivial_iff.1 hσ
    unfold pushCovDer
    have : (fun x' ↦ e.symm x' ((g • σ) x')) = g • s := by
      ext y
      simp [s, e.symm_map_smul]
    rw [this, hcov.leibniz hs hg hx]
    ext X₀
    simp only [ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_smulₛₗ, RingHom.id_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp',
      continuousLinearMapAt_apply, Pi.smul_apply, Function.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.toSpanSingleton_apply, _root_.map_smul,
      add_right_inj, s]
    congr! 1
    exact e.linearMapAt_symmₗ (R := ℝ) (hu hx) (σ x)

variable {e} in
lemma coordChangeL_pushCovDer
    [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M]
    {e' : Trivialization F (π F V)} [MemTrivializationAtlas e']
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
    [ContMDiffVectorBundle 1 F V I]
    (hcov : IsCovariantDerivativeOn F cov <| e.baseSet ∩ e'.baseSet)
    {x : M} (hx : x ∈ e.baseSet ∩ e'.baseSet)
    {s : M → F} (hs : MDiffAt s x) :
    e.coordChangeL ℝ e' x ∘L (e.pushCovDer cov s x) =
      e'.pushCovDer cov (fun x ↦ e.coordChangeL ℝ e' x (s x)) x := by
  ext1 X₀
  simp only [ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe, Function.comp_apply]
  unfold pushCovDer
  let σ := (fun x' ↦ e.symm x' (s x'))
  rw [coordChangeL_apply e e' hx]
  simp only [ContinuousLinearMap.coe_comp', continuousLinearMapAt_apply, coe_linearMapAt, hx.1,
    ↓reduceIte, Function.comp_apply, hx.2]
  refold_let σ
  have : e.symm x (e ⟨x, cov σ x X₀⟩).2 = cov σ x X₀ := by
    -- TODO fix `simp [hx.1]` not working
    exact symm_apply_apply_mk e hx.1 (cov σ x X₀)
  rw [this]
  -- TODO: extract lemma?
  have : ∀ x' ∈ e.baseSet ∩ e'.baseSet, σ x' =
      e'.symm x' ((fun x ↦ (coordChangeL ℝ e e' x) (s x)) x') := by
    rintro x' ⟨hx'e, hx'e'⟩
    simp only
    rw [coordChangeL_apply e e' ⟨hx'e, hx'e'⟩]
    -- simp [hx'e'] -- TODO doesn’t work
    rw [symm_apply_apply_mk e' hx'e']
  have mem : e.baseSet ∩ e'.baseSet ∈ 𝓝 x := by
    -- FIXME: make sure grind can do this proof
    exact inter_mem (baseSet_mem_nhds e (mem_of_mem_inter_left hx))
        (baseSet_mem_nhds e' (mem_of_mem_inter_right hx))
  have hσ : MDiffAt (T% σ) x :=
    mdifferentiableAt_section_of_function e hx.1 hs
  rw [hcov.congr_σ_of_eqOn hσ ?_ mem this]
  -- TODO have automatation doing the next three lines…
  apply mdifferentiableAt_section_of_function e' hx.2
  have := contMDiffAt_coordChangeL (n := 1) (IB := I) hx.1 hx.2
  exact this.mdifferentiableAt (zero_ne_one.symm) |>.clm_apply hs


variable {e} in
lemma coordChangeL_mem_horiz
    [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M] [FiniteDimensional ℝ F]
    {e' : Trivialization F (π F V)} [MemTrivializationAtlas e']
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
    [ContMDiffVectorBundle 1 F V I]
    (hcov : IsCovariantDerivativeOn F cov <| e.baseSet ∩ e'.baseSet)
    {x : M} (hx : x ∈ e.baseSet ∩ e'.baseSet) {u : TangentSpace I x} {v w : F} :
    haveI hcove := e.pushCovDer_isCovariantDerivativeOn inter_subset_left hcov
    haveI hcove' := e'.pushCovDer_isCovariantDerivativeOn inter_subset_right hcov
    (u, w) ∈ hcove.horiz x v →
    (u, e.coordChangeL ℝ e' x w) ∈ hcove'.horiz x (e.coordChangeL ℝ e' x v) := by
  have hcove := e.pushCovDer_isCovariantDerivativeOn inter_subset_left hcov
  have hcove' := e'.pushCovDer_isCovariantDerivativeOn inter_subset_right hcov
  rw [hcove.mem_horiz_iff_exists, hcove'.mem_horiz_iff_exists]
  rintro ⟨s, sdiff, sxv, sxuw, covs⟩
  use fun x ↦ e.coordChangeL ℝ e' x (s x), ?_, ?_, ?_
  · let X := extend I E u
    have hX : MDiffAt (T% X) x := by
      -- TODO: extract as lemma?
      exact (mdifferentiable_extend I E u).mdifferentiableAt
    -- TODO: investigate whether the following line comes from inconsistent ways to
    -- state assumptions
    rw [mdifferentiableAt_section_trivial_iff] at sdiff
    rw [← e.coordChangeL_pushCovDer hcov hx sdiff]
    simp [covs]
  · sorry
  · congr
  · rw [← sxuw]
    sorry

-- This is PAIIIIINNNN
variable {e} in
lemma coordChangeL_coordChangeL
    {e' : Trivialization F (π F V)} [MemTrivializationAtlas e']
    {x : M} (hx : x ∈ e.baseSet ∩ e'.baseSet) (v : F) :
    e'.coordChangeL ℝ e x (e.coordChangeL ℝ e' x v) = v := by
  have hx' := inter_comm _ _ ▸ hx
  change ((coordChangeL ℝ e' e x) ∘ (coordChangeL ℝ e e' x)) v = v
  rw [coe_coordChangeL _ _ hx]
  rw [coe_coordChangeL _ _ hx']
  change
    ((linearEquivAt ℝ e x hx'.2 ∘ (linearEquivAt ℝ e' x hx'.1).symm)  ∘
    (linearEquivAt ℝ e' x hx'.1 ∘ (linearEquivAt ℝ e x hx'.2).symm))
     v = v
  rw [Function.comp_assoc]
  conv =>
    congr
    congr
    rfl
    rw [← Function.comp_assoc]
  change
    ((linearEquivAt ℝ e x _) ∘
    (↑(linearEquivAt ℝ e' x hx'.1).symm ∘ₗ (linearEquivAt ℝ e' x hx'.1).toLinearMap) ∘ _)
    v = v
  rw [(linearEquivAt ℝ e' x hx'.1).symm_comp]
  simp only [LinearMap.id_coe, CompTriple.comp_eq]
  change (↑(linearEquivAt ℝ e x hx'.2) ∘ₗ (linearEquivAt ℝ e x _).symm.toLinearMap) v = v
  rw [(linearEquivAt ℝ e x hx'.2).comp_symm]
  simp

variable {e} in
lemma coordChangeL_mem_horiz_iff
    [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M] [FiniteDimensional ℝ F]
    {e' : Trivialization F (π F V)} [MemTrivializationAtlas e']
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
    [ContMDiffVectorBundle 1 F V I]
    (hcov : IsCovariantDerivativeOn F cov <| e.baseSet ∩ e'.baseSet)
    {x : M} (hx : x ∈ e.baseSet ∩ e'.baseSet) {u : TangentSpace I x} {v w : F} :
    haveI hcove := e.pushCovDer_isCovariantDerivativeOn inter_subset_left hcov
    haveI hcove' := e'.pushCovDer_isCovariantDerivativeOn inter_subset_right hcov
    (u, w) ∈ hcove.horiz x v ↔
    (u, e.coordChangeL ℝ e' x w) ∈ hcove'.horiz x (e.coordChangeL ℝ e' x v) := by
  refine ⟨e.coordChangeL_mem_horiz hcov hx, fun hu ↦ ?_⟩
  let v' := e.coordChangeL ℝ e' x v
  let w' := e.coordChangeL ℝ e' x w
  rw [inter_comm] at hx hcov
  have hx' := inter_comm _ _ ▸ hx
  have hvv' : v = e'.coordChangeL ℝ e x v' := (coordChangeL_coordChangeL hx' v).symm
  have hww' : w = e'.coordChangeL ℝ e x w' := (coordChangeL_coordChangeL hx' w).symm
  have key := e'.coordChangeL_mem_horiz hcov hx (w := w') (u := u) (v := v') ?_
  · rw [← hvv', ← hww'] at key
    convert key using 2
    apply inter_comm
  · convert hu using 2
    apply inter_comm

end to_trivialization

end Bundle.Trivialization

section horiz
namespace CovariantDerivative

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [T2Space M] [IsManifold I ∞ M]
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
    [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]

local notation "TM" => TangentSpace I

-- FIXME the statement of CovariantDerivative.isCovariantDerivativeOn should work on any set

noncomputable
def proj (cov : CovariantDerivative I F V) (v : TotalSpace F V) :
    TangentSpace (I.prod 𝓘(ℝ, F)) v →L[ℝ] V v.proj :=
  letI t := trivializationAt F V v.proj
  haveI d_covDerOn := t.pushCovDer_isCovariantDerivativeOn (u := t.baseSet) subset_rfl
    (cov.isCovariantDerivativeOn.mono fun _ _ ↦ mem_univ _)
  letI tproj := d_covDerOn.projection v.proj (t v).2
  letI Tvt := t.deriv I v
  t.symmL ℝ v.proj ∘L tproj ∘L Tvt

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [T2Space M] in
lemma isCovariantDerivativeOn_pushCovDer
    (cov : CovariantDerivative I F V) (e : Trivialization F (π F V)) [MemTrivializationAtlas e] :
    IsCovariantDerivativeOn F (e.pushCovDer cov) e.baseSet :=
  e.pushCovDer_isCovariantDerivativeOn subset_rfl
      (cov.isCovariantDerivativeOn.mono fun _ _ ↦ mem_univ _)



lemma snd_triv_proj (cov : CovariantDerivative I F V) (v : TotalSpace F V) (u : TangentSpace (I.prod
  𝓘(ℝ, F)) v) :
    letI t := trivializationAt F V v.proj
    haveI d_covDerOn := cov.isCovariantDerivativeOn_pushCovDer t
    letI tproj := d_covDerOn.projection v.proj (t v).2
    letI Tvt := t.deriv I v
    (t <| cov.proj v u).2 = tproj (Tvt u) := by
  simp [CovariantDerivative.proj, (mem_baseSet_trivializationAt F V v.proj)]


noncomputable def horiz (cov : CovariantDerivative I F V) (v : TotalSpace F V) :
    Submodule ℝ (TangentSpace (I.prod 𝓘(ℝ, F)) v) :=
  (cov.proj v).ker

lemma mem_horiz_iff_proj {cov : CovariantDerivative I F V} {v : TotalSpace F V}
    (u : TangentSpace (I.prod 𝓘(ℝ, F)) v) :
    u ∈ cov.horiz v ↔ cov.proj v u = 0 := by
  simp [horiz]

lemma comap_trivializationAt_horiz (cov : CovariantDerivative I F V) (v : TotalSpace F V) :
    letI t := trivializationAt F V v.proj
    haveI d_covDerOn := cov.isCovariantDerivativeOn_pushCovDer t
    horiz cov v = Submodule.comap (t.deriv I v).toLinearMap
      (d_covDerOn.horiz v.proj (t v).2) := by
  -- FIXME: needing all those lets and the change is awful
  let t := trivializationAt F V v.proj
  let Tvt := t.deriv I v
  haveI hcov := cov.isCovariantDerivativeOn_pushCovDer t
  let tproj := hcov.projection v.proj (t v).2
  let t' := t.continuousLinearEquivAt ℝ v.proj (mem_baseSet_trivializationAt F V v.proj)
  ext u
  change t'.symm (tproj (Tvt u)) = 0 ↔ tproj (Tvt u) = 0
  simp


omit [ContMDiffVectorBundle 1 F V I] in
lemma horiz_vert_direct_sum [ContMDiffVectorBundle 1 F V I]
    (cov : CovariantDerivative I F V) (v : TotalSpace F V) :
    IsCompl (cov.horiz v) (vert v) := by
  let t := trivializationAt F V v.proj
  let Tvt := t.deriv I v
  have hcov := cov.isCovariantDerivativeOn_pushCovDer t
  rw [t.comap_vert (mem_baseSet_trivializationAt F V v.proj), comap_trivializationAt_horiz]
  apply LinearMap.comap_isCompl
  · apply t.bijective_deriv
    exact FiberBundle.mem_baseSet_trivializationAt' v.proj
  · apply hcov.horiz_vert_direct_sum

variable [IsManifold I 1 M]
variable {cov : CovariantDerivative I F V}

set_option backward.isDefEq.respectTransparency false in
omit [ContMDiffVectorBundle 1 F V I] in
lemma proj_mderiv [ContMDiffVectorBundle 1 F V I]
    {σ : Π x : M, V x} (x : M)
    (hσ : MDiffAt (T% σ) x) :
    cov σ x = cov.proj (σ x) ∘L
      (mfderiv I (I.prod 𝓘(ℝ, F)) (T% σ) x) := by
  let t := trivializationAt F V x
  let s := fun x ↦ (t (σ x)).2
  let Tσx := mfderiv% (T% σ) x
  -- FIXME `mfderiv%` fails in next line (fixed on master?)
  let Ttσx := mfderiv (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) t (σ x)
  ext1 X₀
  change cov σ x X₀ = (cov.proj (T% σ x)) ((mfderiv% (T% σ) x) X₀)
  have hcov := cov.isCovariantDerivativeOn_pushCovDer t
  have hx := mem_baseSet_trivializationAt F V x
  have hs : MDiffAt (T% s) x := by
    rw [t.mdifferentiableAt_section_iff I σ hx] at hσ
    exact (mdifferentiableAt_section I s).mpr hσ
  apply t.eq_of hx
  erw  [cov.snd_triv_proj (T% σ x),
       ← t.pushCovDer_ofSect (cov.isCovariantDerivativeOn.mono fun _ _ ↦ mem_univ _) hσ,
       hcov.cov_eq_proj s X₀ hs, t.mfderiv_comp_section hσ _ hx]

end CovariantDerivative
end horiz

end real

-- variable (E E') in
-- /-- The trivial connection on a trivial bundle, given by the directional derivative -/
-- @[simps]
-- noncomputable def trivial : CovariantDerivative 𝓘(𝕜, E) E'
--   (Bundle.Trivial E E') where
--   toFun X s := fun x ↦ fderiv 𝕜 s x (X x)
--   isCovariantDerivativeOn :=
--   { addX X X' σ x _ := by simp
--     smulX X σ c' x _ := by simp
--     addσ X σ σ' x hσ hσ' hx := by
--       rw [Bundle.Trivial.mdifferentiableAt_iff] at hσ hσ'
--       rw [fderiv_add hσ hσ']
--       rfl
--     smul_const_σ X σ a x hx := by simp [fderiv_const_smul_of_field a]
--     leibniz X σ f x hσ hf hx := by
--       have : fderiv 𝕜 (f • σ) x = f x • fderiv 𝕜 σ x + (fderiv 𝕜 f x).smulRight (σ x) :=
--         fderiv_smul (by simp_all) (by simp_all)
--       simp [this, bar]
--       rfl }
