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
import Mathlib.Geometry.Manifold.VectorBundle.Misc
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.Elaborators

/-!
# Covariant derivatives

TODO: add a more complete doc-string

-/

open Bundle Filter Function Topology Set

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

variable {I} in
structure IsCovariantDerivativeOn
    (f : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x))
    (s : Set M := Set.univ) : Prop where
  -- All the same axioms as CovariantDerivative, but restricted to the set s.
  addX (f) (X X' : Π x : M, TangentSpace I x) (σ : Π x : M, V x) {x : M}
    (hx : x ∈ s := by trivial) : f (X + X') σ x = f X σ x + f X' σ x
  smulX (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (g : M → 𝕜) {x : M}
    (hx : x ∈ s := by trivial) : f (g • X) σ x = g x • f X σ x
  addσ (X : Π x : M, TangentSpace I x) {σ σ' : Π x : M, V x} {x}
    (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x)
    (hx : x ∈ s := by trivial) :
    f X (σ + σ') x = f X σ x + f X σ' x
  leibniz (X : Π x : M, TangentSpace I x) {σ : Π x : M, V x} {g : M → 𝕜} {x}
    (hσ : MDiffAt (T% σ) x) (hg : MDiffAt g x) (hx : x ∈ s := by trivial):
    f X (g • σ) x = (g • f X σ) x + (bar _ <| mfderiv I 𝓘(𝕜) g x (X x)) • σ x
  smul_const_σ (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (a : 𝕜) {x}
    (hx : x ∈ s := by trivial) : f X (a • σ) x = a • f X σ x

omit [IsManifold I 0 M] [∀ (x : M), IsTopologicalAddGroup (V x)]
     [∀ (x : M), ContinuousSMul 𝕜 (V x)] [VectorBundle 𝕜 F V] in
lemma IsCovariantDerivativeOn.smul_const_X
    {f : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    {s : Set M} (h : IsCovariantDerivativeOn F V f s) {x} (a : 𝕜)
    (X : Π x, TangentSpace I x) (σ : Π x, V x) (hx : x ∈ s := by trivial) :
    f (a • X) σ x = a • f X σ x :=
  h.smulX ..

@[ext]
structure CovariantDerivative where
  toFun : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)
  isCovariantDerivativeOn : IsCovariantDerivativeOn F V toFun Set.univ

variable {I F V}

omit [IsManifold I 0 M] [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)]
  [VectorBundle 𝕜 F V] in
lemma IsCovariantDerivativeOn.mono
    {f : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)} {s t : Set M}
    (hf : IsCovariantDerivativeOn F V f t) (hst : s ⊆ t) : IsCovariantDerivativeOn F V f s where
  addX X X' σ _ hx := hf.addX X X' σ (hst hx)
  smulX X σ f _ hx := hf.smulX X σ f (hst hx)
  addσ X _ _ _ hσ hσ' hx := hf.addσ X hσ hσ' (hst hx)
  leibniz X _ _ _ hσ hf' hx := hf.leibniz X hσ hf' (hst hx)
  smul_const_σ X σ a _ hx := hf.smul_const_σ X σ a (hst hx)

omit [IsManifold I 0 M] [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)]
  [VectorBundle 𝕜 F V] in
lemma IsCovariantDerivativeOn.iUnion {ι : Type*}
    {f : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)} {s : ι → Set M}
    (hf : ∀ i, IsCovariantDerivativeOn F V f (s i)) : IsCovariantDerivativeOn F V f (⋃ i, s i) where
  addX X X' σ x hx := by
    obtain ⟨si, ⟨i, rfl⟩, hxsi⟩ := hx
    exact (hf i).addX ..
  smulX X σ f x hx := by
    obtain ⟨si, ⟨i, rfl⟩, hxsi⟩ := hx
    exact (hf i).smulX ..
  addσ X σ σ' x hσ hσ' hx := by
    obtain ⟨si, ⟨i, rfl⟩, hxsi⟩ := hx
    exact (hf i).addσ _ hσ hσ'
  leibniz X σ f x hσ hf' hx := by
    obtain ⟨si, ⟨i, rfl⟩, hxsi⟩ := hx
    exact (hf i).leibniz _ hσ hf'
  smul_const_σ X σ a x hx := by
    obtain ⟨si, ⟨i, rfl⟩, hxsi⟩ := hx
    exact (hf i).smul_const_σ ..
namespace CovariantDerivative

attribute [coe] toFun

/-- Coercion of a `CovariantDerivative` to function -/
instance : CoeFun (CovariantDerivative I F V)
    fun _ ↦ (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x) :=
  ⟨fun e ↦ e.toFun⟩

omit [IsManifold I 0 M] [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)]
  [VectorBundle 𝕜 F V] in
instance (cov : CovariantDerivative I F V) {s : Set M} :
    IsCovariantDerivativeOn F V cov s := by
  apply cov.isCovariantDerivativeOn.mono (fun ⦃a⦄ a ↦ trivial)

omit [IsManifold I 0 M] [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)]
  [VectorBundle 𝕜 F V] in
/-- If `f : Vec(M) × Γ(E) → Vec(M)` is a covariant derivative on each set in an open cover,
it is a covariant derivative. -/
def of_isCovariantDerivativeOn_of_open_cover {ι : Type*} {s : ι → Set M}
    {f : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    (hf : ∀ i, IsCovariantDerivativeOn F V f (s i)) (hs : ⋃ i, s i = Set.univ) :
    CovariantDerivative I F V :=
  ⟨f, hs ▸ IsCovariantDerivativeOn.iUnion hf⟩

omit [IsManifold I 0 M] [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)]
  [VectorBundle 𝕜 F V] in
@[simp]
lemma of_isCovariantDerivativeOn_of_open_cover_coe {ι : Type*} {s : ι → Set M}
    {f : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    (hf : ∀ i, IsCovariantDerivativeOn F V f (s i)) (hs : ⋃ i, s i = Set.univ) :
    of_isCovariantDerivativeOn_of_open_cover hf hs = f := rfl

variable (F) in
/--
A covariant derivative ∇ is called of class `C^k` iff,
whenever `X` is a `C^k` section and `σ` a `C^{k+1}` section, the result `∇ X σ` is a `C^k` section.
This is a class so typeclass inference can deduce this automatically.
-/
class _root_.ContMDiffCovariantDerivativeOn [IsManifold I 1 M] (k : ℕ∞)
    (cov : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x))
    (u : Set M)  where
  regularity : ∀ {X : Π x : M, TangentSpace I x} {σ : Π x : M, V x},
    CMDiff[u] (k + 1) (T% σ) → CMDiff[u] k (T% X) →
    CMDiff[u] k (T% (cov X σ))

-- TODO: relative the definition below to the above one
/--
A covariant derivative ∇ is called of class `C^k` iff,
whenever `X` is a `C^k` section and `σ` a `C^{k+1}` section, the result `∇ X σ` is a `C^k` section.
This is a class so typeclass inference can deduce this automatically.
-/
class _root_.IsCkConnection (cov : CovariantDerivative I F V) (k : ℕ∞) [IsManifold I 1 M] where
  regularity : ∀ {X : Π x : M, TangentSpace I x} {σ : Π x : M, V x},
    CMDiff (k + 1) (T% σ) → ContMDiff I (I.prod 𝓘(𝕜, E)) k (T% X) →
    -- TODO: CMDiff does not work here!
    ContMDiff% k (T% (cov X σ))

-- future: if g is a C^k metric on a manifold M, the corresponding Levi-Civita connection
-- is of class C^k (up to off-by-one errors)

variable {f : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)} {s : Set M}


omit [IsManifold I 0 M] [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)]
  [VectorBundle 𝕜 F V] in
@[simp]
lemma _root_.IsCovariantDerivativeOn.zeroX (hf : IsCovariantDerivativeOn F V f s)
    {x : M} (hx : x ∈ s := by trivial)
    (σ : Π x : M, V x) : f 0 σ x = 0 := by
  simpa using IsCovariantDerivativeOn.addX f hf 0 0 σ hx

omit [IsManifold I 0 M] [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)]
  [VectorBundle 𝕜 F V] in
@[simp]
lemma zeroX (cov : CovariantDerivative I F V) (σ : Π x : M, V x) : cov 0 σ = 0 := by
  ext x
  apply cov.isCovariantDerivativeOn.zeroX

omit [IsManifold I 0 M] [∀ (x : M), IsTopologicalAddGroup (V x)]
     [∀ (x : M), ContinuousSMul 𝕜 (V x)] in
@[simp]
lemma _root_.IsCovariantDerivativeOn.zeroσ (hf : IsCovariantDerivativeOn F V f s)
    (X : Π x : M, TangentSpace I x)
    {x} (hx : x ∈ s := by trivial) : f X 0 x = 0 := by
  simpa using (hf.addσ X (mdifferentiableAt_zeroSection ..)
    (mdifferentiableAt_zeroSection ..) : f X (0+0) x = _)

omit [IsManifold I 0 M] [∀ (x : M), IsTopologicalAddGroup (V x)]
     [∀ (x : M), ContinuousSMul 𝕜 (V x)] in

@[simp]
lemma zeroσ (cov : CovariantDerivative I F V) (X : Π x : M, TangentSpace I x) : cov X 0 = 0 := by
  ext x
  apply cov.isCovariantDerivativeOn.zeroσ

omit [IsManifold I 0 M] [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)]
  [VectorBundle 𝕜 F V] in
lemma _root_.IsCovariantDerivativeOn.sum_X (hf : IsCovariantDerivativeOn F V f s)
    {ι : Type*} {u : Finset ι} {X : ι → Π x : M, TangentSpace I x} {σ : Π x : M, V x}
    {x} (hx : x ∈ s) :
    f (∑ i ∈ u, X i) σ x = ∑ i ∈ u, f (X i) σ x := by
  classical
  have := hf.zeroX hx σ
  induction u using Finset.induction_on with
  | empty => simp [hf.zeroX hx]
  | insert a u ha h =>
    simp [Finset.sum_insert ha, ← h, hf.addX]


omit [IsManifold I 0 M] [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)]
  [VectorBundle 𝕜 F V] in
lemma sum_X (cov : CovariantDerivative I F V)
    {ι : Type*} {s : Finset ι} {X : ι → Π x : M, TangentSpace I x} {σ : Π x : M, V x} :
    cov (∑ i ∈ s, X i) σ = ∑ i ∈ s, cov (X i) σ := by
  ext x
  simpa using cov.isCovariantDerivativeOn.sum_X

/-- A convex combination of covariant derivatives is a covariant derivative. -/
@[simps]
def _root_.IsCovariantDerivativeOn.convexCombination
    {f' : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    (hf : IsCovariantDerivativeOn F V f s) (hf' : IsCovariantDerivativeOn F V f' s) (g : M → 𝕜) :
    IsCovariantDerivativeOn F V (fun X σ ↦ (g • (f X σ)) + (1 - g) • (f' X σ)) s where
  addX X X' σ _ hx := by simp [hf.addX, hf'.addX]; module
  smulX X σ φ _ hx := by simp [hf.smulX, hf'.smulX]; module
  addσ X σ σ' x hx hσ hσ' := by
      simp [hf.addσ X hx hσ hσ', hf'.addσ X hx hσ hσ']
      module
  smul_const_σ X {σ a} x hx := by
      simp [hf.smul_const_σ, hf'.smul_const_σ]
      module
  leibniz X σ φ x hσ hφ hx := by
      simp [hf.leibniz X hσ hφ, hf'.leibniz X hσ hφ]
      module

/-- A convex combination of covariant derivatives is a covariant derivative. -/
@[simps]
def convexCombination (cov cov' : CovariantDerivative I F V) (g : M → 𝕜) :
    CovariantDerivative I F V where
  toFun := fun X σ ↦ (g • (cov X σ)) + (1 - g) • (cov' X σ)
  isCovariantDerivativeOn :=
    cov.isCovariantDerivativeOn.convexCombination cov'.isCovariantDerivativeOn _

/-- A finite convex combination of covariant derivatives is a covariant derivative. -/
def _root_.IsCovariantDerivativeOn.convexCombination' {ι : Type*} {s : Finset ι} [Nonempty s]
    {u : Set M} {cov : ι → (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    (h : ∀ i, IsCovariantDerivativeOn F V (cov i) u) {f : ι → M → 𝕜} (hf : ∑ i ∈ s, f i = 1) :
    IsCovariantDerivativeOn F V (fun X σ x ↦ ∑ i ∈ s, (f i x) • (cov i) X σ x) u where
  addX X X' σ x hx := by
    rw [← Finset.sum_add_distrib]
    congr
    ext i
    simp [(h i).addX]
  smulX X σ g x hx := by
    rw [Finset.smul_sum]
    congr
    ext i
    simp [(h i).smulX]
    module
  addσ X σ σ' x hx hσ hσ' := by
    -- XXX: is this nicer using induction?
    classical
    induction s using Finset.induction with
    | empty => simp
    | insert a s has h =>
      simp [Finset.sum_insert has]
      sorry
  smul_const_σ X {σ a} x hx := by
    rw [Finset.smul_sum]
    congr
    ext i
    simp [(h i).smul_const_σ]
    module
  leibniz X σ g x hσ hg hx := by
    calc ∑ i ∈ s, f i x • (cov i) X (g • σ) x
      _ = ∑ i ∈ s, ((g • (f i • (cov i) X σ)) x
            + f i x • (bar (g x)) ((mfderiv I 𝓘(𝕜) g x) (X x)) • σ x) := by
        congr
        ext i
        rw [(h i).leibniz _ hσ hg]
        simp_rw [Pi.smul_apply', smul_add, add_left_inj]
        rw [smul_comm]
      _ = ∑ i ∈ s, ((g • (f i • (cov i) X σ)) x)
        + ∑ i ∈ s, f i x • (bar (g x)) ((mfderiv I 𝓘(𝕜) g x) (X x)) • σ x := by
        rw [Finset.sum_add_distrib]
      _ = (g • ∑ i ∈ s, f i • (cov i) X σ) x + (bar (g x)) ((mfderiv I 𝓘(𝕜) g x) (X x)) • σ x := by
        -- There has to be a shorter proof!
        simp only [Finset.smul_sum, Pi.smul_apply', Finset.sum_apply, add_right_inj]
        set B := (bar (g x)) ((mfderiv I 𝓘(𝕜) g x) (X x)) • σ x
        trans (∑ i ∈ s, f i x) • B
        · rw [Finset.sum_smul]
        have : ∑ i ∈ s, f i x = 1 := by convert congr_fun hf x; simp
        rw [this, one_smul]
    simp

/-- A finite convex combination of covariant derivatives is a covariant derivative. -/
def convexCombination' {ι : Type*} {s : Finset ι} [Nonempty s]
    (cov : ι → CovariantDerivative I F V) {f : ι → M → 𝕜} (hf : ∑ i ∈ s, f i = 1) :
    CovariantDerivative I F V where
  toFun X t x := ∑ i ∈ s, (f i x) • (cov i) X t x
  isCovariantDerivativeOn := IsCovariantDerivativeOn.convexCombination'
    (fun i ↦ (cov i).isCovariantDerivativeOn) hf

omit [IsManifold I 0 M]
  [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)] in
/-- A convex combination of two `C^k` connections is a `C^k` connection. -/
lemma ContMDiffCovariantDerivativeOn.convexCombination [IsManifold I 1 M]
    {cov cov' : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    {u: Set M} {f : M → 𝕜} {n : ℕ∞} (hf : CMDiff[u] n f)
    (Hcov : ContMDiffCovariantDerivativeOn (F := F) n cov u)
    (Hcov' : ContMDiffCovariantDerivativeOn (F := F) n cov' u) :
    ContMDiffCovariantDerivativeOn F n (fun X σ ↦ (f • (cov X σ)) + (1 - f) • (cov' X σ)) u where
  regularity hX hσ := by
    apply ContMDiffOn.add_section
    · exact hf.smul_section <| Hcov.regularity hX hσ
    · exact (contMDiffOn_const.sub hf).smul_section <| Hcov'.regularity hX hσ

omit [IsManifold I 0 M]
  [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)] in
/-- A convex combination of two `C^k` connections is a `C^k` connection. -/
lemma _root_.IsCovariantDerivativeOn.convexCombination_isRegular [IsManifold I 1 M]
  (cov cov' : CovariantDerivative I F V)
    {f : M → 𝕜} {n : ℕ∞} (hf : ContMDiff I 𝓘(𝕜) n f)
    (hcov : IsCkConnection cov n) (hcov' : IsCkConnection cov' n) :
    IsCkConnection (convexCombination cov cov' f) n where
  regularity {X σ} hX hσ := by
    apply ContMDiff.add_section
    · exact hf.smul_section <| hcov.regularity hX hσ
    · exact (contMDiff_const.sub hf).smul_section <| hcov'.regularity hX hσ

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
      apply (hf' i hi).smul_section <| IsCkConnection.regularity hX hσ (self := hcov i hi)
    exact .sum_section (t := fun i ↦ f i • (cov i) X σ) ms

-- Future: prove a version with a locally finite sum, and deduce that C^k connections always
-- exist (using a partition of unity argument)

section trivial_bundle

omit [IsManifold I 0 M] in
lemma mfderiv_const_smul (s : M → F) {x : M} (a : 𝕜) (v : TangentSpace I x) :
    mfderiv I 𝓘(𝕜, F) (a • s) x v = a • mfderiv I 𝓘(𝕜, F) s x v := by
  by_cases hs : MDifferentiableAt% s x
  · have hs' := hs.const_smul a
    suffices
      (fderivWithin 𝕜 ((a • s) ∘ (chartAt H x).symm ∘ I.symm) (range I) (I ((chartAt H x) x))) v =
       a • (fderivWithin 𝕜 (s ∘ (chartAt H x).symm ∘ I.symm) (range I)
       (I ((chartAt H x) x))) v by simpa [mfderiv, hs, hs']
    change fderivWithin 𝕜 (a • (s ∘ ↑(chartAt H x).symm ∘ ↑I.symm)) _ _ _ = _
    rw [fderivWithin_const_smul_field _ I.uniqueDiffWithinAt_image ]
    rfl
  · by_cases ha : a = 0
    · have : a • s = 0 := by ext; simp [ha]
      rw [this, ha]
      change (mfderiv I 𝓘(𝕜, F) (fun _ ↦ 0) x) v = _
      simp
    have hs' : ¬ MDifferentiableAt I 𝓘(𝕜, F) (a • s) x :=
      fun h ↦ hs (by simpa [ha] using h.const_smul a⁻¹)
    rw [mfderiv_zero_of_not_mdifferentiableAt hs, mfderiv_zero_of_not_mdifferentiableAt hs']
    simp
    rfl

lemma mfderiv_smul {f : M → F} {s : M → 𝕜} {x : M} (hf : MDiffAt f x)
    (hs : MDiffAt s x) (v : TangentSpace I x) :
    letI dsxv : 𝕜 := mfderiv I 𝓘(𝕜, 𝕜) s x v
    letI dfxv : F := mfderiv I 𝓘(𝕜, F) f x v
    mfderiv I 𝓘(𝕜, F) (s • f) x v = (s x) • dfxv + dsxv • f x := by
  sorry

variable (I M F) in
@[simps]
noncomputable def trivial : CovariantDerivative I F (Trivial M F) where
  toFun X s := fun x ↦ mfderiv I 𝓘(𝕜, F) s x (X x)
  isCovariantDerivativeOn :=
  { addX X X' σ x _ := by simp
    smulX X σ c' x _ := by simp
    addσ X σ σ' x hσ hσ' hx := by
      rw [mdifferentiableAt_section] at hσ hσ'
      -- TODO: specialize mdifferentiableAt_section to trivial bundles?
      change MDifferentiableAt I 𝓘(𝕜, F) σ x at hσ
      change MDifferentiableAt I 𝓘(𝕜, F) σ' x at hσ'
      rw [mfderiv_add hσ hσ']
      rfl
    smul_const_σ X σ a x hx := by
      rw [mfderiv_const_smul]
    leibniz X σ f x hσ hf hx := by
      rw [mdifferentiableAt_section] at hσ
      exact mfderiv_smul hσ hf (X x) }
end trivial_bundle

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']

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

-- TODO: does it make sense to speak of analytic connections? if so, change the definition of
-- regularity and use ∞ from `open scoped ContDiff` instead.

/-- The trivial connection on the trivial bundle is smooth -/
lemma trivial_isSmooth : IsCkConnection (𝕜 := 𝕜) (trivial 𝓘(𝕜, E) E E') (⊤ : ℕ∞) where
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


lemma of_endomorophism_isCovariantDerivativeOn (A : E → E →L[𝕜] E' →L[𝕜] E') :
    IsCovariantDerivativeOn E' (Bundle.Trivial E E')
      (fun (X : Π x : E, TangentSpace 𝓘(𝕜, E) x) (σ : E → E') x ↦
        fderiv 𝕜 σ x (X x) + A x (X x) (σ x)) univ where
  addX X X' σ x _ := by
    by_cases h : DifferentiableAt 𝕜 σ x
    · simp [map_add]; abel
    · simp [fderiv_zero_of_not_differentiableAt h]
  smulX X σ c' := by simp
  addσ X σ σ' x hσ hσ' hx := by
    rw [Bundle.Trivial.mdifferentiableAt_iff] at hσ hσ'
    simp [fderiv_add hσ hσ']
    abel
  smul_const_σ X σ a x hx := by simp [fderiv_const_smul_of_field a]
  leibniz X σ f x hσ hf hx := by
    rw [Bundle.Trivial.mdifferentiableAt_iff] at hσ
    rw [mdifferentiableAt_iff_differentiableAt] at hf
    have : fderiv 𝕜 (f • σ) x = f x • fderiv 𝕜 σ x + (fderiv 𝕜 f x).smulRight (σ x) :=
      fderiv_smul (by simp_all) (by simp_all)
    simp [this, bar]
    module

noncomputable def of_endomorphism (A : E → E →L[𝕜] E' →L[𝕜] E') :
    CovariantDerivative 𝓘(𝕜, E) E' (Bundle.Trivial E E') where
  toFun X σ := fun x ↦ fderiv 𝕜 σ x (X x) + A x (X x) (σ x)
  isCovariantDerivativeOn := of_endomorophism_isCovariantDerivativeOn A

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
lemma congr_X_at {cov : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    [T2Space M] [IsManifold I ∞ M] {u : Set M} (hcov : IsCovariantDerivativeOn F V cov u)
    (X X' : Π x : M, TangentSpace I x) {σ : Π x : M, V x} {x : M} (hx : x ∈ u) (hXX' : X x = X' x) :
    cov X σ x = cov X' σ x := by
  apply tensoriality_criterion' (E := E) (I := I) E (TangentSpace I) F V hXX'
  · intro f X
    rw [hcov.smulX]
  · intro X X'
    rw [hcov.addX]

/- TODO: are these lemmas still useful after the general tensoriality lemma?
are they worth extracting separately?
omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul ℝ (V x)]
  [VectorBundle ℝ F V] in
lemma congr_σ_smoothBumpFunction (cov : CovariantDerivative I F V) [T2Space M] [IsManifold I ∞ M]
    (X : Π x : M, TangentSpace I x) {σ : Π x : M, V x}
    (hσ : MDiffAt (T% σ) x)
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
    (hσ : MDiffAt (T% σ) x)
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
    _ = cov X ((ψ : M → ℝ) • σ') x := sorry -- use simp [funext hσ] and (by simp [this])
    _ = cov X σ' x := by
      simp [cov.congr_σ_smoothBumpFunction, mdifferentiableAt_dependent_congr hs hσ hσσ']
-/

-- TODO: prove that `cov X σ x` depends on σ only via σ(X) and the 1-jet of σ at x

/-- The difference of two covariant derivatives, as a function `Γ(TM) × Γ(E) → Γ(E)`.
Future lemmas will upgrade this to a map `TM ⊕ E → E`. -/
def differenceAux (cov cov' : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)) :
    (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x) :=
  fun X σ ↦ cov X σ - cov' X σ

omit [FiniteDimensional ℝ E] [∀ (x : M), IsTopologicalAddGroup (V x)]
  [∀ (x : M), ContinuousSMul ℝ (V x)] [VectorBundle ℝ F V]
  [(x : M) → Module ℝ (V x)] [(x : M) → TopologicalSpace (V x)] in
@[simp]
lemma differenceAux_apply
    (cov cov' : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x))
    (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) :
    differenceAux cov cov' X σ = cov X σ - cov' X σ := rfl

omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul ℝ (V x)]
  [VectorBundle ℝ F V] [FiniteDimensional ℝ E] in
lemma _root_.IsCovariantDerivativeOn.differenceAux_smul_eq
    {cov cov' : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    {u : Set M} (hcov : IsCovariantDerivativeOn F V cov u)
    (hcov' : IsCovariantDerivativeOn F V cov' u)
    (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (f : M → ℝ)
    {x : M} (hx : x ∈ u := by trivial)
    (hσ : MDiffAt (T% σ) x)
    (hf : MDiffAt f x) :
    differenceAux cov cov' X ((f : M → ℝ) • σ) x = f x • differenceAux cov cov' X σ x:=
  calc _
    _ = cov X ((f : M → ℝ) • σ) x - cov' X ((f : M → ℝ) • σ) x := rfl
    _ = (f x • cov X σ x +  (bar _ <| mfderiv I 𝓘(ℝ) f x (X x)) • σ x)
        - (f x • cov' X σ x +  (bar _ <| mfderiv I 𝓘(ℝ) f x (X x)) • σ x) := by
      simp [hcov.leibniz X hσ hf, hcov'.leibniz X hσ hf]
    _ = f x • cov X σ x - f x • cov' X σ x := by simp
    _ = f x • (cov X σ x - cov' X σ x) := by simp [smul_sub]
    _ = _ := rfl

omit [FiniteDimensional ℝ E] [∀ (x : M), IsTopologicalAddGroup (V x)]
    [∀ (x : M), ContinuousSMul ℝ (V x)] [VectorBundle ℝ F V] in
lemma _root_.IsCovariantDerivativeOn.differenceAux_smul_eq'
    {cov cov' : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    {u : Set M} (hcov : IsCovariantDerivativeOn F V cov u)
    (hcov' : IsCovariantDerivativeOn F V cov' u)
    (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (f : M → ℝ)
    {x : M} (hx : x ∈ u := by trivial) :
    differenceAux cov cov' (f • X) σ x = f x • differenceAux cov cov' X σ x := by
  simp [differenceAux, hcov.smulX, hcov'.smulX, smul_sub]

omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul ℝ (V x)] in
/-- The value of `differenceAux cov cov' X σ` at `x₀` depends only on `X x₀` and `σ x₀`. -/
lemma _root_.IsCovariantDerivativeOn.differenceAux_tensorial
    {cov cov' : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    {u : Set M} (hcov : IsCovariantDerivativeOn F V cov u)
    (hcov' : IsCovariantDerivativeOn F V cov' u)
    [T2Space M] [IsManifold I ∞ M]
    [FiniteDimensional ℝ F] [ContMDiffVectorBundle 1 F V I]
    {X X' : Π x : M, TangentSpace I x} {σ σ' : Π x : M, V x} {x₀ : M}
    (hσ : MDiffAt (T% σ) x₀)
    (hσ' : MDiffAt (T% σ') x₀)
    (hXX' : X x₀ = X' x₀) (hσσ' : σ x₀ = σ' x₀) (hx : x₀ ∈ u := by trivial) :
    differenceAux cov cov' X σ x₀ = differenceAux cov cov' X' σ' x₀ := by
  trans differenceAux cov cov' X' σ x₀
  · let φ : (Π x : M, TangentSpace I x) → (Π x, V x) := fun X ↦ differenceAux cov cov' X σ
    change φ X x₀ = φ X' x₀
    apply tensoriality_criterion' (E := E) (I := I) E (TangentSpace I) F V hXX'
    · intro f X
      apply hcov.differenceAux_smul_eq' hcov'
    · intro X X'
      unfold φ CovariantDerivative.differenceAux
      simp only [Pi.sub_apply, hcov.addX, hcov'.addX]
      abel
  · let φ : (Π x : M, V x) → (Π x, V x) := fun σ ↦ differenceAux cov cov' X' σ
    change φ σ x₀ = φ σ' x₀
    apply tensoriality_criterion (E := E) (I := I) F V F V hσ hσ' hσσ'
    · intro f σ x hf
      exact hcov.differenceAux_smul_eq hcov' X' σ f hx hf x
    · intro σ σ' hσ hσ'
      unfold φ differenceAux
      simp
      rw [hcov.addσ, hcov'.addσ] <;> try assumption
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
lemma extend_smul [FiniteDimensional ℝ F] [T2Space M] {a : ℝ} (v : V x) :
  extend I F (a • v) = a • extend I F v := by simp [extend, localExtensionOn_smul]; module

omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul ℝ (V x)] in
@[simp] lemma extend_apply_self [FiniteDimensional ℝ F] [T2Space M] {x : M} (v : V x) :
    extend I F v x = v := by
  simpa [extend] using
    localExtensionOn_apply_self _ _ (FiberBundle.mem_baseSet_trivializationAt' x) v

omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul ℝ (V x)] in
lemma contMDiff_extend [IsManifold I ∞ M] [FiniteDimensional ℝ F] [T2Space M]
    [ContMDiffVectorBundle ∞ F V I] {x : M} (σ₀ : V x) :
    ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% extend I F σ₀) := by
  letI t := trivializationAt F V x
  letI ht := t.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x)
  have hx : x ∈ t.baseSet := by exact FiberBundle.mem_baseSet_trivializationAt' x
  let ψ := Classical.choose <| (SmoothBumpFunction.nhds_basis_support (I := I) ht).mem_iff.1 ht
  let hψ :=
    Classical.choose_spec <| (SmoothBumpFunction.nhds_basis_support (I := I) ht).mem_iff.1 ht
  apply ψ.contMDiff.contMDiffOn.smul_section_of_tsupport t.open_baseSet hψ.1
  apply contMDiffOn_localExtensionOn _ hx

variable (F I) in
omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul ℝ (V x)] in
lemma mdifferentiable_extend [IsManifold I ∞ M] [FiniteDimensional ℝ F] [T2Space M]
    [ContMDiffVectorBundle ∞ F V I] {x : M} (σ₀ : V x) :
    MDiff (T% extend I F σ₀) :=
  contMDiff_extend σ₀ |>.mdifferentiable (by simp)

omit [FiniteDimensional ℝ E] [∀ (x : M), IsTopologicalAddGroup (V x)]
  [∀ (x : M), ContinuousSMul ℝ (V x)] in
lemma isBilinearMap_differenceAux
    [FiniteDimensional ℝ F] [T2Space M] [FiniteDimensional ℝ E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle ∞ F V I] {s : Set M} {cov cov'} {x : M}
    (hcov : IsCovariantDerivativeOn F V cov s)
    (hcov' : IsCovariantDerivativeOn F V cov' s) (hx : x ∈ s := by trivial) :
    IsBilinearMap ℝ (fun (X₀ : TangentSpace I x) (σ₀ : V x) ↦
      differenceAux cov cov' (extend I E X₀) (extend I F σ₀) x) where
  add_left u v w := by
    simp only [differenceAux, extend_add, Pi.sub_apply, hcov.addX, hcov'.addX]
    abel
  add_right u v w := by
    have hv := mdifferentiable_extend I F v x
    have hw := mdifferentiable_extend I F w x
    simp only [differenceAux, extend_add, Pi.sub_apply]
    rw [hcov.addσ _ hv hw, hcov'.addσ _ hv hw]
    abel
  smul_left a u v := by
    unfold differenceAux
    simp only [extend_smul, Pi.sub_apply, hcov.smul_const_X, hcov'.smul_const_X]
    module
  smul_right a u v := by
    unfold differenceAux
    simp only [extend_smul, Pi.sub_apply, hcov.smul_const_σ, hcov'.smul_const_σ]
    module

/-- The difference of two covariant derivatives, as a tensorial map -/
noncomputable def difference [∀ x, FiniteDimensional ℝ (V x)] [∀ x, T2Space (V x)]
    [FiniteDimensional ℝ F] [T2Space M] [FiniteDimensional ℝ E] [IsManifold I ∞ M]
    [FiniteDimensional ℝ E] [ContMDiffVectorBundle ∞ F V I]
    {cov cov' : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    {s : Set M} {x : M}
    (hcov : IsCovariantDerivativeOn F V cov s)
    (hcov' : IsCovariantDerivativeOn F V cov' s)
    (hx : x ∈ s := by trivial) : TangentSpace I x →L[ℝ] V x →L[ℝ] V x :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := by assumption
  (isBilinearMap_differenceAux (F := F) hcov hcov').toContinuousLinearMap

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

lemma difference_def [∀ x, FiniteDimensional ℝ (V x)] [∀ x, T2Space (V x)]
    [FiniteDimensional ℝ F] [T2Space M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle ∞ F V I]
    {cov cov' : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    {s : Set M} {x : M}
    (hcov : IsCovariantDerivativeOn F V cov s)
    (hcov' : IsCovariantDerivativeOn F V cov' s)
    (hx : x ∈ s := by trivial) (X₀ : TangentSpace I x) (σ₀ : V x) :
    difference hcov hcov' hx X₀ σ₀ =
      cov (extend I E X₀) (extend I F σ₀) x - cov' (extend I E X₀) (extend I F σ₀) x := rfl

@[simp]
lemma difference_apply [∀ x, FiniteDimensional ℝ (V x)] [∀ x, T2Space (V x)]
    [FiniteDimensional ℝ F] [T2Space M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle ∞ F V I]
    {cov cov' : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    {s : Set M} {x : M}
    (hcov : IsCovariantDerivativeOn F V cov s)
    (hcov' : IsCovariantDerivativeOn F V cov' s)
    (hx : x ∈ s := by trivial) (X : Π x, TangentSpace I x) {σ : Π x, V x}
    (hσ : MDiffAt (T% σ) x) :
    difference hcov hcov' hx (X x) (σ x) =
      cov X σ x - cov' X σ x :=
  hcov.differenceAux_tensorial hcov' (mdifferentiable_extend ..) hσ (extend_apply_self _)
    (extend_apply_self _) hx

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
    MDiffAt (T% σ) x →
    cov X σ x = (CovariantDerivative.of_endomorphism A) X σ x := by
  use fun x ↦ difference cov.isCovariantDerivativeOn
    (CovariantDerivative.trivial 𝓘(ℝ, E) E E').isCovariantDerivativeOn (mem_univ x)
  intro X σ x hσ
  simp only [of_endomorphism]
  erw [difference_apply cov.isCovariantDerivativeOn
       (CovariantDerivative.trivial 𝓘(ℝ, E) E E').isCovariantDerivativeOn _ X hσ, trivial]
  simp only [mfderiv_eq_fderiv]
  module

end classification

section from_trivialization

variable (e : Trivialization F (π F V)) [MemTrivializationAtlas e]

noncomputable
def _root_.Trivialization.covDeriv (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x)
    (x : M) : V x := e.symm x (mfderiv I 𝓘(ℝ, F) (fun x' ↦ (e (σ x')).2) x (X x))

lemma _root_.Trivialization.covDeriv_isCovariantDerivativeOn :
    IsCovariantDerivativeOn (I := I) F V e.covDeriv e.baseSet where
  addX X X' σ x hx := by sorry
  smulX X σ c' x hx := by sorry
  addσ X σ σ' x hσ hσ' hx := by sorry
  smul_const_σ X σ a x hx := by sorry
  leibniz X σ f x hσ hf hx := by sorry

end from_trivialization

section horiz

def proj (cov : CovariantDerivative I F V) (v : TotalSpace F V) :
    TangentSpace (I.prod 𝓘(ℝ, F)) v →L[ℝ] V v.proj := by
  sorry

noncomputable def horiz (cov : CovariantDerivative I F V) (v : TotalSpace F V) :
    Submodule ℝ (TangentSpace (I.prod 𝓘(ℝ, F)) v) :=
  LinearMap.ker (cov.proj v)

noncomputable def _root_.Bundle.vert (v : TotalSpace F V) :
    Submodule ℝ (TangentSpace (I.prod 𝓘(ℝ, F)) v) :=
  LinearMap.ker (mfderiv (I.prod 𝓘(ℝ, F)) I Bundle.TotalSpace.proj v)

lemma horiz_vert_direct_sum (cov : CovariantDerivative I F V) (v : TotalSpace F V) :
    IsCompl (cov.horiz v) (vert v) := by
  sorry

variable [IsManifold I 1 M]
variable {cov : CovariantDerivative I F V}

lemma proj_mderiv {X : Π x : M, TangentSpace I x} {σ : Π x : M, V x} (x : M)
    (hX : MDiffAt (T% X) x)
    (hσ : MDiffAt (T% σ) x) :
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

set_option linter.style.commandStart false -- new delaborators confuse the pretty-printer

variable (Y) in
lemma torsion_add_left_apply [CompleteSpace E] {x : M}
    (hX : MDiffAt (T% X) x)
    (hX' : MDiffAt (T% X') x) :
    torsion cov (X + X') Y x = torsion cov X Y x + torsion cov X' Y x := by
  simp [torsion, cov.isCovariantDerivativeOn.addX X X' (x := x)]
  rw [cov.isCovariantDerivativeOn.addσ Y hX hX', VectorField.mlieBracket_add_left hX hX']
  module

variable (Y) in
lemma torsion_add_left [CompleteSpace E]
    (hX : MDiff (T% X)) (hX' : MDiff (T% X')) :
    torsion cov (X + X') Y = torsion cov X Y + torsion cov X' Y := by
  ext x
  exact cov.torsion_add_left_apply _ (hX x) (hX' x)

lemma torsion_add_right_apply [CompleteSpace E] {x : M}
    (hX : MDiffAt (T% X) x)
    (hX' : MDiffAt (T% X') x) :
    torsion cov Y (X + X') x = torsion cov Y X x + torsion cov Y X' x := by
  rw [torsion_antisymm, Pi.neg_apply,
    cov.torsion_add_left_apply _ hX hX', torsion_antisymm Y, torsion_antisymm Y]
  simp; abel

lemma torsion_add_right [CompleteSpace E]
    (hX : MDiff (T% X)) (hX' : MDiff (T% X')) :
    torsion cov Y (X + X') = torsion cov Y X + torsion cov Y X' := by
  rw [torsion_antisymm, torsion_add_left _ hX hX', torsion_antisymm X, torsion_antisymm X']; module

variable (Y) in
lemma torsion_smul_left_apply [CompleteSpace E] {f : M → ℝ} {x : M} (hf : MDiffAt f x)
    (hX : MDiffAt (T% X) x) :
    torsion cov (f • X) Y x = f x • torsion cov X Y x := by
  simp only [torsion, cov.isCovariantDerivativeOn.smulX X Y f, Pi.sub_apply]
  rw [cov.isCovariantDerivativeOn.leibniz Y hX hf, VectorField.mlieBracket_smul_left hf hX]
  simp [bar, smul_sub]
  abel

variable (Y) in
lemma torsion_smul_left [CompleteSpace E] {f : M → ℝ} (hf : MDiff f) (hX : MDiff (T% X)) :
    torsion cov (f • X) Y = f • torsion cov X Y := by
  ext x
  exact cov.torsion_smul_left_apply _ (hf x) (hX x)

variable (X) in
lemma torsion_smul_right_apply [CompleteSpace E] {f : M → ℝ} {x : M} (hf : MDiffAt f x)
    (hX : MDiffAt (T% Y) x) :
    torsion cov X (f • Y) x = f x • torsion cov X Y x := by
  rw [torsion_antisymm, Pi.neg_apply, torsion_smul_left_apply X hf hX, torsion_antisymm X]
  simp

variable (X) in
lemma torsion_smul_right [CompleteSpace E] {f : M → ℝ} (hf : MDiff f) (hY : MDiff (T% Y)) :
    torsion cov X (f • Y) = f • torsion cov X Y := by
  ext x
  apply cov.torsion_smul_right_apply _ (hf x) (hY x)

omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul ℝ (V x)] in
/-- The torsion of a covariant derivative is tensorial:
the value of `torsion cov X Y` at `x₀` depends only on `X x₀` and `Y x₀`. -/
def torsion_tensorial [T2Space M] [IsManifold I ∞ M]
    [FiniteDimensional ℝ F] [ContMDiffVectorBundle 1 F V I]
    {X X' Y Y' : Π x : M, TangentSpace I x} {x₀ : M}
    (hX : MDiffAt (T% X) x₀) (hX' : MDiffAt (T% X') x₀)
    (hY : MDiffAt (T% Y) x₀) (hY' : MDiffAt (T% Y') x₀)
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

set_option linter.style.commandStart true

variable (cov) in
/-- A covariant derivation is called **torsion-free** iff its torsion tensor vanishes. -/
def IsTorsionFree : Prop := torsion cov = 0

lemma isTorsionFree_def : IsTorsionFree cov ↔ torsion cov = 0 := by simp [IsTorsionFree]

-- This should be obvious, I'm doing something wrong.
lemma isTorsionFree_iff : IsTorsionFree cov ↔
    ∀ X Y, cov X Y - cov Y X = VectorField.mlieBracket I X Y := by
  simp [IsTorsionFree]
  constructor
  · intro h X Y
    have : torsion cov X Y = 0 := by simp [h]
    -- XXX: abel, ring, module and grind all fail here
    exact eq_of_sub_eq_zero this
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
