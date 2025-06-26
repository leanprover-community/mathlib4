import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable

open Bundle Filter Function Topology

open scoped Bundle Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

section localFrame

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 0 M]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  -- `F` model fiber
  (n : WithTop ℕ∞)
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V] [ContMDiffVectorBundle n F V I]
  -- `V` vector bundle

set_option linter.style.commandStart false

namespace Basis

variable {ι : Type*}

noncomputable def localFrame_toBasis_at
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas e]
    (b : Basis ι 𝕜 F) {x : M} (hx : x ∈ e.baseSet) : Basis ι 𝕜 (V x) :=
  b.map (e.linearEquivAt (R := 𝕜) x hx).symm

open scoped Classical in
-- If x is outside of `e.baseSet`, this returns the junk value 0.
noncomputable def localFrame
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas e]
    (b : Basis ι 𝕜 F) : ι → (x : M) → V x := fun i x ↦
  -- idea: take the vector b i and apply the trivialisation e to it.
  if hx : x ∈ e.baseSet then b.localFrame_toBasis_at e hx i else 0

-- TODO: understand why this isn’t already a simp lemma
attribute [simp] Trivialization.apply_mk_symm

omit [IsManifold I 0 M]
    [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)]
    [ContMDiffVectorBundle n F V I] in
/-- Each local frame `s^i ∈ Γ(E)` of a `C^k` vector bundle, defined by a local trivialisation `e`,
is `C^k` on `e.baseSet`. -/
lemma contMDiffOn_localFrame_baseSet
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas e] (b : Basis ι 𝕜 F) (i : ι) :
    ContMDiffOn I (I.prod 𝓘(𝕜, F)) n
      (fun x ↦ TotalSpace.mk' F x (b.localFrame e i x)) e.baseSet := by
  rw [contMDiffOn_section_of_mem_baseSet]
  apply (contMDiffOn_const (c := b i)).congr
  intro y hy
  simp [localFrame, hy, localFrame_toBasis_at]

omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)] in
@[simp]
lemma localFrame_apply_of_mem_baseSet
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas e] (b : Basis ι 𝕜 F) {i : ι} {x : M} (hx : x ∈ e.baseSet) :
    b.localFrame e i x = b.localFrame_toBasis_at e hx i := by
  simp [localFrame, hx]

omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)] in
@[simp]
lemma localFrame_apply_of_notMem
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas e] (b : Basis ι 𝕜 F) {i : ι} {x : M} (hx : x ∉ e.baseSet) :
    b.localFrame e i x = 0 := by
  simp [localFrame, hx]

omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)] in
lemma localFrame_toBasis_at_coe
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas e]
    (b : Basis ι 𝕜 F) {x : M} (i : ι) (hx : x ∈ e.baseSet) :
    b.localFrame_toBasis_at e hx i = b.localFrame e i x := by simp [hx]

-- XXX: is this result actually needed now? perhaps not, because of the toBasis definition?
/-- At each point `x ∈ M`, the sections `{sⁱ(x)}` of a local frame form a basis for `V x`. -/
def isBasis_localFrame
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas e]
    (b : Basis ι 𝕜 F) : sorry := by
  -- the b i form a basis of F,
  -- and the trivialisation e is a linear equivalence (thus preserves bases)
  sorry

open scoped Classical in
/-- Coefficients of a section `s` of `V` w.r.t. the local frame `b.localFrame e i` -/
-- If x is outside of `e.baseSet`, this returns the junk value 0.
noncomputable def localFrame_repr
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas e]
    (b : Basis ι 𝕜 F) (s : Π x : M, V x) : ι → M → 𝕜 :=
  fun i x ↦ if hx : x ∈ e.baseSet then (b.localFrame_toBasis_at e hx).repr (s x) i else 0

variable {e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M)}
    [MemTrivializationAtlas e] {b : Basis ι 𝕜 F}

variable (e b) in
omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)] in
@[simp]
lemma localFrame_repr_apply_of_notMem_baseSet {x : M}
    (hx : x ∉ e.baseSet) (s : Π x : M, V x) (i : ι) : b.localFrame_repr e s i x = 0 := by
  simpa [localFrame_repr] using fun hx' ↦ (hx hx').elim

-- uniqueness of the decomposition: will follow from the IsBasis property above

variable (b) in
lemma localFrame_repr_spec [Fintype ι] {x : M} (hxe : x ∈ e.baseSet) (s : Π x : M,  V x) :
    ∀ᶠ x' in 𝓝 x, s x' = ∑ i, (b.localFrame_repr e s i x') • b.localFrame e i x' := by
  have {x'} (hx : x' ∈ e.baseSet) :
      s x' = (∑ i, (b.localFrame_repr e s i x') • b.localFrame e i x') := by
    simp [Basis.localFrame_repr, hx]
    exact (sum_repr (localFrame_toBasis_at e b hx) (s x')).symm
  exact eventually_nhds_iff.mpr ⟨e.baseSet, fun y a ↦ this a, e.open_baseSet, hxe⟩

-- uniqueness implies this, but it also follows from our definition
lemma Basis.localFrame_repr_add [Fintype ι] {x : M} (hxe : x ∈ e.baseSet)
    (s s' : Π x : M,  V x) (i : ι) :
    b.localFrame_repr e (s + s') i x =
      (b.localFrame_repr e s i x) + (b.localFrame_repr e s' i x) := by
  by_cases hx : x ∈ e.baseSet; swap
  · exact False.elim (hx hxe)
  · simp [localFrame_repr, hx]

end Basis

variable {ι : Type*} [Fintype ι] {x : M}
  {e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M)}
  [MemTrivializationAtlas e]

-- corollary of linearity and uniqueness, or follows directly
-- TODO: better name!
lemma Basis.localFrame_repr_apply_zero_at
    (b : Basis ι 𝕜 F) {s : Π x : M, V x} (hs : s x = 0) (i : ι) :
    b.localFrame_repr e s i x = 0 := by
  by_cases hxe : x ∈ e.baseSet; swap
  · simp [localFrame_repr, hxe]
  have : (e { proj := x, snd := 0 }).2 = 0 := sorry -- same sorry as above
  simp [localFrame_repr, localFrame_toBasis_at, hxe, hs, this]

-- TODO: better name
lemma Basis.localFrame_repr_apply_zero (b : Basis ι 𝕜 F) (i : ι) :
    b.localFrame_repr e 0 i x = 0 :=
  b.localFrame_repr_apply_zero_at (s := 0) (by simp) i

omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)] [Fintype ι] in
/-- The representation of `s` in a local frame at `x` only depends on `s` at `x`. -/
lemma Basis.localFrame_repr_congr (b : Basis ι 𝕜 F)
    (s s' : Π x : M,  V x) (i : ι) (hss' : s x = s' x) :
    b.localFrame_repr e s i x = b.localFrame_repr e s' i x := by
  by_cases hxe : x ∈ e.baseSet
  · simp [localFrame_repr, hxe, localFrame_toBasis_at]
    congr
  · simp [localFrame_repr, hxe]

variable {n}

lemma Basis.contMDiffAt_localFrame_repr (hxe : x ∈ e.baseSet) (b : Basis ι 𝕜 F)
    {s : Π x : M,  V x} {k : WithTop ℕ∞} (hk : k ≤ n)
    (hs : ContMDiffAt I (I.prod 𝓘(𝕜, F)) k (fun x ↦ TotalSpace.mk' F x (s x)) x)
    (i : ι) : ContMDiffAt I 𝓘(𝕜) n (b.localFrame_repr e s i) x := by
  -- "check this locally, then it's very easy"
  -- more precisely: (1) we have the following lemma:
  -- suppose e is a compat. trivialisation and x ∈ e.baseSet, then on e.baseSet
  -- b.localFrame_repr e s i equals the coefficient of "s x in trivialisation e" ∈ E for b i,
  -- the RHS is (b.repr i) (s in trivialisation e).2
  -- (2) s in trivialisation e is contmdiff
  -- (3) b.repr is a continuous linear map, so the composition is smooth
  sorry

lemma Basis.contMDiffOn_baseSet_localFrame_repr (b : Basis ι 𝕜 F)
    {s : Π x : M,  V x} {k : WithTop ℕ∞} (hk : k ≤ n) {t : Set M} (ht : IsOpen t) (ht' : t ⊆ e.baseSet)
    (hs : ContMDiffOn I (I.prod 𝓘(𝕜, F)) k (fun x ↦ TotalSpace.mk' F x (s x)) t) (i : ι) :
    ContMDiffOn I 𝓘(𝕜) n (b.localFrame_repr e s i) t :=
  fun _ hx ↦ (b.contMDiffAt_localFrame_repr I (ht' hx) hk
    (hs.contMDiffAt (ht.mem_nhds hx)) i).contMDiffWithinAt

end localFrame

section

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 0 M]

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  -- `F` model fiber
  (n : WithTop ℕ∞)
  (V : M → Type*) [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  -- `V` vector bundle

def bar (a : 𝕜) : TangentSpace 𝓘(𝕜) a ≃L[𝕜] 𝕜 where
  toFun v := v
  invFun v := v
  map_add' := by simp
  map_smul' := by simp

variable (x : M)

structure CovariantDerivative where
  toFun : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)
  addX : ∀ (X X' : Π x : M, TangentSpace I x) (σ : Π x : M, V x),
    toFun (X + X') σ = toFun X σ + toFun X' σ
  smulX : ∀ (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (f : M → 𝕜),
    toFun (f • X) σ = f • toFun X σ
  addσ : ∀ (X : Π x : M, TangentSpace I x) (σ σ' : Π x : M, V x) (x : M),
    MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (σ x)) x
    → MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (σ' x)) x
    → toFun X (σ + σ') x = toFun X σ x + toFun X σ' x
  leibniz : ∀ (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (f : M → 𝕜) (x : M),
    MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (σ x)) x
    → MDifferentiableAt I 𝓘(𝕜) f x
    → toFun X (f • σ) x = (f • toFun X σ) x + (bar _ <| mfderiv I 𝓘(𝕜) f x (X x)) • σ x
  do_not_read : ∀ (X : Π x : M, TangentSpace I x) {σ : Π x : M, V x} {x : M},
    ¬ MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (σ x)) x → toFun X σ x = 0

namespace CovariantDerivative

attribute [coe] toFun

/-- Coercion of a `CovariantDerivative` to function -/
instance : CoeFun (CovariantDerivative I F V)
    fun _ ↦ (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x) :=
  ⟨fun e ↦ e.toFun⟩

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
  have : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (0 : V x)) x := by
    exact (contMDiff_zeroSection 𝕜 V).mdifferentiableAt le_rfl
  have := cov.addσ X (0 : (x : M) → V x) (0 : (x : M) → V x) x this this
  simpa using this

lemma _root_.FiberBundle.trivializationAt.baseSet_mem_nhds {B : Type*} (F : Type*)
    [TopologicalSpace B] [TopologicalSpace F]
    (E : B → Type*) [TopologicalSpace (TotalSpace F E)] [(b : B) → TopologicalSpace (E b)]
    [FiberBundle F E] (b : B) : (trivializationAt F E b |>.baseSet) ∈ 𝓝 b :=
  (trivializationAt F E b).open_baseSet.eventually_mem (FiberBundle.mem_baseSet_trivializationAt' b)


omit [IsManifold I 0 M] [∀ (x : M), IsTopologicalAddGroup (V x)]
     [∀ (x : M), ContinuousSMul 𝕜 (V x)] in
lemma smul_const_σ (cov : CovariantDerivative I F V)
    (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (a : 𝕜) :
    cov X (a • σ) = a • cov X σ := by
  ext x
  by_cases hσ : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (σ x)) x
  · simpa using cov.leibniz X σ (fun _ ↦ a) x hσ mdifferentiable_const.mdifferentiableAt
  have hσ₂ : cov X (a • σ) x = 0 := by
    by_cases ha: a = 0
    · simp [ha]
    refine cov.do_not_read X ?_
    contrapose! hσ
    have : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (a⁻¹ • a • σ x)) x := by
      rw [← mdifferentiableWithinAt_univ, mdifferentiableWithinAt_totalSpace] at *
      refine ⟨mdifferentiableAt_id, ?_⟩
      have : ∀ᶠ x' in 𝓝 x, ((trivializationAt F V x) ⟨x', a⁻¹ • a • σ x'⟩).2 =
                           a⁻¹ • ((trivializationAt F V x) ⟨x', a • σ x'⟩).2 := by
        filter_upwards [FiberBundle.trivializationAt.baseSet_mem_nhds F V x] with x' hx'
        exact (trivializationAt F V x).linear 𝕜 hx' |>.map_smul a⁻¹ (a • σ x')
      exact MDifferentiableAt.const_smul hσ.2 a⁻¹ |>.congr_of_eventuallyEq this
    apply this.congr_of_eventuallyEq
    filter_upwards with x
    simp [ha]
  simp [cov.do_not_read X hσ, hσ₂]

omit [IsManifold I 0 M] [∀ (x : M), IsTopologicalAddGroup (V x)]
  [∀ (x : M), ContinuousSMul 𝕜 (V x)] [VectorBundle 𝕜 F V] in
variable {I F V} in
/-- If `σ` and `σ'` are equal sections of `E`, they have equal covariant derivatives. -/
lemma congr_σ (cov : CovariantDerivative I F V)
    (X : Π x : M, TangentSpace I x) {σ σ' : Π x : M, V x} (hσ : ∀ x, σ x = σ' x) :
    cov X σ x = cov X σ' x := by
  simp [funext hσ]

omit [IsManifold I 0 M] [∀ (x : M), IsTopologicalAddGroup (V x)] [(x : M) → Module 𝕜 (V x)]
     [(x : M) → AddCommGroup (V x)]
     [∀ (x : M), ContinuousSMul 𝕜 (V x)] [VectorBundle 𝕜 F V] in
variable {I F V x} in
/-- If two sections `σ` and `σ'` are equal on a neighbourhood `s` of `x`,
if one is differentiable at `x` then so is the other.
Issue: EventuallyEq does not work for dependent functions. -/
lemma _root_.mdifferentiableAt_dependent_congr {σ σ' : Π x : M, V x} {s : Set M} (hs : s ∈ nhds x)
    (hσ₁ : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (σ x)) x)
    (hσ₂ : ∀ x ∈ s, σ x = σ' x) :
    MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (σ' x)) x := by
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
lemma _root_.mfderiv_dependent_congr_iff {σ σ' : Π x : M, V x} {s : Set M} (hs : s ∈ nhds x)
    (hσ : ∀ x ∈ s, σ x = σ' x) :
    MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (σ x)) x  ↔
    MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (σ' x)) x :=
  ⟨fun h ↦ _root_.mdifferentiableAt_dependent_congr hs h hσ,
   fun h ↦ _root_.mdifferentiableAt_dependent_congr hs h (fun x hx ↦ (hσ x hx).symm)⟩

omit [IsManifold I 0 M] [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)]
  [VectorBundle 𝕜 F V] in
lemma sum_X (cov : CovariantDerivative I F V)
    {ι : Type*} {s : Finset ι} {X : ι → Π x : M, TangentSpace I x} {σ : Π x : M, V x} :
    cov (∑ i ∈ s, X i) σ = ∑ i ∈ s, cov (X i) σ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha h => simp [Finset.sum_insert ha, Finset.sum_insert ha, ← h, cov.addX]

/-- A convex combination of covariant derivatives is a covariant derivative. -/
@[simps]
def convexCombination (cov cov' : CovariantDerivative I F V) (t : 𝕜) :
    CovariantDerivative I F V where
  toFun X s := (t • (cov X s)) + (1 - t) • (cov' X s)
  addX X X' σ := by simp only [cov.addX, cov'.addX]; module
  smulX X σ f := by simp only [cov.smulX, cov'.smulX]; module
  addσ X σ σ' x hσ hσ' := by
    simp [cov.addσ X σ σ' x hσ hσ', cov'.addσ X σ σ' x hσ hσ']
    module
  leibniz X σ f x hσ hf := by
    simp [cov.leibniz X σ f x hσ hf, cov'.leibniz X σ f x hσ hf]
    module
  do_not_read X {σ} {x} hσ := by simp [cov.do_not_read X hσ, cov'.do_not_read X hσ]

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

omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul ℝ (V x)]
  [VectorBundle ℝ F V] in
/-- If `X` and `X'` agree in a neighbourhood of `p`, then `∇_X σ` and `∇_X' σ` agree at `p`. -/
lemma congr_X_of_eventuallyEq (cov : CovariantDerivative I F V) [T2Space M]
    {X X' : Π x : M, TangentSpace I x} {σ : Π x : M, V x} {x : M} {s : Set M} (hs : s ∈ nhds x)
    (hσσ' : ∀ x ∈ s, X x = X' x) :
    cov X σ x = cov X' σ x := by
  by_cases hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, F)) (fun x ↦ TotalSpace.mk' F x (σ x)) x; swap
  · simp [cov.do_not_read X hσ, cov.do_not_read X' hσ]
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
  let a := b.localFrame_repr e X
  have : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have aux : ∀ᶠ (x' : M) in 𝓝 x, X x' = ∑ i, a i x' • Xi i x' := b.localFrame_repr_spec this X
  -- have realAux : ∃ s : Set M, (s ∈ nhds x ∧ ∀ x' ∈ s, X x' = ∑ i, a i x' • Xi i x') := by
  --   refine ⟨_, aux, by simp⟩
  have (i : Fin n) : a i x = 0 := b.localFrame_repr_apply_zero_at hX i
  calc cov X σ x
    _ = cov (∑ i, a i • Xi i) σ x := cov.congr_X_of_eventuallyEq aux (by simp)
    _ = ∑ i, cov (a i • Xi i) σ x := by rw [cov.sum_X]; simp
    _ = ∑ i, a i x • cov (Xi i) σ x := by
      congr; ext i; simp [cov.smulX (Xi i) σ (a i)]
    _ = 0 := by simp [this]

-- XXX: better name?
-- golfing welcome!
omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul ℝ (V x)]
  [VectorBundle ℝ F V] in
/-- `cov X σ x` only depends on `X` via `X x` -/
lemma congr_X_at (cov : CovariantDerivative I F V) [T2Space M] [IsManifold I ∞ M]
    (X X' : Π x : M, TangentSpace I x) {σ : Π x : M, V x} {x : M} (hXX' : X x = X' x) :
    cov X σ x = cov X' σ x := by
  have : cov X' σ x = cov X σ x + cov (X' - X) σ x := by
    have : X' = X + (X' - X) := by simp
    nth_rw 1 [this]
    rw [cov.addX X (X' - X) σ]
    simp
  have h : (X' - X) x = 0 := by simp [hXX']
  simp [this, cov.congr_X_at_aux (X' - X) h]

omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul ℝ (V x)]
  [VectorBundle ℝ F V] in
lemma congr_σ_smoothBumpFunction (cov : CovariantDerivative I F V) [T2Space M] [IsManifold I ∞ M]
    (X : Π x : M, TangentSpace I x) {σ : Π x : M, V x}
    (hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, F)) (fun x ↦ TotalSpace.mk' F x (σ x)) x)
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
    (hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, F)) (fun x ↦ TotalSpace.mk' F x (σ x)) x)
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
      simp [cov.congr_σ_smoothBumpFunction, _root_.mdifferentiableAt_dependent_congr hs hσ hσσ']

-- TODO: prove that `cov X σ x` depends on σ only via σ(X) and the 1-jet of σ at x

/-- The difference of two covariant derivatives, as a function `Γ(TM) × Γ(E) → Γ(E)`.
Future lemmas will upgrade this to a map `TM ⊕ E → E`. -/
def differenceAux (cov cov' : CovariantDerivative I F V) :
    (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x) :=
  fun X σ ↦ cov X σ - cov' X σ

omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul ℝ (V x)]
  [VectorBundle ℝ F V] [FiniteDimensional ℝ E] in
lemma differenceAux_smul_eq (cov cov' : CovariantDerivative I F V)
    (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (f : M → ℝ)
    (hσ : MDifferentiable I (I.prod 𝓘(ℝ, F)) (fun x ↦ TotalSpace.mk' F x (σ x)))
    (hf : MDifferentiable I 𝓘(ℝ) f) :
    differenceAux cov cov' X ((f : M → ℝ) • σ) = (f : M → ℝ) • (differenceAux cov cov' X σ) :=
  calc _
    _ = cov X ((f : M → ℝ) • σ) - cov' X ((f : M → ℝ) • σ) := rfl
    _ = (f • cov X σ +  (fun x ↦ bar _ <| mfderiv I 𝓘(ℝ) f x (X x)) • σ)
        - (f • cov' X σ +  (fun x ↦ bar _ <| mfderiv I 𝓘(ℝ) f x (X x)) • σ) := by
      ext x
      simp [cov.leibniz X _ _ _ (hσ x) (hf x), cov'.leibniz X _ _ _ (hσ x) (hf x)]
    _ = f • cov X σ - f • cov' X σ := by simp
    _ = f • (cov X σ - cov' X σ) := by simp [smul_sub]
    _ = _ := rfl

omit [FiniteDimensional ℝ E] [∀ (x : M), IsTopologicalAddGroup (V x)]
    [∀ (x : M), ContinuousSMul ℝ (V x)] [VectorBundle ℝ F V] in
lemma differenceAux_smul_eq' (cov cov' : CovariantDerivative I F V)
    (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (f : M → ℝ) :
    differenceAux cov cov' (f • X) σ = (f : M → ℝ) • differenceAux cov cov' X σ := by
  simp [differenceAux, cov.smulX, cov'.smulX, smul_sub]

/-- The value of `differenceAux cov cov' X σ` at `x₀` depends only on `X x₀` and `σ x₀`. -/
lemma foo (cov cov' : CovariantDerivative I F V) [T2Space M] [IsManifold I ∞ M]
    (X X' : Π x : M, TangentSpace I x) (σ σ' : Π x : M, V x) (x₀ : M)
    (hσ : MDifferentiable I (I.prod 𝓘(ℝ, F)) (fun x ↦ TotalSpace.mk' F x (σ x)))
    (hσ' : MDifferentiable I (I.prod 𝓘(ℝ, F)) (fun x ↦ TotalSpace.mk' F x (σ' x))) :
    differenceAux cov cov' X σ x₀ = differenceAux cov cov' X' σ' x₀ := by
  -- use the previous two lemmas: they prove that differenceAux is tensorial
  sorry

-- TODO: generalise this to any section in a vector bundle

/-- Extend a tangent vector `X₀` at `x₀ ∈ M` to *some* vector field `X` on `M` with `X x = X₀`. -/
def extend {x : M} (X₀ : TangentSpace I x) : (x : M) → TangentSpace I x :=
  -- idea: choose a local frame, and choose X to have constant coefficients in that frame
  -- cap with a smooth bump function, to make it smooth everywhere
  sorry

@[simp]
lemma extend_apply {x : M} (X₀ : TangentSpace I x) : (extend X₀) x = X₀ := sorry

/-lemma-/ def contMDiff_extend  {x : M} (X₀ : TangentSpace I x) :
  sorry /- ContMDiff I I.tangent 2 (extend X₀) doesn't type-check -/ := sorry

-- The difference of two covariant derivatives, as a tensorial map
def difference (cov cov' : CovariantDerivative I F V) :
    Π x : M, TangentSpace I x → V x → V x :=
  fun x X₀ σ₀ ↦
  let σ : (x : M) → V x := sorry -- `extend σ₀` once generalized
  differenceAux cov cov' (extend X₀) σ x

end real

end CovariantDerivative

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']

@[simp]
theorem Bundle.Trivial.mdifferentiableAt_iff (σ : (x : E) → Trivial E E' x) (e : E) :
    MDifferentiableAt 𝓘(𝕜, E) (𝓘(𝕜, E).prod 𝓘(𝕜, E')) (fun x ↦ TotalSpace.mk' E' x (σ x)) e ↔
    DifferentiableAt 𝕜 σ e := by
  sorry

attribute [simp] mdifferentiableAt_iff_differentiableAt

@[simps]
noncomputable def CovariantDerivative.trivial : CovariantDerivative 𝓘(𝕜, E) E'
  (Bundle.Trivial E E') where
  toFun X s := fun x ↦ fderiv 𝕜 s x (X x)
  addX X X' σ := by ext; simp
  smulX X σ c' := by ext; simp
  addσ X σ σ' e hσ hσ' := by
    rw [Bundle.Trivial.mdifferentiableAt_iff] at hσ hσ'
    rw [fderiv_add hσ hσ']
    rfl
  leibniz X σ f x hσ hf := by
    have : fderiv 𝕜 (f • σ) x = f x • fderiv 𝕜 σ x + (fderiv 𝕜 f x).smulRight (σ x) :=
      fderiv_smul (by simp_all) (by simp_all)
    simp [this, bar]
    rfl
  do_not_read X σ x hσ := by
    rw [Bundle.Trivial.mdifferentiableAt_iff] at hσ
    simp [fderiv_zero_of_not_differentiableAt hσ]

end
