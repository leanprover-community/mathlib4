/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

/-!
# Torsion of a covariant derivative

- define torsion of a covariant derivative (and its local version)
- torsion-free ness (local and global version)
- prove: torsion-freeness on `s` can be checked using a local frame on `s`

TODO: add a more complete doc-string

-/

@[expose] public section -- TODO: think if we want to expose all definitions!

open Bundle Filter Module Topology Set

open scoped Bundle Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {x : M}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (n : WithTop ℕ∞) {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)] [FiberBundle F V]

-- TODO: where is a good namespace for this?
/-- The torsion of a covariant derivative on the tangent bundle `TM` -/
noncomputable def Bundle.torsion
    (f : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x)) :
    (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x) :=
  fun X Y ↦ f X Y - f Y X - VectorField.mlieBracket I X Y

variable
  {f g : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x)}
  {X X' Y : Π x : M, TangentSpace I x}

variable (f X) in
lemma torsion_self : torsion f X X = 0 := by
  simp [torsion]

variable (X Y) in
lemma torsion_antisymm : torsion f X Y = - torsion f Y X := by
  simp only [torsion]
  rw [VectorField.mlieBracket_swap]
  module

namespace IsCovariantDerivativeOn

variable [h : IsManifold I ∞ M]
variable {U : Set M} (hf : IsCovariantDerivativeOn E f U)

variable (Y) in
lemma torsion_add_left_apply [CompleteSpace E]
    (hf : IsCovariantDerivativeOn E f U) (hx : x ∈ U)
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x) :
    torsion f (X + X') Y x = torsion f X Y x + torsion f X' Y x := by
  sorry -- simp [torsion, hf.addX (x := x) (hx := sorry) hX hX']
  -- rw [hf.addσ Y hX hX', VectorField.mlieBracket_add_left hX hX']
  -- module

lemma torsion_add_right_apply [CompleteSpace E] (hf : IsCovariantDerivativeOn E f U) (hx : x ∈ U)
    (hX : MDiffAt (T% X) x)
    (hX' : MDiffAt (T% X') x) :
    torsion f Y (X + X') x = torsion f Y X x + torsion f Y X' x := by
  rw [torsion_antisymm, Pi.neg_apply,
    hf.torsion_add_left_apply _ hx hX hX', torsion_antisymm Y, torsion_antisymm Y]
  simp; abel

variable (Y) in
lemma torsion_smul_left_apply [CompleteSpace E]
    {F : ((x : M) → TangentSpace I x) → ((x : M) → TangentSpace I x) → (x : M) → TangentSpace I x}
    (hF : IsCovariantDerivativeOn E F U) (hx : x ∈ U)
    -- TODO: making hx an auto-param := by trivial doesn't fire at the application sites below
    {f : M → ℝ} (hf : MDiffAt f x) (hX : MDiffAt (T% X) x) :
    torsion F (f • X) Y x = f x • torsion F X Y x := by
  sorry /-simp only [torsion, Pi.sub_apply, hF.smulX (X := X) (σ := Y) (f := f)]
  rw [hF.leibniz Y hX hf hx, VectorField.mlieBracket_smul_left hf hX]
  simp [bar, smul_sub]
  abel -/

variable (X) in
lemma torsion_smul_right_apply [CompleteSpace E]
    {F : ((x : M) → TangentSpace I x) → ((x : M) → TangentSpace I x) → (x : M) → TangentSpace I x}
    (hF : IsCovariantDerivativeOn E F U) (hx : x ∈ U)
    {f : M → ℝ} (hf : MDiffAt f x) (hX : MDiffAt (T% Y) x) :
    torsion F X (f • Y) x = f x • torsion F X Y x := by
  rw [torsion_antisymm, Pi.neg_apply, hF.torsion_smul_left_apply X hx hf hX, torsion_antisymm X]
  simp

end IsCovariantDerivativeOn

/-- `f` is torsion-free on `U` if its torsion vanishes at each `x ∈ U` -/
noncomputable def IsTorsionFreeOn
    (f : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x))
    (U : Set M) : Prop :=
  ∀ x ∈ U, ∀ X Y : Π x : M, TangentSpace I x, torsion f X Y x = 0

namespace IsTorsionFreeOn

section changing_set

/-! Changing set
In this changing we change `s` in `IsTorsionFreeOn F f s`.
-/

lemma mono {s t : Set M} (hf : IsTorsionFreeOn f t) (hst : s ⊆ t) : IsTorsionFreeOn f s :=
  fun _ hx _ _ ↦ hf _ (hst hx) ..

lemma iUnion {ι : Type*} {s : ι → Set M} (hf : ∀ i, IsTorsionFreeOn f (s i)) :
    IsTorsionFreeOn f (⋃ i, s i) := by
  rintro x ⟨si, ⟨i, hi⟩, hxsi⟩ X Y
  exact hf i x (by simp [hi, hxsi]) X Y

end changing_set

/- Congruence properties -/
section

-- unused?
lemma congr {s : Set M} (h : IsTorsionFreeOn f s)
    (hfg : ∀ {X Y : Π x : M, TangentSpace I x}, ∀ {x}, x ∈ s → f X Y x = g X Y x) :
    IsTorsionFreeOn g s := by
  intro x hx X Y
  specialize h x hx X Y
  -- now, use torsion congruence lemma, i.e. tensoriality of sorts!
  -- TODO: generalise tensoriality to the local setting!
  sorry

end

end IsTorsionFreeOn

namespace CovariantDerivative

variable [h : IsManifold I ∞ M]
-- The torsion tensor of a covariant derivative on the tangent bundle `TM`.
variable {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}

variable {U : Set M} (hf : IsCovariantDerivativeOn E f U)

-- TODO: prove applied versions of these, for IsCovariantDerivativeOn --- using tensoriality, later!
variable (f) in
@[simp]
lemma torsion_zero (hX : MDiff T% X) : torsion cov 0 X = 0 := by
  simp [torsion, cov.zeroX hX, cov.zeroσ hX]


@[simp]
lemma torsion_zero' (hX : MDiff T% X) : torsion cov X 0 = 0 := by
  rw [torsion_antisymm, torsion_zero hX]; simp

variable (Y) in
lemma torsion_add_left [CompleteSpace E]
    (hX : MDiff (T% X)) (hX' : MDiff (T% X')) :
    torsion cov (X + X') Y = torsion cov X Y + torsion cov X' Y := by
  ext x
  exact cov.isCovariantDerivativeOn.torsion_add_left_apply _ (by trivial) (hX x) (hX' x)

lemma torsion_add_right [CompleteSpace E]
    (hX : MDiff (T% X)) (hX' : MDiff (T% X')) :
    torsion cov Y (X + X') = torsion cov Y X + torsion cov Y X' := by
  rw [torsion_antisymm, torsion_add_left _ hX hX', torsion_antisymm X, torsion_antisymm X']; module

variable (Y) in
lemma torsion_smul_left [CompleteSpace E] {f : M → ℝ} (hf : MDiff f) (hX : MDiff (T% X)) :
    torsion cov (f • X) Y = f • torsion cov X Y := by
  ext x
  exact cov.isCovariantDerivativeOn.torsion_smul_left_apply _ (by trivial) (hf x) (hX x)

variable (X) in
lemma torsion_smul_right [CompleteSpace E] {f : M → ℝ} (hf : MDiff f) (hY : MDiff (T% Y)) :
    torsion cov X (f • Y) = f • torsion cov X Y := by
  ext x
  exact cov.isCovariantDerivativeOn.torsion_smul_right_apply _ (by trivial) (hf x) (hY x)

/-- The torsion of a covariant derivative is tensorial:
the value of `torsion cov X Y` at `x₀` depends only on `X x₀` and `Y x₀`. -/
def torsion_tensorial [T2Space M] [IsManifold I ∞ M] [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]
    {X X' Y Y' : Π x : M, TangentSpace I x} {x₀ : M}
    (hX : MDiffAt (T% X) x₀) (hX' : MDiffAt (T% X') x₀)
    (hY : MDiffAt (T% Y) x₀) (hY' : MDiffAt (T% Y') x₀)
    (hXX' : X x₀ = X' x₀) (hYY' : Y x₀ = Y' x₀) :
    (torsion cov X Y) x₀ = (torsion cov X' Y') x₀ := by
  apply tensoriality_criterion₂ I E (TangentSpace I) E (TangentSpace I) hX hX' hY hY' hXX' hYY'
  · intro f σ τ hf hσ
    exact cov.isCovariantDerivativeOn.torsion_smul_left_apply _ (by trivial) hf hσ
  · intro σ σ' τ hσ hσ'
    exact cov.isCovariantDerivativeOn.torsion_add_left_apply _ (by trivial) hσ hσ'
  · intros f σ σ' hf hσ'
    exact cov.isCovariantDerivativeOn.torsion_smul_right_apply _ (by trivial) hf hσ'
  · intro σ τ τ' hτ hτ'
    exact cov.isCovariantDerivativeOn.torsion_add_right_apply (by trivial) hτ hτ'

-- TODO: define a torsion tensor of a covariant derivative,
-- and related torsion-freeness to this
-- (That will not work for torsion-freeness on a set, though.)

-- TODO: generalise tensoriality result above to `IsCovariantDerivativeOn`,
-- so it would apply here as well

variable (cov) in
/-- A covariant derivation is called **torsion-free** iff its torsion tensor vanishes. -/
def IsTorsionFree : Prop := torsion cov = 0

@[simp]
lemma isTorsionFreeOn_univ : IsTorsionFreeOn cov univ ↔ IsTorsionFree cov := by
  simp only [IsTorsionFree, IsTorsionFreeOn]
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  ext X Y x
  simp [h x]

/-- If a covariant derivative `cov` is torsion-free on each set in an open cover,
it is torsion-free. -/
def of_isTorsionFreeOn_of_open_cover {ι : Type*} {s : ι → Set M}
    (hf : ∀ i, IsTorsionFreeOn cov (s i)) (hs : ⋃ i, s i = Set.univ) :
    IsTorsionFree cov := by
  rw [← isTorsionFreeOn_univ, ← hs]
  exact IsTorsionFreeOn.iUnion hf

lemma isTorsionFree_def : IsTorsionFree cov ↔ torsion cov = 0 := by simp [IsTorsionFree]

-- This should be obvious; am I doing something wrong?
lemma isTorsionFree_iff : IsTorsionFree cov ↔
    ∀ X Y, cov X Y - cov Y X = VectorField.mlieBracket I X Y := by
  simp only [IsTorsionFree]
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

variable {n} in
lemma aux1 {ι : Type*} [Fintype ι]
    {f : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x)}
    {U : Set M} {s : ι → (x : M) → TangentSpace I x} (hs : IsLocalFrameOn I E n s U) (hx : x ∈ U)
    (X Y : (x : M) → TangentSpace I x) :
    torsion f X Y x = ∑ i, hs.coeff i x (X x) • torsion f (s i) Y x := by
  have hU : U ∈ 𝓝 x := sorry
  have aux := hs.eventually_eq_sum_coeff_smul X hU
  have hX : X x = ∑ i, hs.coeff i x (X x) • s i x := sorry
  calc torsion f X Y x
    _ = torsion f (fun x ↦ ∑ i, hs.coeff i x (X x) • s i x) Y x := by
      sorry -- tensoriality and [hX]
    _ = ∑ i, torsion f (fun x ↦ hs.coeff i x (X x) • s i x) Y x := sorry
    _ = ∑ i, hs.coeff i x (X x) • (torsion f (s i) Y x) := sorry

-- Weaker hypotheses possible, e.g. local frame on U ∈ 𝓝 x, while a cov. derivative on s ∋ x
variable {n} in
lemma aux2 {ι : Type*} [Fintype ι] [CompleteSpace E]
    {f : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x)}
    {U : Set M} {s : ι → (x : M) → TangentSpace I x}
    (hf : IsCovariantDerivativeOn E f U) (hs : IsLocalFrameOn I E n s U) (hx : x ∈ U)
    (X Y : (x : M) → TangentSpace I x) :
    torsion f X Y x = ∑ i, hs.coeff i x (Y x) • torsion f X (s i) x :=
  have hU : U ∈ 𝓝 x := sorry
  have aux := hs.eventually_eq_sum_coeff_smul Y hU
  have hY : Y x = ∑ i, hs.coeff i x (Y x) • s i x := hs.coeff_sum_eq Y hx
  calc torsion f X Y x
    _ = torsion f X (fun x ↦ ∑ i, hs.coeff i x (Y x) • s i x) x := by
      sorry -- tensoriality and [hY]
    _ = ∑ i, torsion f X (fun x ↦ hs.coeff i x (Y x) • s i x) x := sorry
    _ = ∑ i, hs.coeff i x (Y x) • (torsion f X (s i) x) := by
      congr with i
      have hsi : MDiffAt ((LinearMap.piApply (hs.coeff i)) Y) x := sorry
      have hsi' : MDiffAt (T% (s i)) x := sorry
      have := hf.torsion_smul_right_apply (X := X) (Y := s i)
        (f := (LinearMap.piApply (hs.coeff i)) Y) hx hsi hsi'
      dsimp at this
      rw [← this]
      congr

/-- We can test torsion-freeness on a set using a local frame. -/
lemma _root_.IsCovariantDerivativeOn.isTorsionFreeOn_iff_localFrame
    {ι : Type*} [Finite ι] [CompleteSpace E]
    {f : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x)}
    {U : Set M} {s : ι → (x : M) → TangentSpace I x}
    (hf: IsCovariantDerivativeOn E f U) (hs : IsLocalFrameOn I E n s U) :
    IsTorsionFreeOn f U ↔ ∀ i j, ∀ x ∈ U, torsion f (s i) (s j) x = 0 := by
  have := Fintype.ofFinite ι
  rw [IsTorsionFreeOn]
  refine ⟨fun h i j x hx ↦ h x hx (s i) (s j), fun h ↦ ?_⟩
  intro x hx X Y
  rw [aux1 hs hx]
  calc
    _ = ∑ i, hs.coeff i x (X x) • ∑ j, hs.coeff j x (Y x) • torsion f (s i) (s j) x := by
      congr!
      rw [aux2 hf hs hx]
    _ = ∑ i, hs.coeff i x (X x) • ∑ j, hs.coeff j x (Y x) • 0 := by
      congr! with i _ j _
      exact h i j x hx
    _ = 0 := by simp

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

end CovariantDerivative
