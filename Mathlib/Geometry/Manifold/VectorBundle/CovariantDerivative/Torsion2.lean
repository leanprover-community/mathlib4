/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame

/-!
# More properties about torsion of a covariant derivative

- might and should be refactored!
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

variable
  {cov cov' : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)}
  {X X' Y : Π x : M, TangentSpace I x}

namespace CovariantDerivative

variable [IsManifold I ∞ M]
-- The torsion tensor of a covariant derivative on the tangent bundle `TM`.
variable {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
  {U : Set M} (hf : IsCovariantDerivativeOn E cov U)

-- variable {n} in
-- lemma aux1 {ι : Type*} [Fintype ι]
--     {f : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)}
--     {U : Set M} {s : ι → (x : M) → TangentSpace I x} (hs : IsLocalFrameOn I E n s U) (hx : x ∈ U)
--     (X Y : (x : M) → TangentSpace I x) :
--     torsion f X Y x = ∑ i, (hs.coeff i) x (X x) • torsion f (s i) Y x :=
--   have hU : U ∈ 𝓝 x := sorry
--   have aux := hs.eventually_eq_sum_coeff_smul X hU
--   have hX : X x = ∑ i, (hs.coeff i) x (X x) • s i x := sorry
--   calc torsion f X Y x
--     _ = torsion f (fun x ↦ ∑ i, (hs.coeff i) x (X x) • s i x) Y x := by
--       sorry -- tensoriality and [hX]
--     _ = ∑ i, (torsion f (fun x ↦ (hs.coeff i) x (X x) • s i x) Y x) := sorry
--     _ = ∑ i, (hs.coeff i) x (X x) • (torsion f (s i) Y x) := sorry
--
-- -- Weaker hypotheses possible, e.g. local frame on U ∈ 𝓝 x, while a cov. derivative on s ∋ x
-- variable {n} in
-- lemma aux2 {ι : Type*} [Fintype ι] [CompleteSpace E]
--     {f : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)}
--     {U : Set M} {s : ι → (x : M) → TangentSpace I x}
--     (hf : IsCovariantDerivativeOn E f U) (hs : IsLocalFrameOn I E n s U) (hx : x ∈ U)
--     (X Y : (x : M) → TangentSpace I x) :
--     torsion f X Y x = ∑ i, (hs.coeff i) x (Y x) • torsion f X (s i) x :=
--   have hU : U ∈ 𝓝 x := sorry
--   have aux := hs.eventually_eq_sum_coeff_smul Y hU
--   have hY : Y x = ∑ i, (hs.coeff i) x (Y x) • s i x := hs.coeff_sum_eq Y hx
--   calc torsion f X Y x
--     _ = torsion f X (fun x ↦ ∑ i, (hs.coeff i) x (Y x) • s i x) x := by
--       sorry -- tensoriality and [hY]
--     _ = ∑ i, (torsion f X (fun x ↦ (hs.coeff i) x (Y x) • s i x) x) := sorry
--     _ = ∑ i, (hs.coeff i) x (Y x) • (torsion f X (s i) x) := by
--       congr with i
--       have hsi : MDiffAt (LinearMap.piApply (hs.coeff i) Y) x := sorry
--       have hsi' : MDiffAt (T% (s i)) x := sorry
--       have := hf.torsion_smul_right_apply X (f := LinearMap.piApply (hs.coeff i) Y) hsi hsi'
--       erw [← this]
--       congr
--
-- /-- We can test torsion-freeness on a set using a local frame. -/
-- lemma _root_.IsCovariantDerivativeOn.isTorsionFreeOn_iff_localFrame
--     {ι : Type*} [Fintype ι] [CompleteSpace E]
--     {f : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)}
--     {U : Set M} {s : ι → (x : M) → TangentSpace I x}
--     (hf: IsCovariantDerivativeOn E f U) (hs : IsLocalFrameOn I E n s U) :
--     IsTorsionFreeOn f U ↔ ∀ i j, ∀ x ∈ U, torsion f (s i) (s j) x = 0 := by
--   rw [IsTorsionFreeOn]
--   refine ⟨fun h i j x hx ↦ h x hx (s i) (s j), fun h ↦ ?_⟩
--   intro x hx X Y
--   rw [aux1 hs hx]
--   calc
--     _ = ∑ i, (hs.coeff i) x (X x) • ∑ j, (hs.coeff j) x (Y x) • torsion f (s i) (s j) x := by
--       congr!
--       rw [aux2 hf hs hx]
--     _ = ∑ i, (hs.coeff i) x (X x) • ∑ j, (hs.coeff j) x (Y x) • 0 := by
--       congr! with i _ j _
--       exact h i j x hx
--     _ = 0 := by simp

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
