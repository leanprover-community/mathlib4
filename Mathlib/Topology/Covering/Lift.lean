/-
Copyright (c) 2025 Vincent Beffara. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Beffara
-/
import Mathlib.Tactic.Peel
import Mathlib.Topology.ContinuousMap.Interval
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.UnitInterval

/-!
# Lifting through covering maps

This path proves the existence of path and homotopy lifts through a covering map.

## Main definitions

Let `f : E → X` be a covering map. The main theorems in the file are:
* `exists_unique_lift`: Given a path `γ : C(I, X)` starting at `f e`, there is a unique lift `Γ :
  C(I, E)` starting at `e` such that `f ∘ Γ = γ`.
* `exists_unique_hlift`: Given a continuous map `Γ₀ : C(Y, X)` and a homotopy `γ : C(I × Y, X)`
  satisfying `γ (0, ⬝) = f ∘ Γ₀`, there is a unique homotopy `Γ : C(I × Y, E)` satisfying `Γ (0, ⬝)
  = Γ₀` and `f ∘ Γ = γ`.
* `exists_unique_hlift'`: Specialized version of `exists_unique_hlift` lifting from `C(I, C(Y, X))`
  to `C(I, C(Y, E))` when `Y` is locally compact.
In addition:
* `lift hf γ he`: Given a path `γ : C(I, X)` starting at `f e`, this is the lift of `γ` starting at
  `e`.
-/

open Set Topology unitInterval Filter ContinuousMap

local instance : Fact ((0 : ℝ) ≤ 1) := ⟨zero_le_one⟩

variable {E X Y Z : Type*}
  [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {f : E → X} (hf : IsCoveringMap f) {e e₀ : E} {x x₀ : X} {γ : C(I, X)} {m n : ℕ}

namespace IsCoveringMap

/-- Subdivision of an interval with an associated sequence of trivializations of the covering `p`.
  One can lift a path `γ` by gluing local lifts along such a subdivision if it is adapted to it,
  see `fits`. -/
structure LiftSetup (p : E → X) where
  /-- The bounds of the intervals in the subdivision. -/
  t : ℕ → ℝ
  /-- The number of (non-trivial) pieces. -/
  n : ℕ
  /-- The sequence of basepoints for the trivializations. -/
  c : ℕ → X
  /-- The trivializations. -/
  T : ∀ i, Trivialization (p ⁻¹' {c i}) p
  ht : Monotone t
  ht0 : t 0 = 0
  ht1 : ∀ m ≥ n, t m = 1

variable {S : LiftSetup f}

local instance : Fact (S.t 0 ≤ S.t n) := ⟨S.ht n.zero_le⟩

local instance : Fact (S.t n ≤ S.t (n + 1)) := ⟨S.ht n.le_succ⟩

namespace LiftSetup

/-- The `n`th interval in the partition contained in `S`. -/
abbrev icc (S : LiftSetup f) (n : ℕ) : Set ℝ := Icc (S.t n) (S.t (n + 1))

theorem htn : S.t S.n = 1 := S.ht1 S.n le_rfl

theorem t_mem_I : S.t n ∈ I := by
  refine ⟨?_, ?_⟩ <;> simp only [← S.ht0, ← S.ht1 (n + S.n) (by omega)] <;> apply S.ht <;> omega

@[simp]
theorem icc_subset_I : Icc (S.t m) (S.t n) ⊆ I := by
  rintro t ⟨ht0, ht1⟩ ; exact ⟨le_trans t_mem_I.1 ht0, le_trans ht1 t_mem_I.2⟩

attribute [simp] ht0 ht1

/-- The embedding of intervals adapted to the partition in `S` into the unit interval. -/
def embed (S : LiftSetup f) (m n : ℕ) : C(Icc (S.t m) (S.t n), I) :=
  ⟨fun t => ⟨t, icc_subset_I t.2⟩, by fun_prop⟩

/-- This holds if the path `γ` maps each interval in the partition in `S` to the base set of the
corresponding trivialization. -/
def fits (S : LiftSetup f) (γ : C(I, X)) : Prop :=
  ∀ n ∈ Finset.range S.n, MapsTo (IccExtendCM γ) (S.icc n) (S.T n).baseSet

theorem fits.eventually {y₀ : Y} {γ : C(Y, C(I, X))} (hS : S.fits (γ y₀)) :
    ∀ᶠ y in 𝓝 y₀, S.fits (γ y) := by
  simp only [LiftSetup.fits, eventually_all_finset] at hS ⊢
  peel hS with n hn hS
  have key := ContinuousMap.eventually_mapsTo CompactIccSpace.isCompact_Icc (S.T n).open_baseSet hS
  have h4 := IccExtendCM.2.tendsto (γ y₀) |>.eventually key
  exact γ.2.tendsto y₀ |>.eventually h4

theorem exist (hf : IsCoveringMap f) (γ : C(I, X)) : ∃ S : LiftSetup f, S.fits γ := by
  choose T hT using fun t => (hf (γ t)).2
  let V t : Set I := γ ⁻¹' (T t).baseSet
  have h1 t : IsOpen (V t) := (T t).open_baseSet.preimage γ.continuous
  have h2 : univ ⊆ ⋃ t, V t := fun t _ => mem_iUnion.2 ⟨t, hT t⟩
  choose t ht0 ht ht1 c hc using exists_monotone_Icc_subset_open_cover_unitInterval h1 h2
  obtain ⟨n, ht1⟩ := ht1
  use ⟨(t ·), n, γ ∘ c, fun n => T (c n), ht, by simpa using ht0, by simpa using ht1⟩
  rintro k - s hs
  simpa [icc_subset_I hs] using hc k hs

/-- This gathers a path which is adapted to a `LiftSetup` and a point in the fiber above its
starting point. -/
private abbrev Liftable (S : LiftSetup f) := {γe : C(I, X) × E // S.fits γe.1 ∧ f γe.2 = γe.1 0}

private noncomputable def partial_lift (S : LiftSetup f) : ∀ n ≤ S.n,
    {F : C(S.Liftable, C(Icc (S.t 0) (S.t n), E)) // ∀ γe,
      F γe ⊥ = γe.1.2 ∧ ∀ t, f (F γe t) = γe.1.1 (S.embed _ _ t)}
  | 0 => fun _ => by
    use ContinuousMap.const'.comp ⟨fun ye => ye.1.2, by fun_prop⟩
    rintro ⟨⟨γ, e⟩, -, h2⟩
    refine ⟨rfl, ?_⟩
    simp only [Subtype.forall, LiftSetup.ht0, Icc_self, mem_singleton_iff]
    rintro t rfl
    exact h2
  | n + 1 => fun hn => by
    obtain ⟨Φ, hΦ⟩ := S.partial_lift n (by omega)
    replace hn : n ∈ Finset.range S.n := by simp ; omega
    refine ⟨?_, ?_⟩
    · refine (concatCM (b := S.t n)).comp ⟨?_, ?_⟩
      · intro γe
        have h5 : f (Φ γe ⊤) = γe.1.1 ⟨S.t n, _⟩ := (hΦ γe).2 ⊤
        have h6 : S.t n ∈ S.icc n := by simpa using S.ht n.le_succ
        let left : C(↑(Icc (S.t 0) (S.t n)), E) := Φ γe
        let next : C(S.icc n, E) := by
          let γn : C(S.icc n, (S.T n).baseSet) := by
            refine ⟨fun t => ⟨γe.1.1 (S.embed _ _ t), ?_⟩, ?_⟩
            · simpa [icc_subset_I t.2] using γe.2.1 n hn t.2
            · fun_prop
          refine .comp ⟨_, continuous_subtype_val⟩ <| (S.T n).clift (⟨left ⊤, ?_⟩, γn)
          simpa [Trivialization.mem_source, left, h5, icc_subset_I h6] using γe.2.1 n hn h6
        use ⟨left, next⟩
        simp only [comp_apply, coe_mk, next]
        rw [Trivialization.clift_self]
        simp only [hΦ, left, next]
        rfl
      · refine Continuous.subtype_mk (continuous_prod_mk.2 ⟨by fun_prop, ?_⟩) _
        apply ContinuousMap.continuous_postcomp _ |>.comp
        apply (S.T n).clift.continuous.comp
        refine continuous_prod_mk.2 ⟨?_, ?_⟩
        · exact (continuous_eval_const _).comp Φ.continuous |>.subtype_mk _
        · let Ψ : C(S.Liftable × S.icc n, C(I, X) × I) :=
            ⟨fun fx => (fx.1.1.1, ⟨fx.2.1, icc_subset_I fx.2.2⟩), by fun_prop⟩
          let Φ : C(S.Liftable × S.icc n, (S.T n).baseSet) := by
            refine ⟨fun fx => ⟨fx.1.1.1 ⟨fx.2.1, icc_subset_I fx.2.2⟩, ?_⟩, ?_⟩
            · obtain ⟨_, _⟩ := icc_subset_I fx.2.2
              have := fx.1.2.1 n hn fx.2.2
              rw [IccExtendCM_of_mem] at this ; assumption
            · apply Continuous.subtype_mk
              exact ContinuousEval.continuous_eval.comp Ψ.continuous
          exact Φ.curry.continuous
    · rintro ⟨⟨γ, e⟩, hγ, he⟩
      dsimp
      constructor
      · rw [concatCM_left (S.ht n.zero_le)]
        exact hΦ ⟨⟨γ, e⟩, hγ, he⟩ |>.1
      · rintro ⟨t, ht⟩
        by_cases htn : t ≤ S.t n
        · rw [concatCM_left htn] ; exact hΦ ⟨⟨γ, e⟩, hγ, he⟩ |>.2 ⟨t, _⟩
        · rw [concatCM_right <| le_of_not_le htn]
          simp only [comp_apply, coe_mk, Trivialization.proj_clift (proj := f)]
          rfl

/-- Lifting paths through a `LiftSetup`, as a bundled continuous map from paths adapted to the
setup. -/
noncomputable def lift (S : LiftSetup f) :
    {F : C(S.Liftable, C(I, E)) // ∀ γe, F γe 0 = γe.1.2 ∧ ∀ t, f (F γe t) = γe.1.1 t} := by
  obtain ⟨F, hF⟩ := S.partial_lift S.n le_rfl
  let Φ : C(I, Icc (S.t 0) (S.t S.n)) := ⟨fun t => ⟨t, by simp⟩, by fun_prop⟩
  refine ⟨⟨fun γe => (F γe).comp Φ, by fun_prop⟩, fun γe => ⟨?_, fun t => ?_⟩⟩
  · simpa [Bot.bot] using hF γe |>.1
  · simpa [embed] using hF γe |>.2 (Φ t)

end LiftSetup

include hf

theorem exists_unique_lift (he : f e = γ 0) : ∃! Γ : C(I, E), Γ 0 = e ∧ f ∘ Γ = γ := by
  obtain ⟨S, hS⟩ := LiftSetup.exist hf γ
  obtain ⟨F, hF⟩ := S.lift
  have h1 : F ⟨⟨γ, e⟩, hS, he⟩ 0 = e := hF ⟨⟨γ, e⟩, hS, he⟩ |>.1
  have h2 : f ∘ F ⟨⟨γ, e⟩, hS, he⟩ = γ := by ext t ; exact hF ⟨⟨γ, e⟩, hS, he⟩ |>.2 t
  refine ⟨F ⟨⟨γ, e⟩, hS, he⟩, ⟨h1, h2⟩, ?_⟩
  rintro Γ ⟨rfl, hΓ₂⟩
  apply coe_injective
  apply hf.eq_of_comp_eq (a := 0) Γ.continuous (ContinuousMap.continuous _) <;> simp [*]

/-- The path obtained by lifting through a covering map. -/
noncomputable def lift (γ : C(I, X)) (he : f e = γ 0) : C(I, E) :=
  (hf.exists_unique_lift he).choose

@[simp]
theorem lift_spec (γ : C(I, X)) (he : f e = γ 0) : hf.lift γ he 0 = e ∧ f ∘ hf.lift γ he = γ :=
  (hf.exists_unique_lift he).choose_spec.1

variable {Y : Type*} [TopologicalSpace Y] {γ : C(I × Y, X)} {Γ₀ : C(Y, E)}

private def slice (γ : C(I × Y, X)) : C(Y, C(I, X)) := γ.comp prodSwap |>.curry

private noncomputable def joint_lift (hΓ₀ : ∀ y, f (Γ₀ y) = γ (0, y)) : C(Y, C(I, E)) := by
  use fun y => hf.lift (slice γ y) (hΓ₀ y)
  rw [continuous_iff_continuousAt]
  intro y₀
  obtain ⟨S, hS⟩ := LiftSetup.exist hf (slice γ y₀)
  apply ContinuousOn.continuousAt ?_ hS.eventually
  rw [continuousOn_iff_continuous_restrict]
  obtain ⟨G₁, hG₁⟩ := S.lift
  let G₂ : C({y // S.fits (slice γ y)}, S.Liftable) :=
    ⟨fun y => ⟨⟨slice γ y, Γ₀ y⟩, y.2, hΓ₀ y⟩, by fun_prop⟩
  convert G₁.comp G₂ |>.continuous
  ext1 y
  have h3 := hG₁ ⟨⟨slice γ y, Γ₀ y⟩, y.2, hΓ₀ y⟩
  apply coe_injective
  apply hf.eq_of_comp_eq (a := 0) (ContinuousMap.continuous _) (ContinuousMap.continuous _)
  · simp [G₂, h3]
  · simp only [Set.restrict_apply, mem_setOf_eq, hf.lift_spec, comp_apply, coe_mk, G₂]
    ext t
    simp [h3]

theorem exists_unique_hlift (hΓ₀ : ∀ y, f (Γ₀ y) = γ (0, y)) :
    ∃! Γ : C(I × Y, E), ∀ y, Γ (0, y) = Γ₀ y ∧ f ∘ (Γ ⟨·, y⟩) = (γ ⟨·, y⟩) := by
  refine ⟨hf.joint_lift hΓ₀ |>.uncurry |>.comp prodSwap, ?_, ?_⟩
  · exact fun y => hf.lift_spec (slice γ y) (hΓ₀ y)
  · rintro Γ hΓ ; ext1 ⟨t, y⟩
    have h1 : f (Γ₀ y) = slice γ y 0 := hΓ₀ y
    suffices (Γ.comp prodSwap |>.curry y) = (hf.lift _ h1) from ContinuousMap.congr_fun this t
    apply coe_injective
    apply hf.eq_of_comp_eq (a := 0) (ContinuousMap.continuous _) (ContinuousMap.continuous _)
    · simp [lift_spec _ hf h1, hΓ]
    · simp only [lift_spec]
      ext t
      have : f (Γ (t, y)) = γ (t, y) := congr_fun (hΓ y |>.2) t
      simp [this, slice]

/-- Specialized version of `exists_unique_hlift` stated in terms of a continuous map from the unit
interval to `C(Y, X)` in the case when `Y` is locally compact. -/
theorem exists_unique_hlift' [LocallyCompactSpace Y] {γ : C(I, C(Y, X))}
    (hΓ₀ : ∀ y, f (Γ₀ y) = γ 0 y) :
    ∃! Γ : C(I, C(Y, E)), ∀ y, Γ 0 y = Γ₀ y ∧ f ∘ (Γ · y) = (γ · y) := by
  obtain ⟨Γ, h1, h2⟩ := exists_unique_hlift hf hΓ₀ (γ := γ.uncurry)
  refine ⟨Γ.curry, h1, fun Γ' h3 => ?_⟩
  simp [← h2 Γ'.uncurry h3] ; rfl

end IsCoveringMap
