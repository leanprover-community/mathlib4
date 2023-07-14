import Mathlib.Tactic
import Mathlib.Dynamics.OmegaLimit
import Mathlib.Dynamics.Ergodic.AddCircle

open MeasureTheory Filter Metric Function Set
open scoped omegaLimit
set_option autoImplicit false

set_option autoImplicit false

/- For every objective, first write down a statement that Lean understands, with a proof given
by `sorry`. Then try to prove it! -/

section Topological_Dynamics

/- TODO: at some point translate to topological spaces -/

/- We could do everything in a topological space, using filters and neighborhoods, but it will
be more comfortable with a metric space. -/
variable {α : Type _} [MetricSpace α]

/- Define the non-wandering set of `f`-/
def nonWanderingSet (f : α → α) : Set α :=
  {x | ∀ ε, 0 < ε → ∃ (y : α), ∃ (n : ℕ), y ∈ ball x ε ∧ f^[n] y ∈ ball x ε ∧ n ≠ 0}

variable [CompactSpace α] (f : α → α) (hf : Continuous f)

/- Show that periodic points belong to the non-wandering set -/
theorem periodicpts_is_mem (x : α) (n : ℕ) (nnz: n ≠ 0) (pp: IsPeriodicPt f n x) :
    x ∈ nonWanderingSet f := by
  intro ε hε
  use x, n
  -- unfold IsPeriodicPt at pp
  -- unfold IsFixedPt at pp
  refine' ⟨_, _, _⟩
  . exact mem_ball_self hε
  . rw [pp]
    exact mem_ball_self hε
  . exact nnz
  done

lemma periodic_arbitrary_large_time (N : ℕ) (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 < ε) (x : α)
    (hx : IsPeriodicPt f m x) :
    ∃ (y : α), ∃ (n : ℕ), y ∈ ball x ε ∧ f^[n] y ∈ ball x ε ∧ N ≤ n := by
  use x, m * N
  refine' ⟨_,_,_⟩
  · exact mem_ball_self hε
  · rw [IsPeriodicPt.mul_const hx N]
    exact mem_ball_self hε
  · exact Nat.le_mul_of_pos_left hm
  done

lemma inter_subset_empty_of_inter_empty (A : Set α) (B: Set α) (C : Set α) (D: Set α) :
(A ⊆ C) → (B ⊆ D) → (C ∩ D = ∅) → (A ∩ B = ∅) := by
  intro hAC hBD hCD
  have hincl : A ∩ B ⊆ C ∩ D := inter_subset_inter hAC hBD
  rw [hCD] at hincl
  exact Iff.mp subset_empty_iff hincl
  done

/- Un lemme d'exercice: boules separees  -/
lemma separated_balls (x : α) (hfx : x ≠ f x) :  ∃ ε, 0 < ε ∧ (ball x ε) ∩ (f '' (ball x ε)) = ∅ := by
   have hfC : ContinuousAt f x := Continuous.continuousAt hf
   rw [Metric.continuousAt_iff] at hfC
   have h00 : 0 < ((dist x (f x))/4) := by
     apply div_pos
     rw [dist_pos]
     exact hfx
     exact four_pos
   have hfCp := hfC ((dist x (f x))/4) h00
   rcases hfCp with ⟨a, b, c⟩
   use min a ((dist x (f x))/4)
   refine' ⟨_,_⟩
   · exact lt_min b h00
   · rw [Set.ext_iff]
     intro y
     constructor
     · intro ⟨hy1,hy2⟩
       unfold ball at hy1
       dsimp at hy1
       have hha : min a (dist x (f x) / 4) ≤ a := min_le_left a (dist x (f x) / 4)
       have hy3 : dist y x < a := hy1.trans_le hha
       unfold ball at hy2
       rw [mem_image] at hy2
       rcases hy2 with ⟨z , hz1, hz2⟩
       dsimp at hz1
       have hz3 : dist z x < a := hz1.trans_le hha
       have hy4 := c hz3
       rw [hz2] at hy4
       have hha2 : min a (dist x (f x) / 4) ≤ (dist x (f x) / 4) := min_le_right a (dist x (f x) / 4)
       have hy5 : dist y x < (dist x (f x) / 4) := hy1.trans_le hha2
       rw [dist_comm] at hy5
       exfalso
       have gg := dist_triangle x y (f x)
       linarith
     · exfalso
   done

-- Perhaps this should go inside Mathlib.Dynamics.PeriodicPts.lean
def IsNotPeriodicPt (f : α → α)  (x : α) := ∀ n : ℕ, 0 < n -> ¬IsPeriodicPt f n x

lemma non_periodic_arbitrary_large_time (N : ℕ) (ε0 : ℝ) (hε0 : 0 < ε0) (x : α) (hfx : IsNotPeriodicPt f x) (hxf : x ∈ nonWanderingSet f)
: ∃ (y : α), ∃ (n : ℕ), y ∈ ball x ε0 ∧ f^[n] y ∈ ball x ε0 ∧ N+1 < n :=
by
  unfold IsNotPeriodicPt at hfx
  unfold nonWanderingSet at hxf
  dsimp at hxf
  have hkill : forall (n : ℕ), 0 < n → ∃ ε, 0 < ε ∧ (ball x ε) ∩ (f^[n] '' (ball x ε)) = ∅ := by
    intro n1 hn1
    have hfx2 := hfx n1 hn1
    have hfnC : Continuous f^[n1] := Continuous.iterate hf n1
    have hfx2' : x ≠ f^[n1] x := Ne.symm hfx2
    exact separated_balls (f^[n1]) hfnC x hfx2'
  choose! ε2 hε2 h'ε2 using hkill
  have A : Finset.Nonempty ((Finset.Icc 1 (N+1)).image ε2) := by simp
  let δ := ((Finset.Icc 1 (N+1)).image ε2).min' A
  let δ2 := min δ ε0
  have δmem: δ ∈ (Finset.Icc 1 (N+1)).image ε2 := Finset.min'_mem _ _
  simp at δmem
  rcases δmem with ⟨n, ⟨npos, _⟩, h'n⟩
  change ε2 n = δ at h'n
  have hδ0 : 0 < δ := by
    rw [← h'n]
    exact hε2 n npos
  have hδ20 : 0 < δ2 := by
    rw [lt_min_iff]
    constructor
    exact hδ0
    exact hε0
  have hδ2ε0 : δ2 ≤ ε0 := min_le_right δ ε0
  have hδ2δ : δ2 ≤ δ := min_le_left δ ε0
  have hδ : ∀ (n : ℕ), (0 < n) → (n ≤ N + 1) → (ball x δ) ∩ (f^[n] '' ball x δ) = ∅ := by
    intro n2 hn21 hn22
    have hA : δ ≤ ε2 n2 := by
      apply Finset.min'_le
      simp
      use n2
      refine' ⟨⟨hn21,hn22⟩,rfl⟩
    have hbigball := h'ε2 n2 hn21
    apply inter_subset_empty_of_inter_empty (ball x δ) (f^[n2] '' ball x δ) (ball x (ε2 n2)) (f^[n2] '' ball x (ε2 n2))
    · exact ball_subset_ball (x := x) hA
    · exact image_subset (f^[n2]) (ball_subset_ball (x := x) hA)
    · exact hbigball
  have hxfδ := hxf δ2 hδ20
  rcases hxfδ with ⟨y,⟨n3,hy1,hy2,hy3⟩⟩
  have hsmallball : ball x δ2 ⊆ ball x δ := ball_subset_ball hδ2δ
  have hsmall1 : y ∈ ball x δ := ball_subset_ball hδ2δ hy1
  use y
  use n3
  refine' ⟨ball_subset_ball hδ2ε0 hy1,⟨ball_subset_ball hδ2ε0 hy2,_⟩⟩
  contrapose! hδ
  use n3
  refine' ⟨_,⟨hδ,_⟩⟩
  exact Nat.pos_of_ne_zero hy3
  dsimp
  intro stupido
  have hstupido : f^[n3] y ∈ ∅ := by
    rw [←stupido]
    apply mem_inter
    · exact hsmallball hy2
    · rw [mem_image]
      use y
      refine' ⟨hsmall1,rfl⟩
  assumption
  done

theorem arbitrary_large_time (N : ℕ) (ε : ℝ) (hε : 0 < ε) (x : α) (hx : x ∈ nonWanderingSet f) :
∃ (y : α), ∃ (n : ℕ), y ∈ ball x ε ∧ f^[n] y ∈ ball x ε ∧ N+1 < n :=
by
  by_cases hfx : IsNotPeriodicPt f x
  -- hard case: if x is non-periodic, we use continuity of f
  · exact non_periodic_arbitrary_large_time f hf N ε hε x hfx hx
  -- easy case: if x is periodic, then y = x is a good candidate
  · unfold IsNotPeriodicPt at hfx
    push_neg at hfx
    obtain ⟨n, hn, hn2⟩ := hfx
    -- rcases hfx with ⟨n, hn⟩ also works
    use x
    use n * (N+2)
    refine' ⟨_,_,_⟩
    · exact mem_ball_self hε
    · have h4 : IsPeriodicPt f n x := by
        unfold IsPeriodicPt
        unfold IsFixedPt
        exact hn2
      rw [IsPeriodicPt.mul_const h4 (N+2)]
      exact mem_ball_self hε
    · exact Nat.le_mul_of_pos_left hn
  done


/- Show that the non-wandering set of `f` is closed. -/
theorem is_closed : IsClosed (nonWanderingSet f : Set α) := by
  rw [← isSeqClosed_iff_isClosed]
  unfold IsSeqClosed
  intro u x hu ulim
  rw [tendsto_atTop_nhds] at ulim
  intro ε hepos
  have e2pos : 0 < ε / 2 := by linarith
  have h1 : IsOpen (ball x (ε / 2)) := isOpen_ball
  have h2 : ∃ (z : α), z ∈ ball x (ε/ 2) ∧ z ∈ nonWanderingSet f := by
    have k1 := ulim (ball x (ε / 2))
    have k2 : x ∈ (ball x (ε / 2)) := by
      exact mem_ball_self e2pos
    obtain ⟨N, k3⟩ := k1 k2 h1
    have k4 : u N ∈ ball x (ε / 2) := by
      have k5 : N ≤ N := by
        exact Nat.le_refl N
      exact k3 N k5
    exact ⟨u N, k4, hu N⟩
  rcases h2 with ⟨z, h3, h4⟩
  have h5 : ∃ (y : α), ∃ (n : ℕ), y ∈ ball z (ε / 2) ∧ f^[n] y ∈ ball z (ε / 2) ∧ n ≠ 0 := by
    simp [nonWanderingSet] at h4
    -- let l1 := h4 (ε / 2) e2pos
    -- rcases l1 with ⟨y, l1, ⟨n, l2, l3⟩⟩
    -- obtain below is equivalent to the above two lines
    obtain ⟨y, l1, ⟨n, l2, l3⟩⟩ := h4 (ε / 2) e2pos
    use y, n -- note `use y, n` which is the same as `use y` and `use n`
    -- simp -- was repeatedly doing `mem_ball.mp: y ∈ ball x ε -> dist y x < ε `
    exact ⟨l1, l2, l3⟩
  rcases h5 with ⟨y, n, h6, h7, h8⟩
  have h9 : y ∈ ball x ε := by
    -- simp -- was doing `mem_ball.mp: y ∈ ball x ε -> dist y x < ε `
    have m1 : dist y z + dist z x < ε := by
      rw [mem_ball] at h3 h6
      linarith
    have : dist y x ≤ dist y z + dist z x := by
      exact dist_triangle _ _ _  -- why can I omit argument, but I can't in the line below?
    exact lt_of_le_of_lt this m1
  have h10 : f^[n] y ∈ ball x ε := by
    -- simp -- was doing `mem_ball.mp: y ∈ ball x ε -> dist y x < ε `
    have p1 : dist (f^[n] y) z + dist z x < ε := by
      rw [mem_ball] at h7 h3
      linarith
    have : dist (f^[n] y) x ≤ dist (f^[n] y) z + dist z x := by
      exact dist_triangle _ _ _  -- why can I omit argument, but I can't in the line below?
    exact lt_of_le_of_lt this p1
  exact ⟨y, n, h9, h10, h8⟩
  done


/- Show that the non-wandering set of `f` is compact. -/
theorem is_cpt : IsCompact (nonWanderingSet f : Set α) := by
  apply isCompact_of_isClosed_bounded
  . exact is_closed f
  . exact bounded_of_compactSpace
  done

/- Show that the omega-limit set of any point is nonempty. -/
/- Click F12 on ω⁺ below to go to its definition, and browse a little bit the file to get a
feel of what is already there. -/
theorem omegaLimit_nonempty (x : α) : Set.Nonempty (ω⁺ (fun n ↦ f^[n]) ({x})) := by
  apply nonempty_omegaLimit atTop (fun n ↦ f^[n]) {x}
  exact Set.singleton_nonempty x
  done

/- Show that the omega-limit set of any point is contained in the non-wandering set. -/
theorem omegaLimit_nonwandering (x : α) :
    (ω⁺ (fun n ↦ f^[n]) ({x})) ⊆ (nonWanderingSet f) := by
  intro z hz
  rewrite [mem_omegaLimit_iff_frequently] at hz
  simp at hz
  have subsequence : ∀ U ∈ nhds z, ∃ φ, StrictMono φ ∧ ∀ (n : ℕ), f^[φ n] x ∈ U := by
    intro U hU
    apply Filter.extraction_of_frequently_atTop (hz U hU)
    done
  -- unfold nonWanderingSet
  intro ε hε
  have ball_in_nbd : ball z ε ∈ nhds z := by
    exact ball_mem_nhds z hε
  -- same as `let ⟨φ, hφ, hf⟩ := subsequence (ball z ε) ball_in_nbd` but nicer
  obtain ⟨φ, hφ, hf⟩ : ∃ φ, StrictMono φ ∧ ∀ (n : ℕ), f^[φ n] x ∈ ball z ε :=
    subsequence (ball z ε) ball_in_nbd
  use f^[φ 1] x, φ 2 - φ 1
  refine' ⟨_, _, _⟩
  . exact (hf 1)
  . have : f^[φ 2 - φ 1] (f^[φ 1] x) = f^[φ 2] x := by
      rw [ <-Function.iterate_add_apply, Nat.sub_add_cancel ]
      apply le_of_lt; apply hφ
      group
    rw [this]
    apply (hf 2)
  . simp
    apply hφ
    norm_num
  done

/- Show that the non-wandering set is non-empty -/
theorem nonWandering_nonempty [hα : Nonempty α] : Set.Nonempty (nonWanderingSet f) := by
  have (x : α) : Set.Nonempty (ω⁺ (fun n ↦ f^[n]) ({x})) -> Set.Nonempty (nonWanderingSet f) := by
    apply Set.Nonempty.mono
    apply omegaLimit_nonwandering
  apply this
  apply omegaLimit_nonempty f
  apply Nonempty.some hα
  done


/- Define the recurrent set of `f`. The recurrent set is the set of points that are recurrent,
   i.e. that belong to their omega-limit set. -/
def recurrentSet {α : Type _} [TopologicalSpace α] (f : α → α) : Set α :=
  { x | x ∈ ω⁺ (fun n ↦ f^[n]) ({x}) }

theorem recurrentSet_iff_accumulation_point (x : α) :
    x ∈ recurrentSet f ↔ ∀ (ε : ℝ) (N : ℕ), 0 < ε
                         -> ∃ m : ℕ, N ≤ m ∧ f^[m] x ∈ ball x ε := by
  constructor
  . intro recur_x
    unfold recurrentSet at recur_x
    -- simp is fine as well, but we only need
    -- `x ∈ { y | p y } = p x` here
    -- I hope that being explicit makes compilation faster
    simp only [mem_setOf_eq] at recur_x
    rw [mem_omegaLimit_iff_frequently] at recur_x
    intro ε N hε
    have recur_x_in_ball := recur_x (ball x ε) (ball_mem_nhds x hε)
    simp [frequently_atTop] at recur_x_in_ball
    exact recur_x_in_ball N
  . intro hf
    unfold recurrentSet
    simp only [mem_setOf_eq] -- `x ∈ { y | p y } = p x`
    rw [mem_omegaLimit_iff_frequently]
    intro U hU
    simp [frequently_atTop] -- reduces the goal to `∀ (a : ℕ), ∃ b, a ≤ b ∧ f^[b] x ∈ U`
    -- same as `rcases Metric.mem_nhds_iff.mp hU with ⟨ε, hε, rest⟩` but nicer
    obtain ⟨ε, hε, ball_in_U⟩ : ∃ ε, ε > 0 ∧ ball x ε ⊆ U := Metric.mem_nhds_iff.mp hU
    intro a
    obtain ⟨m, hm, fm_in_ball⟩ := (hf ε a hε)
    exact ⟨m, hm, mem_of_subset_of_mem ball_in_U fm_in_ball⟩
  done

/- Show that periodic points belong to the recurrent set. -/
theorem periodicpts_mem_recurrentSet
    (x : α) (n : ℕ) (nnz: n ≠ 0) (hx: IsPeriodicPt f n x) :
    x ∈ recurrentSet f := by
  -- unfold IsPeriodicPt at hx
  -- unfold IsFixedPt at hx
  -- unfold recurrentSet
  have x_in_omegaLimit : x ∈ ω⁺ (fun n ↦ f^[n]) ({x} : Set α) := by
    rw [mem_omegaLimit_iff_frequently]
    intro U hU
    simp [frequently_atTop]
    intro a
    have hb : ∃ b, a ≤ b ∧ f^[b] x ∈ U := by
      use a * n
      constructor
      . exact Nat.le_mul_of_pos_right (Nat.pos_of_ne_zero nnz)
      . -- have : f^[a * n] x = x := by
        --  exact Function.IsPeriodicPt.const_mul hx a
        -- rw [this]
        rw [Function.IsPeriodicPt.const_mul hx a]
        exact mem_of_mem_nhds hU
      done
    exact hb
    done
  apply x_in_omegaLimit
  done

/- Show that the recurrent set is included in the non-wandering set -/
theorem recurrentSet_nonwandering : recurrentSet f ⊆ (nonWanderingSet f) := by
  intro z hz
  unfold recurrentSet at hz
  simp only [mem_setOf_eq] at hz -- `x ∈ { y | p y } = p x`
  apply omegaLimit_nonwandering
  exact hz
  done

/- Define minimal subsets for `f`, as closed invariant subsets in which all orbits are dense.
   Note that `IsInvariant.isInvariant_iff_image` is a useful function when we use `invariant`.
   Using a structure here allows us to get the various properties via dot notation,
   search e.g. for `hf.minimal` below -/
structure IsMinimalSubset (f : α → α) (U : Set α) : Prop :=
  (closed : IsClosed U)
  (invariant: IsInvariant (fun n x => f^[n] x) U)
  (minimal: ∀ (x y : α) (_: x ∈ U) (_: y ∈ U) (ε : ℝ), ε > 0 -> ∃ n : ℕ, f^[n] y ∈ ball x ε)

/- Define a minimal dynamics (all orbits are dense) -/
def IsMinimal (f : α → α) : Prop := IsMinimalSubset f univ

/- Show that in a minimal dynamics, the recurrent set is all the space -/
theorem recurrentSet_of_minimal_is_all_space (hf: IsMinimal f) :
    ∀ x : α, x ∈ recurrentSet f := by
  intro z
  -- unfold recurrentSet
  -- unfold IsMinimal at hf
  -- simp
  have : ∀ (x : α) (ε : ℝ) (N : ℕ), ε > 0
         -> ∃ m : ℕ, m ≥ N ∧ f^[m] x ∈ ball x ε := by
    intro x ε N hε
    -- rcases (hf x (f^[N] x) ε hε) with ⟨n, hball⟩
    obtain ⟨n, hball⟩ : ∃ n, f^[n] (f^[N] x) ∈ ball x ε :=
      hf.minimal x (f^[N] x) (mem_univ _) (mem_univ _) ε hε
    refine' ⟨n + N, _, _⟩
    . linarith
    . rw [ <-Function.iterate_add_apply ] at hball
      exact hball
    done
  apply (recurrentSet_iff_accumulation_point f z).mpr
  exact this z
  done

-- An example to learn to define maps on the unit interval
noncomputable def doubling_map (x : unitInterval) : unitInterval :=
  ⟨Int.fract (2 * x), by exact unitInterval.fract_mem (2 * x)⟩

/- Give an example of a continuous dynamics on a compact space in which the recurrent set is all
the space, but the dynamics is not minimal -/
example : ¬IsMinimal (id : unitInterval -> unitInterval) := by
  intro H
  have minimality := H.minimal
  contrapose minimality
  -- `push_neg` pushes negations as deep as possible into the conclusion of a hypothesis
  push_neg
  use 0, 1, (mem_univ 0), (mem_univ 1), (dist (1 : unitInterval) (0 : unitInterval))/2
  -- we need this helper twice below
  have dist_pos : 0 < dist (1 : unitInterval) 0 := by
    apply dist_pos.mpr
    apply unitInterval.coe_ne_zero.mp; norm_num -- 1 ≠ 0
  constructor
  . apply div_pos dist_pos
    linarith -- 0 < 2
  . intro n
    -- `simp` is necessary to go from `¬id^[n] 1 ∈ ball 0 (dist 1 0 / 2)`
    -- to `0 ≤ dist 1 0`
    simp
    exact le_of_lt dist_pos
  done

example (x : unitInterval) :
    x ∈ recurrentSet (id : unitInterval -> unitInterval) := by
  -- unfold recurrentSet
  apply periodicpts_mem_recurrentSet _ _ 1
  . linarith
  . exact is_periodic_id 1 x
  done


/- Show that every point in a minimal subset is recurrent -/
theorem minimalSubset_mem_recurrentSet (U : Set α) (hU: IsMinimalSubset f U) :
      U ⊆ recurrentSet f := by
  intro x hx
  obtain ⟨_, hInv, hMin⟩ := hU
  apply (recurrentSet_iff_accumulation_point f x).mpr
  intro ε N hε
  have iterates_in_U : ∀ n : ℕ, f^[n] x ∈ U := by
    -- unfold IsInvariant at hInv
    intro n
    -- let f' := hInv n; simp at f'
    -- apply Set.mapsTo'.mp at f'
    -- leads us to `f^[n] x ∈ (fun n x ↦ f^[n] x) n '' U`
    -- which simplifies to `∃ x', x' ∈ U ∧ f^[n] x' = f^[n] x`
    -- as one can check with `simp`
    apply Set.mapsTo'.mp (hInv n)
    -- once we `use x`
    -- we get the statement from `exact ⟨hx, rfl⟩`
    -- this can be summarized to
    exact ⟨x, hx, rfl⟩
  obtain ⟨n, hball⟩ : ∃ n, f^[n] (f^[N] x) ∈ ball x ε := by
    apply hMin x (f^[N] x) hx (iterates_in_U N) ε hε
  refine' ⟨n + N, _, _⟩
  . exact le_add_self -- N ≤ n + N
  . rw [ <-Function.iterate_add_apply ] at hball
    exact hball
  done

/- Show that every invariant nonempty closed subset contains at least a minimal invariant subset,
using Zorn lemma. -/
theorem nonempty_invariant_closed_subset_has_minimalSubset
    (U : Set α) (hne: Nonempty U) (hC: IsClosed U) (hI: IsInvariant (fun n x => f^[n] x) U) :
    ∃ V : Set α, V ⊆ U -> (hinv: MapsTo f U U) -> IsMinimalSubset f U :=
  sorry



/- Show that the recurrent set of `f` is nonempty -/
theorem recurrentSet_nonempty [Nonempty α]: Set.Nonempty (recurrentSet f) := by
  sorry

end Topological_Dynamics

section Ergodic_Theory

open BigOperators

/- standing assumptions: `f` is a measure preserving map of a probability space `(α, μ)`, and
`g : α → ℝ` is integrable. -/

variable {α : Type _} [MetricSpace α] [CompactSpace α] [MeasurableSpace α] [BorelSpace α]
  {μ : MeasureTheory.Measure α} [IsProbabilityMeasure μ] {f : α → α}
  (hf : MeasurePreserving f μ) {g : α → ℝ} (hg : Integrable g μ)


/- Define Birkhoff sums. -/
noncomputable def birkhoffSum {α : Type _} (f : α → α) (g : α → ℝ) (n : ℕ) (x : α) : ℝ :=
  1 / n * (∑ i in Finset.range n, g (f^[i] x))


/- Define the invariant sigma-algebra of `f` -/



/- Main lemma to prove Birkhoff ergodic theorem:
assume that the integral of `g` on any invariant set is strictly negative. Then, almost everywhere,
the Birkhoff sums `S_n g x` are bounded above.
-/


/- Deduce Birkhoff theorem from the main lemma, in the form that almost surely, `S_n f / n`
converges to the conditional expectation of `f` given the invariant sigma-algebra. -/


/- If `f` is ergodic, show that the invariant sigma-algebra is ae trivial -/


/- Show that the conditional expectation with respect to an ae trivial subalgebra is ae
the integral. -/


/- Give Birkhoff theorem for ergodic maps -/


end Ergodic_Theory
