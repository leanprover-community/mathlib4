import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Combinatorics.Quiver.MaxFlowMinCutAlt.MaxFlowMinCutAlt
import Mathlib.Tactic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic

open Filter Topology

open Finset

/-- Residual capacity given a plain function, no ValidFlow needed. -/
noncomputable def rawResCap {V : Type*} [Fintype V]
    (G : FlowNetwork V) (f : V → V → ℝ) (u v : V) : ℝ :=
  G.c u v - f u v + f v u

/-- Validity of a path under raw residual caps. -/
def rawPathValid {V : Type*} [Fintype V] [DecidableEq V]
    (G : FlowNetwork V) (f : V → V → ℝ) (p : uvPath G.s G.t) : Prop :=
  ∀ (i : ℕ) (h : i < p.verts.length - 1),
    rawResCap G f p.verts[i] p.verts[i+1] > 0

/-- Bottleneck of a path under raw residual caps: min residual cap along the path.
    This is what the augmentation amount should equal. -/
noncomputable def rawBottleneck {V : Type*} [Fintype V] [DecidableEq V]
    (G : FlowNetwork V) (f : V → V → ℝ) (p : uvPath G.s G.t) : ℝ :=
  let caps := List.zipWith (rawResCap G f) p.verts p.verts.tail
  caps.min (by
    have h2 := ge_two_vertices p G.source_not_sink
    -- The length of caps is the minimum of the lengths of p.verts and its tail
    have h_len : caps.length = p.verts.length - 1 := by
      simp [caps, List.length_zipWith]
    -- Since p.verts.length ≥ 2, caps.length ≥ 1, meaning it cannot be empty
    apply List.ne_nil_of_length_pos
    omega
  )

/-- The flow induced by a path: send rawBottleneck along each edge. -/
noncomputable def rawPathFlow {V : Type*} [Fintype V] [DecidableEq V]
    (G : FlowNetwork V) (f : V → V → ℝ) (p : uvPath G.s G.t) : V → V → ℝ :=
  fun u v =>
    if ∃ (i : ℕ) (_ : i < p.verts.length - 1), u = p.verts[i] ∧ v = p.verts[i+1]
    then rawBottleneck G f p
    else 0

/-- Augmentation of f by g: cancel 2-cycles, same as the Mul instance on RelaxedFlow. -/
noncomputable def rawAugment {V : Type*} [Fintype V]
    (f g : V → V → ℝ) : V → V → ℝ :=
  fun u v => max (f u v + g u v - f v u - g v u) 0

/-- The FF flow sequence as plain functions, no ValidFlow anywhere. -/
noncomputable def rawFFFlows {V : Type*} [Fintype V] [DecidableEq V]
    (G : FlowNetwork V) (paths : ℕ → uvPath G.s G.t) : ℕ → V → V → ℝ
  | 0     => fun _ _ => 0
  | n + 1 =>
      let f := rawFFFlows G paths n
      rawAugment f (rawPathFlow G f (paths n))


inductive FFVert | s | t | a | b | c | d
  deriving DecidableEq, Repr

instance : Fintype FFVert where
  elems := ⟨[FFVert.s, FFVert.t, FFVert.a, FFVert.b, FFVert.c, FFVert.d], by decide⟩
  complete := fun x => by cases x <;> decide

noncomputable def ρ : ℝ := (√5 - 1) / 2

lemma ρ_pos : 0 < ρ := by
        simp only [ρ]
        suffices 1 ≤ √5 by
        {
          grind
        }
        simp

lemma ρ_lt_1 : ρ < 1 := by
      unfold ρ;
      suffices Real.sqrt 5 < 3 by
        {
          grind
        }
      rw [Real.sqrt_lt]
      · grind
      · grind
      · grind

lemma ρ_pow (k : ℕ) : ρ ^ k ≤ ρ ^ (k - 1) := by
      have h_pos := ρ_pos
      have h_lt_1 := ρ_lt_1
      exact pow_le_pow_of_le_one h_pos.le h_lt_1.le (Nat.sub_le k 1)

lemma ρ_pow2 (k : ℕ) (h : k ≥ 1) : ρ ^ k ≤ ρ:= by
      have h_pos := ρ_pow
      induction k, h using Nat.le_induction with
      | base =>  linarith
      | succ n hn ih =>
        exact Std.IsPreorder.le_trans (ρ ^ (n + 1)) (ρ ^ (n + 1 - 1)) ρ (h_pos (n + 1)) ih

lemma ρ_pow_transition (k : ℕ) (hk : k ≥ 1) : ρ ^ (k - 1) - ρ ^ k = ρ ^ (k + 1) := by
  -- ρ satisfies ρ² = 1 - ρ
  have hρ_sq : ρ ^ 2 = 1 - ρ := by
    have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    unfold ρ; nlinarith [h5]
  -- Eliminate the natural number subtraction by substituting k = n + 1
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h1 : ρ ^ n - ρ ^ (n + 1) = ρ ^ n * (1 - ρ)   := by ring
  have h2 : ρ ^ n * (1 - ρ)     = ρ ^ n * ρ ^ 2      := by rw [hρ_sq]
  have h3 : ρ ^ n * ρ ^ 2       = ρ ^ (n + 2)        := by ring
  linarith

lemma ρ_pow_transition' (k : ℕ) : ρ ^ k - ρ ^ (k + 1) = ρ ^ (k + 2) := by
  have hρ_sq : ρ ^ 2 = 1 - ρ := by
    have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    unfold ρ; nlinarith [h5]
  have h1 : ρ ^ k - ρ ^ (k + 1) = ρ ^ k * (1 - ρ) := by ring
  have h2 : ρ ^ k * (1 - ρ) = ρ ^ k * ρ ^ 2       := by rw [hρ_sq]
  have h3 : ρ ^ k * ρ ^ 2       = ρ ^ (k + 2)     := by ring
  linarith

-- X is any real number > 2
variable (X : ℝ) (hX : X > 2)

open FFVert in
noncomputable def FFNetwork : FlowNetwork FFVert where
  s := s
  t := t
  source_not_sink := by decide
  c u v := match u, v with
    | s, a => X
    | s, b => X
    | s, d => X
    | b, a => 1
    | b, c => 1
    | d, c => ρ
    | a, t => X
    | c, t => X
    | d, t => X
    | _, _ => 0
  nonneg_capacity := by
    intro u v
    split <;> simp <;> try grind
    grind [ρ_pos]

open FFVert in
def rawPath1 : uvPath (V := FFVert) s t where
  verts := [s, b, c, t]
  nonempty := by decide
  nodup := by decide
  ustart := by decide
  vend := by decide

open FFVert in
def rawPath2 : uvPath (V := FFVert) s t where
  verts := [s, d, c, b, a, t]
  nonempty := by decide
  nodup := by decide
  ustart := by decide
  vend := by decide

open FFVert in
def rawPath3 : uvPath (V := FFVert) s t where
  verts := [s, b, c, d, t]
  nonempty := by decide
  nodup := by decide
  ustart := by decide
  vend := by decide

open FFVert in
def rawPath4 : uvPath (V := FFVert) s t where
  verts := [s, a, b, c, t]
  nonempty := by decide
  nodup := by decide
  ustart := by decide
  vend := by decide

def cycleChoice : ℕ → uvPath FFVert.s FFVert.t
  | 0     => rawPath1
  | n + 1 => match n % 4 with
    | 0     => rawPath2
    | 1     => rawPath3
    | 2     => rawPath2
    | _     => rawPath4

noncomputable def ffRawFlows : ℕ → FFVert → FFVert → ℝ :=
  rawFFFlows (FFNetwork X hX) cycleChoice

open FFVert

/-- Total function representing the exact expected residual capacity for ALL pairs.
    Directly incorporates the network capacities and outer flows to bypass Option matching. -/
noncomputable def expectedResCap (X : ℝ) (k : ℕ) (step : Fin 4) (u v : FFVert) : ℝ :=
  match step, u, v with
  -- Step 0: Figure 5.6
  | 0, a, b => 1 - ρ ^ (k - 1)
  | 0, b, a => ρ ^ (k - 1)
  | 0, b, c => 0
  | 0, c, b => 1
  | 0, c, d => ρ - ρ ^ k
  | 0, d, c => ρ ^ k
  | 0, s, a => X - (ρ - ρ ^ k)
  | 0, s, b => X - (2 - ρ ^ (k - 1))
  | 0, s, d => X - (1 + ρ - ρ ^ (k - 1) - ρ ^ k)
  | 0, a, t => X - (1 + ρ - ρ ^ (k - 1) - ρ ^ k)
  | 0, c, t => X - (1 + ρ - ρ ^ k)
  | 0, d, t => X - (1 - ρ ^ (k - 1))
  | 0, a, s => ρ - ρ ^ k
  | 0, b, s => 2 - ρ ^ (k - 1)
  | 0, d, s => 1 + ρ - ρ ^ (k - 1) - ρ ^ k
  | 0, t, a => 1 + ρ - ρ ^ (k - 1) - ρ ^ k
  | 0, t, c => 1 + ρ - ρ ^ k
  | 0, t, d => 1 - ρ ^ (k - 1)
  -- Step 1: Figure 5.7
  | 1, a, b => 1 - ρ ^ (k + 1)
  | 1, b, a => ρ ^ (k + 1)
  | 1, b, c => ρ ^ k
  | 1, c, b => 1 - ρ ^ k
  | 1, c, d => ρ
  | 1, d, c => 0
  | 1, s, a => X - (ρ - ρ ^ k)
  | 1, s, b => X - (2 - ρ ^ (k - 1))
  | 1, s, d => X - (1 + ρ - ρ ^ (k - 1))
  | 1, a, t => X - (1 + ρ - ρ ^ (k - 1))
  | 1, c, t => X - (1 + ρ - ρ ^ k)
  | 1, d, t => X - (1 - ρ ^ (k - 1))
  | 1, a, s => ρ - ρ ^ k
  | 1, b, s => 2 - ρ ^ (k - 1)
  | 1, d, s => 1 + ρ - ρ ^ (k - 1)
  | 1, t, a => 1 + ρ - ρ ^ (k - 1)
  | 1, t, c => 1 + ρ - ρ ^ k
  | 1, t, d => 1 - ρ ^ (k - 1)
  -- Step 2: Figure 5.8
  | 2, a, b => 1 - ρ ^ (k + 1)
  | 2, b, a => ρ ^ (k + 1)
  | 2, b, c => 0
  | 2, c, b => 1
  | 2, c, d => ρ - ρ ^ k
  | 2, d, c => ρ ^ k
  | 2, s, a => X - (ρ - ρ ^ k)
  | 2, s, b => X - (2 - ρ ^ (k - 1) + ρ ^ k)
  | 2, s, d => X - (1 + ρ - ρ ^ (k - 1))
  | 2, a, t => X - (1 + ρ - ρ ^ (k - 1))
  | 2, c, t => X - (1 + ρ - ρ ^ k)
  | 2, d, t => X - (1 - ρ ^ (k + 1))
  | 2, a, s => ρ - ρ ^ k
  | 2, b, s => 2 - ρ ^ (k - 1) + ρ ^ k
  | 2, d, s => 1 + ρ - ρ ^ (k - 1)
  | 2, t, a => 1 + ρ - ρ ^ (k - 1)
  | 2, t, c => 1 + ρ - ρ ^ k
  | 2, t, d => 1 - ρ ^ (k + 1)
  -- Step 3: Figure 5.9
  | 3, a, b => 1
  | 3, b, a => 0
  | 3, b, c => ρ ^ (k + 1)
  | 3, c, b => 1 - ρ ^ (k + 1)
  | 3, c, d => ρ - ρ ^ (k + 2)
  | 3, d, c => ρ ^ (k + 2)
  | 3, s, a => X - (ρ - ρ ^ k)
  | 3, s, b => X - (2 - ρ ^ (k - 1) + ρ ^ k)
  | 3, s, d => X - (1 + ρ - ρ ^ k)
  | 3, a, t => X - (1 + ρ - ρ ^ k)
  | 3, c, t => X - (1 + ρ - ρ ^ k)
  | 3, d, t => X - (1 - ρ ^ (k - 1) + ρ ^ k)
  | 3, a, s => ρ - ρ ^ k
  | 3, b, s => 2 - ρ ^ (k - 1) + ρ ^ k
  | 3, d, s => 1 + ρ - ρ ^ k
  | 3, t, a => 1 + ρ - ρ ^ k
  | 3, t, c => 1 + ρ - ρ ^ k
  | 3, t, d => 1 - ρ ^ (k - 1) + ρ ^ k
  -- All remaining implicit zero-capacity structural back-edges
  | _, _, _ => 0

/-- Optimized, fast-breaking cycle invariant -/
def cycleInvariant (X : ℝ) (hX : X > 2) (f : FFVert → FFVert → ℝ) (k : ℕ) (step : Fin 4) : Prop :=
  ∀ u v, rawResCap (FFNetwork X hX) f u v = expectedResCap X k step u v

macro "solve_rawBottleneck" h:ident k:ident : tactic => `(tactic|
  ( simp only
      [rawBottleneck, rawPath1, rawPath2, rawPath3, rawPath4, List.tail_cons,
        List.zipWith_cons_cons, List.zipWith_nil_right]
    simp only [$h:ident _ _]
    unfold expectedResCap
    simp only [List.min, List.foldl, min_def]
    have h_pos : 0 < ρ := ρ_pos
    have h_lt1 : ρ < 1 := ρ_lt_1
    have h_pow : ρ ^ $k:ident ≤ ρ ^ ($k:ident - 1) := ρ_pow $k:ident
    have h_pow_nonneg : 0 ≤ ρ ^ ($k:ident - 1) := pow_nonneg h_pos.le ($k:ident - 1)
    have h_pow_k_le_one : ρ ^ $k:ident ≤ 1 := by bound
    have h_pow_kp1 : ρ ^ ($k:ident + 1) ≤ ρ ^ ($k:ident + 1 - 1) := ρ_pow ($k:ident + 1)
    have h_pow_kp1' : ρ ^ ($k:ident + 1) ≤ ρ ^ $k:ident := by
      have := ρ_pow ($k:ident + 1); simp at this; exact this
    have h_pow_kp1_le_one : ρ ^ ($k:ident + 1) ≤ 1 := by bound
    try have h_pow2 : ρ ^ $k:ident ≤ ρ := ρ_pow2 $k:ident (by omega)
    split_ifs <;> linarith )
)

open FFVert in
lemma rawPath1_has_edge (u v : FFVert) :
    (∃ (i : ℕ) (h : i < rawPath1.verts.length - 1), u = rawPath1.verts[i] ∧ v = rawPath1.verts[i+1])
    ↔ (u = s ∧ v = b) ∨ (u = b ∧ v = c) ∨ (u = c ∧ v = t) := by
  simp only [rawPath1, List.getElem_cons_succ, List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.add_one_sub_one]
  constructor
  · rintro ⟨i, hi, rfl, rfl⟩
    -- Since hi : i < 3, it must be 0, 1, or 2. omega splits this perfectly.
    have h_cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    grind
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · use 0; simp
    · use 1; simp
    · use 2; simp

open FFVert in
lemma rawPath2_has_edge (u v : FFVert) :
    (∃ (i : ℕ) (h : i < rawPath2.verts.length - 1), u = rawPath2.verts[i] ∧ v = rawPath2.verts[i+1])
    ↔ (u = s ∧ v = d) ∨ (u = d ∧ v = c) ∨ (u = c ∧ v = b) ∨ (u = b ∧ v = a) ∨ (u = a ∧ v = t) := by
  simp only [rawPath2, List.getElem_cons_succ, List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.add_one_sub_one]
  constructor
  · rintro ⟨i, hi, rfl, rfl⟩
    have h_cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    grind
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · use 0; simp
    · use 1; simp
    · use 2; simp
    · use 3; simp
    · use 4; simp

open FFVert in
lemma rawPath3_has_edge (u v : FFVert) :
    (∃ (i : ℕ) (h : i < rawPath3.verts.length - 1), u = rawPath3.verts[i] ∧ v = rawPath3.verts[i+1])
    ↔ (u = s ∧ v = b) ∨ (u = b ∧ v = c) ∨ (u = c ∧ v = d) ∨ (u = d ∧ v = t) := by
  simp only [rawPath3, List.getElem_cons_succ, List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.add_one_sub_one]
  constructor
  · rintro ⟨i, hi, rfl, rfl⟩
    have h_cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    grind
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · use 0; simp
    · use 1; simp
    · use 2; simp
    · use 3; simp

open FFVert in
lemma rawPath4_has_edge (u v : FFVert) :
    (∃ (i : ℕ) (h : i < rawPath4.verts.length - 1), u = rawPath4.verts[i] ∧ v = rawPath4.verts[i+1])
    ↔ (u = s ∧ v = a) ∨ (u = a ∧ v = b) ∨ (u = b ∧ v = c) ∨ (u = c ∧ v = t) := by
  simp only [rawPath4, List.getElem_cons_succ, List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, Nat.add_one_sub_one]
  constructor
  · rintro ⟨i, hi, rfl, rfl⟩
    have h_cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    grind
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · use 0; simp
    · use 1; simp
    · use 2; simp
    · use 3; simp

lemma rawResCap_augment {V : Type*} [Fintype V] (G : FlowNetwork V) (f g : V → V → ℝ) (u v : V) :
    rawResCap G (rawAugment f g) u v = rawResCap G f u v - g u v + g v u := by
  unfold rawResCap rawAugment
  have h (x : ℝ) : - max x 0 + max (-x) 0 = -x := by
    rcases le_total x 0 with hx | hx
    · rw [max_eq_right hx, max_eq_left (by linarith)]; linarith
    · rw [max_eq_left hx, max_eq_right (by linarith)]; linarith
  have h_eq := h (f u v + g u v - f v u - g v u)
  grind

lemma rawBottleneck_path2_1 (X : ℝ) (hX : X > 2) (f : FFVert → FFVert → ℝ) (k : ℕ)
    (h : cycleInvariant X hX f k 0) :
    rawBottleneck (FFNetwork X hX) f rawPath2 = ρ ^ k := by solve_rawBottleneck h k

lemma rawBottleneck_path3 (X : ℝ) (hX : X > 2) (f : FFVert → FFVert → ℝ) (k : ℕ) (hk : k ≥ 1)
    (h : cycleInvariant X hX f k 1) :
    rawBottleneck (FFNetwork X hX) f rawPath3 = ρ ^ k := by solve_rawBottleneck h k

lemma rawBottleneck_path2_2 (X : ℝ) (hX : X > 2) (f : FFVert → FFVert → ℝ) (k : ℕ) (hk : k ≥ 1)
    (h : cycleInvariant X hX f k 2) :
    rawBottleneck (FFNetwork X hX) f rawPath2 = ρ ^ (k+1) := by solve_rawBottleneck h k

lemma rawBottleneck_path4 (X : ℝ) (hX : X > 2) (f : FFVert → FFVert → ℝ) (k : ℕ) (hk : k ≥ 1)
    (h : cycleInvariant X hX f k 3) :
    rawBottleneck (FFNetwork X hX) f rawPath4 = ρ ^ (k+1) := by solve_rawBottleneck h k


open FFVert in
/-- Step 0 -> 1: Augmenting along rawPath2 -/
lemma step0_to_1 (X : ℝ) (hX : X > 2) (f : FFVert → FFVert → ℝ) (k : ℕ) (hk : k ≥ 1)
    (h : cycleInvariant X hX f k 0) :
    cycleInvariant X hX (rawAugment f (rawPathFlow (FFNetwork X hX) f rawPath2)) k 1 := by
  unfold cycleInvariant
  intro u v
  rw [rawResCap_augment, h u v]
  unfold rawPathFlow
  rw [rawBottleneck_path2_1 X hX f k h]
  simp only [rawPath2_has_edge]
  unfold expectedResCap
  cases u <;> cases v <;> simp <;> linarith [ρ_pow_transition k hk]

/-- Step 1 -> 2: Augmenting along rawPath3 -/
lemma step1_to_2 (X : ℝ) (hX : X > 2) (f : FFVert → FFVert → ℝ) (k : ℕ) (hk : k ≥ 1)
    (h : cycleInvariant X hX f k 1) :
    cycleInvariant X hX (rawAugment f (rawPathFlow (FFNetwork X hX) f rawPath3)) k 2 := by
  unfold cycleInvariant
  intro u v
  rw [rawResCap_augment, h u v]
  unfold rawPathFlow
  rw [rawBottleneck_path3 X hX f k hk h]
  simp only [rawPath3_has_edge]
  unfold expectedResCap
  cases u <;> cases v <;> simp <;> linarith [ρ_pow_transition k hk]


/-- Step 2 -> 3: Augmenting along rawPath2 (again) -/
lemma step2_to_3 (X : ℝ) (hX : X > 2) (f : FFVert → FFVert → ℝ) (k : ℕ) (hk : k ≥ 1)
    (h : cycleInvariant X hX f k 2) :
    cycleInvariant X hX (rawAugment f (rawPathFlow (FFNetwork X hX) f rawPath2)) k 3 := by
  unfold cycleInvariant
  intro u v
  rw [rawResCap_augment, h u v]
  unfold rawPathFlow
  rw [rawBottleneck_path2_2 X hX f k hk h]
  simp only [rawPath2_has_edge]
  unfold expectedResCap
  cases u <;> cases v <;> simp <;> linarith [ρ_pow_transition k hk, ρ_pow_transition' k]

/-- Step 3 -> 0 (Next Cycle): Augmenting along rawPath4.
    Notice that the algebraic index `k` increases by 2 to match the textbook! -/
lemma step3_to_0 (X : ℝ) (hX : X > 2) (f : FFVert → FFVert → ℝ) (k : ℕ) (hk : k ≥ 1)
    (h : cycleInvariant X hX f k 3) :
    cycleInvariant X hX (rawAugment f (rawPathFlow (FFNetwork X hX) f rawPath4)) (k + 2) 0 := by
  unfold cycleInvariant
  intro u v
  rw [rawResCap_augment, h u v]
  unfold rawPathFlow
  rw [rawBottleneck_path4 X hX f k hk h]
  simp only [rawPath4_has_edge]
  unfold expectedResCap
  cases u <;> cases v <;> simp <;> try linarith [ρ_pow_transition k hk, ρ_pow_transition' k]

open FFVert in
/-- Main induction combining the four deterministic steps.
    `n` is the cycle loop counter. The textbook index is exactly `2 * n + 1`. -/
lemma ffRawFlows_invariant (n : ℕ) :
    (n = 0) ∨
    (∃ m, n = 4 * m + 1 ∧ cycleInvariant X hX (ffRawFlows X hX n) (2 * m + 1) 0) ∨
    (∃ m, n = 4 * m + 2 ∧ cycleInvariant X hX (ffRawFlows X hX n) (2 * m + 1) 1) ∨
    (∃ m, n = 4 * m + 3 ∧ cycleInvariant X hX (ffRawFlows X hX n) (2 * m + 1) 2) ∨
    (∃ m, n = 4 * m + 4 ∧ cycleInvariant X hX (ffRawFlows X hX n) (2 * m + 1) 3) := by
  induction n with
  | zero => left; rfl
  | succ n ih =>
    -- Helper to fold one rawFFFlows step back into ffRawFlows
    have fold : ∀ j path,
        cycleChoice j = path →
        rawAugment (ffRawFlows X hX j)
          (rawPathFlow (FFNetwork X hX) (ffRawFlows X hX j) path) =
          ffRawFlows X hX (j + 1) := by
      intros j path hpath
      change _ = rawAugment (ffRawFlows X hX j)
                 (rawPathFlow (FFNetwork X hX) (ffRawFlows X hX j) (cycleChoice j))
      rw [hpath]
    rcases ih with rfl | ⟨m, rfl, h⟩ | ⟨m, rfl, h⟩ | ⟨m, rfl, h⟩ | ⟨m, rfl, h⟩
    · -- n was 0 → successor is 1 = 4*0+1
      right; left; refine ⟨0, rfl, ?_⟩
      have h_bottleneck : rawBottleneck (FFNetwork X hX) (fun _ _ => 0) rawPath1 = 1 := by
        simp [rawBottleneck, rawPath1, rawResCap, FFNetwork, List.min]; grind
      have h_flow : rawPathFlow (FFNetwork X hX) (fun _ _ => 0) rawPath1 =
          fun u v => if (u = s ∧ v = b) ∨ (u = b ∧ v = c) ∨ (u = c ∧ v = t) then 1 else 0 := by
        ext u v; unfold rawPathFlow; rw [h_bottleneck]; simp only [rawPath1_has_edge]
      have h_aug : rawAugment (fun _ _ => 0)
          (fun u v => if (u = s ∧ v = b) ∨ (u = b ∧ v = c) ∨ (u = c ∧ v = t) then 1 else 0) =
          (fun u v => if (u = s ∧ v = b) ∨ (u = b ∧ v = c) ∨ (u = c ∧ v = t) then 1 else 0) := by
        ext u v; unfold rawAugment; simp only
        by_cases h1 : (u = s ∧ v = b) ∨ (u = b ∧ v = c) ∨ (u = c ∧ v = t)
        · by_cases h2 : (v = s ∧ u = b) ∨ (v = b ∧ u = c) ∨ (v = c ∧ u = t)
          · simp only [h1, ↓reduceIte, zero_add, sub_zero, h2, sub_self, max_self, zero_ne_one]
            rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            all_goals rcases h2 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
            all_goals contradiction
          · simp [h1, h2]
        · by_cases h2 : (v = s ∧ u = b) ∨ (v = b ∧ u = c) ∨ (v = c ∧ u = t)
          · simp [h1, h2]
          · simp [h1, h2]
      change cycleInvariant X hX (ffRawFlows X hX 1) 1 0
      change cycleInvariant X hX
        (rawAugment (fun _ _ => 0) (rawPathFlow (FFNetwork X hX) (fun _ _ => 0) rawPath1)) 1 0
      rw [h_flow, h_aug]
      unfold cycleInvariant; simp only [rawResCap, FFNetwork, expectedResCap, Fin.isValue,
        zero_add, tsub_self, pow_zero, sub_self, pow_one, sub_zero,
        add_sub_cancel_right, Nat.reduceAdd]
      intro u v; cases u <;> cases v <;> grind
    · -- Step 0 → 1
      right; right; left; use m
      have hk : 2 * m + 1 ≥ 1 := by omega
      have h_path : cycleChoice (4 * m + 1) = rawPath2 := by
        have h_def : cycleChoice (4 * m + 1) = match (4 * m) % 4 with
          | 0 => rawPath2 | 1 => rawPath3 | 2 => rawPath2 | _ => rawPath4 := rfl
        rw [h_def]; norm_num
      have h_next := step0_to_1 X hX (ffRawFlows X hX (4 * m + 1)) (2 * m + 1) hk h
      simp only [← fold (4 * m + 1) rawPath2 h_path, Fin.isValue, true_and]; exact h_next
    · -- Step 1 → 2
      right; right; right; left; use m
      have hk : 2 * m + 1 ≥ 1 := by omega
      have h_path : cycleChoice (4 * m + 2) = rawPath3 := by
        have h_def : cycleChoice (4 * m + 2) = match (4 * m + 1) % 4 with
          | 0 => rawPath2 | 1 => rawPath3 | 2 => rawPath2 | _ => rawPath4 := rfl
        rw [h_def]; norm_num
      have h_next := step1_to_2 X hX (ffRawFlows X hX (4 * m + 2)) (2 * m + 1) hk h
      simp only [← fold (4 * m + 2) rawPath3 h_path, Fin.isValue, true_and]; exact h_next
    · -- Step 2 → 3
      right; right; right; right; use m
      have hk : 2 * m + 1 ≥ 1 := by omega
      have h_path : cycleChoice (4 * m + 3) = rawPath2 := by
        have h_def : cycleChoice (4 * m + 3) = match (4 * m + 2) % 4 with
          | 0 => rawPath2 | 1 => rawPath3 | 2 => rawPath2 | _ => rawPath4 := rfl
        rw [h_def]; norm_num
      have h_next := step2_to_3 X hX (ffRawFlows X hX (4 * m + 3)) (2 * m + 1) hk h
      simp only [← fold (4 * m + 3) rawPath2 h_path, Fin.isValue, true_and]; exact h_next
    · -- Step 3 → 0 (next cycle)
      right; left; use m + 1
      have hk : 2 * m + 1 ≥ 1 := by omega
      have h_path : cycleChoice (4 * m + 4) = rawPath4 := by
        have h_def : cycleChoice (4 * m + 4) = match (4 * m + 3) % 4 with
          | 0 => rawPath2 | 1 => rawPath3 | 2 => rawPath2 | _ => rawPath4 := rfl
        rw [h_def]; norm_num
      have h_next := step3_to_0 X hX (ffRawFlows X hX (4 * m + 4)) (2 * m + 1) hk h
      simp only [Nat.add_right_cancel_iff, ← fold (4 * m + 4) rawPath4 h_path, Fin.isValue]; trivial

lemma ffState_induction (n : ℕ) :
    cycleInvariant X hX (ffRawFlows X hX (4 * n + 1)) (2 * n + 1) 0 := by
  rcases ffRawFlows_invariant X hX (4 * n + 1) with
    h | ⟨m, hm, hc⟩ | ⟨m, hm, _⟩ | ⟨m, hm, _⟩ | ⟨m, hm, _⟩
  · omega
  · have : m = n := by omega
    subst this; exact hc
  all_goals omega


/-- The raw residual capacity function is definitionally equal to the capacity
    of the formalized ResidualNetwork. -/
lemma rawResCap_eq_residualCap {V : Type*} [Fintype V] (G : FlowNetwork V)
    (F : RelaxedFlow G.toSTVertices) (h_valid : ValidFlow G F) (u v : V) :
    rawResCap G F.f u v = (ResidualNetwork G F h_valid).c u v := by
  unfold rawResCap ResidualNetwork
  rfl

/-- If a path is valid in the raw sense, its raw bottleneck equals the formal
    bottleneck in the residual network. -/
lemma rawBottleneck_eq_formal_bottleneck {V : Type*} [Fintype V] [DecidableEq V]
    (G : FlowNetwork V) (F : RelaxedFlow G.toSTVertices) (h_valid : ValidFlow G F)
    (p : uvPath G.s G.t) :
    rawBottleneck G F.f p = p.bottleneck (ResidualNetwork G F h_valid) G.source_not_sink := by
  unfold rawBottleneck uvPath.bottleneck
  rfl

open FFVert in
lemma expectedResCap_pos (X : ℝ) (hX : X > 2) (k : ℕ) (step : Fin 4) (p : uvPath s t)
    (h_path : p = match step with
      | 0 => rawPath2
      | 1 => rawPath3
      | 2 => rawPath2
      | 3 => rawPath4) :
    ∀ (i : ℕ) (h : i < p.verts.length - 1),
        expectedResCap X k step p.verts[i] p.verts[i+1] > 0 := by
  -- Hoist all arithmetic facts once; linarith picks them up in every branch
  have hρ  := ρ_pos
  have hρ1 := ρ_lt_1
  have hpow  : ∀ n : ℕ, 0 < ρ ^ n   := fun n => pow_pos hρ n
  have hle   : ∀ n : ℕ, ρ ^ (n + 1) ≤ ρ ^ n :=
    fun n => pow_le_pow_of_le_one hρ.le hρ1.le (Nat.le_succ n)
  intro i hi
  fin_cases step <;> subst h_path
  · -- step = 0 : p = rawPath2 = [s, d, c, b, a, t]  (5 edges)
    simp only [rawPath2, List.length_cons, List.length_nil] at hi
    interval_cases i <;>
      simp only [rawPath2, List.getElem_cons_zero, List.getElem_cons_succ,
                 expectedResCap] <;>
      linarith [hpow k, hpow (k - 1), hle k, hle (k - 1)]
  · -- step = 1 : p = rawPath3 = [s, b, c, d, t]  (4 edges)
    simp only [rawPath3, List.length_cons, List.length_nil] at hi
    interval_cases i <;>
      simp only [rawPath3, List.getElem_cons_zero, List.getElem_cons_succ,
                 expectedResCap] <;>
      linarith [hpow k, hpow (k - 1), hpow (k + 1), hle k, hle (k - 1)]
  · -- step = 2 : p = rawPath2 again  (5 edges)
    simp only [rawPath2, List.length_cons, List.length_nil] at hi
    interval_cases i <;>
      simp only [rawPath2, List.getElem_cons_zero, List.getElem_cons_succ,
                 expectedResCap] <;>
      linarith [hpow k, hpow (k - 1), hpow (k + 1), hle k, hle (k - 1), hle (k + 1)]
  · -- step = 3 : p = rawPath4 = [s, a, b, c, t]  (4 edges)
    simp only [rawPath4, List.length_cons, List.length_nil] at hi
    interval_cases i <;>
      simp only [rawPath4, List.getElem_cons_zero, List.getElem_cons_succ,
                 expectedResCap] <;>
      linarith [hpow k, hpow (k + 1), hle k]

/-- If the cycle invariant holds for a step, the chosen path is a valid augmentingPath. -/
noncomputable def step_as_augmentingPath
    (F : RelaxedFlow (FFNetwork X hX).toSTVertices) (h_valid : ValidFlow (FFNetwork X hX) F)
    (k : ℕ) (step : Fin 4) (p : uvPath FFVert.s FFVert.t)
    (h_path : p = match step with
      | 0 => rawPath2
      | 1 => rawPath3
      | 2 => rawPath2
      | 3 => rawPath4)
    (h_inv : cycleInvariant X hX F.f k step) :
    augmentingPath (ResidualNetwork (FFNetwork X hX) F h_valid) := {
  touvPath := p
  valid := by
    intro i h_len
    rw [← rawResCap_eq_residualCap (FFNetwork X hX) F h_valid]
    have h_eq := h_inv p.verts[i] p.verts[i+1]
    rw [h_eq]
    exact expectedResCap_pos X hX k step p h_path i h_len
}

/-- Main Theorem: At each step, the chosen path is a valid augmenting path
    whose formal Flow_value equals its bottleneck. -/
theorem step_flow_value_eq_bottleneck
    (F : RelaxedFlow (FFNetwork X hX).toSTVertices)
    (h_valid : ValidFlow (FFNetwork X hX) F)
    (k : ℕ) (step : Fin 4) (p : uvPath FFVert.s FFVert.t)
    (h_path : p = match step with
      | 0 => rawPath2
      | 1 => rawPath3
      | 2 => rawPath2
      | 3 => rawPath4)
    (h_inv : cycleInvariant X hX F.f k step) :
    let augPath := step_as_augmentingPath X hX F h_valid k step p h_path h_inv
    Flow_value (FFNetwork X hX).toSTVertices augPath.toFlow =
    augPath.bottleneck (ResidualNetwork (FFNetwork X hX) F h_valid) (FFNetwork X hX).source_not_sink
     := by
  intro augPath
  exact (bottleneck_eq_flow augPath).symm

def convertFlow {V : Type*} [Fintype V] {G : FlowNetwork V}
  {F : RelaxedFlow G.toSTVertices} {hF : ValidFlow G F}
  (p_flow : RelaxedFlow (ResidualNetwork G F hF).toSTVertices) : RelaxedFlow G.toSTVertices :=
  {
    f := p_flow.f
    nonneg_flow := p_flow.nonneg_flow
    conservation := p_flow.conservation
    no_edges_in_source := p_flow.no_edges_in_source
    no_edges_out_sink := p_flow.no_edges_out_sink
  }

lemma ffRawFlows_valid_step (X : ℝ) (hX : X > 2) (n : ℕ) :
  rawPathValid (FFNetwork X hX) (ffRawFlows X hX n) (cycleChoice n) := by
  rcases ffRawFlows_invariant X hX n with
    rfl | ⟨m, rfl, h⟩ | ⟨m, rfl, h⟩ | ⟨m, rfl, h⟩ | ⟨m, rfl, h⟩
  · intro i h_len
    simp only [cycleChoice, rawPath1, List.length_cons, List.length_nil] at h_len ⊢
    interval_cases i
    · change (FFNetwork X hX).c FFVert.s FFVert.b - 0 + 0 > 0; simp [FFNetwork]; linarith [hX]
    · change (FFNetwork X hX).c FFVert.b FFVert.c - 0 + 0 > 0; simp [FFNetwork]
    · change (FFNetwork X hX).c FFVert.c FFVert.t - 0 + 0 > 0; simp [FFNetwork]; linarith [hX]
  · intro i h_len
    have h_path : cycleChoice (4 * m + 1) = rawPath2 := by
      have h_def : cycleChoice (4 * m + 1) = match (4 * m) % 4 with
        | 0 => rawPath2 | 1 => rawPath3 | 2 => rawPath2 | _ => rawPath4 := rfl
      rw [h_def]; norm_num
    have heq := h (cycleChoice (4 * m + 1)).verts[i] (cycleChoice (4 * m + 1)).verts[i+1]
    rw [heq]
    exact expectedResCap_pos X hX _ 0 _ h_path i h_len
  · intro i h_len
    have h_path : cycleChoice (4 * m + 2) = rawPath3 := by
      have h_def : cycleChoice (4 * m + 2) = match (4 * m + 1) % 4 with
        | 0 => rawPath2 | 1 => rawPath3 | 2 => rawPath2 | _ => rawPath4 := rfl
      rw [h_def]; norm_num
    rw [h _ _]
    exact expectedResCap_pos X hX _ 1 _ h_path i h_len
  · intro i h_len
    have h_path : cycleChoice (4 * m + 3) = rawPath2 := by
      have h_def : cycleChoice (4 * m + 3) = match (4 * m + 2) % 4 with
        | 0 => rawPath2 | 1 => rawPath3 | 2 => rawPath2 | _ => rawPath4 := rfl
      rw [h_def]; norm_num
    rw [h _ _]
    exact expectedResCap_pos X hX _ 2 _ h_path i h_len
  · intro i h_len
    have h_path : cycleChoice (4 * m + 4) = rawPath4 := by
      have h_def : cycleChoice (4 * m + 4) = match (4 * m + 3) % 4 with
        | 0 => rawPath2 | 1 => rawPath3 | 2 => rawPath2 | _ => rawPath4 := rfl
      rw [h_def]; norm_num
    rw [h _ _]
    exact expectedResCap_pos X hX _ 3 _ h_path i h_len

lemma augPath_toFlow_eq_rawPathFlow (X : ℝ) (hX : X > 2) (n : ℕ)
    (F : RelaxedFlow (FFNetwork X hX).toSTVertices)
    (h_valid : ValidFlow (FFNetwork X hX) F)
    (augPath : augmentingPath (ResidualNetwork (FFNetwork X hX) F h_valid))
    (h_path : augPath.touvPath = cycleChoice n) :
    (convertFlow augPath.toFlow).f = rawPathFlow (FFNetwork X hX) F.f (cycleChoice n) := by
  have eq_b := rawBottleneck_eq_formal_bottleneck (FFNetwork X hX) F h_valid augPath.touvPath
  unfold convertFlow augmentingPath.toFlow pathFlow rawPathFlow
  ext u v
  dsimp only
  rw [← h_path]
  rw [eq_b]
  rfl

structure FFFlowState (X : ℝ) (hX : X > 2) (n : ℕ) where
  F : RelaxedFlow (FFNetwork X hX).toSTVertices
  h_valid : ValidFlow (FFNetwork X hX) F
  h_eq    : F.f = ffRawFlows X hX n

noncomputable def sequence_of_flows (X : ℝ) (hX : X > 2) : (n : ℕ) → FFFlowState X hX n
| 0 => ⟨trivial_flow _, valid_zero_flow _, rfl⟩
| n + 1 =>
  let ⟨Fn, h_Fn_valid, h_Fn_eq⟩ := sequence_of_flows X hX n
  let augPath : augmentingPath (ResidualNetwork (FFNetwork X hX) Fn h_Fn_valid) := {
    touvPath := cycleChoice n
    valid := by
      intro i h_len
      rw [← rawResCap_eq_residualCap (FFNetwork X hX) Fn h_Fn_valid]
      have h_raw_valid := ffRawFlows_valid_step X hX n
      rw [h_Fn_eq]
      exact h_raw_valid i h_len
  }
  let F' := Fn * convertFlow augPath.toFlow
  let h_valid' : ValidFlow (FFNetwork X hX) F' :=
      valid_augmentation (FFNetwork X hX) Fn h_Fn_valid
        (convertFlow augPath.toFlow) augPath.valid_toFlow
  ⟨F', h_valid', by
    ext u v
    have heq := augPath_toFlow_eq_rawPathFlow X hX n Fn h_Fn_valid augPath rfl
    have h1 : (convertFlow augPath.toFlow).f u v
      = rawPathFlow (FFNetwork X hX) Fn.f (cycleChoice n) u v := by
      rw [heq]
    have h2 : (convertFlow augPath.toFlow).f v u
      = rawPathFlow (FFNetwork X hX) Fn.f (cycleChoice n) v u := by
      rw [heq]
    change max (Fn.f u v + (convertFlow augPath.toFlow).f u v
                  - Fn.f v u - (convertFlow augPath.toFlow).f v u) 0 = _
    rw [h1, h2, h_Fn_eq]
    have h_step : ffRawFlows X hX (n + 1) u v = max (ffRawFlows X hX n u v + rawPathFlow
      (FFNetwork X hX) (ffRawFlows X hX n) (cycleChoice n) u v - ffRawFlows X hX n v u - rawPathFlow
      (FFNetwork X hX) (ffRawFlows X hX n) (cycleChoice n) v u) 0 := rfl
    rw [h_step]
  ⟩

noncomputable def ffFlowValues (X : ℝ) (hX : X > 2) : ℕ → ℝ :=
  fun n => Flow_value (FFNetwork X hX).toSTVertices (sequence_of_flows X hX n).F

/-- The limit the FF flow sequence converges to, per the textbook:
    1 + ∑ i=1..∞ 2ρⁱ = 2/(1-ρ) - 1 = 2 + √5 ≈ 4.236 -/
noncomputable def ffFlowLimit : ℝ := 2 + Real.sqrt 5

lemma geom_series_eval : (∑' i : ℕ, 2 * ρ ^ (i + 1)) = (2 * ρ) * (1 - ρ)⁻¹ := by
  -- Rewrite ρ^(i+1) as ρ * ρ^i to isolate the exponent i
  have h_rewrite : (fun (i : ℕ) => 2 * ρ ^ (i + 1)) = fun i => (2 * ρ) * ρ ^ i := by
    ring_nf
  rw [h_rewrite]
  -- Pull the constant (2 * ρ) out of the topological sum
  rw [tsum_mul_left]
  -- Apply the standard geometric series formula for ρ < 1
  have h_geom : (∑' i : ℕ, ρ ^ i) = (1 - ρ)⁻¹ := by
    apply tsum_geometric_of_lt_one
    · exact ρ_pos.le
    · exact ρ_lt_1
  rw [h_geom]

lemma ffFlowLimit_lt_five : ffFlowLimit < 5 := by
  unfold ffFlowLimit
  have : Real.sqrt 5 < 3 := by
    rw [show (3 : ℝ) = Real.sqrt 9 by ring]
    exact Real.sqrt_lt_sqrt (by positivity) (by norm_num)
  linarith

noncomputable def ffMaxFlow :
    RelaxedFlow (FFNetwork X hX).toSTVertices where
  f u v := match u, v with
    | s, a => X
    | s, b => 1
    | s, d => X
    | b, c => 1
    | a, t => X
    | c, t => 1
    | d, t => X
    | _, _ => 0
  nonneg_flow := by
    intro u v; fin_cases u <;> fin_cases v <;> linarith
  conservation := by
    intro v vns vnt
    -- Do this, because otherwise it will think s ≠ source
    simp only [FFNetwork] at vns vnt
    have huniv : Finset.univ (α := FFVert) = {s, t, a, b, c, d} := by decide
    fin_cases v <;> simp_all [mk_out, mk_in]

  no_edges_in_source := by
    intro u; fin_cases u <;> simp [FFNetwork]
  no_edges_out_sink := by
    intro u; fin_cases u <;> simp [FFNetwork]

open FFVert in
lemma ffMaxFlow_valid (X : ℝ) (hX : X > 2) :
    ValidFlow (FFNetwork X hX) (ffMaxFlow X hX) := by
  intro u v
  fin_cases u <;> fin_cases v <;>
    simp [ffMaxFlow, FFNetwork] <;>
    linarith [ρ_pos, ρ_lt_1]

open FFVert in
lemma ffMaxFlow_value (X : ℝ) (hX : X > 2) :
    Flow_value (FFNetwork X hX).toSTVertices (ffMaxFlow X hX) = 2 * X + 1 := by
  simp only [Flow_value, mk_out, ffMaxFlow, FFNetwork]
  simp only [show Finset.univ (α := FFVert) = {s, t, a, b, c, d} from by decide]
  simp [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton]
  ring

lemma maxFlow_ge_ffMaxFlow (X : ℝ) (hX : X > 2)
    (F : RelaxedFlow (FFNetwork X hX).toSTVertices)
    (hF : is_max_flow F) :
    Flow_value (FFNetwork X hX).toSTVertices (ffMaxFlow X hX) ≤
    Flow_value (FFNetwork X hX).toSTVertices F :=
  hF.2 (ffMaxFlow X hX) (ffMaxFlow_valid X hX)

lemma maxFlow_value_ge (X : ℝ) (hX : X > 2)
    (F : RelaxedFlow (FFNetwork X hX).toSTVertices)
    (hF : is_max_flow F) :
    2 * X + 1 ≤ Flow_value (FFNetwork X hX).toSTVertices F := by
  have h := maxFlow_ge_ffMaxFlow X hX F hF
  rw [ffMaxFlow_value X hX] at h
  exact h

/-- The true maximum flow in FFNetwork is 2X + 1, which exceeds 5 when X > 2. -/
lemma ffNetwork_maxFlow_value (X : ℝ) (hX : X > 2) : 2 * X + 1 > 5 := by linarith

noncomputable def expectedFlowValues (X : ℝ) (hX : X > 2) : ℕ → ℝ
  | 0 => 0
  | (n + 1) => expectedFlowValues X hX n
                + rawBottleneck (FFNetwork X hX) (ffRawFlows X hX n) (cycleChoice n)

lemma Flow_value_convertFlow_eq_bottleneck (X : ℝ) (hX : X > 2)
    (F : RelaxedFlow (FFNetwork X hX).toSTVertices)
    (h_valid : ValidFlow (FFNetwork X hX) F)
    (augPath : augmentingPath (ResidualNetwork (FFNetwork X hX) F h_valid)) :
    Flow_value (FFNetwork X hX).toSTVertices (convertFlow augPath.toFlow) =
    augPath.touvPath.bottleneck (ResidualNetwork (FFNetwork X hX) F h_valid)
      (FFNetwork X hX).source_not_sink := by
  have hb := bottleneck_eq_flow augPath
  have : (ResidualNetwork (FFNetwork X hX) F h_valid).s = (FFNetwork X hX).s := rfl
  unfold Flow_value convertFlow
  unfold Flow_value at hb
  rw [hb, this]

lemma ffFlowValues_eq_expected (X : ℝ) (hX : X > 2) (n : ℕ) :
  ffFlowValues X hX n = expectedFlowValues X hX n := by
  induction n with
  | zero =>
    change Flow_value _ (trivial_flow _) = 0
    exact zero_trivial_flow _
  | succ n ih =>
    unfold ffFlowValues expectedFlowValues
    dsimp [sequence_of_flows]
    rw [add_flow]
    unfold ffFlowValues at ih
    rw [ih]
    congr 1
    rw [Flow_value_convertFlow_eq_bottleneck X hX
      (sequence_of_flows X hX n).F (sequence_of_flows X hX n).h_valid]
    change uvPath.bottleneck (ResidualNetwork (FFNetwork X hX) (sequence_of_flows X hX n).F _ )
      (cycleChoice n) _ = _
    have heq := rawBottleneck_eq_formal_bottleneck (FFNetwork X hX) (sequence_of_flows X hX n).F
      (sequence_of_flows X hX n).h_valid (cycleChoice n)
    refine Eq.trans heq.symm ?_
    congr 2
    exact (sequence_of_flows X hX n).h_eq

lemma expectedFlowValues_eq_sum (X : ℝ) (hX : X > 2) (n : ℕ) :
    expectedFlowValues X hX n =
    ∑ i ∈ Finset.range n,
      rawBottleneck (FFNetwork X hX) (ffRawFlows X hX i) (cycleChoice i) := by
  induction n with
  | zero => simp [expectedFlowValues]
  | succ n ih =>
    simp only [expectedFlowValues, Finset.sum_range_succ, ← ih]
lemma rawBottleneck_n0 (X : ℝ) (hX : X > 2) :
    rawBottleneck (FFNetwork X hX) (ffRawFlows X hX 0) (cycleChoice 0) = 1 := by
  simp only [cycleChoice, ffRawFlows, rawFFFlows]
  simp [rawBottleneck, rawPath1, rawResCap, FFNetwork, List.min,
        List.zipWith, List.foldl]
  linarith [hX]

lemma rawBottleneck_4m1 (X : ℝ) (hX : X > 2) (m : ℕ) :
    rawBottleneck (FFNetwork X hX) (ffRawFlows X hX (4 * m + 1)) (cycleChoice (4 * m + 1)) =
    ρ ^ (2 * m + 1) := by
  have h_path : cycleChoice (4 * m + 1) = rawPath2 := by
    simp [cycleChoice]
  rw [h_path]
  have hc := ffState_induction X hX m
  exact rawBottleneck_path2_1 X hX _ _ hc

lemma rawBottleneck_4m2 (X : ℝ) (hX : X > 2) (m : ℕ) :
    rawBottleneck (FFNetwork X hX) (ffRawFlows X hX (4 * m + 2)) (cycleChoice (4 * m + 2)) =
    ρ ^ (2 * m + 1) := by
  have h_path : cycleChoice (4 * m + 2) = rawPath3 := by
    simp [cycleChoice]
  rw [h_path]
  have hc : cycleInvariant X hX (ffRawFlows X hX (4 * m + 2)) (2 * m + 1) 1 := by
    have h0 := ffState_induction X hX m
    have h_path2 : cycleChoice (4 * m + 1) = rawPath2 := by simp [cycleChoice]
    have fold : rawAugment (ffRawFlows X hX (4 * m + 1))
        (rawPathFlow (FFNetwork X hX) (ffRawFlows X hX (4 * m + 1)) rawPath2) =
        ffRawFlows X hX (4 * m + 2) := by
      change _ = rawAugment (ffRawFlows X hX (4 * m + 1))
          (rawPathFlow (FFNetwork X hX) (ffRawFlows X hX (4 * m + 1)) (cycleChoice (4 * m + 1)))
      rw [h_path2]
    rw [← fold]
    exact step0_to_1 X hX _ _ (by omega) h0
  exact rawBottleneck_path3 X hX _ _ (by omega) hc

lemma rawBottleneck_4m3 (X : ℝ) (hX : X > 2) (m : ℕ) :
    rawBottleneck (FFNetwork X hX) (ffRawFlows X hX (4 * m + 3)) (cycleChoice (4 * m + 3)) =
    ρ ^ (2 * m + 2) := by
  have h_path : cycleChoice (4 * m + 3) = rawPath2 := by
    simp [cycleChoice]
  rw [h_path]
  have hc2 : cycleInvariant X hX (ffRawFlows X hX (4 * m + 3)) (2 * m + 1) 2 := by
    have h1 : cycleInvariant X hX (ffRawFlows X hX (4 * m + 2)) (2 * m + 1) 1 := by
      have h0 := ffState_induction X hX m
      have h_path2 : cycleChoice (4 * m + 1) = rawPath2 := by simp [cycleChoice]
      have fold : rawAugment (ffRawFlows X hX (4 * m + 1))
          (rawPathFlow (FFNetwork X hX) (ffRawFlows X hX (4 * m + 1)) rawPath2) =
          ffRawFlows X hX (4 * m + 2) := by
        change _ = rawAugment (ffRawFlows X hX (4 * m + 1))
            (rawPathFlow (FFNetwork X hX) (ffRawFlows X hX (4 * m + 1)) (cycleChoice (4 * m + 1)))
        rw [h_path2]
      rw [← fold]; exact step0_to_1 X hX _ _ (by omega) h0
    have h_path3 : cycleChoice (4 * m + 2) = rawPath3 := by simp [cycleChoice]
    have fold : rawAugment (ffRawFlows X hX (4 * m + 2))
        (rawPathFlow (FFNetwork X hX) (ffRawFlows X hX (4 * m + 2)) rawPath3) =
        ffRawFlows X hX (4 * m + 3) := by
      change _ = rawAugment (ffRawFlows X hX (4 * m + 2))
          (rawPathFlow (FFNetwork X hX) (ffRawFlows X hX (4 * m + 2)) (cycleChoice (4 * m + 2)))
      rw [h_path3]
    rw [← fold]; exact step1_to_2 X hX _ _ (by omega) h1
  have := rawBottleneck_path2_2 X hX _ _ (by omega) hc2
  convert this using 2

lemma rawBottleneck_4m4 (X : ℝ) (hX : X > 2) (m : ℕ) :
    rawBottleneck (FFNetwork X hX) (ffRawFlows X hX (4 * m + 4)) (cycleChoice (4 * m + 4)) =
    ρ ^ (2 * m + 2) := by
  have h_path : cycleChoice (4 * m + 4) = rawPath4 := by
    simp [cycleChoice]
  rw [h_path]
  -- Need step-3 invariant
  have hc3 : cycleInvariant X hX (ffRawFlows X hX (4 * m + 4)) (2 * m + 1) 3 := by
    -- Build up through steps 0→1→2→3
    have h0 := ffState_induction X hX m
    have h1 : cycleInvariant X hX (ffRawFlows X hX (4 * m + 2)) (2 * m + 1) 1 := by
      have h_path2 : cycleChoice (4 * m + 1) = rawPath2 := by simp [cycleChoice]
      have fold : rawAugment (ffRawFlows X hX (4 * m + 1))
          (rawPathFlow (FFNetwork X hX) (ffRawFlows X hX (4 * m + 1)) rawPath2) =
          ffRawFlows X hX (4 * m + 2) := by
        change _ = rawAugment (ffRawFlows X hX (4 * m + 1))
            (rawPathFlow (FFNetwork X hX) (ffRawFlows X hX (4 * m + 1)) (cycleChoice (4 * m + 1)))
        rw [h_path2]
      rw [← fold]; exact step0_to_1 X hX _ _ (by omega) h0
    have h2 : cycleInvariant X hX (ffRawFlows X hX (4 * m + 3)) (2 * m + 1) 2 := by
      have h_path3 : cycleChoice (4 * m + 2) = rawPath3 := by simp [cycleChoice]
      have fold : rawAugment (ffRawFlows X hX (4 * m + 2))
          (rawPathFlow (FFNetwork X hX) (ffRawFlows X hX (4 * m + 2)) rawPath3) =
          ffRawFlows X hX (4 * m + 3) := by
        change _ = rawAugment (ffRawFlows X hX (4 * m + 2))
            (rawPathFlow (FFNetwork X hX) (ffRawFlows X hX (4 * m + 2)) (cycleChoice (4 * m + 2)))
        rw [h_path3]
      rw [← fold]; exact step1_to_2 X hX _ _ (by omega) h1
    have h_path2b : cycleChoice (4 * m + 3) = rawPath2 := by simp [cycleChoice]
    have fold : rawAugment (ffRawFlows X hX (4 * m + 3))
        (rawPathFlow (FFNetwork X hX) (ffRawFlows X hX (4 * m + 3)) rawPath2) =
        ffRawFlows X hX (4 * m + 4) := by
      change _ = rawAugment (ffRawFlows X hX (4 * m + 3))
          (rawPathFlow (FFNetwork X hX) (ffRawFlows X hX (4 * m + 3)) (cycleChoice (4 * m + 3)))
      rw [h_path2b]
    rw [← fold]; exact step2_to_3 X hX _ _ (by omega) h2
  have := rawBottleneck_path4 X hX _ _ (by omega) hc3
  convert this using 2

-- Helper lemma: Peels off the last 4 elements of the sum cleanly
lemma sum_peel_4 (f : ℕ → ℝ) (k : ℕ) :
  ∑ i ∈ Finset.range (k + 4), f i =
  (∑ i ∈ Finset.range k, f i) + f k + f (k + 1) + f (k + 2) + f (k + 3) := by
  -- sum_range_succ automatically peels off the `n` from `range (n + 1)`
  rw [Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ]

/-- The explicit bottleneck for ANY arbitrary step n -/
noncomputable def explicitBottleneck (n : ℕ) : ℝ :=
  if n = 0 then 1 else ρ ^ ((n + 1) / 2) -- < integer div

/-- The total flow sum after ANY arbitrary step N -/
noncomputable def explicitFlowSum (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, explicitBottleneck i

/-- Step 1: Prove the individual sequence terms match for any i -/
lemma rawBottleneck_eq_explicitBottleneck (X : ℝ) (hX : X > 2) (i : ℕ) :
    rawBottleneck (FFNetwork X hX) (ffRawFlows X hX i) (cycleChoice i) =
    explicitBottleneck i := by
  rcases i with _ | i'
  · simp only [explicitBottleneck, ↓reduceIte]
    exact rawBottleneck_n0 X hX
  · -- Unfold explicitBottleneck and cleanly eliminate the if-branch using omega
    rw [explicitBottleneck]
    have h_pos : i' + 1 ≠ 0 := by omega
    rw [if_neg h_pos]
    -- Extract the quotient (m) and remainder (k)
    obtain ⟨m, k, hk_ge, hk_le, heq⟩ : ∃ m k, 1 ≤ k ∧ k ≤ 4 ∧ i' + 1 = 4 * m + k := by
      use (i' + 1 - 1) / 4, (i' + 1 - 1) % 4 + 1
      omega
    -- Use 'rw' instead of 'subst' since (i' + 1) is a compound expression
    rw [heq]
    interval_cases k
    · have h_div : (4 * m + 1 + 1) / 2 = 2 * m + 1 := by omega
      rw [h_div]
      exact rawBottleneck_4m1 X hX m
    · have h_div : (4 * m + 2 + 1) / 2 = 2 * m + 1 := by omega
      rw [h_div]
      exact rawBottleneck_4m2 X hX m
    · have h_div : (4 * m + 3 + 1) / 2 = 2 * m + 2 := by omega
      rw [h_div]
      exact rawBottleneck_4m3 X hX m
    · have h_div : (4 * m + 4 + 1) / 2 = 2 * m + 2 := by omega
      rw [h_div]
      exact rawBottleneck_4m4 X hX m

/-- Step 2: The final theorem proving the recursive sum equals the explicit sum -/
theorem expectedFlowValues_eq_explicitFlowSum (X : ℝ) (hX : X > 2) (n : ℕ) :
    expectedFlowValues X hX n = explicitFlowSum n := by
  induction n with
  | zero =>
    simp [expectedFlowValues, explicitFlowSum]
  | succ n ih =>
    -- Unfold the expectedFlowValues recursive definition
    rw [expectedFlowValues]
    -- Substitute the induction hypothesis
    rw [ih]
    -- Unfold explicitFlowSum into its range sum to peel off the last term
    simp only [explicitFlowSum, Finset.sum_range_succ]
    -- Substitute our term-by-term lemma
    rw [rawBottleneck_eq_explicitBottleneck X hX n]

/-- Helper lemma: Peels off the last 2 elements of the sum cleanly -/
lemma sum_peel_2 (f : ℕ → ℝ) (k : ℕ) :
    ∑ i ∈ Finset.range (k + 2), f i =
    (∑ i ∈ Finset.range k, f i) + f k + f (k + 1) := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ]

/-- The partial sum N = 2M + 1 exactly equals 1 + 2 * sum_{i=1}^M ρ^i -/
lemma explicitFlowSum_odd (M : ℕ) :
    explicitFlowSum (2 * M + 1) = 1 + ∑ i ∈ Finset.range M, (2 * ρ ^ (i + 1)) := by
  induction M with
  | zero =>
    -- Base case: N = 1, sum should be just 1 (the step 0 bottleneck)
    simp [explicitFlowSum, explicitBottleneck]
  | succ M ih =>
    -- Rewrite the index to expose the `+ 2` offset
    have h_idx : 2 * (M + 1) + 1 = (2 * M + 1) + 2 := by omega
    -- Unfold explicitFlowSum and peel off the last two terms
    unfold explicitFlowSum
    rw [h_idx, sum_peel_2]
    -- Fold the earlier terms back into explicitFlowSum
    have h_fold : (∑ i ∈ Finset.range (2 * M + 1), explicitBottleneck i) =
      explicitFlowSum (2 * M + 1) := rfl
    rw [h_fold, ih]
    -- Evaluate the two newly peeled bottlenecks: k = 2M + 1 and k = 2M + 2
    have h_bot1 : explicitBottleneck (2 * M + 1) = ρ ^ (M + 1) := by
      unfold explicitBottleneck
      have h_pos : 2 * M + 1 ≠ 0 := by omega
      rw [if_neg h_pos]
      have h_div : (2 * M + 1 + 1) / 2 = M + 1 := by omega
      rw [h_div]
    have h_bot2 : explicitBottleneck (2 * M + 2) = ρ ^ (M + 1) := by
      unfold explicitBottleneck
      have h_pos : 2 * M + 2 ≠ 0 := by omega
      rw [if_neg h_pos]
      have h_div : (2 * M + 2 + 1) / 2 = M + 1 := by omega
      rw [h_div]
    rw [h_bot1, h_bot2]
    -- Expand the geometric sum on the right-hand side
    rw [Finset.sum_range_succ]
    -- It's all algebra from here
    ring

lemma explicitFlowSum_even (M : ℕ) (hM : M > 0) :
    explicitFlowSum (2 * M) = explicitFlowSum (2 * M - 1) + ρ ^ M := by
  -- Expose the successor relationship: 2*M is exactly one more than 2*M - 1
  have hk : 2 * M = (2 * M - 1) + 1 := by omega
  -- Unfold the definition of the sum on both sides
  unfold explicitFlowSum
  -- Rewrite ONLY the 2*M on the left-hand side
  rw [hk]
  -- Peel off the last element of the sum on the left-hand side
  rw [Finset.sum_range_succ]
  -- The sums on both sides are now identical.
  -- We just need to prove the remaining terms (the bottleneck and ρ^M) are equal.
  congr 1
  -- Prove that explicitBottleneck (2 * M - 1) = ρ ^ M
  unfold explicitBottleneck
  have h_pos : 2 * M - 1 ≠ 0 := by omega
  rw [if_neg h_pos]
  -- Resolve the integer division
  have h_div : (2 * M - 1 + 1) / 2 = M := by omega
  rw [h_div]

/-- Helper lemma: Prove the geometric series is summable -/
lemma geom_series_summable : Summable (fun (i : ℕ) => 2 * ρ ^ (i + 1)) := by
  -- Isolate the exponent i by rewriting ρ^(i+1) as ρ * ρ^i
  have h_rewrite : (fun (i : ℕ) => 2 * ρ ^ (i + 1)) = fun i => (2 * ρ) * ρ ^ i := by
    ext i
    ring
  rw [h_rewrite]
  -- A constant multiplied by a summable sequence is summable
  apply Summable.mul_left
  -- The core geometric series is summable because 0 ≤ ρ < 1
  apply summable_geometric_of_lt_one ρ_pos.le ρ_lt_1

/-- The convergence of the odd-indexed partial sums -/
lemma explicitFlowSum_odd_tendsto :
    Tendsto (fun M => explicitFlowSum (2 * M + 1)) atTop (𝓝 (1 + (2 * ρ) * (1 - ρ)⁻¹)) := by
  -- Rewrite the target using your exact odd sum formula
  simp_rw [explicitFlowSum_odd]
  -- Extract the HasSum property (which is definitionally a Tendsto)
  have h_hasSum := geom_series_summable.hasSum
  -- Substitute the exact evaluated tsum value from your earlier lemma
  rw [geom_series_eval] at h_hasSum
  -- Convert HasSum (which operates on generalized sets) to a Tendsto over Nat ranges
  have h_tendsto := HasSum.tendsto_sum_nat h_hasSum
  -- The limit of (1 + sum) is the limit of the sum plus 1
  exact Tendsto.add tendsto_const_nhds h_tendsto

/-- Given that the 2M-1 sequence converges to L, the 2M sequence converges to L as well. -/
lemma explicitFlowSum_even_tendsto {L : ℝ}
    (h_prev : Tendsto (fun M => explicitFlowSum (2 * M - 1)) atTop (𝓝 L)) :
    Tendsto (fun M => explicitFlowSum (2 * M)) atTop (𝓝 L) := by
  -- 1. Prove ρ ^ M converges to 0 as M → ∞
  have h_rho : Tendsto (fun M => ρ ^ M) atTop (𝓝 0) := by
    exact tendsto_pow_atTop_nhds_zero_of_lt_one ρ_pos.le ρ_lt_1
  -- 2. Add the two limits together: L + 0 = L
  have h_add := Tendsto.add h_prev h_rho
  rw [add_zero] at h_add
  -- 3. Show that the known expression is eventually equal to the target expression.
  -- We use `.symm` to place our target function on the RHS.
  have h_eq : (fun M => explicitFlowSum (2 * M - 1) + ρ ^ M)
      =ᶠ[atTop] (fun M => explicitFlowSum (2 * M)) := by
    filter_upwards [eventually_gt_atTop 0] with M hM
    exact (explicitFlowSum_even M hM).symm
  -- 4. Substitute the eventual equality into our target limit
  exact Tendsto.congr' h_eq h_add

/-- Shifting the odd sequence index by 1 preserves its limit. -/
lemma explicitFlowSum_odd_minus_one_tendsto {L : ℝ}
    (h_odd : Tendsto (fun M => explicitFlowSum (2 * M + 1)) atTop (𝓝 L)) :
    Tendsto (fun M => explicitFlowSum (2 * M - 1)) atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop] at *
  intro ε hε
  rcases h_odd ε hε with ⟨N, hN⟩
  use N + 1
  intro m hm
  have h_m : m - 1 ≥ N := by omega
  have h_eq : 2 * m - 1 = 2 * (m - 1) + 1 := by omega
  rw [h_eq]
  exact hN (m - 1) h_m

/-- Combining the even and odd limits to prove the entire sequence converges to L. -/
theorem explicitFlowSum_tendsto_of_even_odd {L : ℝ}
    (h_odd : Tendsto (fun M => explicitFlowSum (2 * M + 1)) atTop (𝓝 L))
    (h_even : Tendsto (fun M => explicitFlowSum (2 * M)) atTop (𝓝 L)) :
    Tendsto explicitFlowSum atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop] at *
  intro ε hε
  rcases h_even ε hε with ⟨Ne, hNe⟩
  rcases h_odd ε hε with ⟨No, hNo⟩
  -- Choose a ceiling index that satisfies both bounds
  use max (2 * Ne) (2 * No + 1)
  intro n hn
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · -- Case 1: n is even (m + m)
    have hm : m ≥ Ne := by omega
    -- Change the goal's (m + m) safely into (2 * m) so it matches hNe
    rw [← two_mul]
    exact hNe m hm
  · -- Case 2: n is odd (m + m + 1)
    have hm : m ≥ No := by omega
    -- Change the goal's (m + m + 1) safely into (2 * m + 1) so it matches hNo
    simp only [gt_iff_lt]
    exact hNo m hm

/-- The final master theorem putting it all together for your specific Ford-Fulkerson limit -/
theorem explicitFlowSum_converges :
    Tendsto explicitFlowSum atTop (𝓝 (1 + (2 * ρ) * (1 - ρ)⁻¹)) := by
  have h_odd := explicitFlowSum_odd_tendsto
  have h_minus_1 := explicitFlowSum_odd_minus_one_tendsto h_odd
  have h_even := explicitFlowSum_even_tendsto h_minus_1
  exact explicitFlowSum_tendsto_of_even_odd h_odd h_even

/-- Ford-Fulkerson with cycleChoice does not terminate, and the flow values it
    produces converge to ffFlowLimit, which can be made arbitrarily far below
    the true maximum flow 2X + 1 by choosing X large. -/
theorem ff_non_termination (X : ℝ) (hX : X > 2) :
    -- (1) The algorithm never terminates: every step has a valid augmenting path
    (∀ n : ℕ, rawPathValid (FFNetwork X hX) (ffRawFlows X hX n) (cycleChoice n)) ∧
    -- (2) The flow values converge to 2 + √5
    Filter.Tendsto (ffFlowValues X hX) Filter.atTop (nhds ffFlowLimit) ∧
    -- (3) The limit is strictly less than the true maximum flow
    ffFlowLimit < 2 * X + 1 := by
  refine ⟨?_, ?_, ?_⟩
  · exact ffRawFlows_valid_step X hX
  · -- Step 1: Rewrite ffFlowValues as explicitFlowSum pointwise
    have h_eq : ffFlowValues X hX = explicitFlowSum := by
      funext n
      rw [ffFlowValues_eq_expected X hX n, expectedFlowValues_eq_explicitFlowSum X hX n]
    -- Step 2: Show the geometric series limit equals ffFlowLimit = 2 + √5
    -- i.e. 1 + 2ρ·(1-ρ)⁻¹ = 2 + √5, using ρ = (√5-1)/2
    have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have h_lim_eq : (1 + (2 * ρ) * (1 - ρ)⁻¹) = ffFlowLimit := by
      unfold ffFlowLimit ρ
      -- The denominator 1 - (√5-1)/2 = (3-√5)/2 is nonzero since √5 ≠ 3
      have h_ne : (1 : ℝ) - (Real.sqrt 5 - 1) / 2 ≠ 0 := by
        intro h; nlinarith
      field_simp [h_ne]
      grind
    -- Step 3: Combine to get the desired convergence
    rw [h_eq, ← h_lim_eq]
    exact explicitFlowSum_converges
  · have := ffFlowLimit_lt_five
    linarith [ffNetwork_maxFlow_value X hX]
