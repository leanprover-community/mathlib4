import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Combinatorics.Quiver.MaxFlowMinCutAlt.MaxFlowMinCutAlt
import Mathlib.Tactic

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

/-- Residual capacity of (u,v) given flow F in FFNetwork. No ValidFlow required. -/
noncomputable def resCap (F : RelaxedFlow (FFNetwork X hX).toSTVertices)
    (u v : FFVert) : ℝ :=
  (FFNetwork X hX).c u v - F.f u v + F.f v u

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
  congr 1

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

open FFVert in
noncomputable def base_step_as_augmentingPath (X : ℝ) (hX : X > 2) :
    augmentingPath (ResidualNetwork (FFNetwork X hX)
      (trivial_flow (FFNetwork X hX).toSTVertices)
      (valid_zero_flow (FFNetwork X hX))) := {
  touvPath := rawPath1
  valid := by
    intro i h_len
    simp only [rawPath1, List.length_cons, List.length_nil] at h_len
    interval_cases i
    · -- i = 0: Edge (s, b)
      simp only [ResidualNetwork, FFNetwork, trivial_flow, sub_zero, add_zero, zero_add, gt_iff_lt]
      positivity
    · -- i = 1: Edge (b, c)
      simp [ResidualNetwork, FFNetwork, trivial_flow, rawPath1]
    · -- i = 2: Edge (c, t)
      simp only [ResidualNetwork, FFNetwork, trivial_flow, sub_zero, add_zero, Nat.reduceAdd,
        gt_iff_lt]
      positivity
}

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
