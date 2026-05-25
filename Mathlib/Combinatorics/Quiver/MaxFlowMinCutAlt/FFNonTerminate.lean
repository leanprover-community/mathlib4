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

/-- A candidate augmenting path: structurally a simple s→t path, no capacity constraint. -/
def CandidateAugPath {V : Type*} [Fintype V] (G : FlowNetwork V) :=
  uvPath G.s G.t

/-- Capacity-validity predicate for a candidate path in a given network. -/
def CandidateAugPath.IsValidIn {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (p : CandidateAugPath G) : Prop :=
  ∀ (i : ℕ) (h : i < p.verts.length - 1), G.c p.verts[i] p.verts[i+1] > 0

/-- Promote a valid candidate to a proper augmenting path. -/
def CandidateAugPath.toAugmentingPath {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (p : CandidateAugPath G) (hv : p.IsValidIn) : augmentingPath G :=
  { touvPath := p, valid := hv }

/-- One step of Ford-Fulkerson: augment current flow by a path in the residual network -/
def ff_step {V : Type*} [Fintype V] [DecidableEq V]
    (G : FlowNetwork V) (F : RelaxedFlow G.toSTVertices)
    (h : ValidFlow G F)
    (p : CandidateAugPath (ResidualNetwork G F h))
    (hp : p.IsValidIn) :
    { F' : RelaxedFlow G.toSTVertices // ValidFlow G F' } :=
  let aug := p.toAugmentingPath hp
  let flow : RelaxedFlow G.toSTVertices :=
    show RelaxedFlow G.toSTVertices from aug.toFlow
  ⟨F * flow, valid_augmentation G F h flow aug.valid_toFlow⟩

/-- A FF execution strategy: given any valid flow, pick an augmenting path
    in its residual network -/
def FFPathChoice (V : Type*) [Fintype V] [DecidableEq V] (G : FlowNetwork V) :=
  ℕ → ∀ (F : RelaxedFlow G.toSTVertices) (h : ValidFlow G F),
    CandidateAugPath (ResidualNetwork G F h)

def FFPathChoice.IsValid {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (choice : FFPathChoice V G) : Prop :=
  ∀ n (F : RelaxedFlow G.toSTVertices) (h : ValidFlow G F),
    (choice n F h).IsValidIn

/-- The sequence of flows induced by a path choice function -/
noncomputable def FFPathChoice.toFlows {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (choice : FFPathChoice V G)
    (hc : choice.IsValid) :
    ℕ → { F : RelaxedFlow G.toSTVertices // ValidFlow G F }
  | 0     => ⟨trivial_flow G.toSTVertices, valid_zero_flow G⟩
  | n + 1 =>
      let prev := choice.toFlows hc n
      ff_step G prev.1 prev.2 (choice n prev.1 prev.2) (hc n prev.1 prev.2)

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

/-- The flow is always non-negative. -/
lemma ffRawFlows_nonneg (n : ℕ) (u v : FFVert) :
    ffRawFlows X hX n u v ≥ 0 := by
  cases n with
  | zero =>
    trivial
  | succ m =>
    unfold ffRawFlows rawFFFlows rawAugment
    exact le_max_right _ 0

-- ================================================================================
-- Note: these proofs (until stop) are very similar from the ones in MaxFlowMinCutAlt
-- ================================================================================

lemma rawAugment_conservation {V : Type*} [Fintype V]
  (f g : V → V → ℝ) (v : V)
  (hf : mk_out f {v} = mk_in f {v})
  (hg : mk_out g {v} = mk_in g {v}) :
  mk_out (rawAugment f g) {v} = mk_in (rawAugment f g) {v} := by
  unfold mk_out mk_in at hf hg ⊢
  unfold rawAugment
  simp only [subset_univ, sum_sdiff_eq_sub, sum_singleton] at hf hg ⊢
  have hf_eq : ∑ x, f x v - ∑ x, f v x = 0 := by linarith
  have hg_eq : ∑ x, g x v - ∑ x, g v x = 0 := by linarith
  have h₁ : ∑ x, (max (f x v + g x v - f v x - g v x) 0 -
                  max (-(f x v + g x v - f v x - g v x)) 0) = 0 := by
    simp only [max_zero_sub_max_neg_zero_eq_self]
    have : ∑ x, (f x v + g x v - f v x - g v x) =
           (∑ x, f x v - ∑ x, f v x) + (∑ x, g x v - ∑ x, g v x) := by
      simp only [sum_sub_distrib, sum_add_distrib]
      ring
    rw [this]
    linarith
  symm
  rw [← sub_eq_zero]
  have h_neg : ∀ x, -(f x v + g x v - f v x - g v x) = f v x + g v x - f x v - g x v := by
    intro x; ring
  simp only [h_neg, sum_sub_distrib] at h₁
  simp_all only [sub_left_inj, sub_self, neg_sub, add_sub_cancel_left, max_self, sub_zero]

/-- Amount of flow leaving vertex p.verts[i] under rawPathFlow equals the bottleneck. -/
lemma rawPathlike_flow_out {V : Type*} [Fintype V] [DecidableEq V]
    (G : FlowNetwork V) (f : V → V → ℝ) (p : uvPath G.s G.t)
    (i : ℕ) (h : i < p.verts.length - 1) :
    mk_out (rawPathFlow G f p) {p.verts[i]} = rawBottleneck G f p := by
  simp only [mk_out, subset_univ, sum_sdiff_eq_sub, sum_singleton]
  have hz : ∀ v ≠ p.verts[i + 1], rawPathFlow G f p p.verts[i] v = 0 := by
    intro v vnp
    rw [rawPathFlow]
    have : ¬∃ j, ∃ (_ : j < p.verts.length - 1),
        p.verts[i] = p.verts[j] ∧ v = p.verts[j + 1] := by
      push Not
      intro j hj ij
      have iltlen : i < p.verts.length := by omega
      have jltlen : j < p.verts.length := by omega
      have : j = i := eq_index_if_nodup p.verts j i jltlen iltlen ij.symm p.nodup
      simp_all only [ne_eq, not_false_eq_true]
    simp [this]
  have hself : rawPathFlow G f p p.verts[i] p.verts[i] = 0 := by
    apply hz
    exact neq_if_nodup p.verts i (i + 1) (by omega) (by omega) (by omega) p.nodup
  have hsum : ∑ y, rawPathFlow G f p p.verts[i] y =
      rawPathFlow G f p p.verts[i] p.verts[i + 1] := by
    exact Fintype.sum_eq_single p.verts[i + 1] hz
  have hedge : rawPathFlow G f p p.verts[i] p.verts[i + 1] = rawBottleneck G f p := by
    simp [rawPathFlow, show ∃ j, ∃ (_ : j < p.verts.length - 1),
        p.verts[i] = p.verts[j] ∧ p.verts[i + 1] = p.verts[j + 1] from ⟨i, h, rfl, rfl⟩]
  linarith [hself]

/-- Amount of flow entering vertex p.verts[i] under rawPathFlow equals the bottleneck. -/
lemma rawPathlike_flow_in {V : Type*} [Fintype V] [DecidableEq V]
    (G : FlowNetwork V) (f : V → V → ℝ) (p : uvPath G.s G.t)
    (i : ℕ) (hi : i > 0) (h : i < p.verts.length - 1) :
    mk_in (rawPathFlow G f p) {p.verts[i]} = rawBottleneck G f p := by
  simp only [mk_in, subset_univ, sum_sdiff_eq_sub, sum_singleton]
  have hz : ∀ v ≠ p.verts[i - 1], rawPathFlow G f p v p.verts[i] = 0 := by
    intro v vnp
    rw [rawPathFlow]
    have : ¬∃ j, ∃ (_ : j < p.verts.length - 1),
        v = p.verts[j] ∧ p.verts[i] = p.verts[j + 1] := by
      push Not
      intro j hj ij con
      have iltlen : i < p.verts.length := by omega
      have jltlen : j + 1 < p.verts.length := by omega
      rw [ij] at vnp
      have : i = j + 1 := eq_index_if_nodup p.verts i (j + 1) iltlen jltlen con p.nodup
      simp_all only [add_tsub_cancel_right, ne_eq, not_true_eq_false]
    simp [this]
  have hself : rawPathFlow G f p p.verts[i] p.verts[i] = 0 := by
    apply hz
    exact neq_if_nodup p.verts i (i - 1) (by omega) (by omega) (by omega) p.nodup
  have hsum : ∑ y, rawPathFlow G f p y p.verts[i] =
      rawPathFlow G f p p.verts[i - 1] p.verts[i] := by
    exact Fintype.sum_eq_single p.verts[i - 1] hz
  have hedge : rawPathFlow G f p p.verts[i - 1] p.verts[i] = rawBottleneck G f p := by
    simp [rawPathFlow, show ∃ j, ∃ (_ : j < p.verts.length - 1),
        p.verts[i - 1] = p.verts[j] ∧ p.verts[i] = p.verts[j + 1] from
        ⟨i - 1, by omega, rfl, by congr 1; omega⟩]
  linarith [hself]

/-- Flow is conserved at all internal vertices of a raw path flow. -/
lemma rawPathFlow_conservation {V : Type*} [Fintype V] [DecidableEq V]
    (G : FlowNetwork V) (f : V → V → ℝ) (p : uvPath G.s G.t) (v : V)
    (hvs : v ≠ G.s) (hvt : v ≠ G.t) :
    mk_out (rawPathFlow G f p) {v} = mk_in (rawPathFlow G f p) {v} := by
  by_cases h : ∃ (i : ℕ) (_ : i < p.verts.length), v = p.verts[i]
  · obtain ⟨i, hi_lt, hi_eq⟩ := h
    have iltpm1 : i < p.verts.length - 1 := by grind [p.vend]
    have igt0    : i > 0               := by grind [p.ustart]
    rw [hi_eq, rawPathlike_flow_out G f p i iltpm1,
        rawPathlike_flow_in  G f p i igt0 iltpm1]
  · -- v not on path: every edge of rawPathFlow through v is zero
    grind [mk_out, mk_in, rawPathFlow]
/-- Flow is conserved at all internal vertices. -/
lemma ffRawFlows_conservation (n : ℕ) (v : FFVert)
  (hvs : v ≠ FFVert.s) (hvt : v ≠ FFVert.t) :
  mk_out (ffRawFlows X hX n) {v} = mk_in (ffRawFlows X hX n) {v} := by
  -- Unfold the top-level wrapper first so induction applies cleanly
  unfold ffRawFlows
  induction n with
  | zero =>
    unfold mk_in mk_out rawFFFlows
    norm_num
  | succ m ih =>
    -- Unfold the recursive step
    unfold rawFFFlows
    -- The goal is mk_out (rawAugment f g) = mk_in (rawAugment f g)
    apply rawAugment_conservation
    · -- 1. The accumulated flow satisfies conservation by the induction hypothesis
      exact ih
    · -- 2. The newly chosen path flow satisfies conservation structurally
      apply rawPathFlow_conservation
      · exact hvs
      · exact hvt

-- =================================
-- stop (see comment above)
-- =================================

lemma cycleChoice_mem (n : ℕ) :
    cycleChoice n = rawPath1 ∨ cycleChoice n = rawPath2 ∨
    cycleChoice n = rawPath3 ∨ cycleChoice n = rawPath4 := by
  simp only [cycleChoice]
  grind

/-- The bottleneck along the n-th chosen path is nonneg. -/
lemma rawBottleneck_nonneg_cycleChoice (n : ℕ) :
    0 ≤ rawBottleneck (FFNetwork X hX) (ffRawFlows X hX n) (cycleChoice n) := by
  have h_inv := ffRawFlows_invariant X hX n
  rcases h_inv with
    rfl | ⟨m, rfl, h_inv⟩ | ⟨m, rfl, h_inv⟩ | ⟨m, rfl, h_inv⟩ | ⟨m, rfl, h_inv⟩
  · have h_path : cycleChoice 0 = rawPath1 := rfl
    rw [h_path]
    have : rawBottleneck (FFNetwork X hX) (ffRawFlows X hX 0) rawPath1 = 1 := by
      change rawBottleneck (FFNetwork X hX) (fun _ _ => 0) rawPath1 = 1
      simp [rawBottleneck, rawPath1, rawResCap, FFNetwork, List.min]; grind
    linarith
  · have h_path : cycleChoice (4 * m + 1) = rawPath2 := by
      have h_def : cycleChoice (4 * m + 1) = match (4 * m) % 4 with
        | 0 => rawPath2 | 1 => rawPath3 | 2 => rawPath2 | _ => rawPath4 := rfl
      rw [h_def]; norm_num
    rw [h_path, rawBottleneck_path2_1 X hX _ _ h_inv]
    exact pow_nonneg ρ_pos.le _
  · have h_path : cycleChoice (4 * m + 2) = rawPath3 := by
      have h_def : cycleChoice (4 * m + 2) = match (4 * m + 1) % 4 with
        | 0 => rawPath2 | 1 => rawPath3 | 2 => rawPath2 | _ => rawPath4 := rfl
      rw [h_def]; norm_num
    rw [h_path, rawBottleneck_path3 X hX _ _ (by omega) h_inv]
    exact pow_nonneg ρ_pos.le _
  · have h_path : cycleChoice (4 * m + 3) = rawPath2 := by
      have h_def : cycleChoice (4 * m + 3) = match (4 * m + 2) % 4 with
        | 0 => rawPath2 | 1 => rawPath3 | 2 => rawPath2 | _ => rawPath4 := rfl
      rw [h_def]; norm_num
    rw [h_path, rawBottleneck_path2_2 X hX _ _ (by omega) h_inv]
    exact pow_nonneg ρ_pos.le _
  · have h_path : cycleChoice (4 * m + 4) = rawPath4 := by
      have h_def : cycleChoice (4 * m + 4) = match (4 * m + 3) % 4 with
        | 0 => rawPath2 | 1 => rawPath3 | 2 => rawPath2 | _ => rawPath4 := rfl
      rw [h_def]; norm_num
    rw [h_path, rawBottleneck_path4 X hX _ _ (by omega) h_inv]
    exact pow_nonneg ρ_pos.le _

/-- No flow enters the source vertex. -/
lemma rawPathFlow_no_out_sink_cycleChoice
    (f : FFVert → FFVert → ℝ) (n : ℕ) (v : FFVert) :
    rawPathFlow (FFNetwork X hX) f (cycleChoice n) FFVert.t v = 0 := by
  rcases cycleChoice_mem n with h | h | h | h <;>
  rw [h] <;>
  simp only [rawPathFlow] <;>
  split_ifs with hif <;> try rfl
  all_goals (
    obtain ⟨i, hi, ht, _⟩ := hif
    simp only [rawPath1, rawPath2, rawPath3, rawPath4,
               List.length_cons, List.length_nil, Nat.reduceAdd,
               Nat.add_one_sub_one] at hi ht
    interval_cases i <;> trivial)

/-- No flow enters the source vertex. -/
lemma rawPathFlow_no_in_source_cycleChoice
    (f : FFVert → FFVert → ℝ) (n : ℕ) (u : FFVert) :
    rawPathFlow (FFNetwork X hX) f (cycleChoice n) u FFVert.s = 0 := by
  rcases cycleChoice_mem n with h | h | h | h <;>
  rw [h] <;>
  simp only [rawPathFlow] <;>
  split_ifs with hif <;> try rfl
  all_goals (
    obtain ⟨i, hi, _, hs⟩ := hif
    simp only [rawPath1, rawPath2, rawPath3, rawPath4,
               List.length_cons, List.length_nil, Nat.reduceAdd,
               Nat.add_one_sub_one] at hi hs
    interval_cases i <;> trivial)

lemma ffRawFlows_no_in_source (n : ℕ) (u : FFVert) :
    ffRawFlows X hX n u FFVert.s = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change rawAugment (ffRawFlows X hX n) (rawPathFlow (FFNetwork X hX) (ffRawFlows X hX n)
      (cycleChoice n)) u FFVert.s = 0
    unfold rawAugment
    rw [ih, rawPathFlow_no_in_source_cycleChoice]
    simp only [add_zero, zero_sub]
    apply max_eq_right
    have h_f : 0 ≤ ffRawFlows X hX n FFVert.s u := ffRawFlows_nonneg X hX n FFVert.s u
    have h_g : 0 ≤ rawPathFlow (FFNetwork X hX) (ffRawFlows X hX n) (cycleChoice n) FFVert.s u :=
      le_trans (le_refl 0) (by
        unfold rawPathFlow
        split_ifs
        · exact rawBottleneck_nonneg_cycleChoice X hX n
        · rfl)
    linarith


lemma ffRawFlows_no_out_sink (n : ℕ) (u : FFVert) :
    ffRawFlows X hX n FFVert.t u = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change rawAugment (ffRawFlows X hX n) (rawPathFlow (FFNetwork X hX) (ffRawFlows X hX n)
      (cycleChoice n)) FFVert.t u = 0
    unfold rawAugment
    rw [ih, rawPathFlow_no_out_sink_cycleChoice]
    simp only [add_zero, zero_sub]
    apply max_eq_right
    have h_f : 0 ≤ ffRawFlows X hX n u FFVert.t := ffRawFlows_nonneg X hX n u FFVert.t
    have h_g : 0 ≤ rawPathFlow (FFNetwork X hX) (ffRawFlows X hX n) (cycleChoice n) u FFVert.t :=
      le_trans (le_refl 0) (by
        unfold rawPathFlow
        split_ifs
        · exact rawBottleneck_nonneg_cycleChoice X hX n
        · rfl)
    linarith


/-- The flow never exceeds the raw capacity of the network edges. -/
lemma ffRawFlows_le_cap (n : ℕ) (u v : FFVert) :
  ffRawFlows X hX n u v ≤ (FFNetwork X hX).c u v := by
  sorry

noncomputable def ffRelaxedFlow (n : ℕ) :
  RelaxedFlow (FFNetwork X hX).toSTVertices where
  f := ffRawFlows X hX n
  nonneg_flow := ffRawFlows_nonneg X hX n
  conservation := ffRawFlows_conservation X hX n
  no_edges_in_source := ffRawFlows_no_in_source X hX n
  no_edges_out_sink := ffRawFlows_no_out_sink X hX n

/-- The final theorem establishing that the raw sequence is a completely valid flow sequence. -/
theorem ffRawFlows_isValidFlow (n : ℕ) :
  ValidFlow (FFNetwork X hX) (ffRelaxedFlow X hX n) := by
  intro u v
  exact ffRawFlows_le_cap X hX n u v

theorem ff_non_termination (X : ℝ) (hX : X > 2) :
    ∃ (choice : FFPathChoice FFVert (FFNetwork X hX)) (hc : choice.IsValid),
    Filter.Tendsto
      (fun n => Flow_value (FFNetwork X hX).toSTVertices (choice.toFlows hc n).1)
      Filter.atTop
        (nhds (2 * (∑' n, ρ ^ n) - 1)) ∧
      2 * (∑' n, ρ ^ n) - 1 < 2 * X := by
  sorry
