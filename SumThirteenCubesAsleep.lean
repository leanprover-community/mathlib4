import Batteries.Data.MLList.Basic
import Mathlib.NumberTheory.SumFourSquares
import Mathlib.Data.Real.Basic
import Mathlib.Data.List.MinMax
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Util.Qq

def find_reps {m : Type → Type} [Alternative m] (pow : ℕ) :
    (allowed_nums : ℕ) → (remaining_tot : ℕ) → (lowest_used : ℕ) → m (List ℕ)
  | n, 0, _ => pure (List.replicate n 0)
  | 0, (_ + 1), _ => failure
  | n + 1, m@(_ + 1), k =>
      (List.range' 1 k).reverse.firstM fun i =>
        let ip := i ^ pow
        if m < ip then failure
        else (i :: ·) <$> find_reps pow n (m - ip) i

/-- This is a special case of `find_rep_iff` which makes it a bit easier to prove -/
private lemma find_rep_iff_zero_middle
    {m : Type → Type} [Alternative m] [∀ α, Membership α (m α)]
    (hpure : ∀ {α} (x y : α), x ∈ (pure y : m α) ↔ x = y)
    (i n k : ℕ) (l : List ℕ) (hi : i ≠ 0) :
    l ∈ find_reps (m := m) i n 0 k ↔
      l.length = n ∧ (∀ x ∈ l, x ≤ k) ∧ l.Pairwise (· ≥ ·) ∧ (l.map (· ^ i)).sum = 0 := by
  rw [find_reps]
  simp only [hpure]
  constructor
  · rintro rfl
    simp [hi]
  rintro ⟨h₁, -, -, h₂⟩
  simpa [List.eq_replicate_iff, h₁, List.sum_eq_zero_iff, hi] using h₂

#check List.mem_flatMap

/-- `find_rep` consists exactly of the lists it should -/
lemma find_rep_iff
    {M : Type → Type} [Alternative M] [∀ α, Membership α (M α)]
    (hpure : ∀ {α} (x y : α), x ∈ (pure y : M α) ↔ x = y)
    (hnil : ∀ {α} (x : α), x ∉ (failure : M α))
    {n m k : ℕ} (l : List ℕ) (hi : i ≠ 0) :
    l ∈ find_reps (m := M) i n m k ↔
      l.length = n ∧ (∀ x ∈ l, x ≤ k) ∧ l.Pairwise (· ≥ ·) ∧ (l.map (· ^ i)).sum = m := by
  induction' n with n ih generalizing m k l
  · cases' m with m
    · exact find_rep_iff_zero_middle hpure _ _ _ _ hi
    simp only [find_reps, hnil, List.length_eq_zero, ge_iff_le, false_iff, not_and]
    rintro rfl
    simp
  cases' m with m
  · exact find_rep_iff_zero_middle hpure _ _ _ _ hi
  rw [find_reps]
  simp only [bind_eq_flatMap, mem_flatMap, mem_reverse, mem_range'_1, add_comm 1,
    Nat.lt_add_one_iff]
  simp only [succ_eq_add_one, mem_ite_nil_right, ge_iff_le]
  constructor
  · simp only [forall_exists_index, and_imp]
    rintro x h hxk hx hl
    rw [mem_map] at hl
    obtain ⟨a, ha, rfl⟩ := hl
    rw [ih] at ha
    simp only [length_cons, ha, mem_cons, forall_eq_or_imp, hxk, true_and, pairwise_cons, and_true,
      map_cons, List.sum_cons, hx, add_tsub_cancel_of_le]
    exact ⟨fun i hi => (ha.2.1 _ hi).trans hxk, ha.2.1⟩
  cases' l with x l
  · simp
  simp only [length_cons, succ.injEq, mem_cons, forall_eq_or_imp, ge_iff_le, pairwise_cons, map,
    List.sum_cons, and_imp]
  intros h hxk _ hl₂ hl₃ hl₄
  refine ⟨x, ⟨?_, hxk⟩, ?_⟩
  · rw [Nat.add_one_le_iff, pos_iff_ne_zero]
    rintro rfl
    have : ∀ a ∈ l, a = 0 := by simpa using hl₂
    rw [List.eq_replicate_iff.2 ⟨rfl, this⟩, map_replicate, sum_replicate] at hl₄
    simp [hi] at hl₄
  have : x ^ i ≤ m + 1 := by omega
  simp only [this, mem_map, cons.injEq, true_and, exists_eq_right]
  refine (ih l).2 ⟨h, hl₂, hl₃, ?_⟩
  rw [eq_tsub_iff_add_eq_of_le this, add_comm, hl₄]

#time
#eval find_reps (m := Option) 3 13 9999 20
#time
#eval MLList.head? $ find_reps (m := MLList Id) 3 13 9999 20
