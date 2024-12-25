import Mathlib.Algebra.ContinuedFractions.ConvergentsEquiv
import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat

namespace FiniteContFract

open GenContFract

def evalTail : List ℕ+ → ℚ
  | [] => 0
  | a::l => ((a : ℚ) + evalTail l)⁻¹

theorem evalTail_nonneg : ∀ (l : List ℕ+), 0 ≤ evalTail l
  | [] => le_rfl
  | _::_ => inv_nonneg.2 <| add_nonneg (Nat.cast_nonneg _) (evalTail_nonneg _)

mutual

theorem evalTail_pos : ∀ {l : List ℕ+}, l ≠ [] → 0 < evalTail l
  | [a], h => by
    rw [evalTail, evalTail, add_zero, inv_pos, Nat.cast_pos]
    exact a.2
  | a::b::l, h₂ => by
    rw [evalTail, inv_pos]
    refine add_pos_of_pos_of_nonneg (by simp) (evalTail_nonneg _)

theorem evalTail_lt_one : ∀ {l : List ℕ+}, l ≠ [1] → evalTail l < 1
  | [], _ => by simp [evalTail]
  | [a], h => by
    simp only [evalTail, add_zero, inv_lt_one_iff₀, Nat.cast_nonpos, PNat.ne_zero, Nat.one_lt_cast,
      false_or]
    exact lt_of_le_of_ne a.one_le (by simpa [eq_comm, ← PNat.coe_inj] using h)
  | a::b::l, h => by
    rw [evalTail, inv_lt_one_iff₀]
    right
    refine lt_add_of_le_of_pos ?_ ?_
    · rw [Nat.one_le_cast]; exact a.one_le
    · exact evalTail_pos (by simp)

end

theorem evalTail_le_one (l : List ℕ+) : evalTail l ≤ 1 :=
  if h : l = [1] then by simp [h, evalTail] else le_of_lt (evalTail_lt_one h)

def eval (c : FiniteContFract) : ℚ :=
  c.h + evalTail c.s

theorem head_eq_floor_evalTail_inv (a : ℕ+) (l : List ℕ+) (hl : l ≠ [1]) :
    (a : ℤ) = ⌊(evalTail (a::l))⁻¹⌋ := by
  rw [evalTail, inv_inv]
  refine le_antisymm ?_ ?_
  · simp only [Int.floor_nat_add, le_add_iff_nonneg_right, Int.floor_nonneg]
    exact evalTail_nonneg _
  · simp only [Int.floor_nat_add, add_le_iff_nonpos_right, Int.floor_le_iff, Int.cast_zero,
      zero_add]
    exact evalTail_lt_one hl

theorem evalTail_tail_eq_fract_evalTail_inv (a : ℕ+) (l : List ℕ+) (hl : l ≠ [1]) :
    evalTail l = Int.fract ((evalTail (a::l))⁻¹) := by
  rw [Int.fract, ← head_eq_floor_evalTail_inv a l hl, evalTail, inv_inv]
  simp

theorem evalTail_injOn : Set.InjOn evalTail { l : List ℕ+ | 1 ∉ l.getLast? }
  | [], _, [], _, _ => rfl
  | a::l, _, [], _, h₁₂ => by
    simp only [evalTail, inv_eq_zero] at h₁₂
    refine False.elim (ne_of_gt ?_ h₁₂)
    exact add_pos_of_pos_of_nonneg (Nat.cast_pos.2 a.pos) (evalTail_nonneg _)
  | [], _, a::l, _, h₁₂ => by
    simp only [evalTail, zero_eq_inv] at h₁₂
    refine False.elim (ne_of_lt ?_ h₁₂)
    exact add_pos_of_pos_of_nonneg (Nat.cast_pos.2 a.pos) (evalTail_nonneg _)
  | a₁::l₁, h₁, a₂::l₂, h₂, h₁₂ => by
    replace h₁ : 1 ∉ l₁.getLast? := by simp_all [Option.getD_eq_iff, List.getLast?_cons]
    replace h₂ : 1 ∉ l₂.getLast? := by simp_all [Option.getD_eq_iff, List.getLast?_cons]
    have hhead₁ := head_eq_floor_evalTail_inv a₁ l₁ (by rintro rfl; simp_all)
    have hhead₂ := head_eq_floor_evalTail_inv a₂ l₂ (by rintro rfl; simp_all)
    have htail₁ := evalTail_tail_eq_fract_evalTail_inv a₁ l₁ (by rintro rfl; simp_all)
    have htail₂ := evalTail_tail_eq_fract_evalTail_inv a₂ l₂ (by rintro rfl; simp_all)
    rw [h₁₂, ← hhead₂] at hhead₁
    norm_cast at hhead₁
    subst hhead₁
    rw [h₁₂, ← htail₂] at htail₁
    rw [evalTail_injOn h₁ h₂ htail₁]

theorem h_eq_floor_eval (c : FiniteContFract) (hc : c.s ≠ [1]) : c.h = ⌊c.eval⌋ :=
  le_antisymm (by
      rw [Int.le_floor, eval]
      exact le_add_of_nonneg_right (evalTail_nonneg _))
    (by
      rw [Int.floor_le_iff, eval]
      exact add_lt_add_left (evalTail_lt_one hc) _)

theorem eval_injOn : Set.InjOn eval { c | 1 ∉ c.s.getLast? }  := by
  intro c₁ hc₁ c₂ hc₂ h
  have h₁ : c₁.s ≠ [1] := by intro h; simp [h] at hc₁
  have h₂ : c₂.s ≠ [1] := by intro h; simp [h] at hc₂
  have : c₁.h = c₂.h := by rw [h_eq_floor_eval _ h₁, h, h_eq_floor_eval _ h₂]
  ext1
  · exact this
  · rw [eval, eval, this, add_left_cancel_iff] at h
    exact evalTail_injOn hc₁ hc₂ h

theorem coe_eval_eq_convs'_coe_length {K : Type*} [Field K] [CharZero K] : ∀ (c : FiniteContFract),
    (c.eval : K) = (c : GenContFract K).convs' c.s.length
  | ⟨h, []⟩ => by
    simp [toContFract, ContFract.toGenContFract, eval, evalTail, convs', convs'Aux,
      ContFract.toSimpContFract]
  | ⟨h, a::l⟩ => by
    simpa [toContFract, ContFract.toGenContFract, eval, convs', convs'Aux, evalTail,
      ContFract.toSimpContFract] using coe_eval_eq_convs'_coe_length (K := K) ⟨a, l⟩
  termination_by l => l.s.length

theorem eval_eq_convs'_coe_length (c : FiniteContFract) :
    c.eval = (c : GenContFract ℚ).convs' c.s.length := by
  erw [← coe_eval_eq_convs'_coe_length]
  simp


end FiniteContFract

namespace Rat

open GenContFract FiniteContFract ContFract

def toFiniteContFract (x : ℚ) : FiniteContFract :=
  let c := ContFract.of x
  ⟨c.h, c.s.toList ((ContFract.terminates_coe_iff (α := ℚ)).1 (by
    rw [coe_of, terminates_iff_rat]
    exact ⟨x, rfl⟩))⟩

theorem one_not_mem_getLast?_toFiniteContFract (x : ℚ) : 1 ∉ (toFiniteContFract x).s.getLast? :=
  ContFract.one_not_mem_getLast?_of _ _

@[simp]
theorem coeContFract_toFiniteContFract (x : ℚ) :
    (toFiniteContFract x : ContFract) = ContFract.of x := by
  simp [toFiniteContFract, FiniteContFract.toContFract]

@[simp]
theorem coeGenContFract_toFiniteContFract (x : ℚ) :
    (toFiniteContFract x : GenContFract ℚ) = GenContFract.of x := by
  simp [ContFract.toRegContFract, ContFract.toSimpContFract]

@[simp]
theorem eval_toFiniteContFract (x : ℚ) : x.toFiniteContFract.eval = x := by
  rw [eval_eq_convs'_coe_length, ← RegContFract.convs_eq_convs',
    coeGenContFract_toFiniteContFract, ← of_correctness_of_terminatedAt]
  simpa using (ContFract.terminatedAt_coe_iff (α := ℚ)).2
    (terminatedAt_toContFract (toFiniteContFract x))

def equivFiniteContFract : ℚ ≃ {c : FiniteContFract // 1 ∉ c.s.getLast? } where
  toFun := fun x => ⟨x.toFiniteContFract, one_not_mem_getLast?_toFiniteContFract x⟩
  invFun := fun c => eval c.1
  left_inv := eval_toFiniteContFract
  right_inv := fun x => Subtype.ext <| eval_injOn
    (one_not_mem_getLast?_toFiniteContFract _) x.2
    (by simp only [eval_toFiniteContFract])

end Rat
