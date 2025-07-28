/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib


open scoped Affine Finset
open Module Multiset

namespace IMO2025P1

/-- The `x`-axis, as an affine subspace. -/
def xAxis : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) :=
  line[ℝ, !₂[0, 0], !₂[1, 0]]

/-- The `y`-axis, as an affine subspace. -/
def yAxis : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) :=
  line[ℝ, !₂[0, 0], !₂[0, 1]]

/- The line `x+y=0`, as an affine subspace. -/
noncomputable def linexy0 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) :=
  line[ℝ, !₂[0, 0], !₂[-1, -1]]

/-- The condition on lines in the problem. -/
def Sunny (s : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) : Prop :=
   ¬ s ∥ xAxis ∧ ¬ s ∥ yAxis ∧ ¬ s ∥ linexy0

/-- The answer to be determined. -/
def answer : (Set.Ici 3) → Set ℕ := fun _ => { 0, 1, 3 }

/- Preliminaries -/

lemma mem_line_iff {p} {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≠ x₁ ∨ y₀ ≠ y₁ := by grind) :
    p ∈ line[ℝ, !₂[x₀, y₀], !₂[x₁, y₁]] ↔ (p 0 - x₀) * (y₁ - y₀) = (p 1 - y₀) * (x₁ - x₀) := by
  have : {!₂[x₀, y₀], !₂[x₁, y₁]} = Set.range ![!₂[x₀, y₀], !₂[x₁, y₁]] :=
    (Matrix.range_cons_cons_empty !₂[x₀, y₀] !₂[x₁, y₁] ![]).symm
  constructor
  · intro h
    induction' h using affineSpan_induction' with y hy c u hu v hv w hw h₁ h₂ h₃
    · rcases hy with (rfl | rfl)
      · simp
      · simp [mul_comm]
    · simp only [vsub_eq_sub, Fin.isValue, vadd_eq_add, PiLp.add_apply, PiLp.smul_apply,
        PiLp.sub_apply, smul_eq_mul]
      grind only
  · intro h
    rcases hx with (hx | hy)
    · have := affineCombination_mem_affineSpan_of_nonempty
        (s := ⊤) (w := ![1 - (p 0 - x₀) / (x₁ - x₀), (p 0 - x₀) / (x₁ - x₀)])
        (by simp) ![!₂[x₀, y₀], !₂[x₁, y₁]]
      convert this
      ext i; fin_cases i
      <;> simp only [Fin.zero_eta, Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd,
        Finset.top_eq_univ, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, sub_add_cancel, Finset.affineCombination_eq_linear_combination,
        PiLp.add_apply, PiLp.smul_apply, PiLp.toLp_apply, smul_eq_mul,
        Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      <;> apply mul_right_cancel₀ (sub_ne_zero_of_ne hx.symm)
      <;> rw [add_mul, sub_mul, sub_mul, sub_add_comm]
      <;> field_simp [mul_div_cancel_right₀ _ (sub_ne_zero_of_ne hx.symm)]
      · ring
      · rw [mul_sub] at h
        rw [h]
        ring
    · have := affineCombination_mem_affineSpan_of_nonempty
        (s := ⊤) (w := ![1 - (p 1 - y₀) / (y₁ - y₀), (p 1 - y₀) / (y₁ - y₀)])
        (by simp) ![!₂[x₀, y₀], !₂[x₁, y₁]]
      convert this
      ext i; fin_cases i
      <;> simp only [Fin.mk_one, Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd,
        Finset.top_eq_univ, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, sub_add_cancel, Finset.affineCombination_eq_linear_combination,
        PiLp.add_apply, PiLp.smul_apply, PiLp.toLp_apply, smul_eq_mul]
      <;> apply mul_right_cancel₀ (sub_ne_zero_of_ne hy.symm)
      · rw [add_mul, sub_mul, sub_mul]
        field_simp [mul_div_cancel_right₀ _ (sub_ne_zero_of_ne hy.symm)]
        rw [sub_mul] at h
        rw [eq_add_of_sub_eq h]
        ring
      · rw [add_mul, sub_mul, sub_mul]
        field_simp [mul_div_cancel_right₀ _ (sub_ne_zero_of_ne hy.symm)]
        ring

lemma _root_.AffineSubspace.eq_line_of_mem_mem_finrank
    (l : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)))
    {p q} (hp : p ∈ l) (hq : q ∈ l) (hpq : p ≠ q) (h : finrank ℝ l.direction = 1) :
    l = line[ℝ, p, q] :=
  sorry

lemma _root_.AffineSubspace.finrank_eq_two_of_ne
    (l : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)))
    {p q r} (hp : p ∈ l) (hq : q ∈ l) (hr : r ∈ l)
    (h : (p 0 - q 0) * (r 1 - q 1) ≠ (p 1 - q 1) * (r 0 - q 0)) :
    finrank ℝ l.direction = 2 :=
  sorry

/-- This is still missing non-degeneracy conditions -/
lemma line_eq_iff {a₀ b₀ c₀ d₀ a₁ b₁ c₁ d₁ : ℝ} :
    line[ℝ, !₂[a₀, b₀], !₂[c₀, d₀]] = line[ℝ, !₂[a₁, b₁], !₂[c₁, d₁]] ↔
    (a₀ - a₁) * (d₀ - b₁) = (c₀ - a₁) * (b₀ - b₁) ∧
      (a₀ - c₁) * (d₀ - d₁) = (c₀ - c₁) * (b₀ - d₁) := by
  sorry

@[simp]
theorem line_rank {p q : EuclideanSpace ℝ (Fin 2)}
    (h : p ≠ q := by {ext i; fin_cases i <;> simp }) :
    finrank ℝ (AffineSubspace.direction line[ℝ, p, q]) = 1 := by
  rw [direction_affineSpan]
  apply Nat.le_antisymm
  · trans
    · apply finrank_vectorSpan_insert_le_set ℝ {q} (p : EuclideanSpace ℝ (Fin 2))
    · simp
  · rw [Submodule.one_le_finrank_iff]
    rw [vectorSpan_def]
    simp
    use q -ᵥ p
    constructor
    · rw [Set.mem_vsub]
      refine ⟨q, by simp, p, by simp, rfl⟩
    · exact vsub_ne_zero.mpr fun a ↦ h (id (Eq.symm a))

@[simp]
lemma point_sub {x₁ y₁ x₂ y₂ : ℝ} : !₂[x₁, y₁] - !₂[x₂, y₂] = !₂[x₁ - x₂, y₁ - y₂] := by
  ext i; fin_cases i <;> simp

@[simp]
lemma point_add {x₁ y₁ x₂ y₂ : ℝ} : !₂[x₁, y₁] + !₂[x₂, y₂] = !₂[x₁ + x₂, y₁ + y₂] := by
  ext i; fin_cases i <;> simp

@[simp]
lemma smul_point {c x₁ y₁ : ℝ} : c • !₂[x₁, y₁] = !₂[c * x₁, c * y₁] := by
  ext i; fin_cases i <;> simp

@[simp]
lemma neg_point {x₁ y₁ : ℝ} : - !₂[x₁, y₁] = !₂[-x₁, -y₁] := by
  ext i; fin_cases i <;> simp

@[simp]
lemma not_sunny_vert {x : ℝ} : ¬Sunny line[ℝ, !₂[x, 0], !₂[x, 1]] := by
  simp only [Sunny, Classical.not_and_iff_not_or_not, not_not]; right; left
  rw [yAxis, AffineSubspace.affineSpan_pair_parallel_iff_vectorSpan_eq, vectorSpan_def]
  congr 1
  simp [Set.vsub, Set.image_insert_eq]

/- Lines we'll use -/

def l1 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) := line[ℝ, !₂[1, 0], !₂[1, 1]]

def l2 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) := line[ℝ, !₂[2, 0], !₂[2, 1]]

def l3 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) := line[ℝ, !₂[3, 0], !₂[3, 1]]

def l4 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) := line[ℝ, !₂[3, 1], !₂[4, 2]]

@[simp]
lemma sunny_l4 : Sunny l4 := by
  sorry

def l5 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) := line[ℝ, !₂[0, 0], !₂[1, 1]]

@[simp]
lemma sunny_l5 : Sunny l5 := by
  sorry

def l6 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) := line[ℝ, !₂[1, 3], !₂[2, 1]]

@[simp]
lemma sunny_l6 : Sunny l6 := by
  sorry

def l7 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) := line[ℝ, !₂[3, 1], !₂[1, 2]]

@[simp]
lemma sunny_l7 : Sunny l7 := by
  sorry

noncomputable instance : DecidablePred Sunny := Classical.decPred _

lemma notSunny_of_horiz {l : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))}
    {x₁ x₂ y₁ y₂ : ℝ} (h₁ : !₂[x₁, y₁] ∈ l) (h₂ : !₂[x₂, y₂] ∈ l) (h : x₁ ≠ x₂ := by simp) :
    ¬ Sunny l :=
  sorry

lemma notSunny_of_vert {l : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))}
    {x₁ x₂ y₁ y₂ : ℝ} (h₁ : !₂[x₁, y₁] ∈ l) (h₂ : !₂[x₂, y₂] ∈ l) (h : y₁ ≠ y₂ := by simp) :
    ¬ Sunny l :=
  sorry

lemma notSunny_of_diag {l : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))}
    {x₁ x₂ y₁ y₂ : ℝ} (h₁ : !₂[x₁, y₁] ∈ l) (h₂ : !₂[x₂, y₂] ∈ l)
    (h : y₂ - y₁ = x₁ - x₂) (h : x₁ ≠ x₂ := by simp) :
    ¬ Sunny l :=
  sorry

lemma sunny_of_ne {l : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))}
    {x₁ x₂ y₁ y₂} (h₁ : !₂[x₁, y₁] ∈ l) (h₂ : !₂[x₂, y₂] ∈ l)
    (h₃ : y₂ - y₁ ≠ x₁ - x₂) (h₄ : x₁ ≠ x₂ := by simp) (h₅ : y₁ ≠ y₂ := by simp) : Sunny l :=
  sorry

lemma zero_mem3 : 0 ∈ {k | ∃ lines : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))),
      have : DecidablePred Sunny := Classical.decPred _;
      #lines = 3 ∧ (∀ l ∈ lines, finrank ℝ l.direction = 1) ∧
      (∀ a b : ℕ, 0 < a → 0 < b → a + b ≤ 4 → ∃ l ∈ lines, !₂[(a : ℝ), b] ∈ l) ∧
      #{l ∈ lines | Sunny l} = k} := by
  simp only [Set.mem_setOf_eq, Finset.card_eq_zero]
  let ls : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) :=
    (({ l1 } : Finset _).cons l2
      (by simp only [Finset.mem_singleton, l2, l1, line_eq_iff]; norm_num)).cons l3 (by
        simp only [Finset.mem_cons, Finset.mem_singleton, not_or]
        constructor <;> simp only [l1, l2, l3, line_eq_iff] <;> norm_num )
  use ls
  refine ⟨by simp [ls], fun l hl => ?_, ?_, ?_⟩
  · simp only [Finset.mem_cons, Finset.mem_singleton, ls] at hl
    rcases hl with (rfl|rfl|rfl)
    <;> apply line_rank (fun h => by have := congr_fun h 1; simp at this)
  · simp only [Finset.mem_cons, Finset.mem_singleton, exists_eq_or_imp, exists_eq_left, ls]
    rintro (a|a|a|a|a) b ha hb hab
    · simp at ha
    · have : b = 1 ∨ b = 2 ∨ b = 3 := by omega
      rcases this with (rfl|rfl|rfl) <;> right <;> right <;>
        simp only [l1, zero_add, Nat.cast_one, Nat.cast_ofNat] <;> rw [mem_line_iff] <;> simp
    · have : b = 1 ∨ b = 2 := by omega
      rcases this with (rfl|rfl) <;> right <;> left <;>
        simp only [l2, zero_add, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one] <;>
        rw [mem_line_iff] <;> simp
    · left
      have : b = 1 := by omega
      subst this
      simp only [zero_add, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one]
      apply right_mem_affineSpan_pair ℝ
    · omega
  · simp only [ls]
    apply Finset.filter_false_of_mem
    rintro x (h | ⟨x, (h | ⟨x, (h | ⟨x, ⟨⟩⟩)⟩)⟩) <;> simp [l1, l2, l3]

lemma one_mem3 : 1 ∈ {k | ∃ lines : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))),
      have : DecidablePred Sunny := Classical.decPred _;
      #lines = 3 ∧ (∀ l ∈ lines, finrank ℝ l.direction = 1) ∧
      (∀ a b : ℕ, 0 < a → 0 < b → a + b ≤ 4 → ∃ l ∈ lines, !₂[(a : ℝ), b] ∈ l) ∧
      #{l ∈ lines | Sunny l} = k} := by
  simp only [Set.mem_setOf_eq]
  let ls : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) :=
    (({ l1 } : Finset _).cons l2
      (by simp only [Finset.mem_singleton, l2, l1, line_eq_iff]; norm_num)).cons l4 (by
        simp only [Finset.mem_cons, Finset.mem_singleton, not_or]
        constructor <;> simp only [l1, l2, l4, line_eq_iff] <;> norm_num )
  use ls
  refine ⟨by simp [ls], fun l hl => ?_, ?_, ?_⟩
  · simp only [Finset.mem_cons, Finset.mem_singleton, ls] at hl
    rcases hl with (rfl|rfl|rfl)
    <;> apply line_rank (fun h => by have := congr_fun h 1; simp at this)
  · simp only [Finset.mem_cons, Finset.mem_singleton, exists_eq_or_imp, exists_eq_left, ls]
    rintro (a|a|a|a|a) b ha hb hab
    · simp at ha
    · have : b = 1 ∨ b = 2 ∨ b = 3 := by omega
      rcases this with (rfl|rfl|rfl) <;> right <;> right <;>
        simp only [l1, zero_add, Nat.cast_one, Nat.cast_ofNat] <;> rw [mem_line_iff] <;> simp
    · have : b = 1 ∨ b = 2 := by omega
      rcases this with (rfl|rfl) <;> right <;> left <;>
        simp only [l2, zero_add, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one] <;>
        rw [mem_line_iff] <;> simp
    · left
      have : b = 1 := by omega
      subst this
      simp only [l4, zero_add, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one]
      rw [mem_line_iff]
      simp
    · omega
  · simp [ls, Finset.filter_cons_of_pos, Finset.filter_cons_of_neg, Finset.filter_singleton, l1, l2]

lemma three_mem3 : 3 ∈ {k | ∃ lines : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))),
      have : DecidablePred Sunny := Classical.decPred _;
      #lines = 3 ∧ (∀ l ∈ lines, finrank ℝ l.direction = 1) ∧
      (∀ a b : ℕ, 0 < a → 0 < b → a + b ≤ 4 → ∃ l ∈ lines, !₂[(a : ℝ), b] ∈ l) ∧
      #{l ∈ lines | Sunny l} = k} := by
  simp only [Set.mem_setOf_eq]
  let ls : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) :=
    (({ l5 } : Finset _).cons l6
      (by simp only [Finset.mem_singleton, l5, l6, line_eq_iff]; norm_num)).cons l7 (by
        simp only [Finset.mem_cons, Finset.mem_singleton, not_or]
        constructor <;> simp only [l5, l6, l7, line_eq_iff] <;> norm_num )
  use ls
  refine ⟨by simp [ls], fun l hl => ?_, ?_, ?_⟩
  · simp only [Finset.mem_cons, Finset.mem_singleton, ls] at hl
    rcases hl with (rfl|rfl|rfl)
    <;> apply line_rank (fun h => by have := congr_fun h 1; simp at this)
  · simp only [Finset.mem_cons, Finset.mem_singleton, exists_eq_or_imp, exists_eq_left, ls]
    rintro (a|a|a|a|a) b ha hb hab
    · simp at ha
    · have : b = 1 ∨ b = 2 ∨ b = 3 := by omega
      rcases this with (rfl|rfl|rfl)
      · right; right; simp [l5]; rw [mem_line_iff]; dsimp
      · left; simp [l7]; rw [mem_line_iff]; dsimp; norm_num
      · right; left; simp [l6]; rw [mem_line_iff]; dsimp; norm_num
    · have : b = 1 ∨ b = 2 := by omega
      rcases this with (rfl|rfl)
      · right; left; simp [l6]; rw [mem_line_iff]; dsimp; norm_num
      · right; right; simp [l5]; rw [mem_line_iff]; dsimp
    · obtain rfl : b = 1 := by omega;
      left; simp [l7]; rw [mem_line_iff]; dsimp; norm_num
    · omega
  · simp [ls, Finset.filter_cons_of_pos _ _ _ _ sunny_l7,
      Finset.filter_cons_of_pos _ _ _ _ sunny_l6,
      Finset.filter_singleton]

noncomputable instance : DecidableEq (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) :=
  Classical.decEq _

structure Config (n k : Nat) where
  ls : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)))
  card : #ls = n
  rank : ∀ l ∈ ls, finrank ℝ ↥l.direction = 1
  cover : ∀ (a b : ℕ)
    (_ : 0 < a := by simp_all) (_ : 0 < b := by simp_all) (_ : a + b ≤ 4 := by simp_all),
    ∃ l ∈ ls, !₂[↑a, ↑b] ∈ l
  sunny : #{l ∈ ls | Sunny l} = k

noncomputable def Config.symm {n k : ℕ} (c : Config n k) : Config n k where
  ls := c.ls.map
    ⟨fun l => l.map (EuclideanGeometry.reflection line[ℝ, !₂[(0 : ℝ), 0], !₂[1, 1]]).toAffineMap,
    fun x y => by { simp;  sorry }⟩
  card := by simp [c.card]
  rank l hl := by
    simp
    sorry
  cover a b ha hb hab := by
    simp at *
    rw [add_comm] at hab
    obtain ⟨l, hl, hbal⟩ := c.cover b a
    refine ⟨l, hl, !₂[b, a], hbal, ?_⟩
    rw [EuclideanGeometry.reflection_apply]
    simp
    sorry
  sunny := by
    sorry

lemma no_config_3_2_no_vert (c : Config 3 2) (h_no_vert : ∀ l ∈ c.ls, ¬ l ∥ yAxis) : False := by
  obtain ⟨l₁, hl₁, meml₁⟩ := c.cover 1 1
  obtain ⟨l₂, hl₂, meml₂⟩ := c.cover 1 2
  obtain ⟨l₃, hl₃, meml₃⟩ := c.cover 1 3
  have hcard : #{l₁, l₂, l₃} = 3 := by
    refine Finset.card_eq_three.mpr ⟨l₁, l₂, l₃, fun h => ?_, fun h => ?_, fun h => ?_, rfl⟩
    <;> subst h
    · fapply h_no_vert l₁ hl₁
      use !₂[-1, -1]
      rw [l₁.eq_line_of_mem_mem_finrank meml₁ meml₂ (fun h => by have := congr_fun h 1; simp_all)
        (c.rank _ hl₁), AffineSubspace.map_span, Set.image_pair, yAxis]
      simp only [AffineEquiv.coe_toAffineMap, AffineEquiv.constVAdd_apply, vadd_eq_add, point_add]
      norm_num
    · fapply h_no_vert l₁ hl₁
      use !₂[-1, -1]
      rw [l₁.eq_line_of_mem_mem_finrank meml₁ meml₃ (fun h => by have := congr_fun h 1; simp_all)
        (c.rank _ hl₁), AffineSubspace.map_span, Set.image_pair, yAxis]
      simp only [AffineEquiv.coe_toAffineMap, AffineEquiv.constVAdd_apply, vadd_eq_add, point_add]
      norm_num
      apply le_antisymm
      · apply affineSpan_pair_le_of_right_mem
        rw [mem_affineSpan_iff_exists]
        refine ⟨!₂[0, 0], by simp, !₂[0, 1], ?_, by simp⟩
        have := smul_vsub_mem_vectorSpan_pair (k := ℝ) (P := EuclideanSpace ℝ (Fin 2))
          (- 1 / 2) !₂[0, 0] !₂[0, 2]
        simpa using this
      · apply affineSpan_pair_le_of_right_mem
        rw [mem_affineSpan_iff_exists]
        refine ⟨!₂[0, 0], by simp, !₂[0, 2], ?_, by simp⟩
        have := smul_vsub_mem_vectorSpan_pair (k := ℝ) (P := EuclideanSpace ℝ (Fin 2))
          (-2) !₂[0, 0] !₂[0, 1]
        simpa using this
    · fapply h_no_vert l₂ hl₂
      use !₂[-1, -2]
      rw [l₂.eq_line_of_mem_mem_finrank meml₂ meml₃ (fun h => by have := congr_fun h 1; simp_all)
        (c.rank _ hl₂), AffineSubspace.map_span, Set.image_pair, yAxis]
      simp only [AffineEquiv.coe_toAffineMap, AffineEquiv.constVAdd_apply, vadd_eq_add, point_add]
      norm_num
  have hcls : {l₁, l₂, l₃} = c.ls := Finset.eq_of_subset_of_card_le (Finset.insert_subset hl₁
    (Finset.insert_subset hl₂ (Finset.singleton_subset_iff.mpr hl₃))) (by rw [c.card, hcard])
  obtain ⟨l₄, hl₄, meml₄⟩ :=  c.cover 2 1
  obtain ⟨l₅, hl₅, meml₅⟩ :=  c.cover 2 2
  obtain ⟨l₆, hl₆, meml₆⟩ :=  c.cover 3 1
  rw [← hcls, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hl₄ hl₅ hl₆
  have hsunny := c.sunny
  simp [← hcls, Finset.filter_insert, Finset.filter_singleton] at hsunny
  rcases hl₄ with (rfl | rfl | rfl)
  · -- l₁ = l₄ must be non-sunny
    have hl₄ : ¬ Sunny l₄ := notSunny_of_horiz meml₁ meml₄
    rcases hl₅ with (rfl | rfl | rfl)
    · -- l₅ = l₄, finrank violated
      suffices h : finrank ℝ l₅.direction = 2
      · have := c.rank l₅ hl₁
        omega
      apply l₅.finrank_eq_two_of_ne meml₅ meml₄ meml₁ (by norm_num)
    · -- l₅ = l₂, only one sunny line
      have hl₅ : ¬ Sunny l₅ := notSunny_of_horiz meml₂ meml₅
      split_ifs at hsunny <;> simp at hsunny
    · -- l₅ = l₃, only one sunny line
      have hl₅ : ¬ Sunny l₅ := notSunny_of_diag meml₃ meml₅ (by simp; norm_num)
      split_ifs at hsunny <;> simp at hsunny
  · -- l₂ = l₄ must be non-sunny
    have hl₄ : ¬ Sunny l₄ := notSunny_of_diag meml₂ meml₄ (by simp)
    rcases hl₅ with (rfl | rfl | rfl)
    · -- l₅ = l₁, only one sunny line
      rcases hl₆ with (rfl | rfl | rfl)
      · -- l₆ = l₅
        have hl₆ : ¬ Sunny l₆ := notSunny_of_diag meml₅ meml₆ (by norm_num)
        split_ifs at hsunny <;> simp at hsunny
      · -- l₆ = l₄, finrank violated
        suffices h : finrank ℝ l₆.direction = 2
        · have := c.rank l₆ hl₂
          omega
        apply l₆.finrank_eq_two_of_ne meml₆ meml₂ meml₄ (by norm_num)
      · -- l₆ = l₃
        have hl₆ : ¬ Sunny l₆ := notSunny_of_diag meml₃ meml₆ (by simp)
        split_ifs at hsunny <;> simp at hsunny
    · -- l₅ = l₄, finrank violated
      suffices h : finrank ℝ l₅.direction = 2
      · have := c.rank l₅ hl₂
        omega
      apply l₅.finrank_eq_two_of_ne meml₅ meml₂ meml₄ (by norm_num)
    · -- l₅ = l₃
      have hl₅ : ¬ Sunny l₅ := notSunny_of_diag meml₃ meml₅ (by norm_num)
      split_ifs at hsunny <;> simp at hsunny
  · -- l₃ = l₄
    have hl₄ : Sunny l₄ := sunny_of_ne meml₄ meml₃ (by simp)
    rcases hl₅ with (rfl | rfl | rfl)
    · -- l₅ = l₁
      have hl₅ : Sunny l₅ := sunny_of_ne meml₁ meml₅ (by simp; norm_num)
      rcases hl₆ with (rfl | rfl | rfl)
      · -- l₆ = l₅, finrank violated
        suffices h : finrank ℝ l₆.direction = 2
        · have := c.rank l₆ hl₁
          omega
        apply l₆.finrank_eq_two_of_ne meml₅ meml₁ meml₆ (by norm_num)
      · -- l₆ = l₂, three sunny lines
        have hl₆ : Sunny l₆ := sunny_of_ne meml₆ meml₂ (by norm_num)
        split_ifs at hsunny
        omega
      · -- l₆ = l₄, finrank violated
        suffices h : finrank ℝ l₆.direction = 2
        · have := c.rank l₆ hl₃
          omega
        apply l₆.finrank_eq_two_of_ne meml₄ meml₃ meml₆ (by norm_num)
    · -- l₅ = l₂
      have hl₅ : ¬ Sunny l₅ := notSunny_of_horiz meml₅ meml₂ (by norm_num)
      rcases hl₆ with (rfl | rfl | rfl)
      · -- l₆ = l₁, only one sunny line
        have : ¬ Sunny l₆ := notSunny_of_horiz meml₁ meml₆ (by norm_num)
        split_ifs at hsunny; simp at hsunny
      · -- l₆ = l₅, finrank violated
        suffices h : finrank ℝ l₆.direction = 2
        · have := c.rank l₆ hl₂
          omega
        apply l₆.finrank_eq_two_of_ne meml₂ meml₅ meml₆ (by norm_num)
      · -- l₆ = l₄, finrank violated
        suffices h : finrank ℝ l₆.direction = 2
        · have := c.rank l₆ hl₃
          omega
        apply l₆.finrank_eq_two_of_ne meml₄ meml₃ meml₆ (by norm_num)
    · -- l₅ = l₄, finrank violated
      suffices h : finrank ℝ l₅.direction = 2
      · have := c.rank l₅ hl₃
        omega
      apply l₅.finrank_eq_two_of_ne meml₅ meml₃ meml₄ (by norm_num)

lemma no_config_3_2 (c : Config 3 2) : False := by
  by_cases h : ∀ l ∈ c.ls, ¬ l ∥ yAxis
  · apply no_config_3_2_no_vert c h
  · let c' := c.symm
    by_cases h' : ∀ l ∈ c'.ls, ¬ l ∥ yAxis
    · apply no_config_3_2_no_vert c' h'
    · simp at h h'
      obtain ⟨l₁, hl₁, yl₁⟩ := h
      obtain ⟨l₂, hl₂, xl₂⟩ := h'
      let l₂' := l₂.map (EuclideanGeometry.reflection line[ℝ, !₂[(0 : ℝ), 0], !₂[1, 1]]).toAffineMap
      have hl₂' : l₂' ∈ c.ls := by
        simp [l₂']
        simp [c', Config.symm] at hl₂
        obtain ⟨l₂'', hl₂'', rfl⟩ := hl₂
        convert hl₂''
        ext
        simp
      obtain ⟨l₃, hl₃, meml₃⟩ := c.cover 2 2
      -- `c.ls` contains two distinct non-sunny lines
      have nsunnyl₁ : ¬ Sunny l₁ := fun h => by simp [Sunny, yl₁] at h
      have yl₂' : l₂' ∥ xAxis := sorry
      have nsunnyl₂' : ¬ Sunny l₂' := fun h => by simp [Sunny, yl₂'] at h
      -- `l₁` and `l₂'` are distinct because they have different directions
      have : l₁ ≠ l₂' := fun h => by
        subst h
        have := yl₂'.symm.trans yl₁
        simp [xAxis, yAxis] at this
        have := AffineSubspace.Parallel.vectorSpan_eq this
        sorry
      have hsunny := c.sunny
      rw [← Finset.union_sdiff_of_subset (Finset.insert_subset hl₁
        (Finset.singleton_subset_iff.mpr hl₂')),
        Finset.filter_union, Finset.card_union_of_disjoint
        (Finset.disjoint_filter_filter Finset.sdiff_disjoint.symm),
        Finset.filter_insert, Finset.filter_singleton] at hsunny
      simp [nsunnyl₁, nsunnyl₂'] at hsunny
      have : #({l ∈ c.ls \ {l₁, l₂'} | Sunny l}) ≤ 1 :=
      calc
        _ ≤ #(c.ls \ {l₁, l₂'}) := Finset.card_filter_le _ Sunny
        _ = #(c.ls \ {l₂'}) - 1 := by rw [Finset.sdiff_insert,
              Finset.card_erase_of_mem (by simp [this, hl₁])]
        _ = #c.ls - 1 - 1 := by rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hl₂']
        _ = 1 := by rw [c.card]
      omega

theorem result (n : Set.Ici 3) :
    {k | ∃ lines : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))),
      have : DecidablePred Sunny := Classical.decPred _;
      #lines = n ∧ (∀ l ∈ lines, finrank ℝ l.direction = 1) ∧
      (∀ a b : ℕ, 0 < a → 0 < b → a + b ≤ (n : ℕ) + 1 → ∃ l ∈ lines, !₂[(a : ℝ), b] ∈ l) ∧
      #{l ∈ lines | Sunny l} = k} = answer n := by
  induction' n.1, n.2 using Nat.le_induction with n hn ih
  · simp only [Nat.reduceAdd, answer]
    ext k; constructor
    · rintro ⟨ls, cardls, rankls, linesls, rfl⟩
      have hk : #({l ∈ ls | Sunny l}) < 4 := by
        apply lt_of_le_of_lt (Finset.card_filter_le ls Sunny)
        rw [cardls]
        norm_num
      have hk' := fun h => no_config_3_2 ⟨ls, cardls, rankls, linesls, h⟩
      interval_cases #({l ∈ ls | Sunny l}) <;> first | contradiction | decide
    · intro h
      rcases n with ⟨n, hn⟩; simp at hn
      rcases h with (rfl|(rfl|rfl))
      · apply zero_mem3
      · apply one_mem3
      · apply three_mem3
  · simp [answer] at ih ⊢
    sorry

end IMO2025P1
