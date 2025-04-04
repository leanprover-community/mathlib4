import Mathlib.Tactic
import Mathlib.Data.Matrix.Rank

section Special_Example_070301
/-
Let $r$ and $n$ be natural numbers, and let $G$ be the set of all $n \times n$ complex matrices with rank no greater than $r$. Prove that $G$ forms a semigroup under matrix multiplication.
-/
noncomputable example (n r : ℕ) : Semigroup {A : Matrix (Fin n) (Fin n) ℂ // Matrix.rank A ≤ r} where
  mul := by
    rintro ⟨A, ha⟩ ⟨B, _⟩
    use A * B
    linarith [Matrix.rank_mul_le_left A B]
  mul_assoc := by
    intro ⟨A, ha⟩ ⟨B, hb⟩ ⟨C, hc⟩
    have : A * (B * C) = A * B * C := by rw[Matrix.mul_assoc A B C]
    exact Eq.symm (SetCoe.ext this)

end Special_Example_070301



section Special_Example_070302
/-
Let $A$ and $B$ be two subgroups of group $G$. Prove that $A \cup B$ is a subgroup of $G$ if and only if $A \le B$ or $B \le A$. Furthermore, prove that group $G$ cannot be expressed as the union of two proper subgroups.
-/
lemma Subgroup.union_subgroup_iff {G : Type*} [Group G] {A B : Subgroup G} :
    (∃ C : Subgroup G , C.carrier = (A.carrier ∪ B.carrier)) ↔
    (A.carrier ⊆ B.carrier) ∨ (B.carrier ⊆ A.carrier) := by
  constructor
  · intro ⟨C, hc⟩
    by_contra h'; push_neg at h'; rcases h' with ⟨h₁,h₂⟩
    have h1 : ∃ g₁, g₁ ∈ A.carrier ∧ g₁ ∉ B.carrier := by
      by_contra h₁'; push_neg at h₁'
      have : A.carrier ⊆ B.carrier := by exact h₁'
      contradiction
    have h2 : ∃ g₂, g₂ ∈ B.carrier ∧ g₂ ∉ A.carrier := by
      by_contra h₂'; push_neg at h₂'
      have : B.carrier ⊆ A.carrier := by exact h₂'
      contradiction
    rcases h1 with ⟨g₁, g₁A, g₁nB⟩
    rcases h2 with ⟨g₂, g₂B, g₂nA⟩
    have g₁C: g₁ ∈ C.carrier := by rw [hc]; exact Set.mem_union_left B.carrier g₁A
    have g₂C: g₂ ∈ C.carrier := by rw [hc]; exact Set.mem_union_right A.carrier g₂B
    have : g₁ * g₂ ∈ C.carrier := by exact C.mul_mem' g₁C g₂C
    rw [hc] at this
    rcases this with h | h
    · have : g₁⁻¹ ∈ A.carrier := by exact A.inv_mem' g₁A
      have g₂A : g₁⁻¹ * (g₁ * g₂) ∈ A.carrier := by exact A.mul_mem' this h
      have : g₁⁻¹ * (g₁ * g₂) = g₂ := by group
      have : g₂ ∈ A.carrier := by rw [← this]; exact g₂A
      contradiction
    · have : g₂⁻¹ ∈ B.carrier := by exact B.inv_mem' g₂B
      have g₂A : (g₁ * g₂) * g₂⁻¹∈ B.carrier := by exact B.mul_mem' h this
      have : (g₁ * g₂)  * g₂⁻¹= g₁ := by group
      have : g₁ ∈ B.carrier := by rw [← this]; exact g₂A
      contradiction
  · intro h
    rcases h with h | h
    · use B
      exact Eq.symm (Set.union_eq_self_of_subset_left h)
    · use A
      exact Eq.symm (Set.union_eq_self_of_subset_right h)

/-
It is impossible to have two proper subgroups of a group $G$ such that their union is the entire group.
-/
example (G : Type*) [Group G] : ¬ ∃ A B : Subgroup G, (A < ⊤ ∧ B < ⊤)
     ∧ A.carrier ∪ B.carrier = Set.univ := by
  rintro ⟨A, B, ⟨ha, hb⟩, h⟩
  have ABeqG: A.carrier ∪ B.carrier = ⊤ := by exact h
  have : ∃ C : Subgroup G , C.carrier = (A.carrier ∪ B.carrier) := by
    use ⊤
    exact id (Eq.symm h)
  have h: (A.carrier ⊆ B.carrier) ∨ (B.carrier ⊆ A.carrier) := Subgroup.union_subgroup_iff.mp this
  rcases h with h | h
  · have ABeqB: A.carrier ∪ B.carrier = B.carrier := by exact Set.union_eq_self_of_subset_left h
    rw [ABeqG] at this
    have : B.carrier = B := by exact rfl
    nth_rw 2[this] at ABeqB
    rw [ABeqB] at ABeqG
    have : ⊤ < ⊤ := by nth_rw 1[← ABeqG]; exact hb
    exact (and_not_self_iff (⊤ ⊆ ⊤)).mp this
  · have ABeqA: A.carrier ∪ B.carrier = A.carrier := by exact Set.union_eq_self_of_subset_right h
    rw [ABeqG] at this
    have : A.carrier = A := by exact rfl
    nth_rw 2[this] at ABeqA
    rw [ABeqA] at ABeqG
    have : ⊤ < ⊤ := by nth_rw 1[← ABeqG]; exact ha
    exact (and_not_self_iff (⊤ ⊆ ⊤)).mp this

end Special_Example_070302



section Special_Example_070201
/-
A variant of Bezout's theorem: If $s$ and $t$ are natural numbers and $t > 0$, then there exist natural numbers $m$ and $n$ such that $s \cdot m + \mathrm{gcd}(s, t) = t \cdot n$.
-/
lemma upup (d s t: ℕ) (a b : ℤ) (ha: a ≥ 0) (hb: b ≥ 0) (h: s * a + d = t * b) : ∃ m n : ℕ, s * m + d = t * n := by
  refine' ⟨(Int.natAbs a), (Int.natAbs b), _⟩
  rw [← (Int.natAbs_of_nonneg ha), ← (Int.natAbs_of_nonneg hb)] at h
  exact Int.ofNat_inj.1 h

theorem Nat.bezout {s t : ℕ } (h₂: 0 < t): ∃ m : ℕ ,∃ n : ℕ , s * m + Nat.gcd s t = t * n := by
  by_cases h₁: s ≤ 0
  · have : s = 0 := by linarith
    use 1, 1
    rw [this]
    norm_num
  · push_neg at h₁
    let x := Nat.gcdA s t
    let y := Nat.gcdB s t
    have L1 : s * (t * (|x| + |y|) - x) +  s.gcd t = t * (s *(|x| + |y|) + y) := by
      rw [Nat.gcd_eq_gcd_ab]
      ring
    have L2 : 0 ≤ (t * (|x| + |y|) - x) := by
      calc
        _ ≤ (|x| + |y|) - x := by linarith [le_abs_self x, abs_nonneg y]
        _ = 1 * (|x| + |y|) - x := by ring
        _ ≤ _ := by
          apply Int.sub_le_sub_right _ x
          apply mul_le_mul_of_nonneg_right
          · exact Int.toNat_le.mp h₂
          · linarith [abs_nonneg x, abs_nonneg y]
    have L3 : 0 ≤ (s * (|x| + |y|) + y) := by
      calc
        _ ≤ (|x| + |y|) + y := by linarith [neg_le_abs y, abs_nonneg x]
        _ = 1 * (|x| + |y|) + y := by ring
        _ ≤ _ := by
          apply Int.add_le_add_right _ y
          apply mul_le_mul_of_nonneg_right
          · exact Int.toNat_le.mp h₁
          · linarith [abs_nonneg x, abs_nonneg y]
    exact upup (Nat.gcd s t) s t (t * (|x| + |y|) - x) (s * (|x| + |y|) + y) L2 L3 L1

end Special_Example_070201
