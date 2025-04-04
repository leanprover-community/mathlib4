import Mathlib.Tactic

/-
Let $A$ be a non-empty finite subset of a group $G$ . Then $A$ is a subgroup of $G$ if and only if for any elements $a,b ∈ A$, we have $ab ∈ A$.
-/
section Special_Example_070404

example { G : Type* } [ Group G ] (A : Subgroup G): ∀ a b : G, a ∈ A → b ∈ A → a * b ∈ A := by
  intro a b ha hb
  exact (Subgroup.mul_mem_cancel_right A hb).mpr ha

lemma pow_inA { G : Type* } [ Group G ] (A : Finset G)(h : ∀ a b : G, a ∈ A → b ∈ A → a * b ∈ A)
    (n : ℕ)(a : G)(ha : a ∈ A): a ^ (n + 1) ∈ A:= by
  induction' n with n ih
  · ring_nf; norm_num; exact ha
  · rw [pow_succ a (n + 1)]
    exact h (a ^ (n + 1)) a ih ha

lemma order_pos{ G : Type* } [ Group G ] (A : Finset G)(h : ∀ a b : G, a ∈ A → b ∈ A → a * b ∈ A)(a : G)(ha : a ∈ A) :
    orderOf a ≥ 1 := by
  let f : ℕ → A := fun n => ⟨a ^ (n + 1), pow_inA A h n a ha⟩
  have : ∃ x y: ℕ , x ≠ y ∧ f x = f y := by exact Finite.exists_ne_map_eq_of_infinite fun x => f x
  rcases this with ⟨x, y, neq, feq⟩
  have : ∃ x y: ℕ , x < y ∧ f x = f y := by
    rcases Nat.lt_or_gt_of_ne (id (Ne.symm neq)) with h | h
    · use y, x
      constructor
      · exact h;
      · symm; exact feq
    · use x, y
  rcases this with ⟨x, y, neq, feq⟩
  have : a ^(y - x : ℕ) * a ^ (x + 1) = a ^ (x + 1) := by--注意类型转化
    calc
      _ = a ^ ((y - x) + (x + 1)) := by rw [← pow_add a (y - x) (x + 1)]
      _ = a ^ (y + 1) := by
        congr 1--(只拆1层括号)（如果不加，则会全拆括号，然后对应匹配 y-x = y , x + 1 = 1两个goal），or :apply congrArg
        zify [neq]--扩域
        ring
      _ = (f y).1 := rfl
      _ = (f x).1 := by exact congrArg Subtype.val (id (Eq.symm feq))
      _ = _ := rfl
  have : a ^(y - x : ℕ) =1:= by exact self_eq_mul_left.mp (id (Eq.symm this))
  have : orderOf a ≠ 0:= by
    by_contra nh
    have : a ^(y - x : ℕ) ≠ 1 := by
      apply orderOf_eq_zero_iff'.mp nh
      exact Nat.zero_lt_sub_of_lt neq
    contradiction
  exact Nat.one_le_iff_ne_zero.mpr this

example { G : Type* } [ Group G ] (A : Finset G)(A_nonempty : A.Nonempty)(h : ∀ a b : G, a ∈ A → b ∈ A → a * b ∈ A) : Subgroup G where
  carrier := A
  mul_mem' := by
    intro a b ha hb
    exact h a b ha hb
  one_mem' := by
    have : ∃ a : G, a ∈ A := by exact A_nonempty
    rcases this with ⟨a, ha⟩
    -- let a' := Classical.choice <| Finset.Nonempty.coe_sort <| A_nonempty
    have t1: a ^ (orderOf a - 1 + 1) = a ^ orderOf a := by
      congr
      apply Nat.sub_add_cancel (order_pos A h a ha)
    have : a ^ (orderOf a -1 + 1) ∈ A := pow_inA A h ((orderOf a-1):ℕ) a ha
    rw [t1] at this
    rw [← pow_orderOf_eq_one a]
    exact this
  inv_mem' := by
    intro a ha
    dsimp
    have : a * a ^ (orderOf a - 1) = 1 := by
      calc
        _ = a ^ orderOf a := by
          apply mul_pow_sub_one
          linarith[order_pos A h a ha]
        _ = _:= by exact pow_orderOf_eq_one a
    have : a ^ (orderOf a - 1) = a⁻¹ := by rw[DivisionMonoid.inv_eq_of_mul a (a ^ (orderOf a - 1)) this]
    rw [← this]
    rcases le_or_lt 2 (orderOf a) with h₁ | h₁
    · have : ∃ y : ℕ, y = orderOf a - 2 := by exact exists_apply_eq_apply (fun a => a) (orderOf a - 2)
      rcases this with ⟨y,hy⟩
      have : a ^ (((orderOf a -2):ℕ) + 1) = a ^ ((orderOf a-1):ℕ) := by congr; omega--高级货
      rw [← this, ← hy]
      exact pow_inA A h y a ha
    · have specialcase: orderOf a = 1 :=by linarith[Nat.le_of_lt_succ h₁, order_pos A h a ha]
      have h₂: a = 1 := by exact orderOf_eq_one_iff.mp specialcase
      have : a ^ (orderOf a - 1) = 1 := by
        calc
          _ = a ^ 0:= by rw[specialcase]
          _ = _ := by exact pow_zero a
      rw [this]
      exact Set.mem_of_eq_of_mem (id (Eq.symm h₂)) ha

end Special_Example_070404
