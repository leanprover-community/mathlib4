import Mathlib

--191 : 设 $A$ 是群 $G$ 的非空有限子集, 则 $A$ 是 $G$ 的子群当且仅当对任意元 $a$, $b \\in A, a b \\in A$.

--lemma1 : $\all x \in A,\all n \in \mathbb {N} n > 0$ we have $ x^n \in A$
--by induction,for $n=1$ we have $x^1 \in A$
--when $x^n \in A$, we also have $x \in A$
--thus $x^(n+1) = x^n * x \in A$ done.

--lemma2 : $\all x \in A$ $x$ has finite order.
--prove by contradiction
--$x$ have infinite order, so $x^n \ne x^m$ for $n \ne m$
--but $n \mapsto x^n$ is not injective from $\mathbb {N} to A$ because $A$ is finite,contradicts


--lemma3 : $\all x \in A$ $x^{-1} \in A$
--if $x=1$ $x^{-1} = 1 \in A$
--else we have $x \ne 1$ thus $orderOf x \ge 2$
--by lemma1 $x^(orderOf x -1)$ is in A
--$x^(orderOf x -1) * x = x^(orderOf x) = 1$,thus $x^{-1} = x^(orderOf x -1) \in A$

--To prove the main theorem
--case1 : ←
--we only have to check that A is closed under multiplication,inversion and $1 \in A$
--closed under multiplication is given
--closed under inversion is proved by lemma3
--because A is nonempty there exist $x \in A$
--by closed under inversion is proved by lemma3
--$x^{-1} \in A$ thus $1 = x^{-1} * x \in A$
--case2 : →
--A is subgroup thus closed under multiplication

--lemma1 : $\all x \in A,\all n \in \mathbb {N} n > 0$ we have $ x^n \in A$
lemma exercise191_lemma1 {G : Type*} [Group G] (A : Finset G) (h : ∀ a b : G,a ∈ A ∧ b ∈ A → a * b ∈ A) (x : G): x ∈ A → ∀ n, x ^ (n + 1) ∈ A := by
  intro xinA n
  --by induction,
  induction' n with n ih
  --for $n=1$ we have $x^1 \in A$
  · simp only [zero_add, pow_one,xinA]
  --when $x^n \in A$, we also have $x \in A$
  --thus $x^(n+1) = x^n * x \in A$ done.
  · rw[pow_succ x (n + 1)]
    apply h
    simp only [ih, xinA, and_self]

--lemma2 : $\all x \in A$ $x$ has finite order.
lemma exercise191_lemma2 {G : Type*} [Group G] (A : Finset G) (h : ∀ a b : G,a ∈ A ∧ b ∈ A → a * b ∈ A) : ∀ x : G, x ∈ A → IsOfFinOrder x := by
  intro x xinA
  --prove by contradiction
  by_contra nfin
  have ord0: orderOf x = 0 := by apply orderOf_eq_zero_iff.mpr nfin
  --$x$ have infinite order, so $x^n \ne x^m$ for $n \ne m$
  have inj : ∀ n m : ℕ, x ^ n = x ^ m ↔ n = m := by
    intro n m
    apply pow_inj_iff_of_orderOf_eq_zero ord0
  absurd inj
  --but $n \mapsto x^n$ is not injective from $\mathbb {N} to A$ because $A$ is finite,contradicts
  have := Finite.exists_ne_map_eq_of_infinite (fun n ↦ (⟨x ^ (n + 1), exercise191_lemma1 A h x xinA n⟩ : A))
  simp only [ne_eq, Subtype.mk.injEq] at this
  rcases this with ⟨n,m,heq⟩
  push_neg
  use (n + 1),(m + 1)
  simp only [heq, ne_eq, add_left_inj, not_false_eq_true, and_self, not_true_eq_false, or_false]

--lemma3 : $\all x \in A$ $x^{-1} \in A$
lemma exercise191_lemma3 {G : Type*} [Group G] (A : Finset G) (h : ∀ a b : G,a ∈ A ∧ b ∈ A → a * b ∈ A): ∀ x : G, x ∈ A → x⁻¹ ∈ A := by
  intro x xinA
  have : IsOfFinOrder x := exercise191_lemma2 A h x xinA
  by_cases eq1 : x = 1
  --if $x=1$ $x^{-1} = 1 \in A$
  · simp only [eq1, inv_one]
    rw [eq1] at xinA
    exact xinA
  --else we have $x \ne 1$ thus $orderOf x \ge 2$
  · have ordpos: orderOf x > 0 := IsOfFinOrder.orderOf_pos this
    have ordne1: orderOf x ≠ 1 := (orderOf_eq_one_iff.mp).mt eq1
    have ordge2: 2 ≤ orderOf x := by
      apply (Nat.two_le_iff (orderOf x)).mpr
      simp only [ne_eq, ordne1, not_false_eq_true, and_true,Nat.not_eq_zero_of_lt ordpos]
    --by lemma1 $x^(orderOf x -1)$ is in A
    have inv_inA': x ^ (orderOf x -2 + 1) ∈ A := exercise191_lemma1 A h x xinA (orderOf x - 2)
    --$x^(orderOf x -1) * x = x^(orderOf x) = 1$,thus $x^{-1} = x^(orderOf x -1) \in A$
    have : x ^ (orderOf x -2 + 1) = x⁻¹ := by
      calc
        _= x ^ (orderOf x -2 + 1) * x * x⁻¹ := by group
        _= x ^ (orderOf x -2 + 1 + 1) * x⁻¹ := by rw [pow_succ x (orderOf x -2 + 1)]
        _= x ^ (orderOf x -2 + 1 + 1) * x⁻¹ := by dsimp
        _= x ^ orderOf x * x⁻¹ := by rw [Nat.sub_add_cancel ordge2]--**key**
        _= _ := by simp only [pow_orderOf_eq_one x, one_mul]
    rw[← this]
    exact inv_inA'
--To prove the main theorem
--case1 : ←
def exercise191_1 {G : Type*} [Group G] (A : Finset G) (h : ∀ a b : G,a ∈ A ∧ b ∈ A → a * b ∈ A) (ne : A.Nonempty): Subgroup G where
  carrier := A
  --we only have to check that A is closed under multiplication,inversion and $1 \in A$
  --closed under multiplication is given
  mul_mem' := by
    intro a b ha hb
    apply h
    constructor
    · exact ha
    · exact hb
  --closed under inversion is proved by lemma3
  inv_mem' := by
    simp only [Finset.mem_coe]
    intro x
    exact exercise191_lemma3 A h x
  --because A is nonempty there exist $x \in A$
  one_mem' := by
    simp only [Finset.mem_coe]
    rcases ne with ⟨x,xinA⟩
    --by closed under inversion is proved by lemma3 $x^{-1} \in A$ thus $1 = x^{-1} * x \in A$
    have inv_inA: x⁻¹ ∈ A := exercise191_lemma3 A h x xinA
    rw [← mul_inv_self x]
    apply h
    simp [xinA,inv_inA]

--case2 : →
theorem exercise191_2 {G : Type*} [Group G] (A : Subgroup G) [Finite A] : ∀ a b : G, a ∈ A ∧ b ∈ A → a * b ∈ A := by
  --A is subgroup thus closed under multiplication
  intro a b hab
  apply mul_mem hab.1 hab.2




--**Method 2**

#check Fintype.bijective_iff_injective_and_card

lemma exercise191_lemma' {G : Type*} [Group G] {A : Finset G} (h : ∀ a b : G,a ∈ A → b ∈ A → a * b ∈ A){x : G}(hx : x ∈ A)
 : ∀ y ∈ A , ∃ z ∈ A ,z * x = y := by
  let f : A → A := by
    intro y
    use y.1 * x
    exact h y.1 x y.2 hx
  have inj : Function.Injective f := by
    intro y z heq
    have : y * x = z * x := by
      show (f y).1 = (f z).1
      rw [heq]
    simp only [mul_left_inj] at this
    exact SetCoe.ext this
  have bij : Function.Bijective f := by
    exact Finite.injective_iff_bijective.mp inj
  intro y hy
  rcases bij.2 ⟨y, hy⟩ with ⟨z, hz⟩
  have : z * x = y := by
    show (f z).1 = y
    rw [hz]
  use z.1
  simp only [z.2, Finset.coe_mem, true_and, this]

def exercise191_1' {G : Type*} [Group G] {A : Finset G} (h : ∀ a b : G,a ∈ A → b ∈ A → a * b ∈ A) (ne : A.Nonempty): Subgroup G where
  carrier := A
  mul_mem' := by
    intro a b ha hb
    exact h a b ha hb
  inv_mem' := by
    intro x hx
    have := exercise191_lemma' h hx x hx
    rcases this with ⟨u, uinA, hu⟩
    have : u = 1 := self_eq_mul_left.mp (id (Eq.symm hu))
    rw [this] at uinA
    have := exercise191_lemma' h hx 1 uinA
    rcases this with ⟨inv, invinA, hinv⟩
    have : inv = x⁻¹ := eq_inv_of_mul_eq_one_left hinv
    rw [this] at invinA
    exact invinA
  one_mem' := by
    rcases ne with ⟨x, hx⟩
    have := exercise191_lemma' h hx x hx
    rcases this with ⟨u, uinA, hu⟩
    have : u = 1 := self_eq_mul_left.mp (id (Eq.symm hu))
    rw [this] at uinA
    exact uinA
