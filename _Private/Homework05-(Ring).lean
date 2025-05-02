import Mathlib.Tactic
import Mathlib.GroupTheory.Coset


section Exercise_259
/-
In an integral domain a prime element is always irreducible.
-/
noncomputable example {R : Type*}[CommRing R][IsDomain R]{p : R}(hp : Prime p): Irreducible p where
  not_unit := Prime.not_unit hp
  isUnit_or_isUnit' := by
    --Suppose ( $p$ ) is a nonzero prime ideal and $p=a b$. Then $a b=p \in(p)$,
    intro a b h
    -- so by definition of prime ideal one of $a$ or $b$, say $a$, is in $(p)$.
    rcases Prime.dvd_or_dvd hp (dvd_of_eq h) with ha | hb
    · right
      --Thus $a=p r$ for some $r$.
      rcases ha with ⟨qa, ha⟩
      have : qa * b = 1 := by
        have : p * (1 - qa * b) = 0 := by calc
          _ = p - (p * qa) * b := by ring
          _ = p - p := by rw [← ha, h]
          _ = _ := by ring
        simp only [mul_eq_zero] at this
        have : p ≠ 0 := Prime.ne_zero hp
        -- This implies $p=a b=p r b$ so $r b=1$ and $b$ is a unit.
        have : 1 - qa * b = 0 := by tauto
        calc
          _ = 1 - (1 - qa * b) := by ring
          _ = _ := by rw [this]; norm_num
      exact isUnit_of_mul_eq_one_right qa b this
      -- This shows that $p$ is irreducible.
    · left
      rcases hb with ⟨qb, hb⟩
      have : qb * a = 1 := by
        have : p * (1 - qb * a) = 0 := by calc
          _ = p - a * (p * qb) := by ring
          _ = _ := by rw [← hb, h]; ring
        simp only [mul_eq_zero] at this
        have : p ≠ 0 := Prime.ne_zero hp
        have : 1 - qb * a = 0 := by tauto
        calc
          _ = 1 - (1 - qb * a) := by ring_nf
          _ = _ := by rw [this]; norm_num
      exact isUnit_of_mul_eq_one_right qb a this

/-
In a Principal Ideal Domain a nonzero element is irreducible, then it is a prime.
-/
noncomputable example {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {p : R}(hp : Irreducible p) : Prime p := by
  --We must show conversely that if $p$ is irreducible, then $p$ is a prime, i.e., the ideal $(p)$ is a prime ideal.
  have : Ideal.IsMaximal (Submodule.span R {p}) :=
    PrincipalIdealRing.isMaximal_of_irreducible hp
  --If $M$ is any ideal containing $(p)$ then by hypothesis $M=(m)$ is a principal ideal. Since $p \in(m), p=r m$ for some $r$. But $p$ is irreducible so by definition either $r$ or $m$ is a unit. This means either $(p)=(m)$ or $(m)=(1)$, respectively. Thus the only ideals containing ( $p$ ) are ( $p$ ) or (1), i.e., $(p)$ is a maximal ideal.
  have : Ideal.IsPrime (Submodule.span R {p}) := Ideal.IsMaximal.isPrime this
  -- Since maximal ideals are prime ideals, the proof is complete.
  exact irreducible_iff_prime.mp hp

end Exercise_259



section Exercise_1769
/-
Let $A$ be a commutative ring, and let $J$ and $K$ be ideals of $A$.

Prove the following parts:

1 If $J \cap K=\{0\}$, then $j k=0$ for every $j \in J$ and $k \in K$.

2 For any $a \in A, I_{a}=\{a x+j+k: x \in A, j \in J, k \in K\}$ is an ideal of $A$.
-/
variable {A : Type*}[CommRing A](J : Ideal A)(K : Ideal A)

example (h : J ⊓ K = ⊥) : ∀ j ∈ J, ∀ k ∈ K , j * k = 0 := by
  intro j hj k hk
  --We have $jk \in J$ and $jk \in K$,hence $jk \in J \cap K$
  have : j * k ∈ J ⊓ K := by
    refine Submodule.mem_inf.mpr ?_
    constructor
    · exact Ideal.mul_mem_right k J hj
    · exact Ideal.mul_mem_left K j hk
  --i.e. $jk = 0$,we are done
  rw [h] at this
  exact this

def I (a : A) : Set A := {t | ∃ x: A, ∃j ∈ J, ∃k ∈ K, a * x + j + k = t}

example (a : A) : Ideal A where
  carrier := I J K a
  add_mem' := by
    --We have if $s = a * x_{1} + j_{1} + k_{1}$ and $t = a * x_{2} + j_{2} + k_{2}$ $\in I$
    intro s t ⟨x, j₁, hj₁, k₁, hk₁, hs⟩ ⟨y, j₂, hj₂, k₂, hk₂, ht⟩
    --Then $s + t = a * (x_{1} + x_{2}) + (j_{1} + j_{2}) + (k_{1} + k_{2})$
    use x + y, j₁ + j₂
    constructor
    · exact (Submodule.add_mem_iff_right J hj₁).mpr hj₂
    · use k₁ + k₂
      constructor
      · exact (Submodule.add_mem_iff_right K hk₁).mpr hk₂
      · rw [← hs, ← ht]
        ring
  zero_mem' := by
    --We have $0 \in I$ because $0 = a \cdot 0 + 0 + 0$ where $0 \in A J K$
    simp only
    use 0, 0
    constructor
    · exact Submodule.zero_mem J
    · use 0
      constructor
      · exact Submodule.zero_mem K
      · ring
  smul_mem' := by
    intro c x ⟨x, j, hj, k, hk, hx⟩
    simp only [smul_eq_mul]
    --We have if $s = a * x + j + k \in I$
    use c * x, c * j
    --Then $c * s = a * (c * x) + (c * j) + (c * k) \in I$
    constructor
    · exact Ideal.mul_mem_left J c hj
    · use c * k
      constructor
      · exact Ideal.mul_mem_left K c hk
      · rw [← hx]
        ring

end Exercise_1769



section Special_Example_072701

open BigOperators Classical

/-
If the product of a finite number of elements in the commutative semiring $R$ lies in the prime ideal $p$, then at least one of those elements is in $p$.
-/
theorem IsPrime.prod_mem {R ι : Type*} [CommSemiring R] {p : Ideal R} [hp : p.IsPrime] {s : Finset ι}
  {x : ι → R} (h : ∏ i in s, x i ∈ p) : ∃ i : s, x i ∈ p := by
  --We do induction on the cardinality of the finite set $S$.
  generalize hn : s.card = n
  induction' n with n ih generalizing s
  · -- When $S$ is an empty set, the condition is false
    rw [Finset.card_eq_zero] at hn
    subst hn
    simp only [IsEmpty.exists_iff]
    have : p = ⊤ := (Ideal.eq_top_iff_one p).mpr h
    have : p ≠ ⊤ := Ideal.IsPrime.ne_top hp
    contradiction
  · --Suppose for any $\operatorname S = n(n\ge 0)$ the hypothesis holds true
    classical
    --, then for ${n+1}$, we take a subset $T$ with $n$ elements. Then we do some case analysis.
    replace hn : ∃ (i : ι) (t : Finset ι), i ∉ t ∧ insert i t = s ∧ t.card = n := Finset.card_eq_succ.mp hn
    --We suppose $i_{0}$ which $\nin T$ and $T \cup \{i_{0}\} = S$
    rcases hn with ⟨i, t, int, its, ht⟩
    by_cases Ht : x i ∈ p
    · --If there are $x_{i_{0}} \in p$
      have : i ∈ s := by
        rw [← its]
        exact Finset.mem_insert_self i t
      --Then we use $i_{0}$ is done
      use ⟨i, this⟩
    · --We have $x_{i_{0}} \cdot \prod_{i \in T}{x_i} \in p$
      rw [← its, Finset.prod_insert int] at h
      --Because p is a prime ideal,hence $\prod_{i \in T}{x_i} \in p$ or $x_{i_{0}} \in p$
      have : x i ∈ p ∨ ∏ i ∈ t, x i ∈ p := Ideal.IsPrime.mem_or_mem hp h
      have h : ∏ i ∈ t, x i ∈ p := by tauto
      --Then $\prod_{i \in T}{x_i} \in p$ as we assume that $x_{i_{0}} \nin p$
      have : ∃ i : t, x i ∈ p := ih h ht
      --Thus we use the inductive hypothesis and we have there exists $j \in T$ which $x_j \in p$
      rcases this with ⟨j,jh⟩
      have : (j: ι) ∈ s := by
        rw [← its]
        have : (j : ι) ∈ t := Finset.coe_mem j
        exact Finset.mem_insert_of_mem this
      --and we use this $j$ and we are done
      use ⟨(j : ι),this⟩

end Special_Example_072701




section Example_1755
/-
A ring $A$ is a boolean ring if $a^{2}=a$ for every $a \in A$. Prove that parts 1 and 2 are true in any boolean ring A.

1 For every $a \in A, a=-a$. [HinT: Expand $(a+a)^{2}$.]

2 Use part 1 to prove that $A$ is a commutative ring. [HINT: Expand $(a+b)^{2}$.]
-/
lemma part1{A : Type*}[Ring A](ha : ∀ a : A, a ^ 2 = a)(a : A) : a = -a := by
  --We have $a + a = (a + a) ^ 2 = a ^ 2 + a ^ 2 + a ^ 2 + a ^ 2 = a + a = a + a + a + a$
  have : a + a = a + a + (a + a) := by
    calc
      _ = (a + a) ^ 2 := by rw [ha (a + a)]
      _ = (a + a) * (a + a) := pow_two (a + a)
      _ = a * (a + a) + a * (a + a) := by rw [@NonUnitalNonAssocRing.right_distrib]
      _ = a * a + a * a + (a * a + a * a) := by rw [@left_distrib]
      _ = a ^ 2 + a ^ 2 + (a ^ 2 + a ^ 2) := by rw [pow_two a]
      _ = _ := by rw [ha]
  --Hence $a + a = 0$ and we are done
  have : a + a = 0 := by exact self_eq_add_right.mp this
  exact eq_neg_of_add_eq_zero_left this

example {A : Type*}[Ring A](ha : ∀ a : A, a ^ 2 = a) : CommRing A := by
  apply CommRing.mk
  intro a b
  --For all $a b$, we have $(a + b) = (a + b) ^ 2 = a ^ 2 + b ^ 2 + a b + b a = a + b + a b + b a$
  have : a + b = a + b + (a * b + b * a) := by
    calc
      _ = (a + b) ^ 2 := by rw [ha]
      _ = (a + b) * (a + b) := pow_two (a + b)
      _ = a * (a + b) + b * (a + b) := by rw [@NonUnitalNonAssocRing.right_distrib]
      _ = a * a + a * b + (b * a + b * b) := by rw [@left_distrib, @left_distrib]
      _ = a * a + (a * b + (b * a + b * b)) := by rw [@AddSemigroup.add_assoc]
      _ = a * a + ((a * b + b * a) + b * b) := by rw [@AddSemigroup.add_assoc]
      _ = a * a + (b * b + (a * b + b * a)) := by rw [@add_left_cancel_iff, @AddCommMonoidWithOne.add_comm]
      _ = a * a + b * b + (a * b + b * a) := by rw [@AddSemigroup.add_assoc]
      _ = a ^ 2 + b ^ 2 + (a * b + b * a) := by rw [pow_two a, pow_two b]
      _ = _ := by rw [ha, ha]
  --Hence $a b + b a = 0$
  have t1 : a * b + b * a = 0 := by exact self_eq_add_right.mp this
  --And according to part1 we have $a b + a b = 0$
  have t2 : a * b = - (a * b) := by exact part1 ha (a * b)
  rw [t2] at t1
  --Hence $a b = b a$
  symm
  calc
    _ = -(a * b) + a * b + b * a := by rw [@self_eq_add_left, @neg_add_eq_zero]
    _ = -(a * b) + (a * b + b * a) := by rw [@AddSemigroup.add_assoc]
    _ = -(a * b) + (b * a + a * b) := by rw [@add_left_cancel_iff, @AddCommMonoidWithOne.add_comm]
    _ = -(a * b) + b * a + a * b := by rw [@AddSemigroup.add_assoc]
    _ = _ := by rw [t1]; simp only [zero_add]

end Example_1755
