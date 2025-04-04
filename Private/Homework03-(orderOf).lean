import Mathlib.Tactic
import Mathlib.Tactic.LinearCombination



section Example_1510B
/-
Let $G$ and $H$ be groups. Prove that if $G \times H$ is a cyclic group, then $G$ and $H$ are both cyclic.
-/
example {G H : Type*} [Group G] [Group H] (h : IsCyclic (G × H) ) : (IsCyclic G) ∧ (IsCyclic H) := by
  rcases h with ⟨g, hg⟩
  constructor
  · --1.We suppose that $g=(x,y)$ is the generator of $G \times H$ and we will prove that x is the generator of $G$,
    use g.1
    intro x
    let x1 : G × H := ⟨x, 1⟩
    rcases hg x1 with ⟨tx, hx⟩
    use tx
    --because $g ^ n = (x^n,y^n)$ and so every element in $H$ can be represented in $x ^ n$ for some n
    calc
      _ = (g ^ tx).1 := rfl
      _ = x1.1 := congrArg Prod.fst hx
      _ = x := rfl
  · --2.The simialr reason as the former part,we have $H$ also is a cyclic group
    use g.2
    intro y
    let y1 : G × H := ⟨1, y⟩
    rcases hg y1 with ⟨ty, hy⟩
    use ty
    calc
      _ = (g ^ ty).2 := rfl
      _ = y1.2 := congrArg Prod.snd hy
      _ = y := rfl

end Example_1510B



section Special_Example_070601

/-A subgroup $N$ of a group $6$ with index $2$ must be a normal subgroup of $G$.-/
example {G :Type*} [Group G](N:Subgroup G)(h :N.index = 2): N.Normal := by
/-We use this condition of index $2$ by found a powerful lemma: $lexists a, \forall (b : 6), (b* a \in H)$ and $(b \in H)$ have only one holds true.-/
  apply Subgroup.index_eq_two_iff.mp at h
  rcases h with ⟨a, ha⟩
/-The conclusion that $N$ is normal is equivalent to: $\forall n \in N, \forall (g : G), g * n * g⁻¹ \in N$.-/
  refine {conj_mem := ?conj_mem }
  intro n hn g
  /-First we suppose that $g \in N$.-/
  by_cases hg : g ∈ N
  /-Then we have $g *n * g⁻¹ \in N$ because the inverse of $g$ is in $N$ and the product of two elements of $N$ is also in $N$.
  These are the properties of subgroup.-/
  · have h₁ : g⁻¹ ∈ N := (Subgroup.inv_mem_iff N).mpr hg
    have h₂ : g * n ∈ N := (Subgroup.mul_mem_cancel_right N hn).mpr hg
    exact (Subgroup.mul_mem_cancel_right N h₁).mpr h₂
  /-Then we suppose $g$ is not in $N$, We use proof by contradiction. Suppose that $g * n * g⁻¹$ is not in $N$.-/
  · by_contra h₁
    have h₂ : g⁻¹ ∉ N := by
      by_contra ng
      have : g ∈ N := (Subgroup.inv_mem_iff N).mp ng
      exact hg this
    /-Use the condition we have $g^{-1} * a in N$ and $g * n * g^{-1} * a \in N, -/
    rcases (ha g⁻¹) with g₂| g₀
    rcases (ha (g * n * g⁻¹) )with g₁ | g₀'
    rw [mul_assoc] at g₁
    /-So $g*n \in N$ and $g \in N$, which leads to contradiction-/
    · have h : g * n ∈ N := (Subgroup.mul_mem_cancel_right N g₂.1).mp g₁.1
      have : g ∈ N := (Subgroup.mul_mem_cancel_right N hn).mp h
      exact hg this
    · exact h₁ g₀'.1
    · exact h₂ g₀.1

end Special_Example_070601



section Example_2204B
/-
Let $G$ be a group and suppose $a \in G$ generates a cyclic subgroup of order 2 and is the unique such element. Show that $a x=x a$ for all $x \in G$. [Hint: Consider $\left(x a x^{-1}\right)^{2}$.]
-/
example {G : Type*} [Group G] {a : G} (h₁: orderOf a = 2) (h₂: ∃! (x : G), orderOf x = 2) : ∀ x : G, a * x = x * a := by
  intro x
  rcases h₂ with ⟨y, _, hy₁⟩
  --1.We have $(x^{-1} a x) ^ 2 = 1$ by calculating that $LHS = x^{-1} a ^ 2 x = x^{-1} \cdot 1 \cdot x = 1$
  have step1: (x⁻¹ * a * x) ^ 2 = 1 := by
    calc
      _ = (x⁻¹ * a * x) * (x⁻¹ * a * x) := pow_two (x⁻¹ * a * x)
      _ = x⁻¹ * (a * a) * x := by group
      _ = x⁻¹ * a ^ 2 * x := by simp only [mul_left_inj, mul_right_inj]; exact Eq.symm (pow_two a)
      _ = x⁻¹ * 1 * x := by rw [← h₁, pow_orderOf_eq_one a]
      _ = _ := by group
  --2.Hence we have $\operatorname{ord}(x^{-1} a x) = 2$
  have : orderOf (x⁻¹ * a * x) = 2 := by
    have : orderOf (x⁻¹ * a * x) ≤ 2 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one step1)
    by_contra nh
    have : orderOf (x⁻¹ * a * x) ≤ 1 := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne this nh)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp this with h | h
    · --because it is obviously that $\operatorname{ord}(x^{-1} a x) \neq 1$
      have : IsOfFinOrder (x⁻¹ * a * x) := by
        use 2; norm_num
        exact (isPeriodicPt_mul_iff_pow_eq_one (x⁻¹ * a * x)).mpr step1
      have : ¬ IsOfFinOrder (x⁻¹ * a * x) := orderOf_eq_zero_iff.mp h
      contradiction
    · have : x⁻¹ * a * x = 1 := by exact orderOf_eq_one_iff.mp h
      have : a = 1 := by calc
        _ = x * (x⁻¹ * a * x) * x⁻¹ := by group
        _ = x * 1 * x⁻¹ := by rw [this]
        _ = 1 := by group
      have : orderOf a = 1 := by rw [this]; norm_num
      linarith
  --3.According to the problem,we have $a = x^{-1} a x$ i.e. $ax = xa$ and we are done
  calc
    _ = x * (x⁻¹ * a * x) := by group
    _ = x * y := by rw [Mathlib.Tactic.LinearCombination.c_mul_pf (hy₁ (x⁻¹ * a * x) this) x]
    _ = _ := by rw [← hy₁ a h₁]

end Example_2204B



section Example_1409B
/-
Let $a, b$ be elements of a group $G$. Show that $\operatorname{ord}(a)=\operatorname{ord}\left(b a b^{-1}\right)$.

1.We prove a lemma : $b^{-1} \cdot (b a b^{-1}) ^ n \cdot b = a ^ n$.

2.We have $orderOf a \mid orderOf (bab^{-1})$ becuase we use this lemma and we have $a ^ {orderOf (b a b^{-1})} = b^{-1} (b a b⁻¹) ^ {orderOf (b a b⁻¹)} b = b^{-1} \cdot 1 \cdot b = 1$

3.We have $orderOf (bab^{-1}) \mid orderOf a$ becuase we use this lemma and we have $(bab^{-1}) ^ {orderOf a} = b\cdot (b^{-1} (b a b⁻¹) ^ {orderOf a} b) \cdot b ^ {-1} = b \cdot a ^ {orderOf a} \cdot b^{-1} = b \cdot 1 \cdot b^{-1} =1$

4.Hence we have $orderOf a = orderOf (bab^{-1})$
-/

/-
Let $a, b$ be elements of a group $G$. Show that $\operatorname{ord}(a)=\operatorname{ord}\left(b a b^{-1}\right)$.
-/
example {G : Type*} [Group G] (a b : G) : orderOf a = orderOf (b * a * b⁻¹) := by
  --1.We prove a lemma : $b^{-1} \cdot (b a b^{-1}) ^ n \cdot b = a ^ n$.
  have conj(n : ℕ) : b⁻¹ * (b * a * b⁻¹) ^ n * b = a ^ n := by
    rw [@conj_pow]
    group
  --2.We have $orderOf a \mid orderOf (bab^{-1})$
  have t1: orderOf a ∣ orderOf (b * a * b⁻¹) := by
    --becuase we use this lemma and we have $$a ^ {orderOf (b a b^{-1})} = b^{-1} (b a b⁻¹) ^ {orderOf (b a b⁻¹)} b = b^{-1} \cdot 1 \cdot b = 1$$
    have : a ^ orderOf (b * a * b⁻¹) = 1 := by
      calc
        _ = b⁻¹ * (b * a * b⁻¹) ^ orderOf (b * a * b⁻¹) * b := by rw [←conj]
        _ = b⁻¹ * 1 * b := by rw [@pow_orderOf_eq_one]
        _ = _ := by group
    exact orderOf_dvd_of_pow_eq_one this
  --3.We have $orderOf (bab^{-1}) \mid orderOf a$
  have t2: orderOf (b * a * b⁻¹) ∣ orderOf a := by
    --becuase we use this lemma and we have $$(bab^{-1}) ^ {orderOf a} = b\cdot (b^{-1} (b a b⁻¹) ^ {orderOf a} b) \cdot b ^ {-1} = b \cdot a ^ {orderOf a} \cdot b^{-1} = b \cdot 1 \cdot b^{-1} =1$$
    have : (b * a * b⁻¹) ^ orderOf a = 1 := by
      calc
        _ = b * (b⁻¹ * (b * a * b⁻¹) ^ orderOf a * b) * b⁻¹ := by group
        _ = b * a ^ orderOf a * b⁻¹ := by rw [conj]
        _ = b * 1 * b⁻¹ := by rw [@pow_orderOf_eq_one]
        _ = _ := by group
    exact orderOf_dvd_of_pow_eq_one this
  exact Nat.dvd_antisymm t1 t2

end Example_1409B



section Example_1416B
/-
Let $a,b\in G$ such that $ab=ba$. Prove that $\operatorname{ord}(ab)\mid\operatorname{LCM}(\operatorname{ord}(a),\operatorname{ord}(b))$.
-/
example { G : Type* } [ Group G ]  { a b : G } ( mul_comm' : a * b = b * a ) :
  orderOf ( a * b ) ∣ Nat.lcm ( orderOf a ) ( orderOf b ):= by
  --1.We prove a lemma that $b ^ n \cdot a = a \cdot b ^ n$ by induction
  have (n : ℕ) : b ^ n * a = a * b ^ n := by
    induction' n with n ih
    · --It's trivial when $n = 0$;
      simp only [pow_zero, one_mul, mul_one]
    · --And when $n$ is correct,we 'll prove $n + 1$
      calc
        --by caclulating $b ^ {n + 1} \cdot a = b \cdot (a \cdot b ^ n)$,
        _ = (b * b ^ n) * a := by simp only [mul_left_inj]; exact pow_succ' b n;
        _ = b * (b ^ n * a) := by group
        --which is $= (b \cdot a) \cdot b ^ n = a\cdot b \cdot b ^ n = a \cdot b ^ {n+ 1}$ by using inductive hypothesis,and so we are done
        _ = (b * a) * b ^ n := by rw [ih]; group
        _ = a * (b * b ^ n) := by rw [←mul_comm']; group
        _ = a * b ^ (n + 1) := by simp only [mul_right_inj]; exact Eq.symm (pow_succ' b n)
  --2.Moreover we 'll prove $(a \cdot b) ^ n = a ^ n \cdot b ^ n$ by induction
  have (n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := by
    induction' n with n ih
    · --It's trivial when $n = 0$;
      simp only [pow_zero, mul_one]
    · --And when $n$ is correct,we 'll prove $n + 1$ by caclulating $(a \cdot b) ^ {n + 1} = (a \cdot b) ^ n \cdot (a \cdot b) = a ^ n \cdot b ^ n \cdot (a \cdot b)$
      calc
        _ = (a * b) ^ n * (a * b) := pow_succ (a * b) n
        --,which is $ = a ^ n \cdot (b ^ {n + 1} \cdot a) = a ^ n \cdot (a \cdot b ^ {n + 1})$ by using inductive hypothesis, and so we are done
        _ = a ^ n * b ^ n * (b * a) := by rw [ih, mul_comm']
        _ = a ^ n * (b ^ (n + 1) * a) := by group
        _ = a ^ n * (a * b ^ (n + 1)) := by rw [this]
        _ = _ := by group
  --3.Hence $(a \cdot b) ^ {{LCM}(\operatorname{ord}(a),\operatorname{ord}(b))} = a ^ {{LCM}(\operatorname{ord}(a),\operatorname{ord}(b))} \cdot b ^ {{LCM}(\operatorname{ord}(a),\operatorname{ord}(b))} = 1 \cdot 1 = 1$
  apply orderOf_dvd_iff_pow_eq_one.mpr
  --,because $\operatorname{ord}(a) \mid {LCM}(\operatorname{ord}(a),\operatorname{ord}(b))$ and $\operatorname{ord}(b) \mid {LCM}(\operatorname{ord}(a),\operatorname{ord}(b))$
  rw [this]
  rw [orderOf_dvd_iff_pow_eq_one.mp (Nat.dvd_lcm_left (orderOf a) (orderOf b))]
  rw [orderOf_dvd_iff_pow_eq_one.mp (Nat.dvd_lcm_right (orderOf a) (orderOf b))]
  --4.And so we have proved $\operatorname{ord}(ab)\mid\operatorname{LCM}(\operatorname{ord}(a),\operatorname{ord}(b))$.
  norm_num

end Example_1416B



section Example_1407B
/-
Let $a$ be an element of a group $G$. Prove that if $\operatorname{ord}(a)=n$, then $a^{n-r}=\left(a^{r}\right)^{-1}$.
-/
example { G : Type* } [ Group G ] { g : G } { n r : ℤ  } ( h : orderOf g = n ):
    g ^ ( n - r ) = g ^ ( -r ) := by
  --We have $LHS.=a^n (a^r)^{-1}= 1 \cdot (a^r)^{-1}=RHS.$
  calc
    _ = g ^ (n + -r) := rfl
    _ = _ := by
      rw [zpow_add g n (-r), ← h]
      simp only [zpow_natCast, zpow_neg, one_mul, mul_left_eq_self]
      exact pow_orderOf_eq_one g

end Example_1407B



section Example_1409B

/-
Let $a, b$ be elements of a group $G$. Show that $\operatorname{ord}(a)=\operatorname{ord}\left(b a b^{-1}\right)$.
-/
example {G : Type*} [Group G] (a b : G) : orderOf a = orderOf (b * a * b⁻¹) := by
  --1.We use induction to prove a lemma : $b^{-1} \cdot (b a b^{-1}) ^ n \cdot b = a ^ n$.
  have conj(n : ℕ) : b⁻¹ * (b * a * b⁻¹) ^ n * b = a ^ n := by
    simp only [conj_pow]
    group
    -- induction' n with n ih
    -- · --When n = 0 , it is trival;
    --   group
    -- · --When n is correct,we calculate $b^{-1} \cdot (b a b^{-1}) ^ {n + 1} \cdot b = b^{-1} * ((b * a * b^{-1}) ^ n * (b * a * b^{-1})) * b = $.
    --   calc
    --     _ = b⁻¹ * ((b * a * b⁻¹) ^ n * (b * a * b⁻¹)) * b:= by
    --       simp only [mul_left_inj, mul_right_inj]
    --       exact pow_succ (b * a * b⁻¹) n
    --     _ = b⁻¹ * (b * a * b⁻¹) ^ n * b * (a * b⁻¹ * b) := by group
    --     --Then use the Induction hypothesis and we have it $= a ^ n * (a * b⁻¹ * b) = a ^ {n + 1}$
    --     _ = a ^ n * (a * b⁻¹ * b):= by rw [ih]
    --     _ = _ := by group
  --2.We have $orderOf a \mid orderOf (bab^{-1})$
  have t1: orderOf a ∣ orderOf (b * a * b⁻¹) := by
    --becuase we use this lemma and we have $$a ^ {orderOf (b a b^{-1})} = b^{-1} (b a b⁻¹) ^ {orderOf (b a b⁻¹)} b = b^{-1} \cdot 1 \cdot b = 1$$
    have : a ^ orderOf (b * a * b⁻¹) = 1 := by
      calc
        _ = b⁻¹ * (b * a * b⁻¹) ^ orderOf (b * a * b⁻¹) * b := by rw [←conj]
        _ = b⁻¹ * 1 * b := by rw [@pow_orderOf_eq_one]
        _ = _ := by group
    exact orderOf_dvd_of_pow_eq_one this
  --3.We have $orderOf (bab^{-1}) \mid orderOf a$
  have t2: orderOf (b * a * b⁻¹) ∣ orderOf a := by
    --becuase we use this lemma and we have $$(bab^{-1}) ^ {orderOf a} = b\cdot (b^{-1} (b a b⁻¹) ^ {orderOf a} b) \cdot b ^ {-1} = b \cdot a ^ {orderOf a} \cdot b^{-1} = b \cdot 1 \cdot b^{-1} =1$$
    have : (b * a * b⁻¹) ^ orderOf a = 1 := by
      calc
        _ = b * (b⁻¹ * (b * a * b⁻¹) ^ orderOf a * b) * b⁻¹ := by group
        _ = b * a ^ orderOf a * b⁻¹ := by rw [conj]
        _ = b * 1 * b⁻¹ := by rw [@pow_orderOf_eq_one]
        _ = _ := by group
    exact orderOf_dvd_of_pow_eq_one this
  exact Nat.dvd_antisymm t1 t2

end Example_1409B



section Example_1410B

/-
Let $a, b$ be elements of a group $G$. If $a$ has no finite order, then $bab^{-1}$ has no finite order.
-/
example { G : Type* } [ Group G ] { g h : G } { zero_order : orderOf h = 0 } :
  orderOf ( g⁻¹ * h * g ) = 0 := by
  by_contra nh
  --1.We use induction to prove a lemma : $b^{-1} \cdot (b a b^{-1}) ^ n \cdot b = a ^ n$.
  have (n : ℕ) : g * (g⁻¹ * h * g) ^ n * g⁻¹ = h ^ n := by
    induction' n with n ih
    · --When n = 0 , it is trival;
      simp only [pow_zero, mul_one, mul_right_inv]
    · --When n is correct,we calculate $b^{-1} \cdot (b a b^{-1}) ^ {n + 1} \cdot b = b^{-1} * ((b * a * b^{-1}) ^ n * (b * a * b^{-1})) * b = $.
      calc
        _ = g * ((g⁻¹ * h * g) ^ n * (g⁻¹ * h * g)) * g⁻¹:= by
          simp only [mul_left_inj, mul_right_inj]
          exact pow_succ (g⁻¹ * h * g) n
        _ = g * (g⁻¹ * h * g) ^ n * g⁻¹ * (h * g * g⁻¹):= by group
        --Then use the Induction hypothesis and we have it $= a ^ n * (a * b⁻¹ * b) = a ^ {n + 1}$
        _ = h ^ n * (h * g * g⁻¹) := by rw [ih]
        _ = _ := by group
  --2.Hence we have $a ^ {orderOf (bab^{-1})} = b^{-1} \cdot (b a b^{-1}) ^ {orderOf (bab^{-1})} \cdot b = b ^ {-1} \cdot 1 \cdot b = 1$
  have : h ^ orderOf (g⁻¹ * h * g) = 1 := by
    calc
      _ = g * (g⁻¹ * h * g) ^ orderOf (g⁻¹ * h * g) * g⁻¹ := by rw [← this (orderOf (g⁻¹ * h * g))]
      _ = g * 1 * g⁻¹ := by
        simp only [mul_one, mul_right_inv, conj_eq_one_iff]
        exact pow_orderOf_eq_one (g⁻¹ * h * g)
      _ = _ := by group
  --3.If $bab^{-1}$ has finite order,then $a$ also has finite order which is contridicted.
  have : IsOfFinOrder h := by
    apply isOfFinOrder_iff_zpow_eq_one.mpr
    use orderOf (g⁻¹ * h * g)
    constructor
    · exact Int.ofNat_ne_zero.mpr nh
    · exact pow_natAbs_eq_one.mp this
  --Thus,we have prove that $bab^{-1}$ has no finite order
  have : ¬ IsOfFinOrder h := by exact orderOf_eq_zero_iff.mp zero_order
  contradiction

end Example_1410B



section Example_1411B

/-
Let $a$ be elements of a group $G$. Show that $\operatorname{ord}(a)=\operatorname{ord}(a^{-1})$.
-/
example {G : Type*} [Group G] (a : G) : orderOf a = orderOf (a⁻¹) := by exact Eq.symm (orderOf_inv a)
--It is a trivial conclusion
end Example_1411B



section Example_1412B

/-
Let $a$ be elements of a group $G$. If $a$ has no finite order, then $a^{-1}$ has no finite order.
-/
example { G : Type* } [ Group G ] { g : G } { zero_order : orderOf g = 0 } :
    orderOf g⁻¹ = 0 := by
  --We have $orderOf a = orderOf a^{-1}$.
  have : ¬IsOfFinOrder g := by exact orderOf_eq_zero_iff.mp zero_order
  have : ¬IsOfFinOrder g⁻¹ := by
    --If $a^{-1}$ has finite order
    by_contra nh
    --then we have $a$ has the same finite order,which is contradicted.
    have : IsOfFinOrder g := by exact IsOfFinOrder.of_inv nh
    contradiction
  exact orderOf_eq_zero this

end Example_1412B



section Example_1415B

/-
Let $G$ and $H$ be groups. Suppose $g=(a, b) \in G \times H$, where $a$ has order $m$ and $b$ has order $n$. Prove that $\operatorname{ord}(g)=\operatorname{LCM}(m,n)$.
-/
example {G H : Type*} [Group G] [Group H] {a : G} {b : H} : orderOf (a, b) = Nat.lcm (orderOf a) (orderOf b) := by
  --Note that $x = (a,b)$
  let x : G × H := (a, b)
  --We have $m \mid orderOf x$ because $x^{orderOf x} = (1,*) $,i.e $a ^ {orderOf x} = 1$
  have dvd1 : orderOf a ∣ orderOf x := by
    apply orderOf_dvd_of_pow_eq_one
    calc
      _ = (x ^ orderOf x).1 := rfl
      _ = _ := by simp only [pow_orderOf_eq_one x, Prod.fst_one]
  --We have $n \mid orderOf x$ as the same reason
  have dvd2 : orderOf b ∣ orderOf x := by
    apply orderOf_dvd_of_pow_eq_one
    calc
      _ = (x ^ orderOf x).2 := rfl
      _ = _ := by simp only [pow_orderOf_eq_one x, Prod.snd_one]
  --Hence we prove that $\operatorname{LCM}(m,n) \mid orderOf x$
  have h1 : Nat.lcm (orderOf a) (orderOf b) ∣ orderOf x :=  Nat.lcm_dvd dvd1 dvd2
  --We will $orderOf x \mid \operatorname{LCM}(m,n)$
  have h2 : orderOf x ∣ Nat.lcm (orderOf a) (orderOf b) := by
    apply orderOf_dvd_of_pow_eq_one
    -- by prove $a ^ {\operatorname{LCM}(m,n)} = 1$
    have eq1 : a ^ Nat.lcm (orderOf a) (orderOf b) = 1:= by
      apply orderOf_dvd_iff_pow_eq_one.mp
      exact Nat.dvd_lcm_left (orderOf a) (orderOf b)
    -- and $b ^ {\operatorname{LCM}(m,n)} = 1$
    have eq2 : b ^ Nat.lcm (orderOf a) (orderOf b) = 1:= by
      apply orderOf_dvd_iff_pow_eq_one.mp
      exact Nat.dvd_lcm_right (orderOf a) (orderOf b)
    calc
    _ = (a ^ Nat.lcm (orderOf a) (orderOf b), b ^ Nat.lcm (orderOf a) (orderOf b)) := rfl
    _ = _ := by simp only [eq1, eq2, Prod.mk_eq_one, and_self]
  --We have prove that $orderOf x = \operatorname{LCM}(m,n)
  apply Nat.dvd_antisymm h2 h1

end Example_1415B
