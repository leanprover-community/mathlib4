import Mathlib.Algebra.Group.Subgroup.ZPowers
import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms


#check Subgroup.center

section Special_Example_070602
/-
$G/Z(G)$ is a cyclic group, then $G$ is an abelian group, where $Z(G)={g∈G ∣ ∀h∈G,gh=hg}$ is the center of the group $G$.
-/
example {G : Type*} [Group G](h : IsCyclic (G⧸(Subgroup.center G))): CommGroup G := by
  apply CommGroup.mk
  intro a b
  rcases h with ⟨H, h⟩
  have Ha : ∃ m : ℤ , H ^ m = ↑a := by apply Subgroup.mem_zpowers_iff.mp (h a)
  have Hb : ∃ n : ℤ , H ^ n = ↑b := by apply Subgroup.mem_zpowers_iff.mp (h b)
  rcases H with ⟨g⟩
  rcases Ha with ⟨m, ha⟩
  rcases Hb with ⟨n, hb⟩
  let x := (g ^ m)⁻¹ * a
  let y := (g ^ n)⁻¹ * b
  have xg : x ∈ Subgroup.center G := QuotientGroup.eq'.mp ha
  have hx : ∀ h, h * x = x * h := fun h => Eq.symm (xg.comm h)
  have yg : y ∈ Subgroup.center G := QuotientGroup.eq'.mp hb
  have hy : ∀ h, h * y = y * h := fun h => Eq.symm (yg.comm h)
  have aeq : g ^ m * x = a := mul_inv_cancel_left (g ^ m) a
  have beq : g ^ n * y = b := mul_inv_cancel_left (g ^ n) b
  calc
    _ = g ^ m * x * (g ^ n * y) := by rw [← aeq, ← beq]
    _ = x * g ^ m * (y * g ^ n) := by rw [hy, hx]
    _ = x * (g ^ m * y * g ^ n) := by group
    _ = (y * g ^ m * g ^ n) * x := by rw [hx, hy];group
    _ = y * g ^ n * (g ^ m * x) := by group
    _ = g ^ n * y * (g ^ m * x) := by rw [hy]
    _ = _ := by rw[aeq, beq]

end Special_Example_070602



section Special_Example_070401

/-
Let $M$ and $N$ be normal subgroups of the group $G$. If $M \cap N = 1$, then for any $a \in M$ and $b \in N$, we have $ab = ba$.
-/

example {G : Type*} [Group G] (M N: Subgroup G) (h₁: M.Normal) (h₂: N.Normal) (h : M.carrier ∩ N.carrier = {1})
   : ∀ a ∈ M , ∀ b ∈ N , a * b = b * a := by
  intro a ha b hb
  --Equally, we only need to show that $a * b * a ^ {-1} * b ^ {-1} = 1$
  have h₁': ∀ m, m ∈ M → ∀ g : G, g * m * g⁻¹ ∈ M := fun m b g => h₁.conj_mem m b g
  have h₂': ∀ n, n ∈ N → ∀ g : G, g * n * g⁻¹ ∈ N := fun n a g => h₂.conj_mem n a g
  --We have $a * b * a ^ {-1} \in N$ because N is normal
  have hm: a * b * a⁻¹ * b⁻¹ ∈ M := by
    have : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
    rw [this]
    have : a⁻¹ ∈ M := by exact (Subgroup.inv_mem_iff M).mpr ha
    --and so $a * b * a ^ {-1} * b ^ {-1} \in N$
    exact (Subgroup.mul_mem_cancel_right M (h₁' a⁻¹ this b)).mpr ha
  --We have $b * a ^ {-1} * b ^ {-1} \in M$ because M is normal
  have hn: a * b * a⁻¹ * b⁻¹ ∈ N := by
    have : b⁻¹ ∈ N := by exact (Subgroup.inv_mem_iff N).mpr hb
    --and so $a * b * a ^ {-1} * b ^ {-1} \in M$
    exact (Subgroup.mul_mem_cancel_right N this).mpr (h₂' b hb a)
  have h₁: a * b * a⁻¹ * b⁻¹ ∈ M.carrier ∩ N.carrier := Set.mem_inter hm hn
  have h₂: M.carrier ∩ N.carrier ⊆ ({ 1 } : Set G) := by exact Eq.subset h
  --Hence $a * b * a ^ {-1} * b ^ {-1} \in M \cap N$,i.e.$a * b * a ^ {-1} * b ^ {-1} = 1$and we are done
  have : a * b * a⁻¹ * b⁻¹ ∈ ({ 1 } : Set G) := by exact h₂ h₁--Why is uncorrect as I use {(1 : G)}???
  have : a * b * a⁻¹ * b⁻¹ = 1 := by exact h₂ h₁
  exact commutatorElement_eq_one_iff_mul_comm.mp (h₂ h₁)

end Special_Example_070401



section Exercise_2365
/-
Show that if $H$ and $N$ are subgroups of a group $G$, and $N$ is normal in $G$, then $H \cap N$ is normal in $H$.
-/
example {G : Type*}[Group G](H N : Subgroup G)[hN : N.Normal] : ((H ⊓ N).subgroupOf H).Normal := by
  --We only need to prove that $H \cap N \le H$ and $\forall h \in H \cap N$ and $\forall n \in H$,there are $n h n ^ {-1} \ in H \cap N$
  apply (Subgroup.normal_subgroupOf_iff _).mpr _
  · --The former one is trivial
    exact inf_le_left
  · intro h n ⟨hh, hn⟩ nh
    --To prove the latter one, we only need to prove that $n h n ^ {-1} \ in H$ and $n h n ^ {-1} \ in N$
    constructor
    · --Because $n \in H$ and $h \in H$ ,so it is obvious that $n h n ^ {-1} \ in H$
      simp only [Subgroup.coe_toSubmonoid, SetLike.mem_coe]
      have : h ∈ H := by simp only [Subgroup.coe_toSubmonoid, SetLike.mem_coe] at hh; exact hh
      have t1: n * h ∈ H := (Subgroup.mul_mem_cancel_right H hh).mpr nh
      have t2: n⁻¹ ∈ H := by exact (Subgroup.inv_mem_iff H).mpr nh
      exact (Subgroup.mul_mem_cancel_right H t2).mpr t1
    · --Also because $N$ is normal in $G$
      simp only [Subgroup.coe_toSubmonoid, SetLike.mem_coe]
      exact hN.conj_mem h hn n

end Exercise_2365



section Exercise_2391

/-
Show that if $G$ is nonabelian, then the factor group $G / Z(G)$ is not cyclic. [Hint: Show the equivalent contrapositive, namely, that if $G / Z(G)$ is cyclic then $G$ is abelian (and hence $Z(G)=G)$.]
-/
--We will prove the Contrapositivity of the main proposition : if $G / Z(G)$ is cyclic,then $G$ is Commutative Group
def hint {G : Type*} [Group G](h : IsCyclic (G⧸(Subgroup.center G))): CommGroup G := by
  apply CommGroup.mk
  --Equally,We will prove that $\forall a b \in G$,there will be $a * b = b * a$
  intro a b
  rcases h with ⟨H, h⟩
  have Ha : ∃ m : ℤ , H ^ m = ↑a := by apply Subgroup.mem_zpowers_iff.mp (h a)
  have Hb : ∃ n : ℤ , H ^ n = ↑b := by apply Subgroup.mem_zpowers_iff.mp (h b)
  rcases H with ⟨g⟩
  rcases Ha with ⟨m, ha⟩
  rcases Hb with ⟨n, hb⟩
  --Suppose that $g \cdot Z(G)$ is the generator of $G / Z(G)$, $a \cdot Z(G) = (g \cdot Z(G)) ^ m$ and $b \cdot Z(G) = (g \cdot Z(G)) ^ n$
  let x := (g ^ m)⁻¹ * a
  let y := (g ^ n)⁻¹ * b
  have xg : x ∈ Subgroup.center G := QuotientGroup.eq'.mp ha
  have hx : ∀ h, h * x = x * h := fun h => Eq.symm (xg.comm h)
  have yg : y ∈ Subgroup.center G := QuotientGroup.eq'.mp hb
  have hy : ∀ h, h * y = y * h := fun h => Eq.symm (yg.comm h)
  --Hence we have $x = (g ^ m) ^ {-1} a$ and $y = (g ^ n)^{-1} b \in Z(G)$
  have aeq : g ^ m * x = a := mul_inv_cancel_left (g ^ m) a
  have beq : g ^ n * y = b := mul_inv_cancel_left (g ^ n) b
  --We can Calculate that $a b = (g ^ m x)(g ^ n y) = (g ^ n y)(g ^ m x)$ because $g ^ m$ and $g ^ n$ is Commutative with all elements
  calc
    _ = g ^ m * x * (g ^ n * y) := by rw [← aeq, ← beq]
    _ = x * g ^ m * (y * g ^ n) := by rw [hy, hx]
    _ = x * (g ^ m * y * g ^ n) := by group
    _ = (y * g ^ m * g ^ n) * x := by rw [hx, hy];group
    _ = y * g ^ n * (g ^ m * x) := by group
    _ = g ^ n * y * (g ^ m * x) := by rw [hy]
    _ = _ := by rw[aeq, beq]
  --Hence we care done

example {G : Type*} [Group G] (h : ∃ a b : G, a * b ≠ b * a ) : ¬ IsCyclic (G⧸(Subgroup.center G)) := by
  --As we know that the main problem is Equally to its Contrapositivity,and so we are done
  contrapose! h
  exact (hint h).mul_comm

end Exercise_2391



section Exercise_3694

/-
Let $p$ be a prime, $G$ be a group of order $p^3$. If $G$ is not cyclic, then $x^{p^2}=1$ for all $x$ in $G$.
-/
example {G : Type*}[Finite G] [Group G] (pp : Nat.Prime p)(hG : Nat.card G = p ^ 3)
(nc : ¬IsCyclic G):∀ x : G, x ^ (p ^ 2) = 1 := by
  --If there $\exists x, x ^ {p ^ 2} = 1$
  by_contra nh; push_neg at nh
  rcases nh with ⟨x,nh⟩
  --Thus we have $\operatorname{ord} (x) \nmid p ^ 2$
  have ndvd: ¬ orderOf x ∣ p ^ 2 := by
    by_contra dvd
    have : x ^ p ^ 2 = 1 := by exact orderOf_dvd_iff_pow_eq_one.mp dvd
    contradiction
  --Also we have $\operatorname{ord} (x) \mid p ^ 3$ due to $\operatorname{card} G = P ^ 3$
  have : orderOf x ∣ p ^ 3 := by
    rw [←hG]
    exact orderOf_dvd_natCard x
  have :∃ k ≤ 3 , orderOf x = p ^ k := by exact (Nat.dvd_prime_pow pp).mp this
  rcases this with ⟨k, hle, hk⟩
  rw [hk] at ndvd
  have : k > 2 := by
    by_contra nt
    have : p ^ k ∣ p ^ 2 := by
      refine (Nat.pow_dvd_pow_iff_le_right ?w).mpr ?_
      exact Nat.Prime.one_lt pp
      exact Nat.le_of_not_lt nt
    contradiction
  have : k ≥ 3 := by exact this
  have : k = 3 := by linarith
  --Hence we have $\operatorname{ord} x = p ^ 3 = \operatorname{card} G$
  have : orderOf x = Nat.card G := by rw [hk, this, ← hG]
  --,which leads to $G$ is cyclic which is contradicted
  have : IsCyclic G := by
    apply isCyclic_iff_exists_ofOrder_eq_natCard.mpr _
    exact Exists.intro x this
  contradiction

end Exercise_3694
