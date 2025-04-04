import Mathlib.Algebra.Group.Subgroup.ZPowers
import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms


section Example_1108B
@[ext]
/-
Prove that the elements $\{(x,y):x,y\in\mathbb Z, 2\mid x+y\}$ under elementwise addition is a group.
-/
--Define the structure of two_div_sum
structure two_div_sum where
  x : ℤ
  y : ℤ
  h : 2 ∣ x + y

--Define add on this structure
instance : Add two_div_sum where
  add := by
    intro X Y
    use X.x + Y.x
    use X.y + Y.y
    have : (X.x + X.y) + (Y.x + Y.y) = X.x + Y.x + (X.y + Y.y) := by ring
    rw [←this]
    exact (Int.dvd_add_right X.h).mpr Y.h

--Define neg on this structure
instance : Neg two_div_sum where
  neg := by
    intro X
    use -X.x
    use -X.y
    have : -X.x + -X.y = - (X.x + X.y) := by ring
    rw [this]
    exact Int.dvd_neg.mpr X.h

--Check the law of zero plus a element equals itself
instance : Zero two_div_sum where
  zero := by
    use 0
    use 0
    norm_num

--Prove it's a group
instance : AddGroup two_div_sum := by
  apply AddGroup.ofLeftAxioms
  · intro a b c
    ext
    · exact Int.add_assoc a.x b.x c.x
    · exact Int.add_assoc a.y b.y c.y
  · intro a
    ext
    · show (0 : two_div_sum).x + a.x = a.x
      simp only [add_left_eq_self]
      rfl
    · show (0 : two_div_sum).y + a.y = a.y
      simp only [add_left_eq_self]
      rfl
  · intro a
    ext
    · show (-a).x + a.x = 0
      exact eq_neg_iff_add_eq_zero.mp rfl
    · show (-a).y + a.y = 0
      exact eq_neg_iff_add_eq_zero.mp rfl

end Example_1108B



section Example_2301B
/-
If $H$ and $K$ are subgroups of $G$, and $K$ is normal, then $H K$ is a subgroup of $G$. ($HK$ denotes the set of all products $h k$ as $h$ ranges over $H$ and $k$ ranges over $K$.)
-/
--Define the Subgroup $HK = { h * k | h \in H, k \in K }$
def HK {G : Type*} [Group G] (H K: Subgroup G) : Set G := { s | ∃ h : H, ∃ k : K, s = h * k }

--Show this is a subgroup
example {G : Type*} [Group G] (H K: Subgroup G) (h: K.Normal) : Subgroup G where
  carrier := HK H K
  --it's close under multiplication
  mul_mem' := by
    rintro a b ⟨h₁, k₁, ha⟩ ⟨h₂, k₂, hb⟩
    --for each $h_1 k_1 , h_2 k_2 \in HK$, $(h_1 h_2 \in H, k_1 k_2 \in K)$
    --$h_2 ^ {-1} k_1 h_2 \in HK$ because $K$ is normal
    have : (h₂⁻¹ : G) * k₁ * (h₂⁻¹ : G)⁻¹ ∈ K := by
      apply h.conj_mem
      exact SetLike.coe_mem k₁
    use h₁ * h₂
    --So we have $h_1 k_1 h_2 k_2 \in HK$
    use ⟨(h₂⁻¹ : G) * k₁ * (h₂⁻¹ : G)⁻¹, this⟩ * k₂
    rw [ha, hb]
    simp only [Submonoid.coe_mul, Subgroup.coe_toSubmonoid, inv_inv]
    group
  one_mem' := by
    use 1
    use 1
    norm_num
  --Prove every element of $hk$ $(h \in H, k \in K)$'s inverse is also in $Hk$
  inv_mem' := by
    intro x ⟨h₁, k₁, hx⟩
    --$h k h ^ {-1} \in HK$ because $K$ is normal
    have : (h₁ : G) * k₁⁻¹ * (h₁ : G)⁻¹ ∈ K := by
      apply h.conj_mem
      exact SetLike.coe_mem k₁⁻¹
    --So $k ^ {-1} h ^ {-1} = (h k) ^ {-1} \in HK$
    use h₁⁻¹
    use ⟨(h₁ : G) * k₁⁻¹ * (h₁ : G)⁻¹, this⟩
    rw [hx]
    simp only [mul_inv_rev, InvMemClass.coe_inv]
    group

end Example_2301B



section Example_2102B
/-
Prove that if $G$ is a group, then for every element $x\in G$,$\langle x\rangle=\{x^n|n\in\mathbb{Z}\}$ is a subgroup of $G$.
-/
--Define the set $\langle x\rangle=\{x^n|n\in\mathbb{Z}\}$
def zpowergroup{G :Type*}[Group G](x : G):Set G := {y|∃ n : ℤ , y = x ^ n}

--Prove it's a group
example {G :Type*}[Group G](x : G) : Subgroup G where
  carrier := zpowergroup x
  --Every $a = g ^ s, b = g ^ t$,then $a b = g ^ {s + t}$ which is also in the set
  mul_mem' := by
    rintro a b ⟨s, ha⟩ ⟨t, hb⟩
    rw [ha, hb]
    use s + t
    exact Eq.symm (zpow_add x s t)
  one_mem' := by
    use 0
    exact Eq.symm (zpow_zero x)
  inv_mem' := by
    intro g ⟨n, hg⟩
    rw [hg]
    use - n
    exact Eq.symm (zpow_neg x n)

end Example_2102B



section Example_2209B

--Define the set $S = \{g\in G|g^n=e \text{ for some positive integer } n\}.$
def power_subgroup {G : Type*} [CommGroup G] : Set G := { s | ∃ n : ℕ, s ^ (n + 1) = 1 }

--Prove it is a group
example {G : Type*} [CommGroup G] : Subgroup G where
  carrier := power_subgroup
  mul_mem' := by
    intro a b  ⟨n, ha⟩ ⟨m, hb⟩
    --We will prove that $(a * b) ^ {(n + 1) * (m + 1)} = 1$ because G is abelian
    use m * n + m + n
    have t1: m * n + m + n + 1 = (n + 1) * (m + 1) := by ring
    have t2: m * n + m + n + 1 = (m + 1) * (n + 1) := by ring
    calc
      _ = a ^ (m * n + m + n + 1) * b ^ (m * n + m + n + 1) := mul_pow a b (m * n + m + n + 1)
      _ = a ^ ((n + 1) * (m + 1)) * b ^ ((m + 1) * (n + 1)) := by
        nth_rw 1[t1]
        nth_rw 1[t2]
      _ = (a ^ (n + 1)) ^ (m + 1) * b ^ ((m + 1) * (n + 1)) := by
        simp only [mul_left_inj]
        exact pow_mul a (n + 1) (m + 1)
      _ = (a ^ (n + 1)) ^ (m + 1) * (b ^ (m + 1)) ^ (n + 1) := by
        simp only [mul_right_inj]
        exact pow_mul b (m + 1) (n + 1)
      _ = _ := by
        rw[ha, hb]
        simp only [one_pow, mul_one]
  one_mem' := by
    --Because $1 ^ 2 = 1$ , so $1 \in S$
    use 1
    simp only [Nat.reduceAdd, one_pow]
  inv_mem' := by
    --Because if $x ^ n = 1$ for some positive integer
    intro x ⟨n, hx⟩
    use n
    --then $(x ^ {-1}) ^ n = 1$
    simp only [inv_pow, inv_eq_one]
    --and we have $x \in S$
    exact hx

end Example_2209B



section Example_6201B

--Given field $F$, Nonzero elements of $F$ form an Abelian multiplicative group $F^\times$.
def nonezero {F : Type*}[Field F] : Group Fˣ  where
  --We have any two elements $a,b \in F^\time$,then $a b \in F^\time$
  mul := by
    intro a b
    use a.1 * b.1
    --Because $(a b) \cdot (b^{-1} a^{-1}) = (b^{-1} a^{-1}) \cdot (a b) = 1$
    use b.2 * a.2
    --Hence $(b^{-1} a^{-1})$ is the inverse of $ab$
    · calc
        _ = a.1 * (b.1 * b.2) * a.2 := by group
        _ = _ := by rw[b.3]; simp only [mul_one]; rw [a.3]
    · calc
        _ = b.2 * (a.2 * a.1) * b.1 := by group
        _ = _ := by rw [a.4]; simp only [mul_one]; rw [b.4]
  --We have mul association law as usual
  mul_assoc := mul_assoc
  --And the identity is 1,because 1 is its inverse
  one := ⟨1, 1, (by simp only [mul_one]), (by simp only [mul_one])⟩
  --The identity is well-defined is trivial
  one_mul := LeftCancelMonoid.one_mul
  mul_one := LeftCancelMonoid.mul_one
  --We define every element's inverse as $x^{-1}$
  inv := fun x => ⟨x.2, x.1, x.inv_val, x.val_inv⟩
  mul_left_inv := inv_mul_self

--$F^\times$ is a Commutative group as $F$ is Commutative Ring
example {F : Type*}[Field F] : CommGroup Fˣ := by
  apply CommGroup.mk
  intro a b
  exact CommGroup.mul_comm a b
end Example_6201B



section Exercise_1294
/-
6.Define $\varphi: \mathbb{R}^{\times} \rightarrow\{ \pm 1\}$ by letting $\varphi(x)$ be $x$ divided by the absolute value of $x$. Prove that $\varphi$ is a homomorphism.
-/
--We def the set is $\{ \pm 1\}$
def onecarrier : Set ℝ := {1,-1}

--We have $\{ \pm 1\}$ is close by multiple
lemma onemul(a b : onecarrier) : (a : ℝ) * (b : ℝ) ∈ onecarrier := by
  --We prove this by classify that whether $a = 1$ or $a = -1$,and whether $b = 1$ or $b = -1$
  rcases Subtype.coe_prop a with h | h
  · rw [h]
    simp only [one_mul, Subtype.coe_prop]
  · rcases Subtype.coe_prop b with h1 | h1
    · rw [h1]
      simp only [mul_one, Subtype.coe_prop]
    · rw [h, h1]
      unfold onecarrier
      simp only [mul_neg, mul_one, neg_neg, Set.mem_insert_iff, Set.mem_singleton_iff,
        eq_neg_self_iff, one_ne_zero, or_false]

--We also have a lemma that every element $a \in \{ \pm 1\}$, then $a ^ 2 = 1$
lemma oneinv(a : onecarrier) : (a : ℝ) * (a : ℝ) = 1 := by
  unfold onecarrier
  --It is also proved by classification
  rcases Subtype.coe_prop a with h | h
  · rw [h]
    norm_num
  · rw [h]
    norm_num

--Then we prove $\{ \pm 1\}$ is a multiple group
instance : Group onecarrier where
  mul := by
    --Which its muliple is as usual in \mathbb{R}\
    intro a b
    use a * b
    exact onemul a b
  mul_assoc := by
    --Hence it have the similar multiple associate laws
    intro a b c
    have : (a : ℝ) * (b : ℝ) * (c : ℝ) = (a : ℝ) * ((b : ℝ) * (c : ℝ)) := mul_assoc (a : ℝ) (b : ℝ) (c : ℝ)
    exact Eq.symm (SetCoe.ext (id (Eq.symm this)))
  one := by
    --And we define that 1 is the identifity
    use 1
    unfold onecarrier
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, eq_neg_self_iff, one_ne_zero, or_false]
  one_mul := by
    --It is easy to check that $1$ multiple every element is itself
    intro x
    have : 1 * (x : ℝ) = (x : ℝ) := one_mul (x : ℝ)
    exact SetCoe.ext this
  mul_one := by
    --and every element multiple $1$ is itself
    intro x
    have : (x : ℝ) * 1 = (x : ℝ) := mul_one (x : ℝ)
    exact SetCoe.ext this
  inv := by
    --we define $1$'s inverse is $1$ and $-1$'s inverse is $-1$
    intro x
    use x
    exact Subtype.coe_prop x
  mul_left_inv := by
    --It is easy to check it is well defined by the previous lemma which tells us that $x \cdot x = 1$
    intro x
    have : (x : ℝ) * (x : ℝ) = 1 := oneinv x
    exact Eq.symm (SetCoe.ext (id (Eq.symm this)))

--Now,we construct this $\phi$ which is a homomorphism from $\mathbb{R}^{\times}$ to $\{ \pm 1\}$
noncomputable example : ℝˣ →* onecarrier where
  --We map each $x \in \mathbb{R}^{\times}$ to $\frac{|x|}{x}$
  toFun := by
    intro ⟨val, inv, lmul, _⟩
    use |val|/val
    have : val ≠ 0 := by exact left_ne_zero_of_mul_eq_one lmul
    have : val > 0 ∨ val < 0 := by exact lt_or_gt_of_ne (id (Ne.symm this))
    --i.e. it is $1$ when $x$ is positive and $-1$ when $x$ is negative
    rcases this with h | h
    · rw [abs_of_pos h]
      have : (val:ℝ) / (val:ℝ) = 1 := by exact (div_eq_one_iff_eq this).mpr rfl
      rw [this]
      unfold onecarrier
      exact Set.mem_insert 1 {-1}
    · rw [abs_of_neg h]
      have : (-val:ℝ) / (val:ℝ) = -1 := by exact neg_div_self this
      rw [this]
      unfold onecarrier
      exact Set.mem_insert_of_mem 1 rfl
    --It is trivial to check that $1$ maps to $1$
  map_one' := by
    simp only [abs_one, ne_eq, one_ne_zero, not_false_eq_true, div_self]
    exact rfl
  --We also check $\phi (x * y) = \phi (x) \cdot \phi (y)$ which means $\phi$ is a homomorphism
  map_mul' := by
    intro ⟨x , invx, lx, rx⟩ ⟨y, invy, ly, ry⟩
    dsimp
    --It is because $|x \cdot y| = |x| \cdot |y|$
    have : |x * y| / (x * y) = (|x| / x) * (|y| / y) := by
      field_simp
      have : x * y ≠ 0 := by
        apply mul_ne_zero _ _
        exact left_ne_zero_of_mul_eq_one lx
        exact left_ne_zero_of_mul_eq_one ly
      exact congrFun (congrArg HDiv.hDiv (abs_mul x y)) (x * y)
    exact SetCoe.ext this

end Exercise_1294
