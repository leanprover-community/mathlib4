import Mathlib.Tactic

/-
Suppose $S$ is a set.

Let $\operatorname{Sym}(S)$ denote the set of all bijections $f: S\to S$. Prove that $\operatorname{Sym}(S)$ is a group, where the operation is composition.
-/
section Example_1102B
noncomputable instance (S : Type*) : Group {f : S → S // f.Bijective} where
  mul f g := ⟨f.val ∘ g.val, Function.Bijective.comp f.property g.property⟩
  mul_assoc _ _ _ := rfl
  one := ⟨id, Function.bijective_id⟩
  one_mul _ := rfl
  mul_one _ := rfl
  inv := by
    intro f
    use Function.surjInv f.property.2
    apply Function.bijective_iff_has_inverse.mpr
    use f
    constructor
    · exact Function.rightInverse_surjInv f.property.2
    · exact Function.leftInverse_surjInv f.property
  mul_left_inv := by
    intro f
    apply Subtype.val_inj.mp
    exact Function.RightInverse.id (Function.leftInverse_surjInv f.property)
end Example_1102B



section Example_1414B
/-
Let $a,b,c$ be elements of a group $G$ , then $ord(abc)=ord(cab)$.
-/
example { G : Type* } [ Group G ] { a b c: G } :
    orderOf ( a * b * c ) = orderOf ( c * a * b ) := by
  have (x y : G): ∀ k : ℕ , y * (x * y) ^ k = (y * x) ^ k * y := by
    intro k
    induction' k with k ih
    · simp only [pow_zero, mul_one, one_mul]
    · calc
        _ = y * (x * y) ^ k * (x * y) := by rw [pow_succ (x * y) k]; group
        _ = (y * x) ^ k * (y * x) * y := by rw[ih]; group
        _ = _:= by rw [pow_succ (y * x) k]; group
  have div (x y : G): orderOf (x * y) ∣ orderOf (y * x) := by
    apply orderOf_dvd_of_pow_eq_one
    calc
      _ = y⁻¹ * (y * (x * y) ^ orderOf (y * x)) := by group
      _ = y⁻¹ * (y * x) ^ orderOf (y * x) * y := by rw [this x y (orderOf (y * x))]; group
      _ = y⁻¹ * 1 * y := by rw [pow_orderOf_eq_one (y * x)]
      _ = _ := by group
  have div1 : orderOf (a * b * c) ∣ orderOf (c * (a * b)) := div (a * b) c
  have div2 : orderOf (c * (a * b)) ∣ orderOf (a * b * c) := div c (a * b)
  calc
    _ = orderOf (c * (a * b)) := Nat.dvd_antisymm div1 div2
    _ = _ := by have : c * (a * b) = c * a * b := Eq.symm (mul_assoc c a b); congr

end Example_1414B



section Example_2302B
def H_cap_K {G : Type*} [Group G] (H K: Subgroup G) : Set G := { s | s ∈ H.carrier ∩ K.carrier }

def intersect_subgroup {G : Type*} [Group G] (H K: Subgroup G) (h₁: H.Normal) (h₂: K.Normal) : Subgroup G where
  carrier := H_cap_K H K
  mul_mem' := by
    rintro a b ⟨ah, ak⟩ ⟨bh, bk⟩
    -- 简写
    -- constructor
    -- ·exact H.mul_mem' ah ak
    -- ·exact K.mul_mem' ak bk
    exact ⟨(H.mul_mem' ah bh), (K.mul_mem' ak bk)⟩
  one_mem' := by
    exact ⟨H.one_mem', K.one_mem'⟩
  inv_mem' := by
    rintro x ⟨xh, xk⟩
    exact ⟨(Subgroup.inv_mem_iff H).mpr xh, (Subgroup.inv_mem_iff K).mpr xk⟩

example {G : Type*} [Group G] (H K: Subgroup G) (h₁: H.Normal) (h₂: K.Normal) : (intersect_subgroup H K h₁ h₂).Normal where
  conj_mem := by
    rintro g ⟨gh, gk⟩ g₁
    exact ⟨Subgroup.mem_carrier.mpr (h₁.conj_mem g gh g₁), Subgroup.mem_carrier.mpr (h₂.conj_mem g gk g₁)⟩
end Example_2302B



section Example_2207B
def power_subgroup {G : Type*} [CommGroup G] (n : ℕ): Set G := { s | s ^ n = 1 }

example {G : Type*} [CommGroup G] (n : ℕ): Subgroup G where
  carrier := power_subgroup n
  mul_mem' := by
    intro a b ha hb
    have : (a * b) ^ n = 1 := by
      calc
        _ = a ^ n * b ^ n := by exact mul_pow a b n
        _ = 1 * 1 := by rw [ha, hb]
        _ = _ := by norm_num
    apply this
  one_mem' := by
    --注意type转化
    -- have : (1: G) ^ n = 1 := by exact one_pow n
    exact one_pow n
  inv_mem' := by
    intro x hx
    have : (x⁻¹) ^ n = 1 := by
      calc
        _ = (x ^ n)⁻¹ := by exact inv_pow x n
        _ = 1⁻¹ := by rw [hx]
        _ = _ := by norm_num
    apply this
end Example_2207B



section Example_2206B
/-
Let $G$ be an Abelian group. Assume $n$ is an integer. Show that $nG=\{ng|g\in G\}$ is a subgroup of $G$.
-/
def smul_subgroup {G : Type*} [CommGroup G] (n : ℕ): Set G := { s | ∃ g : G, s = g ^ n }

example {G : Type*} [CommGroup G] (n : ℕ): Subgroup G where
  --Prove Set $G$ is a subgroup
  carrier := smul_subgroup n
  --If have $a,b \in G$ and we suppose $a ^ {sa} = 1 , b ^ {sb} = 1$
  mul_mem' := by
    intro a b ⟨sa, ha⟩ ⟨sb, hb⟩
    use sa * sb
    --then we have $(a b) ^ {sa * sb} = 1$
    calc
      _ = sa ^ n * sb ^ n := by rw[ha, hb]
      _ = _ := by exact Eq.symm (mul_pow sa sb n)
  one_mem' := by
    use 1
    norm_num
  inv_mem' := by
    --To prove if $a \in G$,then $a ^ {-1}\in G$
    intro x ⟨sx, hx⟩
    use sx⁻¹
    rw [hx]
    exact Eq.symm (inv_pow sx n)
end Example_2206B


/-
Prove that if $G$ is an Abelian group, written multiplicatively, with identity element $e$, then all elements $x$ of $G$ satisfying the equation $x^{2}=e$ form a subgroup $H$ of $G$.
-/
section Example_2203B
def unit_subgroup {G : Type*} [CommGroup G] : Set G := { s | s ^ 2 = 1 }
--Prove $Unit Subgroup = \{s | s ^ {2} = 1\}$ is a subgroup
example {G : Type*} [CommGroup G] (n : ℕ): Subgroup G where
  carrier := unit_subgroup
  --$\forall a b \in G$ will have $(a b) ^ {2} = 1$ which means $a b \in Unit Subgroup$
  mul_mem' := by
    intro a b ha hb
    calc
      _ = a ^ 2 * b ^ 2 := by exact mul_pow a b 2
      _ = 1 * 1 := by rw [ha, hb]
      _ = _ := by norm_num
  one_mem' := by
    simp [unit_subgroup]
  --$\forall a \in G$ will have $(a ^ {-1}) ^ {2} = 1$ which means $a \in Unit Subgroup$
  inv_mem' := by
    intro x hx
    calc
      _ = (x ^ 2)⁻¹ := by exact inv_pow x 2
      _ = 1⁻¹ := by rw[hx]
      _ = 1 := by norm_num

end Example_2203B
