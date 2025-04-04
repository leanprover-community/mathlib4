import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.Coset
import Mathlib.Deprecated.Subgroup
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Init.Data.Nat.Basic

section Special_Example_070903
open Classical
open Pointwise
/-
Suppose that $G$ is a group with subgroups $H$ and $K$ such that $H \cap K = \{1\}$, then $HK \cong H \times K$ (as sets).

1.We prove lemma1 : If $H \cap K = \{1\}$ and $h_1,h_2 \in H,k_1,k_2\in K$ which have $h_1 k_1 = h_2 k_2$ will lead to $h_1 = k_1$ and $h_2 = k_2$
We have $h_1^{-1}h_2=k_1k_2^{-1}$ by the condition,then the Left-Hand-Side is $\in H$ and the Right-Hand-Side is $\in K$ and so we have the equation is $\in H \cap K$,i.e the both side $h_1^{-1}h_2=k_1k_2^{-1}=1$,which leads to $h_1=h_2$ and $k_1 = k_2$ and we are done

2.We prove lemma2 : If $H \cap K = \{1\}$ and $H,K$ is normal in $G$,then $\forall a \in H,b \in K$ will lead to $ab = ba$
We consider $aba^{-1}b^{-1}$.It is $\in H$ because $a\in H$ and $ba^{-1}b^{-1}\in H$ as $H$ is normal. Also,it is $\in K$ because $b^{-1}\in K$ and $aba^{-1}\in K$ as $K$ is normal. So we have the result that $aba^{-1}b^{-1} \in H \cap K$,i.e the both $aba^{-1}b^{-1}=1$,which leads to $ab=ba$ and we are done

3.Comeback to the main problem ,it is obvious that $\forall x \in HK$,there $\exists h\in H $and $k\in K$ which $hk = x$ by Axiom of Choice.Then we may construct the map $\phi$ which $\phi (x) = (h,k)$ .

4.Moreover $\phi^{-1}(h,k)=hk$ which satisfies $\phi(\phi^{-1}(h,k))=\phi(hk)=(h_1 , k_1)$.So we have $h_1k_1 = hk$.Hence$\phi(\phi^{-1}(h,k)) = (h , k)$.Suppose that $x = hk$ which $h\in H $and $k\in K$.So it also satisfies $\phi^{-1}(\phi(x))=\phi^{-1}(h,k) = hk =x$,i.e. we have $\phi^{-1}(\phi(x)) = x$.Now, we proved that $\phi^{-1}(h,k)=hk$ is well defined and so $\phi$ is bijective.

5.Further more ,We have $\phi$ is a homomorphism because if $x = h_1k_1$ and $y = h_2k_2$,then$\phi (x) \phi (y) = h_1k_1h_2k_2 = h_1h_2k_1k_2 =\phi (xy)$ by using lemma2.Hence $\phi$ is a isomorphism and we proved $HK \cong H \times K$.
-/

/-
Suppose that $G$ is a group with subgroups $H$ and $K$ such that $H \cap K = \{1\}$, then $HK \cong H \times K$ (as sets).
-/
--We prove lemma1 : If $H \cap K = \{1\}$ and $h_1,h_2 \in H,k_1,k_2\in K$ which have $h_1 k_1 = h_2 k_2$ will lead to $h_1 = k_1$ and $h_2 = k_2$
lemma useful{G : Type*} [Group G] (H K : Subgroup G) (h : H ⊓ K = ⊥)
    {h₁ h₂ : H} {k₁ k₂ : K}(eq : (h₁ : G) * (k₁ : G) = (h₂ : G) * (k₂ : G)) : (h₁, k₁) = (h₂, k₂) := by
  --We have $h_1^{-1}h_2=k_1k_2^{-1}$ by the condition,
  have eq : (h₂ : G)⁻¹ * (h₁ : G) = (k₂ : G) * (k₁ : G)⁻¹ := by calc
    _ = (h₂ : G)⁻¹ * ((h₁ : G) * (k₁ : G)) * (k₁ : G)⁻¹ := by group
    _ = (h₂ : G)⁻¹ * ((h₂ : G) * (k₂ : G)) * (k₁ : G)⁻¹ := by rw [eq]
    _ = _ := by group
  --then the Left-Hand-Side is $\in H$
  have inH : (h₂ : G)⁻¹ * (h₁ : G) ∈ H := by
    have : (h₂ : G)⁻¹  ∈ H := (Subgroup.inv_mem_iff H).mpr (SetLike.coe_mem h₂)
    exact (Subgroup.mul_mem_cancel_right H (SetLike.coe_mem h₁)).mpr this
  --and the Right-Hand-Side is $\in K$
  have inK : (h₂ : G)⁻¹ * (h₁ : G) ∈ K := by
    rw [eq]
    have : (k₁ : G)⁻¹  ∈ K := (Subgroup.inv_mem_iff K).mpr (SetLike.coe_mem k₁)
    exact (Subgroup.mul_mem_cancel_right K this).mpr (SetLike.coe_mem k₂)
  have heq : h₁ = h₂ := by calc
    _ = h₂ * (h₂⁻¹ * h₁) := by group
    _ = h₂ * 1 := by
      ---- and so we have the equation is $\in H \cap K$,
      have : (h₂ : G)⁻¹ * (h₁ : G) ∈ H ⊓ K := Set.mem_inter inH inK
      have : (h₂ : G)⁻¹ * (h₁ : G) = 1 := by rw [h] at this; exact this
      have : h₂⁻¹ * h₁ = 1 := OneMemClass.coe_eq_one.mp this
      rw [this]
    _ = _ := by group
  have keq : k₁ = k₂ := by
    have : (k₂ : G) = (k₁ : G) := by calc
      _ = (k₂ : G) * (k₁ : G)⁻¹ * (k₁ : G) := by group
      _ = 1 * (k₁ : G) := by
        rw [heq] at eq
        simp only [mul_left_inv] at eq
        rw [eq]
      _ = (k₁ : G) := by group
    exact SetCoe.ext (id (Eq.symm this))
    ----i.e the both side $h_1^{-1}h_2=k_1k_2^{-1}=1$,which leads to $h_1=h_2$ and $k_1 = k_2$ and we are done
  exact Prod.ext heq keq

--2.We prove lemma2 : If $H \cap K = \{1\}$ and $H,K$ is normal in $G$,then $\forall a \in H,b \in K$ will lead to $ab = ba$
lemma used {G : Type*} [Group G](H K : Subgroup G) [hN : H.Normal] [kN : K.Normal](h : H ⊓ K = ⊥)(a : H)(b : K)
   : (a : G) * (b : G) = (b : G) * (a : G) := by
  have h₁': ∀ m, m ∈ H → ∀ g : G, g * m * g⁻¹ ∈ H := fun m b g => hN.conj_mem m b g
  --We consider $aba^{-1}b^{-1}$.
  have hm: (a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹ ∈ H := by
    --It is $\in H$ because $a\in H$ and $ba^{-1}b^{-1}\in H$ as $H$ is normal.
    have : (a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹ = (a : G) * ((b : G) * (a : G)⁻¹ * (b : G)⁻¹) := by group
    rw [this]
    have : (a : G)⁻¹ ∈ H := (Subgroup.inv_mem_iff H).mpr (SetLike.coe_mem a)
    exact (Subgroup.mul_mem_cancel_right H this).mp (h₁' (↑b * ↑a⁻¹ * ↑b⁻¹) (h₁' (↑a⁻¹) this ↑b) ↑a)
  -- Also,it is $\in K$ because $b^{-1}\in K$ and $aba^{-1}\in K$ as $K$ is normal.
  have hn: (a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹ ∈ K := by
    have : (b : G)⁻¹ ∈ K := (Subgroup.inv_mem_iff K).mpr (SetLike.coe_mem b)
    exact (Subgroup.mul_mem_cancel_right K this).mpr (kN.conj_mem ↑b ((Subgroup.inv_mem_iff K).mp this) ↑a)
  -- So we have the result that $aba^{-1}b^{-1} \in H \cap K$,
  have h₁: (a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹ ∈ H ⊓ K := Set.mem_inter hm hn
  rw [h] at h₁
  -- i.e the both $aba^{-1}b^{-1}=1$
  have : (a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹ = 1 := by exact h₁
  --,which leads to $ab=ba$ and we are done
  exact commutatorElement_eq_one_iff_mul_comm.mp h₁

noncomputable def Group.product_mul_equiv_of_normal_of_disjoint {G : Type*} [Group G] (H K : Subgroup G) [hN : H.Normal] [kN : K.Normal] (h : H ⊓ K = ⊥) : (H ⊔ K : Subgroup G) ≃* (H × K) := by
  --3.Comeback to the main problem ,it is obvious that $\forall x \in HK$
  have hkeq : (H ⊔ K).carrier = H.carrier * K.carrier := by
    apply Subgroup.normal_mul
  have In1 (x : (H ⊔ K : Subgroup G)) : x.1 ∈ H.carrier * K.carrier := by
    #check x  --x : ↥(H ⊔ K)
    #check x.1--↑x : G
    #check x.2--↑x ∈ H.carrier * K.carrier
    rw [← hkeq]
    exact Subtype.coe_prop x
  have In2 (x : H × K) : x.1.1 * x.2.1 ∈ (H ⊔ K).carrier := by
    rw [hkeq]
    refine Set.mul_mem_mul ?_ ?_
    exact Subtype.coe_prop x.1
    exact Subtype.coe_prop x.2
  exact {
    toFun := by
      --,there $\exists h\in H $and $k\in K$ which $hk = x$ by Axiom of Choice.Then we may construct the map $\phi$ which $\phi (x) = (h,k)$ .
      intro x
      let x₁ : H := ⟨choose (In1 x), (choose_spec (In1 x)).1⟩
      let x₂ : K := ⟨choose (choose_spec (In1 x)).2, (choose_spec (choose_spec (In1 x)).2).1⟩
      use x₁, x₂
      exact (choose_spec (choose_spec (In1 x)).2).1
    -- fun (x : (H ⊔ K : Subgroup G)) ↦
    -- ⟨⟨choose (In1 x), (choose_spec (In1 x)).1⟩, ⟨choose (choose_spec (In1 x)).2, (choose_spec (choose_spec (In1 x)).2).1⟩⟩
    --上面尖括号负责将type H ⊔ K 转化为 type H，type K
    --4.Moreover $\phi^{-1}(h,k)=hk$
    invFun := fun (x : H × K) ↦ ⟨x.1.1 * x.2.1, In2 x⟩
    left_inv := by
      intro x
      #check choose (In1 x)                         --choose ⋯ : G
      #check (choose_spec (In1 x)).1                --(choose_spec (In1 x)).left : choose ⋯ ∈ H.carrier
      #check (choose_spec (In1 x)).2                --(choose_spec (In1 x)).right : ∃ b ∈ K.carrier, (fun x x_1 => x * x_1) (choose ⋯) b = ↑x
      #check choose (choose_spec (In1 x)).2         --choose ⋯ : G
      #check (choose_spec (choose_spec (In1 x)).2).1--(choose_spec (choose_spec (In1 x)).right).left : choose ⋯ ∈ K.carrier
      #check (choose_spec (choose_spec (In1 x)).2).2--(choose_spec (choose_spec (In1 x)).right).right : (fun x x_1 => x * x_1) (choose ⋯) (choose ⋯) = ↑x
      ext
      -- which satisfies $\phi(\phi^{-1}(h,k))=\phi(hk)=(h_1 , k_1)$.
      show choose (In1 x) * choose (choose_spec (In1 x)).2 = x
      --So we have $h_1k_1 = hk$.Hence$\phi(\phi^{-1}(h,k)) = (h , k)$.
      exact (choose_spec (choose_spec (In1 x)).2).2
    right_inv := by
      --Suppose that $x = hk$ which $h\in H $and $k\in K$.
      intro ⟨h₁, k₁⟩
      let x : (H ⊔ K : Subgroup G) := ⟨h₁.1 * k₁.1, In2 ⟨h₁, k₁⟩⟩
      let x₁ : H := ⟨choose (In1 x), (choose_spec (In1 x)).1⟩
      let x₂ : K := ⟨choose (choose_spec (In1 x)).2, (choose_spec (choose_spec (In1 x)).2).1⟩
      show (x₁, x₂) = (h₁, k₁)
      --So it also satisfies $\phi^{-1}(\phi(x))=\phi^{-1}(h,k) = hk =x$,
      have : (x₁ : G) * (x₂ : G) = (h₁ : G) * (k₁ : G) := (choose_spec (choose_spec (In1 x)).2).2
      exact useful H K h this
      --i.e. we have $\phi^{-1}(\phi(x)) = x$.Now, we proved that $\phi^{-1}(h,k)=hk$ is well defined and so $\phi$ is bijective.
    map_mul' := by
      --5.Further more ,We have $\phi$ is a homomorphism
      intro x y
      dsimp
      let x₁ : H := ⟨choose (In1 x), (choose_spec (In1 x)).1⟩
      let x₂ : K := ⟨choose (choose_spec (In1 x)).2, (choose_spec (choose_spec (In1 x)).2).1⟩
      let y₁ : H := ⟨choose (In1 y), (choose_spec (In1 y)).1⟩
      let y₂ : K := ⟨choose (choose_spec (In1 y)).2, (choose_spec (choose_spec (In1 y)).2).1⟩
      let xy₁ : H := ⟨choose (In1 (x * y)), (choose_spec (In1 (x * y))).1⟩
      let xy₂ : K := ⟨choose (choose_spec (In1 (x * y))).2, (choose_spec (choose_spec (In1 (x * y))).2).1⟩
      --because if $x = h_1k_1$ and $y = h_2k_2$,then$\phi (x) \phi (y) = h_1k_1h_2k_2 = h_1h_2k_1k_2 =\phi (xy)$ by using lemma2.
      show (xy₁, xy₂) = (x₁, x₂) * (y₁, y₂)
      apply useful; apply h
      have xyeq : (xy₁ : G) * (xy₂ : G) = x * y := (choose_spec (choose_spec (In1 (x * y))).2).2
      have xeq : (x₁ : G) * (x₂ : G) = x := (choose_spec (choose_spec (In1 x)).2).2
      have yeq : (y₁ : G) * (y₂ : G) = y := (choose_spec (choose_spec (In1 y)).2).2
      rw [xyeq, ←xeq, ←yeq]
      calc
        _ = (x₁ : G) * ((x₂ : G) * (y₁ : G)) * (y₂ : G) := by group
        _ = (x₁ : G) * ((y₁ : G) * (x₂ : G)) * (y₂ : G) := by
          have : (y₁ : G) * (x₂ : G) = (x₂ : G) * (y₁ : G) := by apply used; apply h
          rw [this]
        _ = (x₁ : G) * (y₁ : G) * ((x₂ * y₂) : G) := by group
        _ = ↑((x₁, x₂).1 * (y₁, y₂).1) * ↑((x₁, x₂).2 * (y₁, y₂).2) := by
          have x1 : (x₁, x₂).1 = x₁ := rfl
          have x2 : (x₁, x₂).2 = x₂ := rfl
          have y1 : (y₁, y₂).1 = y₁ := rfl
          have y2 : (y₁, y₂).2 = y₂ := rfl
          rw [x1, x2, y1, y2]
          simp only [Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup,
            Subgroup.mem_toSubmonoid, Submonoid.coe_mul]
      --Hence $\phi$ is a isomorphism and we proved $HK \cong H \times K$.

  }

end Special_Example_070903




section ex3224B
open Function
variable [Group G] {H1 H2 : Subgroup G} [H1.Normal] [H2.Normal](h1 : H1 ⊓ H2 = ⊥)
def prod_to_ele (H1 H2 : Subgroup G): H1 × H2 → G := fun x => x.1.1 * x.2.1
lemma injective_of_inf_eg_bot (h1 : H1 ⊓ H2 = ⊥) : Injective <| prod_to_ele H1 H2 := by
  intro x y hxy
  simp [prod_to_ele] at hxy
  have : y.1⁻¹ * x.1 = y.2.1 * x.2⁻¹ := sorry
  have mem_inf : y.1⁻¹ * x.1.1 ∈ H1 ⊓ H2 := sorry
  have fst_eq : x.1 =y.1 := by
    have := Subgroup.mem_bot.1 <| h1 ▸ mem_inf
    simp [inv_mul_eq_one] at this
    exact this.symm
  sorry

lemma surjective_of_inf_eg_bot (h1 : H1 ⊓ H2 = ⊥) : Function.Surjective (prod_to_ele H1 H2 ) := by
  sorry

-- Define the mul on sbugroup pointwisely.-/
def subgroup.mul_pointwise {H1 H2 : Subgroup G} : Set G :=
  (prod_to_ele H1 H2)'' (Set.univ)



noncomputable instance [H1.Normal][H2.Normal](h1 :H1 ⊓ H2 = ⊥)
(h2 :Function.Surjective (prod_to_ele H1 H2 )) :  (H1 × H2) ≃ G :=
  Equiv.ofBijective (prod_to_ele H1 H2) ⟨(injective_of_inf_eg_bot h1), h2⟩

end ex3224B
