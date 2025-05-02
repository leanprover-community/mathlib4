import Mathlib.Tactic
import Mathlib.Logic.Equiv.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Group.Subgroup.ZPowers



section Exercise_2170
/-
59. Show by a counterexample that the following "converse" of Theorem 6.6 is not a theorem: "If a group $G$ is such that every proper subgroup is cyclic, then $G$ is cyclic."
-/
abbrev SymmGroup (n : ℕ) := Equiv.Perm <| Fin n
--We prove that $S3$ is a example
--To begin with, $S3$ is not cyclic
lemma S3_not_cyclic' : ¬ IsCyclic (SymmGroup 3) := by
  intro h
  --As if it is cyclic,it is Commutative
  let h_comm : CommGroup (SymmGroup 3) := @IsCyclic.commGroup _ _ h
  --But $(0,1) ⬝ (1,2) \neq (1,2) \cdot (0,1)$
  let x1 : SymmGroup 3 := c[0, 1]
  let x2 : SymmGroup 3 := c[1, 2]
  have h_eq : x1 * x2 = x2 * x1 := mul_comm x1 x2
  --hence it is not cyclic,a contradiction
  have h_ne : x1 * x2 ≠ x2 * x1 := by unfold_let; decide
  exact h_ne h_eq

#eval Nat.factors 6

--Now we prove that every proper subgroup of $G$ is cyclic
theorem proper_Subgroup (G : Subgroup (SymmGroup 3))(h : G ≠ ⊤) : IsCyclic G := by
  --As we have $\operatorname{card} G = 6$
  have symm3_card : Fintype.card (SymmGroup 3) = 6 := by
    rw [Fintype.card_perm, Fintype.card_fin]
    decide
  have : Finite G := Subgroup.instFiniteSubtypeMem G
  have : Fintype G := Set.Finite.fintype this
  --Hence every proper subgroup $G$ have $\operatorname {card} G \mid 6$
  have dvd : Fintype.card G ∣ 6 := by
    rw [← symm3_card]
    exact Subgroup.card_subgroup_dvd_card G
  have : Fintype.card G ≤ 6 := by
    apply Nat.le_of_dvd
    norm_num
    exact dvd
  generalize h: Fintype.card G = n at *
  interval_cases n
  <;> norm_num at dvd
  --Now ,we have only 4 cases which $operatorname {card} G = 1 , 2, 3 ,6$
  · --When $operatorname {card} G = 1$,i.e.$G={1}$ which is trivial
    have : G = ⊥ := Subgroup.eq_bot_of_card_eq G h
    rw [this]
    exact Bot.isCyclic
  · --When $operatorname {card} G = 2$,Because $2$ is a prime
    have : Fact (Nat.Prime 2) := Nat.fact_prime_two
    --Hence it is a cyclic group
    exact isCyclic_of_prime_card h
  · --When $operatorname {card} G = 3$,Because $3$ is a prime
    have : Fact (Nat.Prime 2) := Nat.fact_prime_two
    --Hence it is a cyclic group
    exact isCyclic_of_prime_card h
  · --And When $\operatorname {card} G = 6$ ,then $G = S3$ which contricdicted to $G$ is a proper subgroup
    rw [← symm3_card] at h
    have : G = ⊤ := Subgroup.eq_top_of_card_eq G h
    contradiction

end Exercise_2170



def next {A: Type*} [Inhabited A] [DecidableEq A] (l: List A) (x : A) : A :=
  match l with
  | [] => default
  | List.cons x' xs' =>
    if x = x'
      then List.headD  xs' default
      else next xs' x



section Special_Example_070901

open Equiv.Perm
lemma Equiv.Perm.perm_entry_eq_of_conj_perm (n : ℕ) (σ : Perm <| Fin n)
(l : List <| Fin n)
  (hnd : l.Nodup) : σ * l.formPerm * σ⁻¹ = (l.map σ).formPerm := by
  --即证：对任意x : Fin n有σ(l(σ⁻¹(x))) = x
  apply Equiv.ext
  intro x
  show σ (l.formPerm (σ⁻¹ x)) = (l.map σ).formPerm x
  by_cases In : σ⁻¹ x ∈ l
  --若σ⁻¹(x) ∈ l，设σ⁻¹(x) = l_k
  · let h := List.mem_iff_get.mp In
    rcases h with ⟨⟨k,kle⟩, hk⟩
    have : List.length (l.map σ) = List.length l := List.length_map l ⇑σ
    have kle' : k < List.length (l.map σ) := by
      exact Nat.lt_of_lt_of_eq kle (id (Eq.symm this))
    --则(σ l)_k = x
    have hk' : σ (l.get ⟨k, kle⟩) = (l.map σ).get ⟨k, kle'⟩ := by
      symm
      apply List.get_map
    have hk : l.get ⟨k, kle⟩ = σ⁻¹ x := by
      rw [← hk]
    have hk' : (l.map σ).get ⟨k, kle'⟩ = x := by
      rw [← hk', hk]
      exact apply_inv_self σ x
    rw [← hk, ← hk']
    --又l不重复，故l (σ₁⁻¹(x)) = l_(k+1)，(σ l) x = (σ l)_(k+1)(mod长度考虑)
    rw [List.formPerm_apply_get, List.formPerm_apply_get]
    --而l与(σ l)长度相同，故l_(k+1)与(σ l)_(k+1)下标相同
    have : (k + 1) % (List.length l) = (k + 1) % (List.length (l.map
σ)) := by
      exact congrArg (HMod.hMod (k + 1)) (id (Eq.symm this))
    have le : (k + 1) % (List.length l) < List.length l := by
      refine Nat.mod_lt (k + 1) ?_
      exact List.length_pos_of_mem In
    have le' : (k + 1) % (List.length (l.map σ)) < List.length l := by
      rw [← this]
      apply le
    have : l.get ⟨(k + 1) % (List.length l), le⟩ = l.get ⟨(k + 1) %
(List.length (l.map σ)), le'⟩ := by
      refine (List.Nodup.get_inj_iff hnd).mpr ?_
      exact Fin.mk.inj_iff.mpr this
    rw [this]
    --故σ(l_(k+1)) = (σ l)_(k+1)，即原命题成立
    exact Eq.symm (List.get_map ⇑σ)
    refine (List.nodup_map_iff_inj_on hnd).mpr ?_
    intro x _ y _ xy
    have eq : σ⁻¹ (σ x) = σ⁻¹ (σ y) := by
      exact congrArg (⇑σ⁻¹) xy
    have : σ⁻¹ (σ x) = x := inv_apply_self σ x
    rw [← this, eq]
    exact inv_apply_self σ y
    exact hnd
  --若σ⁻¹(x) ∉ l，则x ∉ (σ l)
  · have : l.formPerm (σ⁻¹ x) = σ⁻¹ x := List.formPerm_apply_of_not_mem In
    rw [this]
    have : σ (σ⁻¹ x) ∉ l.map σ := by
      intro In'
      apply In
      let h := List.mem_iff_get.mp In'
      rcases h with ⟨⟨k,kle⟩, hk⟩
      have : List.length (l.map σ) = List.length l := List.length_map l ⇑σ
      have kle' : k < List.length l := by
        exact Nat.lt_of_lt_of_eq kle this
      have hk' : σ (l.get ⟨k, kle'⟩) = (l.map σ).get ⟨k, kle⟩ := by
        symm
        apply List.get_map
      rw [hk] at hk'
      have : σ⁻¹ (σ (l.get ⟨k, kle'⟩)) = σ⁻¹ (σ (σ⁻¹ x)) := by
        rw [hk']
      rw [inv_apply_self, inv_apply_self] at this
      refine List.mem_iff_get.mpr ?intro.mk.a
      exact Exists.intro ⟨k, kle'⟩ this
    --故σ(l(σ⁻¹(x))) = σ(σ⁻¹(x)) = x = (σ l) x，即原命题成立
    rw [apply_inv_self] at this
    have : (l.map σ).formPerm x = x := List.formPerm_apply_of_not_mem this
    rw [this, apply_inv_self]

end Special_Example_070901
