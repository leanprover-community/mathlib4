import Mathlib

open Equiv.Perm
#check List.get
--重要定理  List.get
--相当于把 List 当成 C++ 中的数组来使用

lemma Equiv.Perm.perm_entry_eq_of_conj_perm (n : ℕ) (σ : Perm <| Fin n)
(l : List <| Fin n)
  (hnd : l.Nodup) : σ * l.formPerm * σ⁻¹ = (l.map σ).formPerm := by
  --It suffice to show that, for all x : Fin n, we have σ(l(σ⁻¹(x))) = x
  apply Equiv.ext
  intro x
  by_cases In : σ⁻¹ x ∈ l
  --If σ⁻¹(x) ∈ l，Suppose σ⁻¹(x) = l_k
  · show σ (l.formPerm (σ⁻¹ x)) = (l.map σ).formPerm x
    let h := List.mem_iff_get.mp In
    rcases h with ⟨⟨k,kle⟩, hk⟩--尖括号把type转成Fin n
    have : List.length (l.map σ) = List.length l := List.length_map l ⇑σ
    have kle' : k < List.length (l.map σ) := by
      exact Nat.lt_of_lt_of_eq kle (id (Eq.symm this))
    --Hence (σ l)_k = x
    have hk' : σ (l.get ⟨k, kle⟩) = (l.map σ).get ⟨k, kle'⟩ := Eq.symm (List.get_map ⇑σ)
      --List.get_map 是化简List.map的关键步骤
    have hk' : (l.map σ).get ⟨k, kle'⟩ = x := by
      rw [← hk', hk]
      exact apply_inv_self σ x
    rw [← hk, ← hk']
    --but l is disjoint ，thus l (σ₁⁻¹(x)) = l_(k+1)，(σ l) x = (σ l)_(k+1) (mod l.length)
    rw [List.formPerm_apply_get, List.formPerm_apply_get]
    --相当于把list的第i项映射到第i+1项
    --and l and (σ l) have the same length，which means l_(k+1) and (σ l)_(k+1) have the same subscript
    have : (k + 1) % (List.length l) = (k + 1) % (List.length (l.map σ)) := congrArg (HMod.hMod (k + 1)) (id (Eq.symm this))
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
    --hence σ(l_(k+1)) = (σ l)_(k+1)，and we are done
    exact Eq.symm (List.get_map ⇑σ)
    refine (List.nodup_map_iff_inj_on hnd).mpr ?_
    intro x _ y _ xy
    have eq : σ⁻¹ (σ x) = σ⁻¹ (σ y) := congrArg (⇑σ⁻¹) xy
    have : σ⁻¹ (σ x) = x := inv_apply_self σ x
    rw [← this, eq]
    exact inv_apply_self σ y
    exact hnd
  --If σ⁻¹(x) ∉ l，we have x ∉ (σ l)
  · rw [List.formPerm_apply_of_not_mem]
    · --Hence σ(l(σ⁻¹(x))) = σ(σ⁻¹(x)) = x = (σ l) x，and we are done
      calc
        _ = σ (l.formPerm (σ⁻¹ x)) := rfl
        _ = σ (σ⁻¹ x) := by rw [List.formPerm_apply_of_not_mem In]
        _ = _ := apply_inv_self σ x
    · by_contra h
      rcases (List.mem_map.mp h) with ⟨y, y_in_l, hy⟩
      rw [inv_eq_iff_eq.mpr (id (Eq.symm hy))] at In
      contradiction

    /-show σ (l.formPerm (σ⁻¹ x)) = (l.map σ).formPerm x
    have : l.formPerm (σ⁻¹ x) = σ⁻¹ x := List.formPerm_apply_of_not_mem In
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
    -/
