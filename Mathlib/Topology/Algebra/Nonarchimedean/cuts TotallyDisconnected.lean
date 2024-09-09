/-let t := y⁻¹ * x
      have ht' : t ≠ 1 :=  ht

      by exact open_subgroup_separating G x y hxy-/

/-
/-theorem Units.inv_mul{α : Type u} [Monoid α] (a : αˣ) :
↑a⁻¹ * ↑a = 1-/

/-@[to_additive]
theorem non_singleton_set_disconnected -- trying to use open_subgroup_separating' vs unprimed
    (x y : G) (U : Set G)
    (hx : x ∈ U) (hy :  y ∈ U) (hxy : y ≠ x) : ¬ IsConnected U := by
  have exv : ∃ (A B : Set G),
    IsOpen A ∧ IsOpen B ∧ (y⁻¹ * x) ∈ A  ∧ 1 ∈ B ∧ Disjoint A B ∧
    ∃ V : OpenSubgroup G, (V : Set G) ⊆ B   := by exact?
      by exact open_subgroup_separating' G x y hxy
  rcases exv with ⟨A , B, _, _, xya, _, dab, V, vb⟩
  have dva : Disjoint (V : Set G) A :=
    Set.disjoint_of_subset vb (fun ⦃a⦄ a ↦ a) (id (Disjoint.symm dab))
  obtain ⟨u , v, ou, ov, Uuv, Uu, Uv, emptyUuv⟩
      : ∃ u v : Set G, (IsOpen u) ∧ (IsOpen v) ∧ (U ⊆ u ∪ v) ∧ ((U ∩ u).Nonempty) ∧
      ((U ∩ v).Nonempty) ∧ (¬(U ∩ (u ∩ v)).Nonempty) := by
    use (y • (V : Set G))
    use (y • (V : Set G))ᶜ
    refine ⟨is_open_coset G y V, is_open_compl_coset' G y V, subset_coset_comp G y U V,
        non_empty_intersection_coset G x y U hy hxy V,
        non_empty_intersection_compl_coset G x y U hx A xya V dva,
        intersection_of_intersection_of_complements_empty G y U V⟩
  rintro ⟨_, h2⟩
  exact emptyUuv <| ((((h2 u v ou) ov) Uuv) Uu) Uv -/ -/
