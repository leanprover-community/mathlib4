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


/-open TopologicalSpace in
@[to_additive]
lemma open_subgroup_separating
    (t : G) (ht : t ≠ 1) : ∃ (A : Opens G),
    IsOpen A ∧ IsOpen B ∧ (y⁻¹ * x) ∈ A  ∧ 1 ∈ B ∧ Disjoint A B ∧
    ∃ V : OpenSubgroup G, (V : Set G) ⊆ B := by
  change (y = x) → False at hxy
  rw [← inv_mul_eq_one] at hxy
  apply t2_separation at hxy
  rcases hxy with ⟨A, B, opena, openb, diff, one, disj⟩
  use A
  use B
  refine ⟨opena, openb, diff, one, disj, ?_⟩
  · apply IsOpen.mem_nhds at one
    apply NonarchimedeanGroup.is_nonarchimedean at one
    exact one
    exact openb-/

-- I don't know if `Opens G` is better than `A : Set G` + `IsOpen A`.
/-open TopologicalSpace in
@[to_additive]
lemma open_subgroup_separating'
    (t : G) (ht : t ≠ 1) : ∃ (A : Opens G) (V : OpenSubgroup G),
    t ∈ A ∧ 1 ∈ V ∧ Disjoint A V := by
  rcases (t2_separation ht) with ⟨A, B, opena, openb, diff, one, disj⟩
  obtain ⟨V, hV⟩ := NonarchimedeanGroup.is_nonarchimedean B (IsOpen.mem_nhds openb one)
  exact ⟨⟨A, opena⟩, V, diff, one_mem V,
    fun _ ↦ by apply Set.disjoint_of_subset_right hV disj⟩-/


/-@[to_additive]
lemma non_empty_intersection_compl_coset (x y : G) (U : Set G) (hx : x ∈ U)
    (A : Opens G) (quot : (y⁻¹ * x) ∈ A ) (V : OpenSubgroup G) (dva : Disjoint (V : Opens G) A) :
    (U ∩ ((y • (V : Set G))ᶜ)).Nonempty := by
  simp_rw [Set.inter_nonempty, Set.mem_compl_iff]
  use x, hx
  intro con
  rw [mem_leftCoset_iff y] at con
  simp only [Disjoint, le_bot_iff] at dva
  sorry
  -- have ne : (V : Opens G) ∩ A = ∅ → False := by
  -- exact Disjoint.subset_compl_right (Disjoint.symm dva) quot con -/

/-open TopologicalSpace in
/-- In a nonarchimedean group `G`, any set which contains two distinct points is disconnected. This
can be used to show that for any `x : G`, the connected component of `x` is `{x}`.-/
@[to_additive]
theorem non_singleton_set_disconnected
    (x y : G) (U : Set G)
    (hx : x ∈ U) (hy :  y ∈ U) (hxy : y ≠ x) : ¬ IsConnected U := by
  have exv : ∃ (A B : Opens G),
    (y⁻¹ * x) ∈ A  ∧ 1 ∈ B ∧ Disjoint A B ∧
    ∃ V : OpenSubgroup G, (V : Set G) ⊆ B   := by
      have ht : y⁻¹ * x ≠ 1 := by
        by_contra! con
        have hy : y⁻¹ * y = 1 := inv_mul_cancel y
        rw [← hy] at con
        have : x = y := by
          apply mul_left_cancel at con
          exact con
        exact hxy (id (Eq.symm this))
      have : ∃ (A : Opens G) (V : OpenSubgroup G), y⁻¹ * x ∈ A ∧ 1 ∈ V ∧ Disjoint A V := by
        exact open_subgroup_separating' G (y⁻¹ * x) ht
      rcases this with ⟨A , V, ha, hv, dav⟩
      use A , V
      constructor
      · exact ha
      · constructor
        · exact hv
        · constructor
          · exact dav
          · use V
            exact fun ⦃a⦄ a ↦ a
  rcases exv with ⟨A , B, ha, hb , dab, V, vb⟩
  have dva : Disjoint (V : Opens G) A   := by
    exact Disjoint.mono vb (fun ⦃a⦄ a ↦ a) (id (Disjoint.symm dab))
  have dva' : Disjoint (V : Set G) A := by
    apply Disjoint.mono vb (fun ⦃a⦄ a ↦ a)
    refine Disjoint.symm ?_
    convert dab
    constructor
    · exact fun a ↦ dab
    · intro h
      sorry
  obtain ⟨u , v, ou, ov, Uuv, Uu, Uv, emptyUuv⟩
      : ∃ u v : Set G, (IsOpen u) ∧ (IsOpen v) ∧ (U ⊆ u ∪ v) ∧ ((U ∩ u).Nonempty) ∧
      ((U ∩ v).Nonempty) ∧ (¬(U ∩ (u ∩ v)).Nonempty) := by
    use (y • (V : Set G)) , (y • (V : Set G))ᶜ
    refine ⟨is_open_coset G y V, is_open_compl_coset' G y V, subset_coset_comp G y U V,
        non_empty_intersection_coset G x y U hy hxy V,
        non_empty_intersection_compl_coset' G x y U hx A ha V dva',
        intersection_of_intersection_of_complements_empty G y U V⟩
  rintro ⟨_, h2⟩
  exact emptyUuv <| ((((h2 u v ou) ov) Uuv) Uu) Uv-/

/-open TopologicalSpace in
@[to_additive]
theorem non_singleton_set_disconnected'
    (x y : G) (U : Set G)
    (hx : x ∈ U) (hy :  y ∈ U) (hxy : y ≠ x) : ¬ IsConnected U := by
  have exv : ∃ (A B : Opens G),
    (y⁻¹ * x) ∈ A  ∧ 1 ∈ B ∧ Disjoint (A : Set G) B ∧
    ∃ V : OpenSubgroup G, (V : Set G) ⊆ B   := by
      have ht : y⁻¹ * x ≠ 1 := by
        by_contra! con
        have hy : y⁻¹ * y = 1 := inv_mul_cancel y
        rw [← hy] at con
        have : x = y := by
          apply mul_left_cancel at con
          exact con
        exact hxy (id (Eq.symm this))
      have : ∃ (A : Opens G) (V : OpenSubgroup G), y⁻¹ * x ∈ A ∧ 1 ∈ V ∧ Disjoint A V := by
        exact open_subgroup_separating' G (y⁻¹ * x) ht
      rcases this with ⟨A , V, ha, hv, dav⟩
      use A , V
      constructor
      · exact ha
      · constructor
        · exact hv
        · constructor
          · simp only [OpenSubgroup.coe_toOpens]
            unfold Disjoint
            intro x ha hv
            unfold Disjoint at dav
            have habot : ⊥ ≤ A := OrderBot.bot_le A
            have hvbot : ⊥ ≤ (V : Opens G) := OrderBot.bot_le ↑V
            by_contra! con
            have hx : x ≤ (A : Opens G) := by exact ha
            specialize dav habot hvbot
            -- refine Set.disjoint_iff.mpr ?h.right.right.left.a dav
            sorry
          · use V
            exact fun ⦃a⦄ a ↦ a
  rcases exv with ⟨A , B, ha, hb , dab, V, vb⟩
  -- have dva : Disjoint (V : Opens G) A   := by sorry
   -- exact Disjoint.mono vb (fun ⦃a⦄ a ↦ a) (id (Disjoint.symm dab))
  have dva' : Disjoint (V : Set G) A := by
    apply Disjoint.mono vb (fun ⦃a⦄ a ↦ a)
    refine Disjoint.symm ?_
    convert dab
  obtain ⟨u , v, ou, ov, Uuv, Uu, Uv, emptyUuv⟩
      : ∃ u v : Set G, (IsOpen u) ∧ (IsOpen v) ∧ (U ⊆ u ∪ v) ∧ ((U ∩ u).Nonempty) ∧
      ((U ∩ v).Nonempty) ∧ (¬(U ∩ (u ∩ v)).Nonempty) := by
    use (y • (V : Set G)) , (y • (V : Set G))ᶜ
    refine ⟨is_open_coset G y V, is_open_compl_coset' G y V, subset_coset_comp G y U V,
        non_empty_intersection_coset G x y U hy hxy V,
        non_empty_intersection_compl_coset' G x y U hx A ha V dva',
        intersection_of_intersection_of_complements_empty G y U V⟩
  rintro ⟨_, h2⟩
  exact emptyUuv <| ((((h2 u v ou) ov) Uuv) Uu) Uv-/


-- have dva : Disjoint (V : Opens G) A   := by sorry
   -- exact Disjoint.mono vb (fun ⦃a⦄ a ↦ a) (id (Disjoint.symm dab))

/-should be elsewhere
lemma _root_.mem_unique_to_singleton {X : Type*} {U : Set X} {x : X} (hx : x ∈ U)
    (h : ∀ y : X, y ∈ U → y = x) : U = {x} := by
  ext
  constructor <;> simp_all-/

/-theorem Set.disjoint_iff {α : Type u} {s : Set α} {t : Set α} :
Disjoint s t ↔ s ∩ t ⊆ ∅-/
