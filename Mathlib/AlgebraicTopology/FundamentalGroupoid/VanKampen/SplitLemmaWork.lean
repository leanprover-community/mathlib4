module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.ComposeMorphisms

@[expose] public section

open CategoryTheory

variable {C : Type*} [Groupoid C]

/-- Explicit split lemma for comp_list: inserting one object in the middle and splitting
    one morphism into two does not change the overall composition (up to eqToHom transport). -/
theorem comp_list_split_explicit_proof {n : ℕ} (k : Fin n)
    (objs : Fin (n + 1) → C)
    (homs : ∀ i : Fin n, objs (Fin.castSucc i) ⟶ objs (Fin.succ i))
    {mid : C} (f : objs (Fin.castSucc k) ⟶ mid) (g : mid ⟶ objs (Fin.succ k))
    (h_eq : homs k = f ≫ g)
    (objs' : Fin (n + 2) → C)
    (homs' : ∀ i : Fin (n + 1), objs' (Fin.castSucc i) ⟶ objs' (Fin.succ i))
    (h_before : ∀ (i : Fin n), i.val < k.val →
      ∃ (h1 : objs' (Fin.castSucc (Fin.castSucc i)) = objs (Fin.castSucc i))
        (h2 : objs' (Fin.succ (Fin.castSucc i)) = objs (Fin.succ i)),
      eqToHom h1.symm ≫ homs' (Fin.castSucc i) ≫ eqToHom h2 = homs i)
    (h_split1 : objs' (Fin.castSucc (Fin.castSucc k)) = objs (Fin.castSucc k))
    (h_split2 : objs' (Fin.succ (Fin.castSucc k)) = mid)
    (h_split3 : homs' (Fin.castSucc k) = eqToHom h_split1 ≫ f ≫ eqToHom h_split2.symm)
    (h_split4 : objs' (Fin.castSucc (Fin.succ k)) = mid)
    (h_split5 : objs' (Fin.succ (Fin.succ k)) = objs (Fin.succ k))
    (h_split6 : homs' (Fin.succ k) = eqToHom h_split4 ≫ g ≫ eqToHom h_split5.symm)
    (h_after : ∀ (j : Fin n), j.val > k.val →
      let i : Fin (n + 1) := Fin.succ j
      ∃ (h1 : objs' (Fin.castSucc i) = objs (Fin.castSucc j))
        (h2 : objs' (Fin.succ i) = objs (Fin.succ j)),
      eqToHom h1.symm ≫ homs' i ≫ eqToHom h2 = homs j)
    (h0 : objs' 0 = objs 0)
    (h_last : objs' (Fin.last (n + 1)) = objs (Fin.last n)) :
    eqToHom h0.symm ≫ comp_list (n + 1) objs' homs' ≫ eqToHom h_last =
    comp_list n objs homs := by
  induction n with
  | zero =>
    -- Base case n = 0: k : Fin 0 is impossible
    exfalso
    exact Fin.elim0 k
  | succ n ih =>
    -- Inductive step: n → n + 1
    by_cases h_k_lt : k.val < n
    · -- Case 1: k.val < n (split is not at last position)
      have h_k'_val : k.val < n := h_k_lt
      let k' : Fin n := ⟨k.val, h_k'_val⟩
      have h_k_eq : k = Fin.castSucc k' := by
        apply Fin.ext
        simp [k', Fin.castSucc] <;> omega
      let objs₁ : Fin (n + 1) → C := fun i : Fin (n + 1) => objs (Fin.castSucc i)
      let homs₁ : ∀ i : Fin n, objs₁ (Fin.castSucc i) ⟶ objs₁ (Fin.succ i) :=
        fun i : Fin n => homs (Fin.castSucc i)
      let objs'₁ : Fin (n + 2) → C := fun i : Fin (n + 2) => objs' (Fin.castSucc i)
      let homs'₁ : ∀ i : Fin (n + 1), objs'₁ (Fin.castSucc i) ⟶ objs'₁ (Fin.succ i) :=
        fun i : Fin (n + 1) => homs' (Fin.castSucc i)
      have h0₁ : objs'₁ 0 = objs₁ 0 := by
        simpa [objs'₁, objs₁] using h0
      have h_before₁ : ∀ (i : Fin n), i.val < k'.val →
          ∃ (h1 : objs'₁ (Fin.castSucc (Fin.castSucc i)) = objs₁ (Fin.castSucc i))
            (h2 : objs'₁ (Fin.succ (Fin.castSucc i)) = objs₁ (Fin.succ i)),
          eqToHom h1.symm ≫ homs'₁ (Fin.castSucc i) ≫ eqToHom h2 = homs₁ i := by
        intro i h_i_lt
        rcases h_before (Fin.castSucc i) (by simp [k', Fin.castSucc] <;> omega) with ⟨h1, h2, h_hom⟩
        refine' ⟨_, _, _⟩
        · simpa [objs'₁, objs₁] using h1
        · simpa [objs'₁, objs₁] using h2
        · convert h_hom <;> simp [objs'₁, objs₁, homs'₁, homs₁] <;> rfl
      have h_split1₁ : objs'₁ (Fin.castSucc (Fin.castSucc k')) = objs₁ (Fin.castSucc k') := by
        simpa [objs'₁, objs₁, h_k_eq] using h_split1
      have h_split2₁ : objs'₁ (Fin.succ (Fin.castSucc k')) = mid := by
        simpa [objs'₁, h_k_eq] using h_split2
      have h_split3₁ : homs'₁ (Fin.castSucc k') =
          eqToHom h_split1₁ ≫ f ≫ eqToHom h_split2₁.symm := by
        have h_k_cast : Fin.castSucc (Fin.castSucc k') = Fin.castSucc k := by
          exact congr_arg Fin.castSucc h_k_eq.symm
        have h : homs'₁ (Fin.castSucc k') = homs' (Fin.castSucc k) := by
          dsimp only [homs'₁]
          <;> congr
          <;> exact h_k_cast
        rw [h]
        have h1 : h_split1₁ = h_split1 := by
          exact Subsingleton.elim h_split1₁ h_split1
        have h2 : h_split2₁ = h_split2 := by
          exact Subsingleton.elim h_split2₁ h_split2
        rw [h1, h2]
        exact h_split3
      have h_split4₁ : objs'₁ (Fin.castSucc (Fin.succ k')) = mid := by
        simpa [objs'₁, h_k_eq] using h_split4
      have h_split5₁ : objs'₁ (Fin.succ (Fin.succ k')) = objs₁ (Fin.succ k') := by
        simpa [objs'₁, objs₁, h_k_eq] using h_split5
      have h_split6₁ : homs'₁ (Fin.succ k') =
          eqToHom h_split4₁ ≫ g ≫ eqToHom h_split5₁.symm := by
        have h_k_cast : Fin.succ (Fin.castSucc k') = Fin.succ k := by
          exact congr_arg Fin.succ h_k_eq.symm
        have h : homs'₁ (Fin.succ k') = homs' (Fin.succ k) := by
          dsimp only [homs'₁]
          <;> congr
          <;> exact h_k_cast
        rw [h]
        have h4 : h_split4₁ = h_split4 := by
          exact Subsingleton.elim h_split4₁ h_split4
        have h5 : h_split5₁ = h_split5 := by
          exact Subsingleton.elim h_split5₁ h_split5
        rw [h4, h5]
        exact h_split6
      have h_after₁ : ∀ (j : Fin n), j.val > k'.val →
          let i : Fin (n + 1) := Fin.succ j
          ∃ (h1 : objs'₁ (Fin.castSucc i) = objs₁ (Fin.castSucc j))
            (h2 : objs'₁ (Fin.succ i) = objs₁ (Fin.succ j)),
          eqToHom h1.symm ≫ homs'₁ i ≫ eqToHom h2 = homs₁ j := by
        intro j h_j_gt
        rcases h_after (Fin.castSucc j) (by simp [k', Fin.castSucc] <;> omega) with ⟨h1, h2, h_hom⟩
        refine' ⟨_, _, _⟩
        · simpa [objs'₁, objs₁] using h1
        · simpa [objs'₁, objs₁] using h2
        · convert h_hom <;> simp [objs'₁, objs₁, homs'₁, homs₁] <;> rfl
      have h_last₁ : objs'₁ (Fin.last (n + 1)) = objs₁ (Fin.last n) := by
        rcases h_after (Fin.last n) (by simp [k', Fin.last] <;> omega) with ⟨h1, h2, h_hom⟩
        simpa [objs'₁, objs₁] using h1
      have h_ih : eqToHom h0₁.symm ≫ comp_list (n + 1) objs'₁ homs'₁ ≫ eqToHom h_last₁ =
          comp_list n objs₁ homs₁ :=
        ih k' objs₁ homs₁ f g h_eq objs'₁ homs'₁ h_before₁ h_split1₁ h_split2₁ h_split3₁
          h_split4₁ h_split5₁ h_split6₁ h_after₁ h0₁ h_last₁
      rcases h_after (Fin.last n) (by simp [k', Fin.last] <;> omega) with ⟨h1_last, h2_last, h_hom_last⟩
      let f := comp_list (n + 1) objs'₁ homs'₁
      let g := homs' (Fin.last (n + 1))
      let f' := comp_list n objs₁ homs₁
      let g' := homs (Fin.last n)
      let hX : objs' 0 = objs 0 := h0
      let hY : objs' (Fin.castSucc (Fin.last (n + 1))) = objs₁ (Fin.last n) := h_last₁
      let hZ : objs' (Fin.succ (Fin.last (n + 1))) = objs (Fin.succ (Fin.last n)) := h_last
      have hY_eq : hY = h1_last := by
        simp [h_last₁, objs'₁, objs₁] <;> rfl
      have hZ_eq : hZ = h2_last := by
        simp [h_last, objs'₁, objs₁] <;> rfl
      have h_ih2 : eqToHom hX.symm ≫ f ≫ eqToHom hY = f' := by
        convert h_ih <;> simp [h0₁, h_last₁, objs'₁, objs₁] <;> rfl
      have h_last_hom : eqToHom hY.symm ≫ g ≫ eqToHom hZ = g' := by
        rw [hY_eq, hZ_eq]
        exact h_hom_last
      have h_comp : (eqToHom hX.symm ≫ f ≫ eqToHom hY) ≫ (eqToHom hY.symm ≫ g ≫ eqToHom hZ) =
          eqToHom hX.symm ≫ (f ≫ g) ≫ eqToHom hZ :=
        eqToHom_comp_cancel hX hY hZ f g
      have h_step : (eqToHom hX.symm ≫ f ≫ eqToHom hY) ≫ (eqToHom hY.symm ≫ g ≫ eqToHom hZ) = f' ≫ g' := by
        rw [h_ih2, h_last_hom]
        <;> rfl
      have h_main : eqToHom hX.symm ≫ (f ≫ g) ≫ eqToHom hZ = f' ≫ g' := by
        rw [←h_comp]
        exact h_step
      have h1 : comp_list (n + 2) objs' homs' = f ≫ g := by
        rw [comp_list_succ] <;> rfl
      have h2 : comp_list (n + 1) objs homs = f' ≫ g' := by
        rw [comp_list_succ] <;> rfl
      have h3 : h0 = hX := by rfl
      have h4 : h_last = hZ := by rfl
      rw [h1, h2, h3, h4]
      exact h_main
    · -- Case 2: k.val = n (split is at last position)
      have h_k_val : k.val = n := by omega
      have h_k_eq_last : k = Fin.last n := by
        apply Fin.ext
        simp [Fin.last, h_k_val] <;> omega
      subst h_k_eq_last
      let objs₁ : Fin (n + 1) → C := fun i : Fin (n + 1) => objs (Fin.castSucc i)
      let homs₁ : ∀ i : Fin n, objs₁ (Fin.castSucc i) ⟶ objs₁ (Fin.succ i) :=
        fun i : Fin n => homs (Fin.castSucc i)
      let objs'₁ : Fin (n + 2) → C := fun i : Fin (n + 2) => objs' (Fin.castSucc i)
      let homs'₁ : ∀ i : Fin (n + 1), objs'₁ (Fin.castSucc i) ⟶ objs'₁ (Fin.succ i) :=
        fun i : Fin (n + 1) => homs' (Fin.castSucc i)
      have h0₁ : objs'₁ 0 = objs₁ 0 := by
        simpa [objs'₁, objs₁] using h0
      have h_corresp₁ : ∀ (i : Fin n),
          ∃ (h1 : objs'₁ (Fin.castSucc (Fin.castSucc i)) = objs₁ (Fin.castSucc i))
            (h2 : objs'₁ (Fin.succ (Fin.castSucc i)) = objs₁ (Fin.succ i)),
          eqToHom h1.symm ≫ homs'₁ (Fin.castSucc i) ≫ eqToHom h2 = homs₁ i := by
        intro i
        have h_i_lt_k : (Fin.castSucc i).val < (Fin.last n : Fin (n + 1)).val := by
          simp [Fin.last, Fin.castSucc] <;> omega
        rcases h_before (Fin.castSucc i) h_i_lt_k with ⟨h1, h2, h_hom⟩
        refine' ⟨_, _, _⟩
        · simpa [objs'₁, objs₁] using h1
        · simpa [objs'₁, objs₁] using h2
        · convert h_hom <;> simp [objs'₁, objs₁, homs'₁, homs₁] <;> rfl
      have h_succ_last_eq_last : Fin.succ (Fin.last n) = Fin.last (n + 1) := by
        apply Fin.ext
        simp [Fin.last, Fin.succ] <;> omega
      have h_split4_eq : objs'₁ (Fin.last (n + 1)) = mid := by
        have h_eq : objs'₁ (Fin.last (n + 1)) = objs' (Fin.castSucc (Fin.succ (Fin.last n))) := by
          rw [←h_succ_last_eq_last] <;> simp [objs'₁] <;> rfl
        rw [h_eq]
        exact h_split4
      let h_f_type : objs₁ (Fin.last n) ⟶ mid := by
        simpa [objs₁] using f
      have h1' : objs'₁ (Fin.castSucc (Fin.last n)) = objs₁ (Fin.last n) := by
        have h_eq1 : objs'₁ (Fin.castSucc (Fin.last n)) = objs' (Fin.castSucc (Fin.castSucc (Fin.last n))) := by
          simp [objs'₁] <;> rfl
        have h_objs_eq : objs (Fin.castSucc (Fin.last n)) = objs₁ (Fin.last n) := by
          simp [objs₁] <;> rfl
        rw [h_eq1]
        exact Eq.trans h_split1 h_objs_eq
      have h2' : objs'₁ (Fin.succ (Fin.last n)) = mid := by
        have h_eq2 : objs'₁ (Fin.succ (Fin.last n)) = objs' (Fin.castSucc (Fin.succ (Fin.last n))) := by
          simp [objs'₁] <;> rfl
        rw [h_eq2]
        exact h_split4
      have h_eq3 : homs'₁ (Fin.last n) = homs' (Fin.castSucc (Fin.last n)) := by
        simp [homs'₁] <;> rfl
      have h_last_hom₁ :
          ∃ (h1 : objs'₁ (Fin.castSucc (Fin.last n)) = objs₁ (Fin.last n))
            (h2 : objs'₁ (Fin.succ (Fin.last n)) = mid),
          eqToHom h1.symm ≫ homs'₁ (Fin.last n) ≫ eqToHom h2 = h_f_type := by
        refine' ⟨h1', h2', _⟩
        have h_step1 : eqToHom h1'.symm ≫ homs'₁ (Fin.last n) ≫ eqToHom h2' =
            eqToHom h1'.symm ≫ homs' (Fin.castSucc (Fin.last n)) ≫ eqToHom h2' := by
          rw [h_eq3] <;> rfl
        rw [h_step1]
        have h_eq_h1 : h1' = h_split1 := Subsingleton.elim h1' h_split1
        have h_eq_h2 : h2' = h_split2 := Subsingleton.elim h2' h_split2
        rw [h_eq_h1, h_eq_h2, h_split3]
        have h_dom_eq : objs (Fin.castSucc (Fin.last n)) = objs₁ (Fin.last n) := by
          simp [objs₁] <;> rfl
        have h_main : eqToHom h_split1.symm ≫ (eqToHom h_split1 ≫ f ≫ eqToHom h_split2.symm) ≫ eqToHom h_split2 = h_f_type := by
          have h1 : eqToHom h_split1.symm ≫ eqToHom h_split1 = 𝟙 _ := by
            rw [eqToHom_trans, eqToHom_refl] <;> simp
          have h2 : eqToHom h_split2.symm ≫ eqToHom h_split2 = 𝟙 _ := by
            rw [eqToHom_trans, eqToHom_refl] <;> simp
          have h3 : eqToHom h_split1.symm ≫ (eqToHom h_split1 ≫ f ≫ eqToHom h_split2.symm) ≫ eqToHom h_split2 =
              (eqToHom h_split1.symm ≫ eqToHom h_split1) ≫ f ≫ (eqToHom h_split2.symm ≫ eqToHom h_split2) := by
            simp [Category.assoc] <;> rfl
          rw [h3, h1, h2]
          have h4 : 𝟙 _ ≫ f ≫ 𝟙 _ = h_f_type := by
            simp [Category.comp_id, Category.id_comp]
            <;> dsimp only [h_f_type]
            <;> rfl
          exact h4
        exact h_main
      let f_snoc := comp_list (n + 1) objs'₁ homs'₁
      let g_snoc := homs' (Fin.last (n + 1))
      let f'_snoc := comp_list n objs₁ homs₁
      let g'_snoc : objs₁ (Fin.last n) ⟶ mid := h_f_type
      let hX_snoc : objs' 0 = objs 0 := h0
      let hY_snoc : objs'₁ (Fin.last (n + 1)) = mid := h_split4_eq
      let hZ_snoc : objs' (Fin.succ (Fin.last (n + 1))) = objs (Fin.succ (Fin.last n)) := by
        have h_last' : objs' (Fin.succ (Fin.last (n + 1))) = objs (Fin.last (n + 1)) := by
          simpa using h_last
        have h_objs_eq : objs (Fin.last (n + 1)) = objs (Fin.succ (Fin.last n)) := by
          have h_eq : Fin.last (n + 1) = Fin.succ (Fin.last n) := by
            apply Fin.ext
            simp [Fin.last, Fin.succ] <;> omega
          rw [h_eq]
        rw [h_last', h_objs_eq]
      have h_snoc : eqToHom h0₁.symm ≫ f_snoc ≫ eqToHom h_split4_eq =
          f'_snoc ≫ g'_snoc :=
        comp_list_snoc objs₁ homs₁ objs'₁ homs'₁ h0₁ h_corresp₁ h_split4_eq g'_snoc h_last_hom₁
      have h_ih2 : eqToHom hX_snoc.symm ≫ f_snoc ≫ eqToHom hY_snoc = f'_snoc ≫ g'_snoc := by
        convert h_snoc <;> simp [h0₁, h_split4_eq, objs'₁, objs₁] <;> rfl
      have h_last_hom : eqToHom hY_snoc.symm ≫ g_snoc ≫ eqToHom hZ_snoc = g := by
        have h3 : (Fin.last (n + 1) : Fin (n + 2)) = Fin.succ (Fin.last n) := by
          apply Fin.ext
          simp [Fin.last, Fin.succ] <;> omega
        have h2 : g_snoc = homs' (Fin.succ (Fin.last n)) := by
          have h4 : g_snoc = homs' (Fin.last (n + 1)) := by rfl
          rw [h4]
          <;> congr
          <;> exact h3
        have h_eq_hY : hY_snoc = h_split4 := by
          exact Subsingleton.elim hY_snoc h_split4
        have h_eq_hZ : hZ_snoc = h_split5 := by
          exact Subsingleton.elim hZ_snoc h_split5
        rw [h2, h_eq_hY, h_eq_hZ]
        have h_goal : eqToHom h_split4.symm ≫ (eqToHom h_split4 ≫ g ≫ eqToHom h_split5.symm) ≫ eqToHom h_split5 = g := by
          simp [Category.assoc, eqToHom_refl, Category.comp_id, Category.id_comp]
          <;> rfl
        rw [h_split6]
        exact h_goal
      have h_comp : (eqToHom hX_snoc.symm ≫ f_snoc ≫ eqToHom hY_snoc) ≫ (eqToHom hY_snoc.symm ≫ g_snoc ≫ eqToHom hZ_snoc) =
          eqToHom hX_snoc.symm ≫ (f_snoc ≫ g_snoc) ≫ eqToHom hZ_snoc :=
        eqToHom_comp_cancel hX_snoc hY_snoc hZ_snoc f_snoc g_snoc
      have h_step : (eqToHom hX_snoc.symm ≫ f_snoc ≫ eqToHom hY_snoc) ≫ (eqToHom hY_snoc.symm ≫ g_snoc ≫ eqToHom hZ_snoc) =
          (f'_snoc ≫ g'_snoc) ≫ g := by
        have h1 : (eqToHom hX_snoc.symm ≫ f_snoc ≫ eqToHom hY_snoc) = f'_snoc ≫ g'_snoc := h_ih2
        have h2 : (eqToHom hY_snoc.symm ≫ g_snoc ≫ eqToHom hZ_snoc) = g := h_last_hom
        rw [h1, h2]
        <;> rfl
      have h_main : eqToHom hX_snoc.symm ≫ (f_snoc ≫ g_snoc) ≫ eqToHom hZ_snoc = (f'_snoc ≫ g'_snoc) ≫ g := by
        rw [←h_comp]
        exact h_step
      have h1 : comp_list (n + 2) objs' homs' = f_snoc ≫ g_snoc := by
        rw [comp_list_succ] <;> rfl
      have h2 : comp_list (n + 1) objs homs = (f'_snoc ≫ g'_snoc) ≫ g := by
        have h5 : comp_list (n + 1) objs homs = comp_list n objs₁ homs₁ ≫ homs (Fin.last n) := by
          rw [comp_list_succ] <;> rfl
        rw [h5, h_eq]
        have h_assoc : comp_list n objs₁ homs₁ ≫ (f ≫ g) = (comp_list n objs₁ homs₁ ≫ f) ≫ g := by
          rw [Category.assoc]
        rw [h_assoc]
        have h6 : comp_list n objs₁ homs₁ ≫ f = comp_list n objs₁ homs₁ ≫ h_f_type := by
          rfl
        rw [h6]
        <;> rfl
      have h3 : h0 = hX_snoc := by rfl
      have h4 : h_last = hZ_snoc := by
        exact Subsingleton.elim h_last hZ_snoc
      rw [h1, h2, h3, h4]
      exact h_main

end
