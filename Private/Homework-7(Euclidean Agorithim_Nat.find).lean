import Mathlib.Tactic



section Example_2205B

open Classical
#check Nat.find

/-
Each subgroup of a cyclic group is cyclic.
-/
example {G : Type*} [Group G] {H: Subgroup G} (h: IsCyclic G): IsCyclic H := by
  --We suppose $g$ is the generator element of $G$
  rcases h with ⟨g, hg⟩
  by_cases hx : ∃ x : G, x ∈ H ∧ x ≠ (1 : G)
  · --If $H$ is nontrivial
    rcases hx with ⟨x, hx₁, hx₂⟩
    -- then choose a $x\neq 1$ which $x \in H$ and suppose $x = g ^ k$
    rcases hg x with ⟨k, hk⟩
    dsimp at hk
    --We define $P = \{n \in \mathbb N | 0 < n , g ^ n ∈ H \}$
    have hex : ∃ n : ℕ, 0 < n ∧ g ^ n ∈ H := by
      -- then $P$ is nonempty as $|k| \in P$
      use k.natAbs
      constructor
      · --because $|k| > 0$
        have : k ≠ 0 := by
          by_contra nh
          have : x = 1 := by simp only [← hk, nh, zpow_zero]
          contradiction
        exact Int.natAbs_pos.mpr this
      · have : k.natAbs = k ∨ k.natAbs = - k := Int.natAbs_eq_natAbs_iff.mp rfl
        rcases this with pos | neg
        · --$|k|$ is $k$ when $k > 0$
          rw [Eq.symm (zpow_natCast g k.natAbs), pos, hk]
          exact hx₁
        · --and is $-k$ when $k < 0$
          simp only [Eq.symm (zpow_natCast g k.natAbs), neg, zpow_neg, hk, inv_mem_iff]
          exact hx₁
          --hence $g ^ {|k|} \in H$.
    --We can choose the minimite element in $H$ according to Zorn Lemma,we suppose it is $m$
    let m := Nat.find hex
    --,$g ^ m \in H$ .
    let hm := (Nat.find_spec hex)
    have : g ^ (m : ℤ) = g ^ m := by simp only [zpow_natCast]
    have : g ^ (m : ℤ) ∈ H := by rw [this]; exact hm.2
    --We will show $g ^ {m}$ is a generator of $H$.
    use ⟨g ^ (m : ℤ), this⟩
    ----$\forall x \in H$,
    intro x
    ----we suppose $x = g ^ k$
    rcases hg x with ⟨k, hk⟩
    dsimp at hk
    --and $q = \lfloor k/m \rfloor$
    let q := (k / m : ℤ)
    --, $k \equiv r (mod m)$ .
    let r := (k % m : ℤ)
    --Then it is obvious that $k = q \cdot m + r$
    have xeq : g ^ r * g ^ ((m : ℤ) * q) = x := by calc
      _ = g ^ (r + ((m : ℤ) * q)) := Eq.symm (zpow_add g r (↑m * q))
      _ = _ := by rw [Int.emod_add_ediv k ↑m ,hk]
    --We have $g ^ q \cdot m = (g ^ m) ^ q \in H$
    have gr_in_H : g ^ r ∈ H := by
      -- because $g ^ m \in H$,
      have h1 : g ^ ((m : ℤ) * q) ∈ H := by
        rw [zpow_mul]; apply Subgroup.zpow_mem H _ q
        rw [zpow_natCast g m]; exact hm.2
      --then $g ^ r \in H$.Thus
      have h2: g ^ r * g ^ ((m : ℤ) * q) ∈ H := by
        rw [xeq]; exact SetLike.coe_mem x
      apply (Subgroup.mul_mem_cancel_right H h1).1 h2
    have r_pos: r = r.natAbs := by
      rw [Int.natAbs_of_nonneg]
      exact Int.emod_nonneg k (Int.natCast_ne_zero_iff_pos.mpr hm.1)
    --, we have $g ^ {|r|} \in H$ and $|r| < m$
    --Because m is the minimite element in $P$,hence $|r| \notin P$ ,which leads to $|r|=0$ i.e. $r = 0$
    have r_zero: r = 0 := by
      have : r.natAbs = 0 := by
        by_contra nr
        have r_hex: 0 < r.natAbs ∧ g ^ r.natAbs ∈ H := by
          constructor
          · exact Nat.zero_lt_of_ne_zero nr
          · rw [← (zpow_natCast g r.natAbs), ← r_pos]
            exact gr_in_H
        have r_ge_m : r.natAbs ≥ m := Nat.find_min' hex r_hex
        have : (r.natAbs : ℤ) < m := by
          calc
            _ = (r:ℤ) := by rw [← r_pos]
            _ = k % (m : ℤ) := rfl
            _ < (m : ℤ) := by
              apply Int.emod_lt_of_pos
              apply Int.ofNat_pos.mpr hm.1
            _ = _ := rfl
        have r_lt_m: r.natAbs < m := Int.ofNat_lt.mp this
        linarith
      exact Int.natAbs_eq_zero.mp this
    -- and we have $x = g ^ k=(g ^ m)^q \in H$
    simp only [r_zero, zpow_zero, one_mul] at xeq
    use (q : ℤ)
    apply Subtype.ext_iff_val.2
    rw [← xeq]
    exact Eq.symm (zpow_mul g (↑m) q)
    -- and so we have proved $H$ is a cyclic group
  · --It is trivial when $H$ is trivial
    have : H = (⊥ : Subgroup G) := by
      push_neg at hx
      exact (Subgroup.eq_bot_iff_forall H).mpr hx
    rw [this]
    exact Bot.isCyclic




#check Subgroup.isCyclic

example {G : Type*} [Group G] {H: Subgroup G} (h: IsCyclic G): IsCyclic H := by
  exact Subgroup.isCyclic H

--The Solution in Mathlib
@[to_additive]
instance Subgroup.isCyclic_This_Problem {α : Type u} [Group α] [IsCyclic α] (H : Subgroup α) : IsCyclic H :=
  haveI := Classical.propDecidable
  let ⟨g, hg⟩ := IsCyclic.exists_generator (α := α)
  if hx : ∃ x : α, x ∈ H ∧ x ≠ (1 : α) then
    let ⟨x, hx₁, hx₂⟩ := hx
    let ⟨k, hk⟩ := hg x
    have hk : g ^ k = x := hk
    have hex : ∃ n : ℕ, 0 < n ∧ g ^ n ∈ H :=
      ⟨k.natAbs,
        Nat.pos_of_ne_zero fun h => hx₂ <| by
          rw [← hk, Int.natAbs_eq_zero.mp h, zpow_zero], by
            cases' k with k k
            · rw [Int.ofNat_eq_coe, Int.natAbs_cast k, ← zpow_natCast, ← Int.ofNat_eq_coe, hk]
              exact hx₁
            · rw [Int.natAbs_negSucc, ← Subgroup.inv_mem_iff H]; simp_all⟩
    ⟨⟨⟨g ^ Nat.find hex, (Nat.find_spec hex).2⟩, fun ⟨x, hx⟩ =>
        let ⟨k, hk⟩ := hg x
        have hk : g ^ k = x := hk
        have hk₂ : g ^ ((Nat.find hex : ℤ) * (k / Nat.find hex : ℤ)) ∈ H := by
          rw [zpow_mul]
          apply H.zpow_mem
          exact mod_cast (Nat.find_spec hex).2
        have hk₃ : g ^ (k % Nat.find hex : ℤ) ∈ H :=
          (Subgroup.mul_mem_cancel_right H hk₂).1 <| by
            rw [← zpow_add, Int.emod_add_ediv, hk]; exact hx
        have hk₄ : k % Nat.find hex = (k % Nat.find hex).natAbs := by
          rw [Int.natAbs_of_nonneg
              (Int.emod_nonneg _ (Int.natCast_ne_zero_iff_pos.2 (Nat.find_spec hex).1))]
        have hk₅ : g ^ (k % Nat.find hex).natAbs ∈ H := by rwa [← zpow_natCast, ← hk₄]
        have hk₆ : (k % (Nat.find hex : ℤ)).natAbs = 0 :=
          by_contra fun h =>
            Nat.find_min hex
              (Int.ofNat_lt.1 <| by
                rw [← hk₄]; exact Int.emod_lt_of_pos _ (Int.natCast_pos.2 (Nat.find_spec hex).1))
              ⟨Nat.pos_of_ne_zero h, hk₅⟩
        ⟨k / (Nat.find hex : ℤ),
          Subtype.ext_iff_val.2
            (by
              suffices g ^ ((Nat.find hex : ℤ) * (k / Nat.find hex : ℤ)) = x by simpa [zpow_mul]
              rw [Int.mul_ediv_cancel'
                  (Int.dvd_of_emod_eq_zero (Int.natAbs_eq_zero.mp hk₆)),
                hk])⟩⟩⟩
  else by
    have : H = (⊥ : Subgroup α) :=
      Subgroup.ext fun x =>
        ⟨fun h => by simp at *; tauto, fun h => by rw [Subgroup.mem_bot.1 h]; exact H.one_mem⟩
    subst this; infer_instance

end Example_2205B
