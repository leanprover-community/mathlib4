import Mathlib.Tactic.Tendsto.Multiseries.Operations.Add

set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace TendstoTactic

namespace PreMS


/-- Collect leading terms from the list of terms. -/
noncomputable def leadingTerms {basis : Basis} (terms : List (ℝ × PreMS basis)) (shift : ℕ := 0) :
    Option (ℝ × List (PreMS basis × ℕ)) :=
  match terms with
  | [] => .none
  | (hd_deg, hd_coef) :: tl =>
    let pre := leadingTerms tl (shift := shift + 1)
    match pre with
    | none => (hd_deg, [(hd_coef, shift)])
    | some (maxDeg, ans) =>
      if maxDeg < hd_deg then
        (hd_deg, [(hd_coef, shift)])
      else if maxDeg = hd_deg then
        (hd_deg, (hd_coef, shift) :: ans)
      else
        (maxDeg, ans)

-- TODO: rename?
/-- Given CoList of PreMS (which are also CoLists), merge them into single PreMS while maintaining
the correct order. At the step `n` it considers only first `n` elements of `s`. -/
noncomputable def merge1 {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (s : CoList (PreMS (basis_hd :: basis_tl))) : PreMS (basis_hd :: basis_tl) :=
  let T := ℕ × CoList (PreMS (basis_hd :: basis_tl))
  let g : T → CoList.OutType (ℝ × PreMS basis_tl) T := fun (k, li) =>
    let heads : List (ℝ × PreMS basis_tl) :=
      let t := li.take k
      t.filterMap (·.head)
    -- for safe `List.head` below
    -- have heads_nonempty : ∀ shift deg terms, leadingTerms heads (shift := shift) = .some (deg, terms) → terms ≠ [] := by
    --   induction heads with
    --   | nil =>
    --     intro shift deg terms h
    --     simp [leadingTerms] at h
    --   | cons heads_hd heads_tl ih =>
    --     intro shift deg terms h
    --     simp [leadingTerms] at h
    --     specialize ih (shift + 1)
    --     generalize leadingTerms heads_tl (shift + 1) = s at *
    --     cases s with
    --     | none =>
    --       simp at h
    --       simp [← h.right]
    --     | some v =>
    --       obtain ⟨tl_deg, tl_terms⟩ := v
    --       simp at h
    --       split_ifs at h
    --       · simp at h
    --         simp [← h.right]
    --       · simp at h
    --         simp [← h.right]
    --       · simp at h
    --         apply ih
    --         rw [h.right]
    match leadingTerms heads with
    | .none => .nil
    | .some (deg, terms) =>
      let coef := terms.tail.foldl (init := (terms.head!).1) fun acc (curCoef, _) =>
        add acc curCoef
      let next : CoList (PreMS (basis_hd :: basis_tl)) := terms.foldl (init := li) fun acc (_, idx) =>
        acc.modify idx (·.tail)
      .cons (deg, coef) (k + 1, next)
  CoList.corec g (1, s)

--theorems

@[simp]
theorem merge1_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    merge1 (basis_hd := basis_hd) (basis_tl := basis_tl) .nil = .nil := by
  simp [merge1]
  rw [CoList.corec_nil]
  simp [leadingTerms]

theorem megre1_cons_head_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {s_tl : CoList (PreMS (basis_hd :: basis_tl))} :
    merge1 (.cons .nil s_tl) = .nil := by
  simp [merge1]
  rw [CoList.corec_nil]
  simp [leadingTerms]

theorem merge1_cons_head_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {deg : ℝ}
    {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
    {s_tl : CoList (PreMS (basis_hd :: basis_tl))} :
    merge1 (.cons (.cons (deg, coef) tl) s_tl) = .cons (deg, coef) (tl.add (merge1 s_tl)) := by
  sorry

-- add here the assumption that `s.map head` is sorted
theorem merge1_cons_eq_add {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {s_hd : PreMS (basis_hd :: basis_tl)} {s_tl : CoList (PreMS (basis_hd :: basis_tl))} :
    merge1 (.cons s_hd s_tl) = add s_hd (merge1 s_tl) := by
  sorry

end PreMS

end TendstoTactic
