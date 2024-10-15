import Mathlib.Tactic.Tendsto.Multiseries.Operations.Add

set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace TendstoTactic

namespace PreMS

noncomputable def maxExp {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (li : List (PreMS (basis_hd :: basis_tl))) : WithBot ℝ :=
  (li.map leadingExp).maximum.bind (·)

noncomputable def merge_aux_coef {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (firsts : List (PreMS (basis_hd :: basis_tl))) (deg : ℝ) : PreMS basis_tl :=
  firsts.foldl (init := zero _) fun curCoef elem =>
    elem.casesOn'
    (nil := curCoef)
    (cons := fun (deg', coef) tl =>
      if deg' == deg then
        curCoef.add coef
      else
        curCoef
    )

noncomputable def merge_aux_liNew {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (firsts : List (PreMS (basis_hd :: basis_tl))) (deg : ℝ)
    (li : CoList (PreMS (basis_hd :: basis_tl))) : CoList (PreMS (basis_hd :: basis_tl)) :=
  firsts.foldlIdx (init := li) fun idx curLi elem =>
    elem.casesOn'
    (nil := curLi)
    (cons := fun (deg', coef) tl =>
      if deg' == deg then
        curLi.set idx tl
      else
        curLi
    )

noncomputable def merge_aux_kNew {basis_hd : ℝ → ℝ} {basis_tl : Basis} (deg : ℝ) (k : ℕ)
    (li : CoList (PreMS (basis_hd :: basis_tl))) : ℕ :=
  match li.get k with
  | none => k
  | some ms =>
    if ms.leadingExp = deg then
      k + 1
    else
      k

noncomputable def merge_aux {basis_hd : ℝ → ℝ} {basis_tl : Basis} : (ℕ × CoList (PreMS (basis_hd :: basis_tl))) →
    CoList.OutType (ℝ × PreMS basis_tl) (ℕ × CoList (PreMS (basis_hd :: basis_tl))) :=
  fun (k, li) =>
  let firsts := li.take (k + 1)
  let deg? : WithBot ℝ := maxExp firsts
  match deg? with
  | ⊥ => .nil
  | .some deg =>
    let coef : PreMS basis_tl := merge_aux_coef firsts deg
    let liNew : CoList (PreMS (basis_hd :: basis_tl)) := merge_aux_liNew firsts deg li
    let kNew : ℕ := merge_aux_kNew deg k li
    .cons (deg, coef) (kNew, liNew)

noncomputable def merge {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (n : ℕ) (s : CoList (PreMS (basis_hd :: basis_tl))) : PreMS (basis_hd :: basis_tl) :=
  CoList.corec merge_aux (n, s)

-- TODO: rename?
/-- Given CoList `s` of PreMS (which are also CoLists), merge them into single PreMS while maintaining
the correct order. At the step `n` it considers only first `n` elements of `s`. -/
noncomputable def merge1 {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (s : CoList (PreMS (basis_hd :: basis_tl))) : PreMS (basis_hd :: basis_tl) :=
  merge 0 s

--theorems

-- План на среду
-- 1. Корекурсивно определить Sorted.
--   Возможно ввести порядок на PreMS, а Sorted определить для всех колистов
--   wellOrdered тоже можно переписать используя Sorted
-- 2. ?
-- 3. Доказать все теоремы в этом файле
-- 4. После этого починить mul (доказать что там Sorted)
-- 5. И powser

@[simp]
theorem maxExp_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    maxExp (basis_hd := basis_hd) (basis_tl := basis_tl) [] = ⊥ := by
  simp [maxExp]
  rfl

@[simp]
theorem maxExp_cons_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {tl : List (PreMS (basis_hd :: basis_tl))} :
    maxExp (.nil :: tl) = maxExp tl := by
  simp [maxExp]
  conv => arg 1; arg 1; arg 1; arg 1; simp [leadingExp]
  rw [List.maximum_cons]
  generalize (List.map leadingExp tl).maximum = m
  cases m with
  | bot => simp [Option.bind]; rfl
  | coe m' => simp

@[simp]
theorem maxExp_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {hd : PreMS (basis_hd :: basis_tl)}
    {tl : List (PreMS (basis_hd :: basis_tl))} : maxExp (hd :: tl) = hd.leadingExp ⊔ maxExp tl := by
  simp [maxExp]
  rw [List.maximum_cons]
  generalize (List.map leadingExp tl).maximum = m
  cases m <;> simp [Option.bind]


-- @[simp]
-- theorem maxExp_cons_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {deg : ℝ} {coef : PreMS basis_tl}
--     {tl : PreMS (basis_hd :: basis_tl)} {li_tl : List (PreMS (basis_hd :: basis_tl))} :
--     maxExp ((.cons (deg, coef) tl) :: li_tl) = ↑deg ⊔ maxExp li_tl := by
--   simp [maxExp]
--   conv => arg 1; arg 1; arg 1; arg 1; simp [leadingExp]
--   rw [List.maximum_cons]
--   generalize (List.map leadingExp li_tl).maximum = m
--   cases m <;> simp [Option.bind]

theorem maxExp_ge {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {li : List (PreMS (basis_hd :: basis_tl))}
    {x : PreMS (basis_hd :: basis_tl)} (hx : x ∈ li) :
    x.leadingExp ≤ maxExp li := by
  simp [maxExp]
  have := List.le_maximum_of_mem' (List.mem_map_of_mem leadingExp hx)
  generalize (List.map leadingExp li).maximum = a at this
  cases a <;> simpa [Option.bind]

-- Ugly
theorem maxExp_eq_bot_iff {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {li : List (PreMS (basis_hd :: basis_tl))} :
    maxExp li = ⊥ ↔ ∀ x ∈ li, x = .nil := by
  constructor
  · intro h x
    apply x.casesOn
    · simp
    · intro (deg, coef) tl hx
      simp [maxExp] at h
      have := List.mem_map_of_mem leadingExp hx
      simp only [leadingExp, CoList.casesOn_cons] at this
      have := List.le_maximum_of_mem' this
      generalize (List.map leadingExp li).maximum = t at *
      cases ht : t with
      | bot => simp [ht] at this
      | coe x =>
        simp [ht, Option.bind] at h
        rw [h] at ht
        rw [ht] at this
        simp at this
  · intro h
    simp [maxExp]
    by_cases h_mem : .nil ∈ li
    · have := List.maximum_eq_coe_iff.mpr ⟨List.mem_map_of_mem leadingExp h_mem, by
        simp [List.forall_mem_map]
        intro a ha
        specialize h a ha
        simp [h]
      ⟩
      conv at this =>
        arg 2; simp [leadingExp]
      rw [this]
      simp [Option.bind]
    · have : li = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro x hx
        specialize h x hx
        rw [h] at hx
        exact h_mem hx
      rw [this]
      simp [Option.bind]
      rfl

noncomputable def merge' {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (n : ℕ) (s : CoList (PreMS (basis_hd :: basis_tl))) : PreMS (basis_hd :: basis_tl) :=
  let firsts := s.take (n + 1)
  let deg? : WithBot ℝ := maxExp firsts
  match deg? with
  | ⊥ => .nil
  | .some deg =>
    let coef : PreMS basis_tl := merge_aux_coef firsts deg
    let liNew : CoList (PreMS (basis_hd :: basis_tl)) := merge_aux_liNew firsts deg s
    let kNew : ℕ := merge_aux_kNew deg n s
    .cons (deg, coef) (merge kNew liNew)

theorem merge_unfold {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {n : ℕ} {s : CoList (PreMS (basis_hd :: basis_tl))} :
    merge n s = merge' n s := by
  simp [merge']
  conv => lhs; unfold merge merge_aux
  simp
  cases h : maxExp (CoList.take (n + 1) s) with
  | bot =>
    simp
    rw [CoList.corec_nil]
    simp [h]
  | coe =>
    simp
    rw [CoList.corec_cons]
    swap
    · simp [h]
      constructor <;> rfl
    unfold merge merge_aux
    simp

scoped instance {basis_hd : ℝ → ℝ} {basis_tl : Basis} : Preorder (PreMS (basis_hd :: basis_tl)) where
  le := fun x y ↦ x.leadingExp ≤ y.leadingExp
  le_refl := by simp
  le_trans := by
    simp
    intro x y z hxy hyz
    apply le_trans hxy hyz

theorem lt_iff_lt {basis_hd : ℝ → ℝ} {basis_tl : Basis} {x y : PreMS (basis_hd :: basis_tl)} :
    (x < y) ↔ (x.leadingExp < y.leadingExp) := by
  constructor
  · intro h
    rw [lt_iff_le_not_le] at h ⊢
    exact h
  · intro h
    rw [lt_iff_le_not_le] at h ⊢
    exact h

theorem eq_nil_of_le_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {x : PreMS (basis_hd :: basis_tl)}
    (h : x ≤ .nil) : x = .nil := by
  revert h
  apply x.casesOn
  · simp
  · intro hd tl h
    simp [LE.le, leadingExp] at h

theorem tail_eq_nil_of_nil_head {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {tl : CoList (PreMS (basis_hd :: basis_tl))}
    (h_sorted : (CoList.cons .nil tl).Sorted (· > ·)) : tl = .nil := by
  revert h_sorted
  apply tl.casesOn
  · simp
  · intro hd tl h_sorted
    replace h_sorted := (CoList.Sorted_cons h_sorted).left
    simp [LT.lt, leadingExp] at h_sorted

theorem all_eq_nil_of_head_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {tl : CoList (PreMS (basis_hd :: basis_tl))}
    (h_sorted : (CoList.cons .nil tl).Sorted (· ≥ ·)) : tl.all (· = .nil) := by
  suffices h : (CoList.cons .nil tl).all (· = .nil) by
    simpa using h
  let motive : CoList (PreMS (basis_hd :: basis_tl)) → Prop := fun x =>
    x.Sorted (· ≥ ·) ∧ (x = .nil ∨ ∃ tl, x = .cons .nil tl)
  apply CoList.all.coind motive
  · intro hd tl ih
    simp [motive] at ih
    obtain ⟨h_sorted, h_hd⟩ := ih
    apply CoList.Sorted_cons at h_sorted
    constructor
    · exact h_hd
    simp only [motive]
    constructor
    · exact h_sorted.right
    · revert h_sorted
      apply tl.casesOn
      · simp
      · intro tl_hd tl_tl h_sorted
        simp at h_sorted ⊢
        rw [h_hd] at h_sorted
        apply eq_nil_of_le_nil h_sorted.left
  · simp only [motive]
    constructor
    · exact h_sorted
    · right
      use ?_
      congr
      exact Eq.refl _

@[simp]
theorem merge_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {n : ℕ} :
    merge n (basis_hd := basis_hd) (basis_tl := basis_tl) .nil = .nil := by
  simp [merge, merge_aux]

@[simp]
theorem merge1_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    merge1 (basis_hd := basis_hd) (basis_tl := basis_tl) .nil = .nil := by
  simp [merge1]

@[simp]
theorem merge1_cons_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {hd : PreMS (basis_hd :: basis_tl)} :
    merge1 (basis_hd := basis_hd) (basis_tl := basis_tl) (.cons hd .nil) = hd := by
  let motive : PreMS (basis_hd :: basis_tl) → PreMS (basis_hd :: basis_tl) → Prop := fun x y =>
    ∃ m, x = merge m (.cons y .nil)
  apply CoList.Eq.coind motive
  · intro x y ih
    simp only [motive] at ih
    obtain ⟨m, ih⟩ := ih
    subst ih
    apply y.casesOn
    · right
      simp
      rw [merge]
      unfold merge_aux
      simp
    · intro (deg, coef) tl
      left
      use (deg, coef), ?_, ?_
      constructor
      · rw [merge_unfold, merge']
        simp [merge_aux_coef, merge_aux_kNew, merge_aux_liNew]
        exact Eq.refl _
      constructor
      · exact Eq.refl _
      simp only [motive]
      use ?_
      congr
      exact Eq.refl _
  · simp only [motive, merge1]
    use 0

@[simp]
theorem megre1_cons_head_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {s_tl : CoList (PreMS (basis_hd :: basis_tl))} :
    merge1 (.cons .nil s_tl) = .nil := by
  simp [merge1, merge]
  rw [CoList.corec_nil]
  simp [merge_aux, leadingExp]

@[simp]
theorem merge_aux_kNew_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {deg : ℝ} {m : ℕ}
    {s_hd : PreMS (basis_hd :: basis_tl)} {s_tl : CoList (PreMS (basis_hd :: basis_tl))} :
    merge_aux_kNew deg (m + 1) (CoList.cons s_hd s_tl) = merge_aux_kNew deg m s_tl + 1 := by
  simp [merge_aux_kNew]
  cases (CoList.tail^[m] s_tl).head
  · simp
  · simp; split_ifs <;> rfl

theorem merge_aux_kNew_eq_or_succ {basis_hd : ℝ → ℝ} {basis_tl : Basis} {deg : ℝ} {m : ℕ}
    {s : CoList (PreMS (basis_hd :: basis_tl))} : merge_aux_kNew deg m s = m ∨ merge_aux_kNew deg m s = m + 1 := by
  simp only [merge_aux_kNew]
  cases CoList.get m s with
  | none => simp
  | some =>
    simp
    symm
    apply em

theorem merge_aux_coef_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {hd_deg deg : ℝ}
    {hd_coef : PreMS basis_tl} {hd_tl : PreMS (basis_hd :: basis_tl)}
    {firsts_tl : List (PreMS (basis_hd :: basis_tl))} :
    merge_aux_coef (CoList.cons (hd_deg, hd_coef) hd_tl :: firsts_tl) deg =
    if hd_deg = deg then
      hd_coef.add (merge_aux_coef firsts_tl deg)
    else
     merge_aux_coef firsts_tl deg := by
  simp [merge_aux_coef]
  split_ifs
  · conv => lhs; rw [show hd_coef = hd_coef.add (zero _) by simp]
    generalize zero basis_tl = init
    induction firsts_tl generalizing init with
    | nil => simp
    | cons firsts_tl_hd firsts_tl_tl ih =>
      simp [add_assoc']
      apply firsts_tl_hd.casesOn
      · simp
        apply ih
      · intro (firsts_tl_hd_deg, firsts_tl_hd_coef) firsts_tl_hd_tl
        simp only [CoList.casesOn_cons]
        split_ifs
        · apply ih
        · apply ih
  · simp

theorem merge_aux_liNew_aux {basis_hd : ℝ → ℝ} {basis_tl : Basis} {deg : ℝ}
    {s_hd : PreMS (basis_hd :: basis_tl)} {s_tl : CoList (PreMS (basis_hd :: basis_tl))}
    {firsts : List (PreMS (basis_hd :: basis_tl))} :
    List.foldlIdx
    (fun idx curLi elem ↦ CoList.casesOn' elem curLi fun x tl ↦ if x.1 = deg then CoList.set idx curLi tl else curLi)
    (CoList.cons s_hd s_tl) firsts 1 =
    .cons s_hd (List.foldlIdx
    (fun idx curLi elem ↦ CoList.casesOn' elem curLi fun x tl ↦ if x.1 = deg then CoList.set idx curLi tl else curLi)
    s_tl firsts 0) := by
  generalize h_offset : 0 = offset
  rw [show 1 = offset + 1 by simp [h_offset]]
  clear h_offset
  induction firsts generalizing offset s_tl with
  | nil => simp
  | cons firsts_hd firsts_tl ih =>
    simp
    apply firsts_hd.casesOn
    · simp
      apply ih
    · intro (firsts_hd_deg, firsts_hd_coef) firsts_hd_tl
      simp
      split_ifs
      · apply ih
      · apply ih

theorem merge_aux_liNew_cons_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {s_hd_deg deg : ℝ}
    {s_hd_coef : PreMS basis_tl} {s_hd_tl : PreMS (basis_hd :: basis_tl)}
    {s_tl : CoList (PreMS (basis_hd :: basis_tl))}
    {firsts_tl : List (PreMS (basis_hd :: basis_tl))}:
    merge_aux_liNew (CoList.cons (s_hd_deg, s_hd_coef) s_hd_tl :: firsts_tl) deg
      (CoList.cons (CoList.cons (s_hd_deg, s_hd_coef) s_hd_tl) s_tl) =
    if s_hd_deg = deg then
      .cons s_hd_tl (merge_aux_liNew firsts_tl deg s_tl)
    else
      .cons (CoList.cons (s_hd_deg, s_hd_coef) s_hd_tl) (merge_aux_liNew firsts_tl deg s_tl) := by
  simp [merge_aux_liNew]
  split_ifs
  · rw [merge_aux_liNew_aux]
  · rw [merge_aux_liNew_aux]

theorem merge_aux_liNew_cons_stable {basis_hd : ℝ → ℝ} {basis_tl : Basis} {deg : ℝ}
    {hd : PreMS (basis_hd :: basis_tl)} (h_deg : hd.leadingExp < deg)
    {firsts_tl : List (PreMS (basis_hd :: basis_tl))} {s_tl : CoList (PreMS (basis_hd :: basis_tl))} :
    merge_aux_liNew (hd :: firsts_tl) deg (.cons hd s_tl) = .cons hd (merge_aux_liNew firsts_tl deg s_tl) := by
  revert h_deg
  apply hd.casesOn
  · intro h_deg
    simp [merge_aux_liNew]
    rw [merge_aux_liNew_aux]
  · intro (hd_deg, hd_coef) hd_tl h_deg
    simp [leadingExp] at h_deg
    rw [merge_aux_liNew_cons_cons]
    split_ifs with h
    · exfalso
      linarith
    · rfl

@[simp]
theorem merge_aux_liNew_cons_nil_stable {basis_hd : ℝ → ℝ} {basis_tl : Basis} {deg : ℝ}
    {tl : List (PreMS (basis_hd :: basis_tl))} {s_tl : CoList (PreMS (basis_hd :: basis_tl))} :
    merge_aux_liNew (.nil :: tl) deg (.cons .nil s_tl) = .cons .nil (merge_aux_liNew tl deg s_tl) := by
  apply merge_aux_liNew_cons_stable
  simp [leadingExp]

theorem merge_aux_liNew_cons_lt {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {s_hd_deg : ℝ} {s_hd_coef : PreMS basis_tl} {s_hd_tl : PreMS (basis_hd :: basis_tl)}
    {s_tl : CoList (PreMS (basis_hd :: basis_tl))}
    {firsts_tl : List (PreMS (basis_hd :: basis_tl))}
    (h_lt : ∀ x ∈ firsts_tl, x.leadingExp < s_hd_deg) :
    merge_aux_liNew (CoList.cons (s_hd_deg, s_hd_coef) s_hd_tl :: firsts_tl) s_hd_deg
    (CoList.cons (CoList.cons (s_hd_deg, s_hd_coef) s_hd_tl) s_tl) =
    CoList.cons s_hd_tl s_tl := by
  rw [merge_aux_liNew_cons_cons]
  simp [merge_aux_liNew]
  generalize 0 = offset
  induction firsts_tl generalizing offset with
  | nil => simp
  | cons firsts_tl_hd firsts_tl_tl ih =>
    simp at h_lt
    specialize ih h_lt.right
    revert h_lt
    apply firsts_tl_hd.casesOn
    · intro h_lt
      simp
      apply ih
    · intro (firsts_tl_hd_deg, firsts_tl_hd_coef) firsts_tl_hd_tl h_lt
      simp
      split_ifs with h
      · simp [leadingExp] at h_lt
        exfalso
        linarith [h, h_lt.left]
      · apply ih

theorem merge_aux_liNew_wellOrdered {basis_hd : ℝ → ℝ} {basis_tl : Basis} {deg : ℝ} {m : ℕ}
    {s : CoList (PreMS (basis_hd :: basis_tl))}
    (hs : s.all wellOrdered) :
    (merge_aux_liNew (s.take m) deg s).all wellOrdered := by
  simp [merge_aux_liNew]
  have h_firsts : ∀ x ∈ s.take m, x.wellOrdered := CoList.take_all hs
  generalize s.take m = firsts at h_firsts
  generalize 0 = offset
  induction firsts generalizing offset s with
  | nil => simpa
  | cons hd tl ih =>
    simp
    simp at h_firsts
    apply ih _ h_firsts.right
    revert h_firsts
    apply hd.casesOn
    · intro
      simpa
    · intro (deg, coef) tl' h_firsts
      simp
      split_ifs
      · apply CoList.set_all hs
        exact (wellOrdered_cons h_firsts.left).right.right
      · assumption

theorem merge_aux_tail_stable {basis_hd : ℝ → ℝ} {basis_tl : Basis} {deg : ℝ} {m : ℕ}
    {s : CoList (PreMS (basis_hd :: basis_tl))} :
    CoList.tail^[merge_aux_kNew deg m s] (merge_aux_liNew (CoList.take (m + 1) s) deg s) =
    CoList.tail^[merge_aux_kNew deg m s] s := by
  simp [merge_aux_liNew]
  generalize h_offset : 0 = offset
  have h_len : (CoList.take (m + 1) s).length + offset ≤ m + 1 := by
    simp [← h_offset]
    apply CoList.take_length_le
  replace h_offset : (CoList.take (m + 1) s) = List.tail^[offset] (CoList.take (m + 1) s) := by
    simp [← h_offset]
  generalize h_firsts : CoList.take (m + 1) s = firsts at h_len
  conv at h_offset => lhs; rw [h_firsts]
  clear h_firsts
  -- clear h_offset
  induction firsts generalizing offset s with
  | nil => simp
  | cons hd tl ih =>
    simp at h_len h_offset
    simp
    apply hd.casesOn (motive := fun x ↦ hd = x → _)
    · intro h_hd
      simp
      apply ih
      · apply_fun List.tail at h_offset
        simpa only [Function.iterate_succ', Function.comp_apply, List.tail_cons] using h_offset
      · linarith
    · intro (hd_deg, hd_coef) hd_tl h_hd
      simp
      split_ifs with h_deg
      · have : offset ≤ m := by omega
        apply Nat.eq_or_lt_of_le at this
        cases this with
        | inl h_offset' =>
          symm at h_offset'
          subst h_offset'
          have : tl = [] := by
            have : tl.length ≤ 0 := by omega
            simpa using this
          subst this
          simp
          have h_get : s.get m = .some (.cons (hd_deg, hd_coef) hd_tl) := by
            simp [h_hd, CoList.take_tail'] at h_offset
            simp
            revert h_offset
            generalize (CoList.tail^[m] s) = t
            apply t.casesOn <;> simp

          simp [-CoList.get_eq_head, merge_aux_kNew, h_get, leadingExp, h_deg, -Function.iterate_succ]
          apply CoList.set_tail_stable_of_lt
          simp
        | inr h_offset_lt =>
          specialize ih (s := (CoList.set offset s hd_tl)) (offset + 1)
          have : tl = List.tail^[offset + 1] (CoList.take (m + 1) (CoList.set offset s hd_tl)) := by
            rw [CoList.take_tail', CoList.set_tail_stable_of_lt (by simp), ← CoList.take_tail']
            apply_fun List.tail at h_offset
            simpa only [Function.iterate_succ', Function.comp_apply, List.tail_cons] using h_offset
          specialize ih this (by linarith)
          have : merge_aux_kNew deg m (CoList.set offset s hd_tl) = merge_aux_kNew deg m s := by
            simp only [merge_aux_kNew]
            rw [CoList.set_get_stable]
            omega
          rw [this] at ih
          rw [ih]
          apply CoList.set_tail_stable_of_lt
          apply lt_of_lt_of_le h_offset_lt
          have : merge_aux_kNew deg m s = m ∨ merge_aux_kNew deg m s = m + 1 := merge_aux_kNew_eq_or_succ
          cases this with
          | inl this => linarith only [this]
          | inr this => linarith only [this]
      · apply ih
        · apply_fun List.tail at h_offset
          simpa only [Function.iterate_succ', Function.comp_apply, List.tail_cons] using h_offset
        · linarith
    · rfl

theorem merge_aux_liNew_Sorted {basis_hd : ℝ → ℝ} {basis_tl : Basis} {deg : ℝ} {m : ℕ}
    {s_hd : PreMS (basis_hd :: basis_tl)}
    {s_tl : CoList (PreMS (basis_hd :: basis_tl))}
    (h : (CoList.tail^[m + 1] (CoList.cons s_hd s_tl)).Sorted (fun (x y : PreMS (basis_hd :: basis_tl)) ↦ x > y)) :
    (CoList.tail^[merge_aux_kNew deg m s_tl] (merge_aux_liNew (CoList.take (m + 1) s_tl) deg s_tl)).Sorted (· > ·) := by
  simp at h
  rw [merge_aux_tail_stable]
  have : merge_aux_kNew deg m s_tl = m ∨ merge_aux_kNew deg m s_tl = m + 1 := merge_aux_kNew_eq_or_succ
  cases this with
  | inl h_kNew =>
    rwa [h_kNew]
  | inr h_kNew =>
    rw [h_kNew]
    simp only [gt_iff_lt, Function.iterate_succ', Function.comp_apply]
    apply CoList.Sorted_tail h

theorem merge_aux_coef_cons_lt {basis_hd : ℝ → ℝ} {basis_tl : Basis} {deg : ℝ}
    {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
    {li : List (PreMS (basis_hd :: basis_tl))} (h_li : ∀ x ∈ li, x.leadingExp < deg) :
    merge_aux_coef (CoList.cons (deg, coef) tl :: li) deg = coef := by
  simp [merge_aux_coef]
  induction li with
  | nil => simp
  | cons li_hd li_tl ih =>
    simp
    -- simp at h_li
    revert h_li
    apply li_hd.casesOn
    · intro h_li
      simp at h_li ⊢
      apply ih
      exact h_li
    · intro (li_hd_deg, li_hd_coef) li_hd_tl h_li
      simp [leadingExp] at h_li ⊢
      split_ifs with h
      · exfalso
        linarith [h, h_li.left]
      · apply ih
        exact h_li.right

theorem merge_succ_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {s_hd : PreMS (basis_hd :: basis_tl)}
    {s_tl : CoList (PreMS (basis_hd :: basis_tl))} {m : ℕ} :
    merge (m + 1) (CoList.cons s_hd s_tl) = s_hd.add (merge m s_tl) := by
  let motive : PreMS (basis_hd :: basis_tl) → PreMS (basis_hd :: basis_tl) → Prop := fun x y =>
    ∃ m s_hd s_tl,
      x = merge (m + 1) (CoList.cons s_hd s_tl) ∧
      y = s_hd.add (merge m s_tl)
  apply CoList.Eq.coind motive
  · intro x y ih
    simp only [motive] at ih
    obtain ⟨m, s_hd, s_tl, hx_eq, hy_eq⟩ := ih
    rw [merge_unfold] at hx_eq hy_eq
    simp [merge'] at hx_eq hy_eq
    revert hx_eq hy_eq
    apply s_hd.casesOn
    · intro hy_eq hx_eq
      cases h_maxExp : maxExp (CoList.take (m + 1) s_tl) with
      | bot =>
        right
        simp [h_maxExp, leadingExp] at hx_eq hy_eq
        exact ⟨hx_eq, hy_eq⟩
      | coe right_deg =>
        left
        simp [h_maxExp, leadingExp] at hx_eq hy_eq
        use ?_, ?_, ?_
        constructor
        · exact hx_eq
        constructor
        · exact hy_eq
        simp [motive]
        use ?_, .nil, ?_
        constructor
        swap
        · simp
          exact Eq.refl _
        · rfl
    · intro (s_hd_deg, s_hd_coef) s_hd_tl hy_eq hx_eq
      left
      cases h_maxExp : maxExp (CoList.take (m + 1) s_tl) with
      | bot =>
        simp [h_maxExp, leadingExp] at hx_eq hy_eq
        use ?_, ?_, ?_
        constructor
        · exact hx_eq
        constructor
        · rw [hy_eq]
          congr
          · rw [merge_aux_coef_cons_lt]
            intro x hx
            rw [maxExp_eq_bot_iff] at h_maxExp
            simp [h_maxExp x hx, leadingExp]
          · exact Eq.refl _
        simp only [motive]
        use ?_, s_hd_tl, s_tl
        constructor
        · congr
          · exact Eq.refl _
          · rw [merge_aux_liNew_cons_lt]
            rw [maxExp_eq_bot_iff] at h_maxExp
            intro x hx
            simp [h_maxExp x hx, leadingExp]
        · symm
          convert add_nil
          rw [merge_unfold, merge']
          rw [maxExp_eq_bot_iff] at h_maxExp
          rw [maxExp_eq_bot_iff.mpr]
          simp only [merge_aux_kNew]
          cases h : CoList.get m s_tl with
          | none => simpa
          | some ms =>
            have : ms = .nil := by
              apply h_maxExp
              apply CoList.get_mem_take _ h
              simp
            rw [this]
            simpa [leadingExp]
      | coe right_deg =>
        simp [h_maxExp, leadingExp] at hx_eq hy_eq
        rw [add_cons_cons] at hy_eq
        split_ifs at hy_eq with h1 h2
        · rw [sup_of_le_left h1.le] at hx_eq
          use ?_, ?_, ?_
          constructor
          · exact hx_eq
          constructor
          · rw [hy_eq]
            congr
            · rw [merge_aux_coef_cons_lt]
              intro x hx
              apply lt_of_le_of_lt (b := ↑right_deg)
              · rw [← h_maxExp]
                apply maxExp_ge hx
              · simpa
            · exact Eq.refl _
          simp only [motive]
          use ?_, ?_, ?_
          constructor
          · congr
            · exact Eq.refl _
            · rw [merge_aux_liNew_cons_lt]
              · exact Eq.refl _
              intro x hx
              apply lt_of_le_of_lt (b := ↑right_deg)
              · rw [← h_maxExp]
                apply maxExp_ge hx
              · simpa
          · congr
            have : merge_aux_kNew s_hd_deg m s_tl = m := by
              simp only [merge_aux_kNew]
              cases h : CoList.get m s_tl with
              | none => simp
              | some ms =>
                simp
                have : ms ∈ CoList.take (m + 1) s_tl := by
                  apply CoList.get_mem_take _ h
                  simp
                have := h_maxExp ▸ maxExp_ge this
                intro h
                simp [h] at this
                linarith
            rw [this]
            conv => rhs; rw [merge_unfold, merge', h_maxExp]; simp
        · rw [sup_of_le_right h2.le] at hx_eq
          use ?_, ?_, ?_
          constructor
          · exact hx_eq
          constructor
          · rw [hy_eq]
            congr 2
            · conv => rhs; rw [merge_aux_coef_cons]
              split_ifs with h
              · exfalso
                linarith
              · rfl
            · exact Eq.refl _
          simp only [motive]
          use ?_, ?_, ?_
          constructor
          swap
          · congr
            · exact Eq.refl _
            · exact Eq.refl _
            · exact Eq.refl _
          · congr
            conv => lhs; simp [merge_aux_liNew_cons_cons]
            split_ifs with h
            · exfalso
              linarith
            · rfl
        · have : s_hd_deg = right_deg := by linarith
          subst this
          clear h1 h2
          simp at hx_eq hy_eq
          use ?_, ?_, ?_
          constructor
          · exact hx_eq
          constructor
          · rw [hy_eq]
            congr
            · conv => rhs; simp [merge_aux_coef_cons]
            · exact Eq.refl _
          simp only [motive]
          use ?_, ?_, ?_
          constructor
          swap
          · congr
            · exact Eq.refl _
            · exact Eq.refl _
            · exact Eq.refl _
          · congr
            conv => lhs; simp [merge_aux_liNew_cons_cons]
  · simp only [motive]
    use m, s_hd, s_tl

@[simp]
theorem merge1_leadingExp {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {s_hd : PreMS (basis_hd :: basis_tl)}
    {s_tl : CoList (PreMS (basis_hd :: basis_tl))} :
    (merge1 (.cons s_hd s_tl)).leadingExp = s_hd.leadingExp := by
  rw [merge1, merge_unfold, merge']
  simp
  apply s_hd.casesOn
  · simp [leadingExp]
  · intro (deg, coef) tl
    simp [leadingExp]

@[simp]
theorem merge1_cons_head {basis_hd : ℝ → ℝ} {basis_tl : Basis} {s_hd_deg : ℝ} {s_hd_coef : PreMS basis_tl}
    {s_hd_tl : PreMS (basis_hd :: basis_tl)} {s_tl : CoList (PreMS (basis_hd :: basis_tl))} :
    (merge1 (.cons (.cons (s_hd_deg, s_hd_coef) s_hd_tl) s_tl)).head = (s_hd_deg, s_hd_coef) := by
  simp [merge1]
  rw [merge_unfold, merge']
  simp [leadingExp, merge_aux_coef]

-- You can change arguments if it's incovenient
theorem merge1_cons_head_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {deg : ℝ}
    {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
    {s_tl : CoList (PreMS (basis_hd :: basis_tl))} :
    merge1 (.cons (.cons (deg, coef) tl) s_tl) = .cons (deg, coef) (tl.add (merge1 s_tl)) := by
  simp [merge1]
  conv => lhs; rw [merge_unfold, merge']; simp [leadingExp]
  simp [merge_aux_coef, merge_aux_kNew, leadingExp, merge_aux_liNew]
  apply merge_succ_cons

-- theorem merge1_cons_eq_add {basis_hd : ℝ → ℝ} {basis_tl : Basis}
--     {s_hd : PreMS (basis_hd :: basis_tl)} {s_tl : CoList (PreMS (basis_hd :: basis_tl))} :
--     merge1 (.cons s_hd s_tl) = add s_hd (merge1 s_tl) := by
--   apply s_hd.casesOn
--   · sorry
--   · intro (deg, coef) tl
--     rw [add_cons_left]
--     · apply merge1_cons_head_cons
--     · apply s_tl.casesOn
--       · simp
--       · simp

end PreMS

end TendstoTactic
