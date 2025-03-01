/-
Copyright (c) 2024 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
-/
import Mathlib.Tactic.Tendsto.Multiseries.Operations.Add

/-!
# Merge opertaion for multiseries

-/

namespace TendstoTactic

namespace PreMS

open Stream' Seq

-- TODO : remove theorems about `Pairwise`

noncomputable def maxExp {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (li : List (PreMS (basis_hd :: basis_tl))) : WithBot ℝ :=
  (li.map leadingExp).maximum.bind (·)

noncomputable def merge_aux_coef {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (firsts : List (PreMS (basis_hd :: basis_tl))) (exp : ℝ) : PreMS basis_tl :=
  firsts.foldl (init := 0) fun curCoef elem =>
    match destruct elem with
    | none => curCoef
    | some ((exp', coef), _) =>
      if exp' == exp then
        curCoef + coef
      else
        curCoef

noncomputable def merge_aux_liNew {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (firsts : List (PreMS (basis_hd :: basis_tl))) (exp : ℝ)
    (li : Seq (PreMS (basis_hd :: basis_tl))) : Seq (PreMS (basis_hd :: basis_tl)) :=
  firsts.foldlIdx (init := li) fun idx curLi elem =>
    match destruct elem with
    | none => curLi
    | some ((exp', _), tl) =>
      if exp' == exp then
        curLi.set idx tl
      else
        curLi

noncomputable def merge_aux_kNew {basis_hd : ℝ → ℝ} {basis_tl : Basis} (exp : ℝ) (k : ℕ)
    (li : Seq (PreMS (basis_hd :: basis_tl))) : ℕ :=
  match li.get? k with
  | none => k
  | some ms =>
    if ms.leadingExp = exp then
      k + 1
    else
      k

noncomputable def merge_aux {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    (ℕ × Seq (PreMS (basis_hd :: basis_tl))) →
    Option ((ℝ × PreMS basis_tl) × (ℕ × Seq (PreMS (basis_hd :: basis_tl)))) :=
  fun (k, li) =>
  let firsts := li.take (k + 1)
  let exp? : WithBot ℝ := maxExp firsts
  match exp? with
  | ⊥ => none
  | .some exp =>
    let coef : PreMS basis_tl := merge_aux_coef firsts exp
    let liNew : Seq (PreMS (basis_hd :: basis_tl)) := merge_aux_liNew firsts exp li
    let kNew : ℕ := merge_aux_kNew exp k li
    some ((exp, coef), (kNew, liNew))

noncomputable def merge {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (n : ℕ) (s : Seq (PreMS (basis_hd :: basis_tl))) : PreMS (basis_hd :: basis_tl) :=
  Seq.corec merge_aux (n, s)

-- TODO: rename?
/-- Given Seq `s` of PreMS (which are also Seqs), merge them into single PreMS while maintaining
the correct order. At the step `n` it considers only first `n` elements of `s`. -/
noncomputable def merge1 {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (s : Seq (PreMS (basis_hd :: basis_tl))) : PreMS (basis_hd :: basis_tl) :=
  merge 0 s

--theorems

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
  conv => arg 1; arg 1; arg 1; arg 1; simp
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

theorem maxExp_ge {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {li : List (PreMS (basis_hd :: basis_tl))}
    {X : PreMS (basis_hd :: basis_tl)} (hX : X ∈ li) :
    X.leadingExp ≤ maxExp li := by
  simp [maxExp]
  have := List.le_maximum_of_mem' (List.mem_map_of_mem leadingExp hX)
  generalize (List.map leadingExp li).maximum = a at this
  cases a <;> simpa [Option.bind]

-- Ugly
theorem maxExp_eq_bot_iff {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {li : List (PreMS (basis_hd :: basis_tl))} :
    maxExp li = ⊥ ↔ ∀ X ∈ li, X = .nil := by
  constructor
  · intro h X
    cases' X with exp coef tl
    · simp
    · intro hX
      simp [maxExp] at h
      have := List.mem_map_of_mem leadingExp hX
      simp only [leadingExp_cons] at this
      have := List.le_maximum_of_mem' this
      generalize (List.map leadingExp li).maximum = t at *
      cases ht : t with
      | bot => simp [ht] at this
      | coe X =>
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
        arg 2; simp
      rw [this]
      simp [Option.bind]
    · have : li = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro X hX
        specialize h X hX
        rw [h] at hX
        exact h_mem hX
      rw [this]
      simp [Option.bind]
      rfl

noncomputable def merge' {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (n : ℕ) (s : Seq (PreMS (basis_hd :: basis_tl))) : PreMS (basis_hd :: basis_tl) :=
  let firsts := s.take (n + 1)
  let exp? : WithBot ℝ := maxExp firsts
  match exp? with
  | ⊥ => .nil
  | .some exp =>
    let coef : PreMS basis_tl := merge_aux_coef firsts exp
    let liNew : Seq (PreMS (basis_hd :: basis_tl)) := merge_aux_liNew firsts exp s
    let kNew : ℕ := merge_aux_kNew exp n s
    .cons (exp, coef) (merge kNew liNew)

theorem merge_unfold {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {n : ℕ} {s : Seq (PreMS (basis_hd :: basis_tl))} :
    merge n s = merge' n s := by
  simp [merge']
  conv => lhs; unfold merge merge_aux
  simp
  cases h : maxExp (Seq.take (n + 1) s) with
  | bot =>
    simp
    rw [Seq.corec_nil]
    simp [h]
  | coe =>
    simp
    rw [Seq.corec_cons]
    swap
    · simp [h]
      constructor <;> rfl
    unfold merge merge_aux
    simp

scoped instance {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    Preorder (PreMS (basis_hd :: basis_tl)) where
  le := fun X Y ↦ X.leadingExp ≤ Y.leadingExp
  le_refl := by simp
  le_trans := by
    simp
    intro X Y Z hXY hYZ
    apply le_trans hXY hYZ

theorem lt_iff_lt {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X Y : PreMS (basis_hd :: basis_tl)} :
    (X < Y) ↔ (X.leadingExp < Y.leadingExp) := by
  constructor
  · intro h
    rw [lt_iff_le_not_le] at h ⊢
    exact h
  · intro h
    rw [lt_iff_le_not_le] at h ⊢
    exact h

theorem eq_nil_of_le_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X : PreMS (basis_hd :: basis_tl)}
    (h : X ≤ .nil) : X = .nil := by
  cases X <;> simp [LE.le] at h ⊢

theorem tail_eq_nil_of_nil_head {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {tl : Seq (PreMS (basis_hd :: basis_tl))}
    (h_Pairwise : (Seq.cons .nil tl).Pairwise (· > ·)) : tl = .nil := by
  cases tl
  · simp
  · replace h_Pairwise := (Seq.Pairwise.cons_elim h_Pairwise).left
    simp [LT.lt, leadingExp] at h_Pairwise

@[simp]
theorem merge_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {n : ℕ} :
    merge n (basis_hd := basis_hd) (basis_tl := basis_tl) .nil = .nil := by
  simp [merge, merge_aux, Seq.corec_nil]

@[simp]
theorem merge1_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    merge1 (basis_hd := basis_hd) (basis_tl := basis_tl) .nil = .nil := by
  simp [merge1]

@[simp]
theorem merge1_cons_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {hd : PreMS (basis_hd :: basis_tl)} :
    merge1 (basis_hd := basis_hd) (basis_tl := basis_tl) (.cons hd .nil) = hd := by
  let motive : PreMS (basis_hd :: basis_tl) → PreMS (basis_hd :: basis_tl) → Prop := fun X Y =>
    ∃ m, X = merge m (.cons Y .nil)
  apply Seq.eq_of_bisim' motive
  · simp only [motive, merge1]
    use 0
  · intro X Y ih
    simp only [motive] at ih
    obtain ⟨m, ih⟩ := ih
    subst ih
    cases' Y with hd tl
    · right
      simp
      rw [merge]
      unfold merge_aux
      simp [Seq.corec_nil]
    · left
      use hd, ?_, ?_
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

@[simp]
theorem megre1_cons_head_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {s_tl : Seq (PreMS (basis_hd :: basis_tl))} :
    merge1 (.cons .nil s_tl) = .nil := by
  simp [merge1, merge]
  rw [Seq.corec_nil]
  simp [merge_aux]

@[simp]
theorem merge_aux_kNew_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ} {m : ℕ}
    {s_hd : PreMS (basis_hd :: basis_tl)} {s_tl : Seq (PreMS (basis_hd :: basis_tl))} :
    merge_aux_kNew exp (m + 1) (Seq.cons s_hd s_tl) = merge_aux_kNew exp m s_tl + 1 := by
  simp [merge_aux_kNew]
  cases s_tl.get? m
  · simp
  · simp; split_ifs <;> rfl

theorem merge_aux_kNew_eq_or_succ {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ} {m : ℕ}
    {s : Seq (PreMS (basis_hd :: basis_tl))} :
    merge_aux_kNew exp m s = m ∨ merge_aux_kNew exp m s = m + 1 := by
  simp only [merge_aux_kNew]
  cases Seq.get? s m with
  | none => simp
  | some =>
    simp
    symm
    apply em

theorem merge_aux_coef_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {hd_exp exp : ℝ}
    {hd_coef : PreMS basis_tl} {hd_tl : PreMS (basis_hd :: basis_tl)}
    {firsts_tl : List (PreMS (basis_hd :: basis_tl))} :
    merge_aux_coef (Seq.cons (hd_exp, hd_coef) hd_tl :: firsts_tl) exp =
    if hd_exp = exp then
      hd_coef + (merge_aux_coef firsts_tl exp)
    else
     merge_aux_coef firsts_tl exp := by
  simp [merge_aux_coef]
  split_ifs
  · conv => lhs; rw [← add_zero hd_coef] --rw [show hd_coef = hd_coef + 0 by simp]
    generalize (0 : PreMS basis_tl) = init
    induction firsts_tl generalizing init with
    | nil => simp
    | cons firsts_tl_hd firsts_tl_tl ih =>
      simp [add_assoc]
      cases firsts_tl_hd
      · simp
        apply ih
      · simp
        split_ifs
        · apply ih
        · apply ih
  · simp

theorem merge_aux_liNew_aux {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ}
    {s_hd : PreMS (basis_hd :: basis_tl)} {s_tl : Seq (PreMS (basis_hd :: basis_tl))}
    {firsts : List (PreMS (basis_hd :: basis_tl))} :
    let f : ℕ → Seq (PreMS (basis_hd :: basis_tl)) → PreMS (basis_hd :: basis_tl) →
        Seq (PreMS (basis_hd :: basis_tl)) := (fun idx curLi elem ↦
      match elem.destruct with
      | none => curLi
      | some ((exp', _), tl) => if exp' = exp then curLi.set idx tl else curLi);
    List.foldlIdx f (Seq.cons s_hd s_tl) firsts 1 =
    .cons s_hd (List.foldlIdx f s_tl firsts 0) := by
  generalize h_offset : 0 = offset
  rw [show 1 = offset + 1 by simp [h_offset]]
  clear h_offset
  induction firsts generalizing offset s_tl with
  | nil => simp
  | cons firsts_hd firsts_tl ih =>
    simp
    cases' firsts_hd with firsts_hd_exp firsts_hd_coef firsts_hd_tl
    · simp
      apply ih
    · simp
      split_ifs
      · apply ih
      · apply ih

theorem merge_aux_liNew_cons_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {s_hd_exp exp : ℝ}
    {s_hd_coef : PreMS basis_tl} {s_hd_tl : PreMS (basis_hd :: basis_tl)}
    {s_tl : Seq (PreMS (basis_hd :: basis_tl))}
    {firsts_tl : List (PreMS (basis_hd :: basis_tl))}:
    merge_aux_liNew (Seq.cons (s_hd_exp, s_hd_coef) s_hd_tl :: firsts_tl) exp
      (Seq.cons (Seq.cons (s_hd_exp, s_hd_coef) s_hd_tl) s_tl) =
    if s_hd_exp = exp then
      .cons s_hd_tl (merge_aux_liNew firsts_tl exp s_tl)
    else
      .cons (Seq.cons (s_hd_exp, s_hd_coef) s_hd_tl) (merge_aux_liNew firsts_tl exp s_tl) := by
  simp [merge_aux_liNew]
  split_ifs
  · exact merge_aux_liNew_aux
  · exact merge_aux_liNew_aux

theorem merge_aux_liNew_cons_stable {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ}
    {hd : PreMS (basis_hd :: basis_tl)} (h_exp : hd.leadingExp < exp)
    {firsts_tl : List (PreMS (basis_hd :: basis_tl))} {s_tl : Seq (PreMS (basis_hd :: basis_tl))} :
    merge_aux_liNew (hd :: firsts_tl) exp (.cons hd s_tl) =
    .cons hd (merge_aux_liNew firsts_tl exp s_tl) := by
  cases' hd with hd_exp h_coef hd_tl
  · simp [merge_aux_liNew]
    exact merge_aux_liNew_aux
  · simp at h_exp
    rw [merge_aux_liNew_cons_cons]
    split_ifs with h
    · exfalso
      linarith
    · rfl

@[simp]
theorem merge_aux_liNew_cons_nil_stable {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ}
    {tl : List (PreMS (basis_hd :: basis_tl))} {s_tl : Seq (PreMS (basis_hd :: basis_tl))} :
    merge_aux_liNew (.nil :: tl) exp (.cons .nil s_tl) =
    .cons .nil (merge_aux_liNew tl exp s_tl) := by
  apply merge_aux_liNew_cons_stable
  simp

theorem merge_aux_liNew_cons_lt {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {s_hd_exp : ℝ} {s_hd_coef : PreMS basis_tl} {s_hd_tl : PreMS (basis_hd :: basis_tl)}
    {s_tl : Seq (PreMS (basis_hd :: basis_tl))}
    {firsts_tl : List (PreMS (basis_hd :: basis_tl))}
    (h_lt : ∀ X ∈ firsts_tl, X.leadingExp < s_hd_exp) :
    merge_aux_liNew (Seq.cons (s_hd_exp, s_hd_coef) s_hd_tl :: firsts_tl) s_hd_exp
    (Seq.cons (Seq.cons (s_hd_exp, s_hd_coef) s_hd_tl) s_tl) =
    Seq.cons s_hd_tl s_tl := by
  rw [merge_aux_liNew_cons_cons]
  simp [merge_aux_liNew]
  generalize 0 = offset
  induction firsts_tl generalizing offset with
  | nil => simp
  | cons firsts_tl_hd firsts_tl_tl ih =>
    simp at h_lt
    specialize ih h_lt.right
    cases' firsts_tl_hd with firsts_tl_hd_exp firsts_tl_hd_coef firsts_tl_hd_tl
    · simp
      apply ih
    · simp
      split_ifs with h
      · simp at h_lt
        exfalso
        linarith [h, h_lt.left]
      · apply ih

theorem merge_aux_liNew_WellOrdered {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ} {m : ℕ}
    {s : Seq (PreMS (basis_hd :: basis_tl))}
    (hs : s.All WellOrdered) :
    (merge_aux_liNew (s.take m) exp s).All WellOrdered := by
  simp [merge_aux_liNew]
  have h_firsts : ∀ X ∈ s.take m, X.WellOrdered := Seq.take_All hs
  generalize s.take m = firsts at h_firsts
  generalize 0 = offset
  induction firsts generalizing offset s with
  | nil => simpa
  | cons hd tl ih =>
    simp
    simp at h_firsts
    apply ih _ h_firsts.right
    cases' hd with exp coef tl'
    · simpa
    · simp
      split_ifs
      · apply Seq.set_All hs
        exact (WellOrdered_cons h_firsts.left).right.right
      · assumption

theorem merge_aux_tail_stable {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ} {m : ℕ}
    {s : Seq (PreMS (basis_hd :: basis_tl))} :
    (merge_aux_liNew (Seq.take (m + 1) s) exp s).drop (merge_aux_kNew exp m s)  =
    s.drop (merge_aux_kNew exp m s) := by
  simp [merge_aux_liNew]
  generalize h_offset : 0 = offset
  have h_len : (Seq.take (m + 1) s).length + offset ≤ m + 1 := by
    simp [← h_offset]
    apply Seq.length_take_le
  replace h_offset : (Seq.take (m + 1) s) = (Seq.take (m + 1) s).drop offset := by
    simp [← h_offset]
  generalize h_firsts : Seq.take (m + 1) s = firsts at h_len
  conv at h_offset => lhs; rw [h_firsts]
  clear h_firsts
  induction firsts generalizing offset s with
  | nil => simp
  | cons hd tl ih =>
    simp at h_len h_offset
    simp
    cases' h_hd : hd with hd_exp hd_coef hd_tl
    · simp
      apply ih
      · apply_fun List.tail at h_offset
        simpa using h_offset
      · linarith
    · simp
      split_ifs with h_exp
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
          have h_get : s.get? m = .some (.cons (hd_exp, hd_coef) hd_tl) := by
            simp [h_hd, Seq.take_drop] at h_offset
            simp [← head_dropn]
            revert h_offset
            generalize (s.drop m) = s'
            cases s' <;> simp
            exact Eq.symm
          simp [merge_aux_kNew, h_get, h_exp]
          apply Seq.set_dropn_stable_of_lt
          simp
        | inr h_offset_lt =>
          specialize ih (s := (s.set offset hd_tl)) (offset + 1)
          have : tl = (Seq.take (m + 1) (s.set offset hd_tl)).drop (offset + 1) := by
            rw [Seq.take_drop, Seq.set_dropn_stable_of_lt (by simp), ← Seq.take_drop]
            apply_fun List.tail at h_offset
            simpa using h_offset
          specialize ih this (by linarith)
          have : merge_aux_kNew exp m (s.set offset hd_tl) = merge_aux_kNew exp m s := by
            simp only [merge_aux_kNew]
            rw [Seq.set_get_stable]
            omega
          rw [this] at ih
          rw [ih]
          apply Seq.set_dropn_stable_of_lt
          apply lt_of_lt_of_le h_offset_lt
          have : merge_aux_kNew exp m s = m ∨ merge_aux_kNew exp m s = m + 1 :=
            merge_aux_kNew_eq_or_succ
          cases this with
          | inl this => linarith only [this]
          | inr this => linarith only [this]
      · apply ih
        · apply_fun List.tail at h_offset
          simpa using h_offset
        · linarith

theorem merge_aux_liNew_Pairwise {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ} {m : ℕ}
    {s_hd : PreMS (basis_hd :: basis_tl)}
    {s_tl : Seq (PreMS (basis_hd :: basis_tl))}
    (h : ((Seq.cons s_hd s_tl).drop (m + 1)).Pairwise
      (fun (X Y : PreMS (basis_hd :: basis_tl)) ↦ X > Y)) :
    ((merge_aux_liNew (Seq.take (m + 1) s_tl) exp s_tl).drop
      (merge_aux_kNew exp m s_tl)).Pairwise (· > ·) := by
  rw [← Seq.dropn_tail, Seq.tail_cons] at h
  rw [merge_aux_tail_stable]
  have : merge_aux_kNew exp m s_tl = m ∨ merge_aux_kNew exp m s_tl = m + 1 :=
    merge_aux_kNew_eq_or_succ
  cases this with
  | inl h_kNew =>
    rwa [h_kNew]
  | inr h_kNew =>
    rw [h_kNew]
    apply Seq.Pairwise_tail h

theorem merge_aux_coef_cons_lt {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ}
    {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
    {li : List (PreMS (basis_hd :: basis_tl))} (h_li : ∀ X ∈ li, X.leadingExp < exp) :
    merge_aux_coef (Seq.cons (exp, coef) tl :: li) exp = coef := by
  simp [merge_aux_coef]
  induction li with
  | nil => simp
  | cons li_hd li_tl ih =>
    simp
    cases' li_hd with li_hd_exp li_hd_coef li_hd_tl
    · simp at h_li ⊢
      apply ih
      exact h_li
    · simp at h_li ⊢
      split_ifs with h
      · exfalso
        linarith [h, h_li.left]
      · apply ih
        exact h_li.right

theorem merge_succ_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {s_hd : PreMS (basis_hd :: basis_tl)}
    {s_tl : Seq (PreMS (basis_hd :: basis_tl))} {m : ℕ} :
    merge (m + 1) (Seq.cons s_hd s_tl) = s_hd + (merge m s_tl) := by
  let motive : PreMS (basis_hd :: basis_tl) → PreMS (basis_hd :: basis_tl) → Prop := fun X Y =>
    ∃ m s_hd s_tl,
      X = merge (m + 1) (Seq.cons s_hd s_tl) ∧
      Y = s_hd + (merge m s_tl)
  apply Seq.eq_of_bisim' motive
  · simp only [motive]
    use m, s_hd, s_tl
  · intro X Y ih
    simp only [motive] at ih
    obtain ⟨m, s_hd, s_tl, hX_eq, hY_eq⟩ := ih
    rw [merge_unfold] at hX_eq hY_eq
    simp [merge'] at hX_eq hY_eq
    cases' s_hd with s_hd_exp s_hd_coef s_hd_tl
    · cases h_maxExp : maxExp (Seq.take (m + 1) s_tl) with
      | bot =>
        right
        simp [h_maxExp] at hX_eq hY_eq
        exact ⟨hX_eq, hY_eq⟩
      | coe right_exp =>
        left
        simp [h_maxExp] at hX_eq hY_eq
        use ?_, ?_, ?_
        constructor
        · exact hX_eq
        constructor
        · exact hY_eq
        simp [motive]
        use ?_, .nil, ?_
        constructor
        swap
        · simp
          exact Eq.refl _
        · rfl
    · left
      cases h_maxExp : maxExp (Seq.take (m + 1) s_tl) with
      | bot =>
        simp [h_maxExp] at hX_eq hY_eq
        use ?_, ?_, ?_
        constructor
        · exact hX_eq
        constructor
        · rw [hY_eq]
          congr
          · rw [merge_aux_coef_cons_lt]
            intro X hX
            rw [maxExp_eq_bot_iff] at h_maxExp
            simp [h_maxExp X hX]
          · exact Eq.refl _
        simp only [motive]
        use ?_, s_hd_tl, s_tl
        constructor
        · congr
          · exact Eq.refl _
          · rw [merge_aux_liNew_cons_lt]
            rw [maxExp_eq_bot_iff] at h_maxExp
            intro X hX
            simp [h_maxExp X hX]
        · symm
          convert add_nil
          rw [merge_unfold, merge']
          rw [maxExp_eq_bot_iff] at h_maxExp
          rw [maxExp_eq_bot_iff.mpr]
          simp only [merge_aux_kNew]
          cases h : Seq.get? s_tl m with
          | none => simpa
          | some ms =>
            have : ms = .nil := by
              apply h_maxExp
              apply Seq.get?_mem_take _ h
              simp
            rw [this]
            simpa
      | coe right_exp =>
        simp [h_maxExp] at hX_eq hY_eq
        rw [add_cons_cons] at hY_eq
        split_ifs at hY_eq with h1 h2
        · rw [sup_of_le_left h1.le] at hX_eq
          use ?_, ?_, ?_
          constructor
          · exact hX_eq
          constructor
          · rw [hY_eq]
            congr
            · rw [merge_aux_coef_cons_lt]
              intro X hX
              apply lt_of_le_of_lt (b := ↑right_exp)
              · rw [← h_maxExp]
                apply maxExp_ge hX
              · simpa
            · exact Eq.refl _
          simp only [motive]
          use ?_, ?_, ?_
          constructor
          · congr
            · exact Eq.refl _
            · rw [merge_aux_liNew_cons_lt]
              · exact Eq.refl _
              intro X hX
              apply lt_of_le_of_lt (b := ↑right_exp)
              · rw [← h_maxExp]
                apply maxExp_ge hX
              · simpa
          · congr
            have : merge_aux_kNew s_hd_exp m s_tl = m := by
              simp only [merge_aux_kNew]
              cases h : Seq.get? s_tl m with
              | none => simp
              | some ms =>
                simp
                have : ms ∈ Seq.take (m + 1) s_tl := by
                  apply Seq.get?_mem_take _ h
                  simp
                have := h_maxExp ▸ maxExp_ge this
                intro h
                simp [h] at this
                linarith
            rw [this]
            conv => rhs; rw [merge_unfold, merge', h_maxExp]; simp
        · rw [sup_of_le_right h2.le] at hX_eq
          use ?_, ?_, ?_
          constructor
          · exact hX_eq
          constructor
          · rw [hY_eq]
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
        · have : s_hd_exp = right_exp := by linarith
          subst this
          clear h1 h2
          simp at hX_eq hY_eq
          use ?_, ?_, ?_
          constructor
          · exact hX_eq
          constructor
          · rw [hY_eq]
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

@[simp]
theorem merge1_cons_leadingExp {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {s_hd : PreMS (basis_hd :: basis_tl)}
    {s_tl : Seq (PreMS (basis_hd :: basis_tl))} :
    (merge1 (.cons s_hd s_tl)).leadingExp = s_hd.leadingExp := by
  rw [merge1, merge_unfold, merge']
  cases s_hd <;> simp

theorem merge1_leadingExp {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {s : Seq (PreMS (basis_hd :: basis_tl))} :
    (merge1 s).leadingExp = s.head.elim ⊥ (·.leadingExp) := by
  cases s <;> simp

@[simp]
theorem merge1_cons_head {basis_hd : ℝ → ℝ} {basis_tl : Basis} {s_hd_exp : ℝ}
    {s_hd_coef : PreMS basis_tl} {s_hd_tl : PreMS (basis_hd :: basis_tl)}
    {s_tl : Seq (PreMS (basis_hd :: basis_tl))} :
    (merge1 (.cons (.cons (s_hd_exp, s_hd_coef) s_hd_tl) s_tl)).head = (s_hd_exp, s_hd_coef) := by
  simp [merge1]
  rw [merge_unfold, merge']
  simp [merge_aux_coef]

@[simp]
theorem merge1_cons_head_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ}
    {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
    {s_tl : Seq (PreMS (basis_hd :: basis_tl))} :
    merge1 (.cons (.cons (exp, coef) tl) s_tl) = .cons (exp, coef) (tl + (merge1 s_tl)) := by
  simp [merge1]
  conv => lhs; rw [merge_unfold, merge']; simp
  simp [merge_aux_coef, merge_aux_kNew, merge_aux_liNew, Seq.cons_eq_cons]
  apply merge_succ_cons

theorem merge1_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {s_hd : PreMS (basis_hd :: basis_tl)} {s_tl : Seq (PreMS (basis_hd :: basis_tl))}
    (h_Pairwise : (Seq.cons s_hd s_tl).Pairwise (· > ·)) :
    merge1 (.cons s_hd s_tl) = s_hd + (merge1 s_tl) := by
  cases' s_hd with  s_hd_exp s_hd_coef s_hd_tl
  · simp [tail_eq_nil_of_nil_head h_Pairwise]
  · rw [add_cons_left]
    · apply merge1_cons_head_cons
    · cases' s_tl with s_tl_hd s_tl_tl
      · simp
      · apply Seq.Pairwise.cons_cons_elim_of_trans at h_Pairwise
        simp at h_Pairwise
        simp
        exact lt_iff_lt.mp h_Pairwise.left

theorem merge1_WellOrdered {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {s : Seq (PreMS (basis_hd :: basis_tl))}
    (h_wo : s.All WellOrdered)
    (h_Pairwise : s.Pairwise (· > ·)) : (merge1 s).WellOrdered := by
  let motive : PreMS (basis_hd :: basis_tl) → Prop := fun ms =>
    ∃ X s,
      ms = X + merge1 s ∧
      X.WellOrdered ∧
      s.All WellOrdered ∧
      s.Pairwise (fun x1 x2 ↦ x1 > x2)
  apply WellOrdered.coind motive
  · simp only [motive]
    use 0, s
    simp
    constructor
    · exact zero_WellOrdered
    constructor
    · exact h_wo
    · exact h_Pairwise
  · intro ms ih
    simp only [motive] at ih ⊢
    obtain ⟨X, s, h_eq, hX_wo, h_wo, h_Pairwise⟩ := ih
    subst h_eq
    cases' X with X_exp X_coef X_tl
    · cases' s with s_hd s_tl
      · simp
      simp at h_wo
      obtain ⟨h_hd_wo, h_tl_wo⟩ := h_wo
      cases' s_hd with s_hd_exp s_hd_coef s_hd_tl
      · simp
      right
      obtain ⟨h_hd_coef_wo, h_hd_comp, h_hd_tl_wo⟩ := WellOrdered_cons h_hd_wo
      cases' s_tl with s_tl_hd s_tl_tl
      · simp
        use ?_, ?_, ?_
        constructor
        · exact Eq.refl _
        apply WellOrdered_cons at h_hd_wo
        constructor
        · assumption
        constructor
        · assumption
        use s_hd_tl, .nil
        constructor
        · simp
        constructor
        · assumption
        constructor
        · simp
        · simp
      obtain ⟨h_Pairwise_hd, h_Pairwise_tl⟩ := Seq.Pairwise.cons_cons_elim_of_trans h_Pairwise
      use ?_, ?_, ?_
      constructor
      · rw [nil_add, merge1_cons_head_cons]
        exact Eq.refl _
      constructor
      · exact h_hd_coef_wo
      constructor
      · simp
        constructor
        · exact h_hd_comp
        · simpa [lt_iff_lt] using h_Pairwise_hd
      use ?_, ?_
      constructor
      · exact Eq.refl _
      constructor
      · exact h_hd_tl_wo
      constructor
      · exact h_tl_wo
      · exact h_Pairwise_tl
    · obtain ⟨hX_coef_wo, hX_comp, hX_tl_wo⟩ := WellOrdered_cons hX_wo
      right
      cases' s with s_hd s_tl
      · use ?_, ?_, ?_
        constructor
        · simp only [merge1_nil, add_nil]
          exact Eq.refl _
        constructor
        · exact hX_coef_wo
        constructor
        · exact hX_comp
        use ?_, .nil
        constructor
        · simp
          exact Eq.refl _
        constructor
        · exact hX_tl_wo
        · simp
      simp at h_wo
      obtain ⟨h_hd_wo, h_tl_wo⟩ := h_wo
      -- obtain ⟨h_Pairwise_hd, h_Pairwise_tl⟩ := Seq.Pairwise.cons_elim h_Pairwise
      cases' s_hd with s_hd_exp s_hd_coef s_hd_tl
      · use ?_, ?_, ?_  -- Copypaste
        constructor
        · simp only [megre1_cons_head_nil, add_nil]
          exact Eq.refl _
        constructor
        · exact hX_coef_wo
        constructor
        · exact hX_comp
        use ?_, .nil
        constructor
        · simp
          exact Eq.refl _
        constructor
        · exact hX_tl_wo
        · simp
      obtain ⟨h_hd_coef_wo, h_hd_comp, h_hd_tl_wo⟩ := WellOrdered_cons h_hd_wo
      rw [merge1_cons_head_cons, add_cons_cons]
      split_ifs with h1 h2
      · use ?_, ?_, ?_
        constructor
        · exact Eq.refl _
        constructor
        · exact hX_coef_wo
        constructor
        · simp
          constructor
          · exact hX_comp
          · exact h1
        use ?_, ?_
        constructor
        · rw [← merge1_cons_head_cons]
          exact Eq.refl _
        constructor
        · exact hX_tl_wo
        constructor
        · simp
          tauto
        · assumption
      · use ?_, ?_, ?_
        constructor
        · exact Eq.refl _
        constructor
        · exact h_hd_coef_wo
        constructor
        · simp
          constructor
          · exact h2
          constructor
          · exact h_hd_comp
          · cases s_tl
            · simp
            · obtain ⟨h_Pairwise_hd, h_Pairwise_tl⟩ := Seq.Pairwise.cons_cons_elim_of_trans h_Pairwise
              simpa [lt_iff_lt] using h_Pairwise_hd
        use ?_, s_tl
        constructor
        · rw [← add_assoc]
          exact Eq.refl _
        constructor
        · apply add_WellOrdered
          · exact hX_wo
          · exact h_hd_tl_wo
        constructor
        · exact h_tl_wo
        · exact h_Pairwise.cons_elim.right
      · have : X_exp = s_hd_exp := by linarith
        subst this
        use ?_, ?_, ?_
        constructor
        · exact Eq.refl _
        constructor
        · apply add_WellOrdered
          · exact hX_coef_wo
          · exact h_hd_coef_wo
        constructor
        · simp
          constructor
          · exact hX_comp
          constructor
          · exact h_hd_comp
          · cases s_tl
            · simp
            · obtain ⟨h_Pairwise_hd, h_Pairwise_tl⟩ := Seq.Pairwise.cons_cons_elim_of_trans h_Pairwise
              simpa [lt_iff_lt] using h_Pairwise_hd
        use ?_, s_tl
        constructor
        · rw [← add_assoc]
          exact Eq.refl _
        constructor
        · apply add_WellOrdered
          · exact hX_tl_wo
          · exact h_hd_tl_wo
        constructor
        · exact h_tl_wo
        · exact h_Pairwise.cons_elim.right

end PreMS

end TendstoTactic
