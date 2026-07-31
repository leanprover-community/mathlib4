/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
import GreensRelations.FactorizationForest.Split

/-!
# The Factorization Forest Theorem

## References
* [T. Colcombet, *The Factorization Forest Theorem*][colombet2008]
-/

namespace FactorizationForest

/-- Indices in `Fin (n+1)` that receive the maximal
  split rank. -/
def splitIndices {n h : ℕ} [Nonempty (Fin h)]
    (s : Split (Fin (n + 1)) h) : List (Fin (n + 1)) :=
  let max_val := Finset.max' Finset.univ Finset.univ_nonempty
  (List.finRange (n + 1)).filter (fun i => s i = max_val)

/-- Adjacent pairs from a list of indices. -/
def partitionIndices {n : ℕ} : List (Fin (n + 1)) → List (Fin (n + 1) × Fin (n + 1))
| [] => []
| _ :: [] => []
| i :: j :: rest => (i, j) :: partitionIndices (j :: rest)

/-- Properties of pairs from `partitionIndices`:
  both elements are in the list, they are strictly ordered,
  and no list element lies strictly between them. -/
lemma partitionIndices_props {n : ℕ} {l : List (Fin (n + 1))} {i j : Fin (n + 1)}
    (hs : List.Pairwise (· < ·) l) (h : (i, j) ∈ partitionIndices l) :
    i ∈ l ∧ j ∈ l ∧ i < j ∧ (j.val - i.val = n → l.map (·.val) = [0, n]) ∧
    (∀ k ∈ l, ¬(i < k ∧ k < j)) := by
  induction l with
  | nil => contradiction
  | cons a l' ih =>
    cases l' with
    | nil => contradiction
    | cons b l'' =>
      unfold partitionIndices at h
      simp only [List.mem_cons, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | h_tail
      · have hab : i < j := List.pairwise_cons.1 hs |>.1 j (by simp)
        exact ⟨by simp, by simp, hab,
          fun _ ↦ by
            cases l'' with
            | nil =>
              have h_eqs : i.val = 0 ∧ j.val = n := by omega
              simp [h_eqs]
            | cons c l''' =>
              have hjc : j < c :=
                List.pairwise_cons.1 (List.pairwise_cons.1 hs |>.2) |>.1 c (by simp)
              omega,
          fun k hk ↦ by
            simp only [List.mem_cons] at hk
            rcases hk with rfl | rfl | hk
            · omega
            · omega
            · have hjk : j < k := List.pairwise_cons.1 (List.pairwise_cons.1 hs |>.2) |>.1 k hk
              omega⟩
      · obtain ⟨hi, hj, hij, h_len, h_adj⟩ := ih (List.pairwise_cons.1 hs |>.2) h_tail
        exact ⟨by simp [hi], by simp [hj], hij,
          fun h_eq_n ↦ by
            have : a < b := List.pairwise_cons.1 hs |>.1 b (by simp)
            have : b.val = 0 := by injection h_len h_eq_n
            omega,
          fun k hk ↦ by
            rcases List.mem_cons.1 hk with rfl | hk
            · have hki : k < i := List.pairwise_cons.1 hs |>.1 i (by simp [hi])
              omega
            · exact h_adj k hk⟩

/-- The split indices are sorted in increasing order. -/
lemma splitIndices_sorted {n h : ℕ} [Nonempty (Fin h)]
  (s : Split (Fin (n + 1)) h) : List.Pairwise (· < ·) (splitIndices s) := by
  unfold splitIndices
  exact List.Pairwise.filter _ (List.sortedLT_finRange _ |>.pairwise)

/-- Restricts a split to a sub-interval `[i, i + len]`. -/
def restrictSplit {n h : ℕ} (s : Split (Fin (n + 1)) h) (i len : ℕ) (h_bound : i + len ≤ n) :
    Split (Fin (len + 1)) h :=
  fun k => s ⟨i + k.val, by omega⟩

/-- Lowers a split whose values are all strictly below `h - 1` into `Fin (h - 1)`. -/
def lowerSplitInterior {n h : ℕ} (s : Split (Fin (n + 1)) h)
    (h_interior : ∀ i : Fin (n + 1), (s i).val < h - 1) : Split (Fin (n + 1)) (h - 1) :=
  fun i => ⟨(s i).val, h_interior i⟩

/-- Recursively builds a factorization tree from a word and a split function. -/
def buildFactorizationTree {A S : Type*} [Semigroup S] {h : ℕ} [Nonempty (Fin h)]
    (eval : List A → S) (u : List A) (hu : u ≠ [])
    (s : Split (Fin (u.length + 1)) h) : FactorizationTree A :=
  if _h_len : u.length ≤ 2 then
    if _h_len2 : u.length = 1 then
      FactorizationTree.leaf (u.head hu)
    else
      have : u.length = 2 := by have := List.length_pos_of_ne_nil hu; omega
      let (u1, u2) := (u.head hu, u.getLast (by omega))
      FactorizationTree.binary (FactorizationTree.leaf u1) (FactorizationTree.leaf u2) u 1
  else
    let idxs := splitIndices s
    if h_idxs : idxs.map (·.val) = [0, u.length] then
      if hh : 1 < h then
        have : Nonempty (Fin (h - 1)) := ⟨⟨0, by omega⟩⟩
        let w := (u.drop 1).take (u.length - 2)
        have h_len_w : w.length = u.length - 2 := by
          rw [List.length_take, List.length_drop]
          omega
        have hw : w ≠ [] := by
          intro h
          have : w.length = 0 := congrArg List.length h
          omega
        have h_bound : 1 + w.length ≤ u.length := by omega
        let s_w := restrictSplit s 1 w.length h_bound
        have h_interior : ∀ i : Fin (w.length + 1), (s_w i).val < h - 1 := by
          intro i
          let j_val := 1 + i.val
          have h_max_val : (Finset.max' Finset.univ Finset.univ_nonempty : Fin h).val = h - 1 := by
            have := (Finset.max' Finset.univ Finset.univ_nonempty : Fin h).isLt
            have := Finset.le_max' Finset.univ (⟨h - 1, by omega⟩ : Fin h) (Finset.mem_univ _)
            grind
          have h_not_max : (s_w i).val ≠ h - 1 := by
            intro h_eq
            have h_s_eq : s ⟨j_val, by omega⟩ = Finset.max' Finset.univ Finset.univ_nonempty := by
              apply Fin.ext
              exact h_max_val ▸ h_eq
            have h_in_idxs : ⟨j_val, by omega⟩ ∈ splitIndices s := by
              simp [splitIndices, h_s_eq]
            have h_map : j_val ∈ (splitIndices s).map (·.val) := List.mem_map_of_mem h_in_idxs
            rw [h_idxs] at h_map
            simp at h_map
            omega
          have := (s_w i).isLt
          omega
        let t_w := buildFactorizationTree eval w hw (lowerSplitInterior s_w h_interior)
        let last_val := u.getLast (by omega)
        FactorizationTree.binary (FactorizationTree.leaf (u.head hu))
          (FactorizationTree.binary t_w (FactorizationTree.leaf last_val)
            (w ++ [last_val]) (t_w.height + 1)) u (t_w.height + 2)
      else
        FactorizationTree.binary (FactorizationTree.leaf (u.head hu))
          (FactorizationTree.leaf (u.head hu)) u 0
    else
      let children := (partitionIndices idxs).map fun ⟨i, j⟩ =>
        let w := (u.drop i.val).take (j.val - i.val)
        if h_valid : w.length < u.length ∧ i.val + w.length ≤ u.length ∧ w ≠ [] then
          buildFactorizationTree eval w h_valid.2.2 (restrictSplit s i.val w.length h_valid.2.1)
        else
          FactorizationTree.leaf (u.head hu)
      let max_h := (children.map FactorizationTree.height).foldl max 0
      match children with
      | [] =>
        let leaf := FactorizationTree.leaf (u.head hu)
        FactorizationTree.binary leaf leaf u (max_h + 1)
      | [c] => FactorizationTree.binary c c u (max_h + 1)
      | [c1, c2] => FactorizationTree.binary c1 c2 u (max_h + 1)
      | c1::c2::c3::rest => FactorizationTree.nary (c1::c2::c3::rest) u (max_h + 1)
termination_by (h, u.length)
decreasing_by
  all_goals simp_wf
  · have : 0 < h := Fin.pos_iff_nonempty.mpr inferInstance
    omega
  · grind

/-- The word of a tree built by `buildFactorizationTree` equals the original word `u`. -/
theorem buildTree_word_eq {A S : Type*} [Semigroup S] {h : ℕ} [Nonempty (Fin h)]
    (eval : List A → S) (u : List A) (hu : u ≠ []) (s : Split (Fin (u.length + 1)) h) :
    (buildFactorizationTree eval u hu s).word = u := by
  rw [buildFactorizationTree]
  split
  · split
    · rename_i h_len h_len2
      cases u with
      | nil => contradiction
      | cons a as =>
        cases as with
        | nil => rfl
        | cons b bs =>
          simp only [List.length_cons] at h_len2
          omega
    · rfl
  · dsimp only
    split <;> split <;> rfl

/-- The `foldl max` of tree heights is bounded by
  any uniform upper bound on the children. -/
lemma foldl_max_bound {A : Type*}
    (children : List (FactorizationTree A))
    (bound : ℕ)
    (h_bound : ∀ c ∈ children,
      c.height ≤ bound) :
    (children.map FactorizationTree.height).foldl
      max 0 ≤ bound := by
  have h_fold : ∀ (l : List (FactorizationTree A)) (init : ℕ), init ≤ bound →
      (∀ c ∈ l, c.height ≤ bound) → (l.map FactorizationTree.height).foldl max init ≤ bound := by
    intro l
    induction l with
    | nil =>
      intro init h_init _
      exact h_init
    | cons hd tl ih =>
      intro init h_init h_all
      apply ih
      · have h_hd : hd.height ≤ bound := h_all hd (by simp)
        omega
      · intro c hc
        exact h_all c (by simp [hc])
  exact h_fold children 0 (by omega) h_bound

/-- The height of the tree built by
  `buildFactorizationTree` is at most `3 * h - 1`. -/
theorem buildTree_height_bound {A S : Type*} [Semigroup S] {h : ℕ} [Nonempty (Fin h)]
    (eval : List A → S) (u : List A) (hu : u ≠ []) (s : Split (Fin (u.length + 1)) h) :
    (buildFactorizationTree eval u hu s).height ≤ 3 * h - 1 := by
  rw [buildFactorizationTree]
  split
  · split <;> {
      dsimp [FactorizationTree.height]
      have : 0 < h := Fin.pos_iff_nonempty.mpr inferInstance
      omega
    }
  · dsimp only
    split
    · split <;> dsimp [FactorizationTree.height]
      · rename_i hh
        have : Nonempty (Fin (h - 1)) := ⟨⟨0, by omega⟩⟩
        exact le_trans (Nat.add_le_add_right (buildTree_height_bound eval _ _ _) 2) (by omega)
      · have : 0 < h := Fin.pos_iff_nonempty.mpr inferInstance
        omega
    · generalize h_children : ((partitionIndices (splitIndices s)).map fun ⟨i, j⟩ =>
        let w := (u.drop i.val).take (j.val - i.val)
        if h_valid : w.length < u.length ∧ i.val + w.length ≤ u.length ∧ w ≠ [] then
          buildFactorizationTree eval w h_valid.2.2 (restrictSplit s i.val w.length h_valid.2.1)
        else
          FactorizationTree.leaf (u.head hu)) = children
      have h_max_bound : (children.map FactorizationTree.height).foldl max 0 ≤ 3 * h - 2 := by
        rw [← h_children]
        apply foldl_max_bound
        intro c hc
        simp only [List.mem_map, Prod.exists] at hc
        rcases hc with ⟨i, j, hp, rfl⟩
        split_ifs with h_valid
        · have h_child : (splitIndices (restrictSplit s i.val
            ((u.drop i.val).take (j.val - i.val)).length h_valid.2.1)).map
            (·.val) = [0, ((u.drop i.val).take (j.val - i.val)).length] := by
            have h_len_eq : ((u.drop i.val).take (j.val - i.val)).length = j.val - i.val := by
              have := j.isLt
              rw [List.length_take, List.length_drop]
              omega
            have hs_sorted : List.Pairwise (· < ·) (splitIndices s) := splitIndices_sorted s
            obtain ⟨hi, hj, hij, _, h_adj⟩ := partitionIndices_props hs_sorted hp
            have h_max_val :
                (Finset.max' Finset.univ Finset.univ_nonempty : Fin h).val = h - 1 := by
              have := (Finset.max' Finset.univ Finset.univ_nonempty : Fin h).isLt
              have := Finset.le_max' Finset.univ (⟨h - 1, by omega⟩ : Fin h) (Finset.mem_univ _)
              grind
            let w := (u.drop i.val).take (j.val - i.val)
            let w_len := w.length
            have h_len_eq : w_len = j.val - i.val := by
              have := j.isLt
              dsimp [w_len, w]
              rw [List.length_take, List.length_drop]
              omega
            have hij_val : i.val < j.val := hij
            have hw_eq : i.val + w_len = j.val := by omega
            have h_child_ext : ∀ x : Fin (w_len + 1),
                x ∈ splitIndices (restrictSplit s i.val w_len (by omega)) ↔
                x.val = 0 ∨ x.val = w_len := by
              intro x
              simp only [splitIndices, restrictSplit, List.mem_filter, List.mem_finRange,
                true_and, Fin.val_eq_zero_iff]
              constructor
              · intro h_max
                have h_in_s : (⟨i.val + x.val, by omega⟩ : Fin _) ∈ splitIndices s := by
                  simp only [splitIndices]
                  grind
                have h_not_between := h_adj ⟨i.val + x.val, by omega⟩ h_in_s
                grind
              · rintro (h0 | hl)
                · have h_eq : (⟨i.val + x.val, by omega⟩ : Fin (u.length + 1)) = i := by
                    ext
                    simp
                    grind
                  simpa [h_eq, splitIndices] using hi
                · have h_eq : (⟨i.val + x.val, by omega⟩ : Fin (u.length + 1)) = j := by
                    ext
                    grind
                  simpa [h_eq, splitIndices] using hj
            generalize hL : (splitIndices (restrictSplit s i.val w_len (by omega))).map (·.val) = L
            have hL_mem : ∀ x, x ∈ L ↔ x = 0 ∨ x = w_len := by
              intro x
              simp only [← hL, List.mem_map]
              constructor
              · rintro ⟨y, hy, rfl⟩
                exact (h_child_ext y).mp hy
              · rintro (rfl | rfl)
                · use ⟨0, by omega⟩
                  refine ⟨(h_child_ext ⟨0, by omega⟩).mpr (Or.inl rfl), rfl⟩
                · use ⟨w_len, by omega⟩
                  refine ⟨(h_child_ext ⟨w_len, by omega⟩).mpr (Or.inr rfl), rfl⟩
            have hL_nodup : L.Nodup := by
              rw [← hL]
              have h1 : List.Nodup (List.finRange (w_len + 1)) := List.nodup_finRange _
              have h2 : List.Nodup (splitIndices (restrictSplit s i.val w_len (by omega))) :=
                List.Nodup.filter _ h1
              exact List.Nodup.map (fun _ _ h => Fin.ext h) h2
            have hL_sorted : List.Pairwise (· < ·) L := by
              rw [← hL]
              have hs_w_sorted : List.Pairwise (· < ·)
                  (splitIndices (restrictSplit s i.val w_len (by omega))) := splitIndices_sorted _
              have h_mono : ∀ {a b : Fin (w_len + 1)}, a < b → a.val < b.val := fun h => h
              have h1 : List.Pairwise (fun a b => a.val < b.val)
                  (splitIndices (restrictSplit s i.val w_len (by omega))) :=
                List.Pairwise.imp (@h_mono) hs_w_sorted
              exact List.pairwise_map.mpr h1
            have h_w_pos : 0 < w_len := by omega
            match L with
            | [a, b] =>
              obtain ⟨ha, hb⟩ : _ ∧ _ := ⟨(hL_mem a).mp (by simp), (hL_mem b).mp (by simp)⟩
              have h_sorted : a < b := by
                have hp : List.Pairwise (· < ·) [a, b] := hL_sorted
                simp only [List.pairwise_cons, List.mem_singleton, forall_eq] at hp
                exact hp.1
              rcases ha with rfl | rfl
              · rcases hb with rfl | rfl
                · omega
                · rfl
              · rcases hb with rfl | rfl <;> omega
            | [] =>
              have h_empty : 0 ∈ [] := (hL_mem 0).mpr (Or.inl rfl)
              contradiction
            | [a] =>
              have h0 : 0 ∈ [a] := (hL_mem 0).mpr (Or.inl rfl)
              have hw : w_len ∈ [a] := (hL_mem w_len).mpr (Or.inr rfl)
              simp only [List.mem_singleton] at h0 hw
              omega
            | a :: b :: c :: rest =>
              obtain ⟨ha, hb, hc⟩ : _ ∧ _ ∧ _ :=
                ⟨(hL_mem a).mp (by simp), (hL_mem b).mp (by simp), (hL_mem c).mp (by simp)⟩
              simp only [List.nodup_cons] at hL_nodup
              rcases ha with rfl | rfl
              · rcases hb with rfl | rfl
                · nomatch (hL_nodup.1 (by simp))
                · rcases hc with rfl | rfl
                  · nomatch (hL_nodup.2.1 (by grind))
                  · nomatch (hL_nodup.2.1 (by simp))
              · rcases hb with rfl | rfl
                · have hp : List.Pairwise (· < ·) (w_len :: 0 :: c :: rest) := hL_sorted
                  simp only [List.pairwise_cons] at hp
                  have h_neg : w_len < 0 := hp.1 0 (by simp)
                  omega
                · nomatch (hL_nodup.1 (by simp))
          rw [buildFactorizationTree]
          split
          · split <;> {
              dsimp [FactorizationTree.height]
              have : 0 < h := Fin.pos_iff_nonempty.mpr inferInstance
              omega
            }
          · dsimp only
            split
            · split <;> dsimp [FactorizationTree.height]
              · have : Nonempty (Fin (h - 1)) := ⟨⟨0, by omega⟩⟩
                exact le_trans (Nat.add_le_add_right (buildTree_height_bound eval _ _ _) 2)
                  (by omega)
              · have : 0 < h := Fin.pos_iff_nonempty.mpr inferInstance
                omega
            · rename_i h_not_idxs
              contradiction
        · dsimp [FactorizationTree.height]
          have : 0 < h := Fin.pos_iff_nonempty.mpr inferInstance
          omega
      have : 0 < h := Fin.pos_iff_nonempty.mpr inferInstance
      split <;> (dsimp [FactorizationTree.height] at h_max_bound ⊢; omega)
termination_by (h, u.length)


/-- Extracts the idempotent from a Ramsey tree
  whose split indices cover the entire word. -/
lemma extract_idempotent {A S : Type*} [Semigroup S] {h : ℕ} [Nonempty (Fin h)]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (u : List A) (s : Split (Fin (u.length + 1)) h)
    (hs_ramsey : IsRamsey (wordLabeling eval hmul u) s)
    (idxs : List (Fin (u.length + 1)))
    (h_idxs : ∀ i ∈ idxs, s i = Finset.max' Finset.univ Finset.univ_nonempty)
    (i0 i1 : Fin (u.length + 1)) (h0 : i0 ∈ idxs) (h1 : i1 ∈ idxs) (hlt : i0 < i1) :
    let L := wordLabeling eval hmul u
    let e := L.σ i0 i1
    e * e = e ∧ ∀ j0 j1, j0 ∈ idxs → j1 ∈ idxs → j0 < j1 → L.σ j0 j1 = e := by
  intros L e
  have h_rel01 : SplitRelation s i0 i1 := by
    dsimp [SplitRelation]
    exact ⟨by rw [h_idxs i0 h0, h_idxs i1 h1], fun z hz1 hz2 ↦ by
      have h_s_min : s (min i0 i1) = Finset.max' Finset.univ Finset.univ_nonempty := by
        rw [min_eq_left (le_of_lt hlt), h_idxs i0 h0]
      rw [h_s_min]
      exact Finset.le_max' _ _ (Finset.mem_univ _)⟩
  constructor
  · exact hs_ramsey.left i0 i1 hlt h_rel01
  · intros j0 j1 hj0 hj1 hlt_j
    have h_rel_j : SplitRelation s j0 j1 := by
      dsimp [SplitRelation]
      exact ⟨by rw [h_idxs j0 hj0, h_idxs j1 hj1], fun z hz1 hz2 ↦ by
        have h_s_min : s (min j0 j1) = Finset.max' Finset.univ Finset.univ_nonempty := by
          rw [min_eq_left (le_of_lt hlt_j), h_idxs j0 hj0]
        rw [h_s_min]
        exact Finset.le_max' _ _ (Finset.mem_univ _)⟩
    have h_rel_cross : SplitRelation s i0 j0 := by
      dsimp [SplitRelation]
      exact ⟨by rw [h_idxs i0 h0, h_idxs j0 hj0], fun z hz1 hz2 ↦ by
        have h_s_min : s (min i0 j0) = Finset.max' Finset.univ Finset.univ_nonempty := by
          obtain h | h := le_total i0 j0
          · rw [min_eq_left h, h_idxs i0 h0]
          · rw [min_eq_right h, h_idxs j0 hj0]
        rw [h_s_min]
        exact Finset.le_max' _ _ (Finset.mem_univ _)⟩
    exact (hs_ramsey.right i0 i1 j0 j1 hlt hlt_j h_rel01 h_rel_j h_rel_cross).symm

/-- A chunk of a word equals the corresponding
  sublist. -/
lemma chunk_eq {A : Type*} {u w : List A} {i : ℕ} (hw : ∃ j, w = (u.drop i).take (j - i))
    (x y : Fin (w.length + 1)) (hxy : x ≤ y) :
    (w.drop x.val).take (y.val - x.val) =
    (u.drop (i + x.val)).take (y.val - x.val) := by
  rcases hw with ⟨j, rfl⟩
  have h_ylt := y.isLt
  have h_len : ((u.drop i).take (j - i)).length = min (j - i) (u.drop i).length := List.length_take
  have h_min : min (y.val - x.val) (j - i - x.val) = y.val - x.val := by omega
  have h_eq : ((u.drop i).take (j - i)).drop x.val = (u.drop (i + x.val)).take (j - i - x.val) := by
    rw [List.drop_take, List.drop_drop]
    try rw [add_comm x.val i]
  rw [h_eq, List.take_take, h_min]

/-- A split relation on a restricted sub-interval
  lifts to a split relation on the original domain. -/
lemma shift_split_relation {n h : ℕ} (s : Split (Fin (n + 1)) h)
    {i len : ℕ} (h_bound : i + len ≤ n) (x y : Fin (len + 1))
    (hsr : SplitRelation (restrictSplit s i len h_bound) x y) :
    SplitRelation s ⟨i + x.val, by omega⟩ ⟨i + y.val, by omega⟩ := by
  exact ⟨hsr.1, fun z hz1 hz2 ↦ by
    have hsr2 := hsr.2
    rcases le_total x y with hxy | hxy
    · have hxy' : (⟨i + x.val, by omega⟩ : Fin (n + 1)) ≤ ⟨i + y.val, by omega⟩ :=
        Fin.le_iff_val_le_val.mpr (by have := Fin.le_iff_val_le_val.mp hxy; simp; grind)
      rw [min_eq_left hxy, max_eq_right hxy] at hsr2
      rw [min_eq_left hxy'] at hz1 ⊢
      rw [max_eq_right hxy'] at hz2
      have hi_le_z : i ≤ z.val := by
        have := Fin.le_iff_val_le_val.mp hz1
        simp
        grind
      let zw : Fin (len + 1) := ⟨z.val - i, by
        have := Fin.le_iff_val_le_val.mp hz2; have := y.isLt; simp; grind⟩
      have hx_zw : x ≤ zw := Fin.le_iff_val_le_val.mpr (by
        dsimp [zw]; have := Fin.le_iff_val_le_val.mp hz1; simp; grind)
      have hzw_y : zw ≤ y := Fin.le_iff_val_le_val.mpr (by
        dsimp [zw]; have := Fin.le_iff_val_le_val.mp hz2; simp; grind)
      have h_res := hsr2 zw hx_zw hzw_y
      rw [(Fin.ext (by dsimp [zw]; omega) : z = (⟨i + zw.val, by dsimp [zw]; omega⟩ : Fin (n + 1)))]
      exact h_res
    · have hyx' : (⟨i + y.val, by omega⟩ : Fin (n + 1)) ≤ ⟨i + x.val, by omega⟩ :=
        Fin.le_iff_val_le_val.mpr (by have := Fin.le_iff_val_le_val.mp hxy; simp; grind)
      rw [min_eq_right hxy, max_eq_left hxy] at hsr2
      rw [min_eq_right hyx'] at hz1 ⊢
      rw [max_eq_left hyx'] at hz2
      have hi_le_z : i ≤ z.val := by
        have := Fin.le_iff_val_le_val.mp hz1
        simp
        grind
      let zw : Fin (len + 1) := ⟨z.val - i, by
        have := Fin.le_iff_val_le_val.mp hz2; have := x.isLt; simp; grind⟩
      have hy_zw : y ≤ zw := Fin.le_iff_val_le_val.mpr (by
        dsimp [zw]; have := Fin.le_iff_val_le_val.mp hz1; simp; grind)
      have hzw_x : zw ≤ x := Fin.le_iff_val_le_val.mpr (by
        dsimp [zw]; have := Fin.le_iff_val_le_val.mp hz2; simp; grind)
      have h_res := hsr2 zw hy_zw hzw_x
      rw [(Fin.ext (by dsimp [zw]; omega) : z = (⟨i + zw.val, by dsimp [zw]; omega⟩ : Fin (n + 1)))]
      exact h_res⟩

/-- A restricted split preserves the Ramsey
  property on the corresponding sub-word. -/
lemma restrictSplit_ramsey {A S : Type*} [Semigroup S] {h : ℕ} [Nonempty (Fin h)]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (u : List A) (s : Split (Fin (u.length + 1)) h)
    (hs_ramsey : IsRamsey (wordLabeling eval hmul u) s)
    (i : ℕ) (w : List A) (h_bound : i + w.length ≤ u.length)
    (hw : ∃ j, w = (u.drop i).take (j - i) := by exact ⟨_, rfl⟩) :
    IsRamsey (wordLabeling eval hmul w) (restrictSplit s i w.length h_bound) := by
  constructor
  · intros x y hxy hsr
    have hx_b : i + x.val < u.length + 1 := by omega
    have hy_b : i + y.val < u.length + 1 := by omega
    have hxy_shift : (⟨i + x.val, hx_b⟩ : Fin (u.length + 1)) < ⟨i + y.val, hy_b⟩ := by
      simp only [Fin.mk_lt_mk]
      omega
    have h_eval := hs_ramsey.1 _ _ hxy_shift (shift_split_relation s h_bound x y hsr)
    dsimp [wordLabeling] at h_eval ⊢
    rw [chunk_eq hw x y (le_of_lt hxy)]
    have h_sub : (i + y.val) - (i + x.val) = y.val - x.val := by omega
    have h_eval_eq : (u.drop (i + x.val)).take (i + y.val - (i + x.val)) =
                     (u.drop (i + x.val)).take (y.val - x.val) := by rw [h_sub]
    rw [h_eval_eq] at h_eval
    exact h_eval
  · intros x y p q hxy hpq hsr1 hsr2 hsr3
    have hx_b : i + x.val < u.length + 1 := by omega
    have hy_b : i + y.val < u.length + 1 := by omega
    have hp_b : i + p.val < u.length + 1 := by omega
    have hq_b : i + q.val < u.length + 1 := by omega
    have hxy_shift : (⟨i + x.val, hx_b⟩ : Fin (u.length + 1)) < ⟨i + y.val, hy_b⟩ := by
      simp
      omega
    have hpq_shift : (⟨i + p.val, hp_b⟩ : Fin (u.length + 1)) < ⟨i + q.val, hq_b⟩ := by
      simp
      omega
    have h_eval := hs_ramsey.2 _ _ _ _ hxy_shift hpq_shift
      (shift_split_relation s h_bound x y hsr1)
      (shift_split_relation s h_bound p q hsr2)
      (shift_split_relation s h_bound x p hsr3)
    dsimp [wordLabeling] at h_eval ⊢
    rw [chunk_eq hw x y (le_of_lt hxy), chunk_eq hw p q (le_of_lt hpq)]
    have h_sub1 : (i + y.val) - (i + x.val) = y.val - x.val := by omega
    have h_sub2 : (i + q.val) - (i + p.val) = q.val - p.val := by omega
    have h_eval_eq1 : (u.drop (i + x.val)).take (i + y.val - (i + x.val)) =
                      (u.drop (i + x.val)).take (y.val - x.val) := by rw [h_sub1]
    have h_eval_eq2 : (u.drop (i + p.val)).take (i + q.val - (i + p.val)) =
                      (u.drop (i + p.val)).take (q.val - p.val) := by rw [h_sub2]
    rw [h_eval_eq1, h_eval_eq2] at h_eval
    exact h_eval

/-- Lowering the interior of a split preserves
  the Ramsey property. -/
lemma lowerSplitInterior_ramsey {A S : Type*} [Semigroup S] {h : ℕ} [Nonempty (Fin h)]
    [Nonempty (Fin (h - 1))]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (u : List A) (s : Split (Fin (u.length + 1)) h)
    (hs_ramsey : IsRamsey (wordLabeling eval hmul u) s) (_ : 1 < h)
    (h_interior : ∀ i : Fin (u.length + 1), (s i).val < h - 1) :
    IsRamsey (wordLabeling eval hmul u) (lowerSplitInterior s h_interior) := by
  have h_rel_eq : ∀ x y,
      SplitRelation (lowerSplitInterior s h_interior) x y ↔ SplitRelation s x y := by
    intro x y
    dsimp [SplitRelation, lowerSplitInterior]
    constructor
    · rintro ⟨h1, h2⟩
      have h1_val := congrArg Fin.val h1
      exact ⟨Fin.ext h1_val, fun z hz1 hz2 ↦
        Fin.le_iff_val_le_val.mpr (Fin.le_iff_val_le_val.mp (h2 z hz1 hz2))⟩
    · rintro ⟨h1, h2⟩
      have h1_val := congrArg Fin.val h1
      exact ⟨Fin.ext h1_val, fun z hz1 hz2 ↦
        Fin.le_iff_val_le_val.mpr (Fin.le_iff_val_le_val.mp (h2 z hz1 hz2))⟩
  exact ⟨fun x y hxy hsr => hs_ramsey.1 x y hxy ((h_rel_eq x y).mp hsr),
         fun x y p q hxy hpq hsr1 hsr2 hsr3 =>
           hs_ramsey.2 x y p q hxy hpq ((h_rel_eq x y).mp hsr1)
             ((h_rel_eq p q).mp hsr2) ((h_rel_eq x p).mp hsr3)⟩

/-- Children of an n-ary node in a Ramsey tree
  all evaluate to the same idempotent. -/
lemma nary_children_ramsey {A S : Type*} [Semigroup S] {h : ℕ} [Nonempty (Fin h)]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (u : List A) (hu : u ≠ []) (s : Split (Fin (u.length + 1)) h)
    (hs_ramsey : IsRamsey (wordLabeling eval hmul u) s)
    (children : List (FactorizationTree A))
    (h_children : ((partitionIndices (splitIndices s)).map fun ⟨i, j⟩ =>
        let w_len := j.val - i.val
        let w := (u.drop i.val).take w_len
        if h_valid : w.length < u.length ∧
            i.val + w.length ≤ u.length ∧
            w ≠ [] then
          let s_w : Split (Fin (w.length + 1)) h :=
            restrictSplit s i.val w.length (by exact h_valid.2.1)
          buildFactorizationTree eval w (by exact h_valid.2.2) s_w
        else
          FactorizationTree.leaf (u.head hu)) = children)
    (h_nonempty : children ≠ [])
    (h_not_idxs : (splitIndices s).map (·.val) ≠ [0, u.length]) :
    ∃ (e : S), e * e = e ∧ ∀ c ∈ children, eval (FactorizationTree.word c) = e := by
  generalize h_idx_eq : splitIndices s = idxs at h_children ⊢
  have h_idxs : ∀ i ∈ idxs, s i = Finset.max' Finset.univ Finset.univ_nonempty := by
    intro i hi
    rw [← h_idx_eq] at hi
    unfold splitIndices at hi
    rw [List.mem_filter] at hi
    exact of_decide_eq_true hi.right
  rcases idxs with _ | ⟨i0, _ | ⟨i1, rest⟩⟩
  · nomatch h_nonempty h_children.symm
  · nomatch h_nonempty h_children.symm
  · have h0 : i0 ∈ i0 :: i1 :: rest := by simp
    have h1 : i1 ∈ i0 :: i1 :: rest := by simp
    have h_sorted : List.Pairwise (· < ·) (i0 :: i1 :: rest) := by
      rw [← h_idx_eq]
      unfold splitIndices
      exact List.Pairwise.filter _ (List.sortedLT_finRange (u.length + 1) |>.pairwise)
    have hlt : i0 < i1 := List.pairwise_cons.1 h_sorted |>.1 i1 (by simp)
    obtain ⟨h_ee, h_all_pairs⟩ :=
      extract_idempotent eval hmul u s hs_ramsey (i0 :: i1 :: rest) h_idxs i0 i1 h0 h1 hlt
    use (wordLabeling eval hmul u).σ i0 i1
    constructor
    · exact h_ee
    · intro c hc
      simp only [← h_children, List.mem_map, Prod.exists] at hc
      rcases hc with ⟨j0, j1, hj_mem, hc_eq⟩
      simp only [← hc_eq]
      split
      · rename_i h_valid
        obtain ⟨hj0, hj1, hjlt, _, _⟩ := partitionIndices_props h_sorted hj_mem
        rw [buildTree_word_eq]
        have h_σ := h_all_pairs j0 j1 hj0 hj1 hjlt
        dsimp [wordLabeling, MultiplicativeLabeling.σ] at h_σ ⊢
        exact h_σ
      · rename_i h_valid_false
        obtain ⟨_, _, _, hj_len, _⟩ := partitionIndices_props h_sorted hj_mem
        have h_len : j1.val - j0.val < u.length := by
          by_contra h_ge
          push Not at h_ge
          have h_eq_u : j1.val - j0.val = u.length := by omega
          exact h_not_idxs (h_idx_eq.symm ▸ hj_len h_eq_u)
        have h_valid_true : ((u.drop j0.val).take (j1.val - j0.val)).length < u.length ∧
            j0.val + ((u.drop j0.val).take (j1.val - j0.val)).length ≤ u.length ∧
            ((u.drop j0.val).take (j1.val - j0.val)) ≠ [] := by
          have h_take_len : ((u.drop j0.val).take (j1.val - j0.val)).length = j1.val - j0.val := by
            rw [List.length_take, List.length_drop]
            exact min_eq_left (by omega)
          exact ⟨by omega, by omega, by
            rw [← List.length_pos_iff, h_take_len]
            omega⟩
        nomatch h_valid_false h_valid_true

/-- The tree built by `buildFactorizationTree`
  satisfies the Ramsey property. -/
theorem buildTree_isRamsey {A S : Type*} [Semigroup S] {h : ℕ} [Nonempty (Fin h)]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (u : List A) (hu : u ≠ []) (s : Split (Fin (u.length + 1)) h)
    (hs_ramsey : IsRamsey (wordLabeling eval hmul u) s) :
    IsRamseyTree eval (buildFactorizationTree eval u hu s) := by
  rw [buildFactorizationTree]
  split
  · split
    · apply IsRamseyTree.leaf
    · apply IsRamseyTree.binary <;> apply IsRamseyTree.leaf
  · dsimp only
    split
    · split
      · rename_i hh
        have h_nonempty : Nonempty (Fin (h - 1)) := ⟨⟨0, by omega⟩⟩
        apply IsRamseyTree.binary
        · apply IsRamseyTree.leaf
        · apply IsRamseyTree.binary
          · apply buildTree_isRamsey eval hmul _ _ _
              (lowerSplitInterior_ramsey eval hmul _ _
                (restrictSplit_ramsey eval hmul u s hs_ramsey 1 _ _) hh _)
          · apply IsRamseyTree.leaf
      · apply IsRamseyTree.binary <;> apply IsRamseyTree.leaf
    · rename_i h_not_idxs
      generalize h_children : ((partitionIndices (splitIndices s)).map fun ⟨i, j⟩ =>
        let w_len := j.val - i.val
        let w := (u.drop i.val).take w_len
        if h_valid : w.length < u.length ∧ i.val + w.length ≤ u.length ∧ w ≠ [] then
          let s_w : Split (Fin (w.length + 1)) h :=
            restrictSplit s i.val w.length (by exact h_valid.2.1)
          buildFactorizationTree eval w (by exact h_valid.2.2) s_w
        else
          FactorizationTree.leaf (u.head hu)) = children
      have h_all : ∀ c ∈ children, IsRamseyTree eval c := by
        intro c hc
        rw [← h_children] at hc
        simp only [List.mem_map, Prod.exists] at hc
        rcases hc with ⟨i, j, hp, rfl⟩
        split_ifs with h_valid
        · have h_take_len : (List.take (j.val - i.val) (u.drop i.val)).length < u.length := by
            omega
          exact buildTree_isRamsey eval hmul _ _ _
            (restrictSplit_ramsey eval hmul u s hs_ramsey i.val _ (by omega))
        · apply IsRamseyTree.leaf
      split
      · apply IsRamseyTree.binary <;> apply IsRamseyTree.leaf
      · rename_i c
        apply IsRamseyTree.binary <;> exact h_all c (by simp)
      · rename_i c1 c2
        apply IsRamseyTree.binary
        · exact h_all c1 (by simp)
        · exact h_all c2 (by simp)
      · rename_i c1 c2 c3 rest
        apply IsRamseyTree.nary
        · simp
        · exact fun c hc => h_all c hc
        · exact nary_children_ramsey eval hmul u hu s hs_ramsey _ h_children (by simp) h_not_idxs
termination_by (h, u.length)
decreasing_by
  all_goals simp_wf
  · have : 0 < h := Fin.pos_iff_nonempty.mpr inferInstance
    grind
  · grind

/-- Given a Ramsey split, one can construct a
  factorization tree with bounded height. -/
theorem exists_factorizationTree_of_split {A S : Type*} [Semigroup S]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (u : List A) (hu : u ≠ []) {h : ℕ} [Nonempty (Fin h)]
    (s : Split (Fin (u.length + 1)) h)
    (hs_ramsey : IsRamsey (wordLabeling eval hmul u) s) :
    ∃ (t : FactorizationTree A), t.word = u ∧
      t.height ≤ 3 * h - 1 ∧ IsRamseyTree eval t := by
  use buildFactorizationTree eval u hu s
  exact ⟨buildTree_word_eq eval u hu s,
         buildTree_height_bound eval u hu s,
         buildTree_isRamsey eval hmul u hu s hs_ramsey⟩

/-- **Simon's Factorization Forest Theorem:**
  Every word over a finite semigroup admits a
  factorization tree of height at most `3 * nS S`. -/
theorem factorization_forest {A S : Type*} [Semigroup S] [Fintype S]
    [Nonempty (Fin (nS S))]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (u : List A) (hu : u ≠ []) :
    ∃ (t : FactorizationTree A), t.word = u ∧
      t.height ≤ 3 * (nS S) - 1 ∧ IsRamseyTree eval t :=
  let ⟨s, _, hs_ramsey⟩ := simon_word eval hmul u
  exists_factorizationTree_of_split eval hmul u hu s hs_ramsey

end FactorizationForest
