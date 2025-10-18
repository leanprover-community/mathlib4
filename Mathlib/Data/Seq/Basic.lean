/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Vasilii Nesterov
-/
import Mathlib.Data.Seq.Defs
import Mathlib.Data.ENat.Basic
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ApplyFun

/-!
# Basic properties of sequences (possibly infinite lists)

This file provides some basic lemmas about possibly infinite lists represented by the
type `Stream'.Seq`.
-/

universe u v w

namespace Stream'

namespace Seq

variable {α : Type u} {β : Type v} {γ : Type w}

section length

theorem length'_of_terminates {s : Seq α} (h : s.Terminates) :
    s.length' = s.length h := by
  simp [length', h]

theorem length'_of_not_terminates {s : Seq α} (h : ¬ s.Terminates) :
    s.length' = ⊤ := by
  simp [length', h]

@[simp]
theorem length_nil : length (nil : Seq α) terminates_nil = 0 := rfl

@[simp]
theorem length'_nil : length' (nil : Seq α) = 0 := by
  simp -implicitDefEqProofs [length']

theorem length_cons {x : α} {s : Seq α} (h : s.Terminates) :
    (cons x s).length (terminates_cons_iff.mpr h) = s.length h + 1 := by
  apply Nat.find_comp_succ
  simp

@[simp]
theorem length'_cons (x : α) (s : Seq α) :
    (cons x s).length' = s.length' + 1 := by
  by_cases h : (cons x s).Terminates <;> have h' := h <;> rw [terminates_cons_iff] at h'
  · simp [length'_of_terminates h, length'_of_terminates h', length_cons h']
  · simp [length'_of_not_terminates h, length'_of_not_terminates h']

@[simp]
theorem length_eq_zero {s : Seq α} {h : s.Terminates} :
    s.length h = 0 ↔ s = nil := by
  simp [length, TerminatedAt]

@[simp]
theorem length'_eq_zero_iff_nil (s : Seq α) :
    s.length' = 0 ↔ s = nil := by
  cases s <;> simp

theorem length'_ne_zero_iff_cons (s : Seq α) :
    s.length' ≠ 0 ↔ ∃ x s', s = cons x s' := by
  cases s <;> simp

/-- The statement of `length_le_iff'` does not assume that the sequence terminates. For a
simpler statement of the theorem where the sequence is known to terminate see `length_le_iff`. -/
theorem length_le_iff' {s : Seq α} {n : ℕ} :
    (∃ h, s.length h ≤ n) ↔ s.TerminatedAt n := by
  simp only [length, Nat.find_le_iff, TerminatedAt, Terminates, exists_prop]
  refine ⟨?_, ?_⟩
  · rintro ⟨_, k, hkn, hk⟩
    exact le_stable s hkn hk
  · intro hn
    exact ⟨⟨n, hn⟩, ⟨n, le_rfl, hn⟩⟩

/-- The statement of `length_le_iff` assumes that the sequence terminates. For a
statement of the where the sequence is not known to terminate see `length_le_iff'`. -/
theorem length_le_iff {s : Seq α} {n : ℕ} {h : s.Terminates} :
    s.length h ≤ n ↔ s.TerminatedAt n := by
  rw [← length_le_iff']; simp [h]

theorem length'_le_iff {s : Seq α} {n : ℕ} :
    s.length' ≤ n ↔ s.TerminatedAt n := by
  by_cases h : s.Terminates
  · simpa [length'_of_terminates h] using length_le_iff
  · simpa [length'_of_not_terminates h] using forall_not_of_not_exists h n

/-- The statement of `lt_length_iff'` does not assume that the sequence terminates. For a
simpler statement of the theorem where the sequence is known to terminate see `lt_length_iff`. -/
theorem lt_length_iff' {s : Seq α} {n : ℕ} :
    (∀ h : s.Terminates, n < s.length h) ↔ ∃ a, a ∈ s.get? n := by
  simp only [Terminates, TerminatedAt, length, Nat.lt_find_iff, forall_exists_index, Option.mem_def,
    ← Option.ne_none_iff_exists', ne_eq]
  refine ⟨?_, ?_⟩
  · intro h hn
    exact h n hn n le_rfl hn
  · intro hn _ _ k hkn hk
    exact hn <| le_stable s hkn hk

/-- The statement of `length_le_iff` assumes that the sequence terminates. For a
statement of the where the sequence is not known to terminate see `length_le_iff'`. -/
theorem lt_length_iff {s : Seq α} {n : ℕ} {h : s.Terminates} :
    n < s.length h ↔ ∃ a, a ∈ s.get? n := by
  rw [← lt_length_iff']; simp [h]

theorem lt_length'_iff {s : Seq α} {n : ℕ} :
    n < s.length' ↔ ∃ a, a ∈ s.get? n := by
  by_cases h : s.Terminates
  · simpa [length'_of_terminates h] using lt_length_iff
  · simp only [length'_of_not_terminates h, ENat.coe_lt_top, Option.mem_def, true_iff]
    rw [not_terminates_iff] at h
    rw [← Option.isSome_iff_exists]
    exact h n

end length

section OfStream

@[simp]
theorem ofStream_cons (a : α) (s) : ofStream (a::s) = cons a (ofStream s) := by
  apply Subtype.eq; simp only [ofStream, cons]; rw [Stream'.map_cons]

end OfStream

section OfList

theorem terminatedAt_ofList (l : List α) :
    (ofList l).TerminatedAt l.length := by
  simp [ofList, TerminatedAt]

theorem terminates_ofList (l : List α) : (ofList l).Terminates :=
  ⟨_, terminatedAt_ofList l⟩

end OfList

section Take

@[simp]
theorem take_nil {n : ℕ} : (nil (α := α)).take n = List.nil := by
  cases n <;> rfl

@[simp]
theorem take_zero {s : Seq α} : s.take 0 = [] := by
  cases s <;> rfl

@[simp]
theorem take_succ_cons {n : ℕ} {x : α} {s : Seq α} :
    (cons x s).take (n + 1) = x :: s.take n := rfl

@[simp]
theorem getElem?_take : ∀ (n k : ℕ) (s : Seq α),
    (s.take k)[n]? = if n < k then s.get? n else none
  | n, 0, s => by simp [take]
  | n, k+1, s => by
    rw [take]
    cases h : destruct s with
    | none =>
      simp [destruct_eq_none h]
    | some a =>
      match a with
      | (x, r) =>
        rw [destruct_eq_cons h]
        match n with
        | 0 => simp
        | n+1 => simp [List.getElem?_cons_succ, getElem?_take]

theorem get?_mem_take {s : Seq α} {m n : ℕ} (h_mn : m < n) {x : α}
    (h_get : s.get? m = some x) : x ∈ s.take n := by
  induction m generalizing n s with
  | zero =>
    obtain ⟨l, hl⟩ := Nat.exists_add_one_eq.mpr h_mn
    rw [← hl, take, head_eq_some h_get]
    simp
  | succ k ih =>
    obtain ⟨l, hl⟩ := Nat.exists_eq_add_of_lt h_mn
    subst hl
    have : ∃ y, s.get? 0 = some y := by
      apply ge_stable _ _ h_get
      simp
    obtain ⟨y, hy⟩ := this
    rw [take, head_eq_some hy]
    simp
    right
    apply ih (by cutsat)
    rwa [get?_tail]

theorem length_take_le {s : Seq α} {n : ℕ} : (s.take n).length ≤ n := by
  induction n generalizing s with
  | zero => simp
  | succ m ih =>
    rw [take]
    cases s.destruct with
    | none => simp
    | some v =>
      obtain ⟨x, r⟩ := v
      simpa using ih

theorem length_take_of_le_length {s : Seq α} {n : ℕ}
    (hle : ∀ h : s.Terminates, n ≤ s.length h) : (s.take n).length = n := by
  induction n generalizing s with
  | zero => simp [take]
  | succ n ih =>
      rw [take, destruct]
      let ⟨a, ha⟩ := lt_length_iff'.1 (fun ht => lt_of_lt_of_le (Nat.succ_pos _) (hle ht))
      simp [Option.mem_def.1 ha]
      rw [ih]
      intro h
      simp only [length, tail, Nat.le_find_iff, TerminatedAt, get?_mk, Stream'.tail]
      intro m hmn hs
      have := lt_length_iff'.1 (fun ht => (Nat.lt_of_succ_le (hle ht)))
      rw [le_stable s (Nat.succ_le_of_lt hmn) hs] at this
      simp at this

end Take

section ToList

@[simp]
theorem length_toList (s : Seq α) (h : s.Terminates) : (toList s h).length = length s h := by
  rw [toList, length_take_of_le_length]
  intro _
  exact le_rfl

@[simp]
theorem getElem?_toList (s : Seq α) (h : s.Terminates) (n : ℕ) : (toList s h)[n]? = s.get? n := by
  ext k
  simp only [toList, getElem?_take, Nat.lt_find_iff, length,
    Option.ite_none_right_eq_some, and_iff_right_iff_imp, TerminatedAt]
  intro h m hmn
  let ⟨a, ha⟩ := ge_stable s hmn h
  simp [ha]

@[simp]
theorem ofList_toList (s : Seq α) (h : s.Terminates) :
    ofList (toList s h) = s := by
  ext n; simp [ofList]

@[simp]
theorem toList_ofList (l : List α) : toList (ofList l) (terminates_ofList l) = l :=
  ofList_injective (by simp)

@[simp]
theorem toList_nil : toList (nil : Seq α) ⟨0, terminatedAt_zero_iff.2 rfl⟩ = [] := by
  ext; simp [nil, toList, const]

theorem getLast?_toList (s : Seq α) (h : s.Terminates) :
    (toList s h).getLast? = s.get? (s.length h - 1) := by
  rw [List.getLast?_eq_getElem?, getElem?_toList, length_toList]

end ToList

section Append

@[simp]
theorem cons_append (a : α) (s t) : append (cons a s) t = cons a (append s t) :=
  destruct_eq_cons <| by
    dsimp [append]; rw [corec_eq]
    dsimp [append]; rw [destruct_cons]

@[simp]
theorem nil_append (s : Seq α) : append nil s = s := by
  apply coinduction2; intro s
  dsimp [append]; rw [corec_eq]
  dsimp [append]
  cases s
  · trivial
  · rw [destruct_cons]
    dsimp
    exact ⟨rfl, _, rfl, rfl⟩

@[simp]
theorem append_nil (s : Seq α) : append s nil = s := by
  apply coinduction2 s; intro s
  cases s
  · trivial
  · rw [cons_append, destruct_cons, destruct_cons]
    dsimp
    exact ⟨rfl, _, rfl, rfl⟩

@[simp]
theorem append_assoc (s t u : Seq α) : append (append s t) u = append s (append t u) := by
  apply eq_of_bisim fun s1 s2 => ∃ s t u, s1 = append (append s t) u ∧ s2 = append s (append t u)
  · intro s1 s2 h
    exact
      match s1, s2, h with
      | _, _, ⟨s, t, u, rfl, rfl⟩ => by
        cases s <;> simp
        case nil =>
          cases t <;> simp
          case nil =>
            cases u <;> simp
            case cons _ u => refine ⟨nil, nil, u, ?_, ?_⟩ <;> simp
          case cons _ t => refine ⟨nil, t, u, ?_, ?_⟩ <;> simp
        case cons _ s => exact ⟨s, t, u, rfl, rfl⟩
  · exact ⟨s, t, u, rfl, rfl⟩

theorem of_mem_append {s₁ s₂ : Seq α} {a : α} (h : a ∈ append s₁ s₂) : a ∈ s₁ ∨ a ∈ s₂ := by
  have := h; revert this
  generalize e : append s₁ s₂ = ss; intro h; revert s₁
  apply mem_rec_on h _
  intro b s' o s₁
  cases s₁ with
  | nil =>
    intro m _
    apply Or.inr
    simpa using m
  | cons c t₁ =>
    intro m e
    have this := congr_arg destruct e
    rcases show a = c ∨ a ∈ append t₁ s₂ by simpa using m with e' | m
    · rw [e']
      exact Or.inl (mem_cons _ _)
    · obtain ⟨i1, i2⟩ := show c = b ∧ append t₁ s₂ = s' by simpa
      rcases o with e' | IH
      · simp [i1, e']
      · exact Or.imp_left (mem_cons_of_mem _) (IH m i2)

theorem mem_append_left {s₁ s₂ : Seq α} {a : α} (h : a ∈ s₁) : a ∈ append s₁ s₂ := by
  apply mem_rec_on h; intros; simp [*]

@[simp]
theorem ofList_append (l l' : List α) : ofList (l ++ l') = append (ofList l) (ofList l') := by
  induction l <;> simp [*]

@[simp]
theorem ofStream_append (l : List α) (s : Stream' α) :
    ofStream (l ++ₛ s) = append (ofList l) (ofStream s) := by
  induction l <;> simp [*, Stream'.nil_append_stream, Stream'.cons_append_stream]

end Append

section Map

@[simp]
theorem map_get? (f : α → β) : ∀ s n, get? (map f s) n = (get? s n).map f
  | ⟨_, _⟩, _ => rfl

@[simp]
theorem map_nil (f : α → β) : map f nil = nil :=
  rfl

@[simp]
theorem map_cons (f : α → β) (a) : ∀ s, map f (cons a s) = cons (f a) (map f s)
  | ⟨s, al⟩ => by apply Subtype.eq; dsimp [cons, map]; rw [Stream'.map_cons]; rfl

@[simp]
theorem map_id : ∀ s : Seq α, map id s = s
  | ⟨s, al⟩ => by
    apply Subtype.eq; dsimp [map]
    rw [Option.map_id, Stream'.map_id]

@[simp]
theorem map_tail (f : α → β) : ∀ s, map f (tail s) = tail (map f s)
  | ⟨s, al⟩ => by apply Subtype.eq; dsimp [tail, map]

theorem map_comp (f : α → β) (g : β → γ) : ∀ s : Seq α, map (g ∘ f) s = map g (map f s)
  | ⟨s, al⟩ => by
    apply Subtype.eq; dsimp [map]
    apply congr_arg fun f : _ → Option γ => Stream'.map f s
    ext ⟨⟩ <;> rfl

@[simp]
theorem terminatedAt_map_iff {f : α → β} {s : Seq α} {n : ℕ} :
    (map f s).TerminatedAt n ↔ s.TerminatedAt n := by
  simp [TerminatedAt]

@[simp]
theorem terminates_map_iff {f : α → β} {s : Seq α} :
    (map f s).Terminates ↔ s.Terminates := by
  simp [Terminates]

@[simp]
theorem length_map {s : Seq α} {f : α → β} (h : (s.map f).Terminates) :
    (s.map f).length h = s.length (terminates_map_iff.1 h) := by
  rw [length]
  congr
  ext
  simp

@[simp]
theorem length'_map {s : Seq α} {f : α → β} :
    (s.map f).length' = s.length' := by
  by_cases h : (s.map f).Terminates <;> have h' := h <;> rw [terminates_map_iff] at h'
  · rw [length'_of_terminates h, length'_of_terminates h', length_map h]
  · rw [length'_of_not_terminates h, length'_of_not_terminates h']

theorem mem_map (f : α → β) {a : α} : ∀ {s : Seq α}, a ∈ s → f a ∈ map f s
  | ⟨_, _⟩ => Stream'.mem_map (Option.map f)

theorem exists_of_mem_map {f} {b : β} : ∀ {s : Seq α}, b ∈ map f s → ∃ a, a ∈ s ∧ f a = b :=
  fun {s} h => by match s with
  | ⟨g, al⟩ =>
    let ⟨o, om, oe⟩ := @Stream'.exists_of_mem_map _ _ (Option.map f) (some b) g h
    rcases o with - | a
    · injection oe
    · injection oe with h'; exact ⟨a, om, h'⟩

@[simp]
theorem map_append (f : α → β) (s t) : map f (append s t) = append (map f s) (map f t) := by
  apply
    eq_of_bisim (fun s1 s2 => ∃ s t, s1 = map f (append s t) ∧ s2 = append (map f s) (map f t)) _
      ⟨s, t, rfl, rfl⟩
  intro s1 s2 h
  exact
    match s1, s2, h with
    | _, _, ⟨s, t, rfl, rfl⟩ => by
      cases s <;> simp
      case nil =>
        cases t <;> simp
        case cons _ t => refine ⟨nil, t, ?_, ?_⟩ <;> simp
      case cons _ s => exact ⟨s, t, rfl, rfl⟩

end Map

section Join


@[simp]
theorem join_nil : join nil = (nil : Seq α) :=
  destruct_eq_none rfl

-- Not a simp lemmas as `join_cons` is more general
theorem join_cons_nil (a : α) (S) : join (cons (a, nil) S) = cons a (join S) :=
  destruct_eq_cons <| by simp [join]

-- Not a simp lemmas as `join_cons` is more general
theorem join_cons_cons (a b : α) (s S) :
    join (cons (a, cons b s) S) = cons a (join (cons (b, s) S)) :=
  destruct_eq_cons <| by simp [join]

@[simp]
theorem join_cons (a : α) (s S) : join (cons (a, s) S) = cons a (append s (join S)) := by
  apply
    eq_of_bisim
      (fun s1 s2 => s1 = s2 ∨ ∃ a s S, s1 = join (cons (a, s) S) ∧ s2 = cons a (append s (join S)))
      _ (Or.inr ⟨a, s, S, rfl, rfl⟩)
  intro s1 s2 h
  exact
    match s1, s2, h with
    | s, _, Or.inl <| Eq.refl s => by
      cases s; · trivial
      · rw [destruct_cons]
        exact ⟨rfl, Or.inl rfl⟩
    | _, _, Or.inr ⟨a, s, S, rfl, rfl⟩ => by
      cases s
      · simp [join_cons_nil]
      · simpa [join_cons_cons, join_cons_nil] using Or.inr ⟨_, _, S, rfl, rfl⟩

@[simp]
theorem join_append (S T : Seq (Seq1 α)) : join (append S T) = append (join S) (join T) := by
  apply
    eq_of_bisim fun s1 s2 =>
      ∃ s S T, s1 = append s (join (append S T)) ∧ s2 = append s (append (join S) (join T))
  · intro s1 s2 h
    exact
      match s1, s2, h with
      | _, _, ⟨s, S, T, rfl, rfl⟩ => by
        cases s <;> simp
        case nil =>
          cases S <;> simp
          case nil =>
            cases T with
            | nil => simp
            | cons s T =>
              obtain ⟨a, s⟩ := s; simp only [join_cons, destruct_cons, true_and]
              refine ⟨s, nil, T, ?_, ?_⟩ <;> simp
          case cons s S =>
            obtain ⟨a, s⟩ := s
            simpa using ⟨s, S, T, rfl, rfl⟩
        case cons _ s => exact ⟨s, S, T, rfl, rfl⟩
  · refine ⟨nil, S, T, ?_, ?_⟩ <;> simp

end Join

section Drop

@[simp]
theorem drop_get? {n m : ℕ} {s : Seq α} : (s.drop n).get? m = s.get? (n + m) := by
  induction n generalizing m with
  | zero => simp [drop]
  | succ k ih =>
    simp [Seq.get?_tail, drop]
    convert ih using 2
    cutsat

theorem dropn_add (s : Seq α) (m) : ∀ n, drop s (m + n) = drop (drop s m) n
  | 0 => rfl
  | n + 1 => congr_arg tail (dropn_add s _ n)

theorem dropn_tail (s : Seq α) (n) : drop (tail s) n = drop s (n + 1) := by
  rw [Nat.add_comm]; symm; apply dropn_add

@[simp]
theorem head_dropn (s : Seq α) (n) : head (drop s n) = get? s n := by
  induction n generalizing s with
  | zero => rfl
  | succ n IH => rw [← get?_tail, ← dropn_tail]; apply IH

@[simp]
theorem drop_zero {s : Seq α} : s.drop 0 = s := rfl

@[simp]
theorem drop_succ_cons {x : α} {s : Seq α} {n : ℕ} :
    (cons x s).drop (n + 1) = s.drop n := by
  simp [← dropn_tail]

@[simp]
theorem drop_nil {n : ℕ} : (@nil α).drop n = nil := by
  induction n with
  | zero => simp [drop]
  | succ m ih => simp [← dropn_tail, ih]

@[simp]
theorem drop_length' {n : ℕ} {s : Seq α} :
    (s.drop n).length' = s.length' - n := by
  cases n with
  | zero => simp
  | succ n =>
    cases s with
    | nil => simp
    | cons x s =>
      simp only [drop_succ_cons, length'_cons, Nat.cast_add, Nat.cast_one]
      convert drop_length' using 1
      generalize s.length' = m
      enat_to_nat
      omega

theorem take_drop {s : Seq α} {n m : ℕ} :
    (s.take n).drop m = (s.drop m).take (n - m) := by
  induction m generalizing n s with
  | zero => simp [drop]
  | succ k ih =>
    cases s
    · simp
    cases n with
    | zero => simp
    | succ l =>
      simp only [take, destruct_cons, List.drop_succ_cons, Nat.reduceSubDiff]
      rw [ih]
      congr 1
      rw [drop_succ_cons]

end Drop

section ZipWith

@[simp]
theorem get?_zipWith (f : α → β → γ) (s s' n) :
    (zipWith f s s').get? n = Option.map₂ f (s.get? n) (s'.get? n) :=
  rfl

@[simp]
theorem get?_zip (s : Seq α) (t : Seq β) (n : ℕ) :
    get? (zip s t) n = Option.map₂ Prod.mk (get? s n) (get? t n) :=
  get?_zipWith _ _ _ _

@[simp]
theorem nats_get? (n : ℕ) : nats.get? n = some n :=
  rfl

@[simp]
theorem get?_enum (s : Seq α) (n : ℕ) : get? (enum s) n = Option.map (Prod.mk n) (get? s n) :=
  get?_zip _ _ _

@[simp]
theorem zipWith_nil_left {f : α → β → γ} {s} :
    zipWith f nil s = nil :=
  rfl

@[simp]
theorem zipWith_nil_right {f : α → β → γ} {s} :
    zipWith f s nil = nil := by
  ext1
  simp

@[simp]
theorem zipWith_cons_cons {f : α → β → γ} {x s x' s'} :
    zipWith f (cons x s) (cons x' s') = cons (f x x') (zipWith f s s') := by
  ext1 n
  cases n <;> simp

@[simp]
theorem zip_nil_left {s : Seq α} :
    zip (@nil α) s = nil :=
  rfl

@[simp]
theorem zip_nil_right {s : Seq α} :
    zip s (@nil α) = nil :=
  zipWith_nil_right

@[simp]
theorem zip_cons_cons {s s' : Seq α} {x x'} :
    zip (cons x s) (cons x' s') = cons (x, x') (zip s s') :=
  zipWith_cons_cons

@[simp]
theorem enum_nil : enum (nil : Seq α) = nil :=
  rfl

@[simp]
theorem enum_cons (s : Seq α) (x : α) :
    enum (cons x s) = cons (0, x) (map (Prod.map Nat.succ id) (enum s)) := by
  ext ⟨n⟩ : 1
  · simp
  · simp only [get?_enum, get?_cons_succ, map_get?, Option.map_map]
    congr

universe u' v'
variable {α' : Type u'} {β' : Type v'}

theorem zipWith_map (s₁ : Seq α) (s₂ : Seq β) (f₁ : α → α') (f₂ : β → β') (g : α' → β' → γ) :
    zipWith g (s₁.map f₁) (s₂.map f₂) = zipWith (fun a b ↦ g (f₁ a) (f₂ b)) s₁ s₂ := by
  ext1 n
  simp only [get?_zipWith, map_get?]
  cases s₁.get? n <;> cases s₂.get? n <;> simp

theorem zipWith_map_left (s₁ : Seq α) (s₂ : Seq β) (f : α → α') (g : α' → β → γ) :
    zipWith g (s₁.map f) s₂ = zipWith (fun a b ↦ g (f a) b) s₁ s₂ := by
  convert zipWith_map _ _ _ (@id β) _
  simp

theorem zipWith_map_right (s₁ : Seq α) (s₂ : Seq β) (f : β → β') (g : α → β' → γ) :
    zipWith g s₁ (s₂.map f) = zipWith (fun a b ↦ g a (f b)) s₁ s₂ := by
  convert zipWith_map _ _ (@id α) _ _
  simp

theorem zip_map (s₁ : Seq α) (s₂ : Seq β) (f₁ : α → α') (f₂ : β → β') :
    (s₁.map f₁).zip (s₂.map f₂) = (s₁.zip s₂).map (Prod.map f₁ f₂) := by
  ext1 n
  simp
  cases s₁.get? n <;> cases s₂.get? n <;> simp

theorem zip_map_left (s₁ : Seq α) (s₂ : Seq β) (f : α → α') :
    (s₁.map f).zip s₂ = (s₁.zip s₂).map (Prod.map f id) := by
  convert zip_map _ _ _ _
  simp

theorem zip_map_right (s₁ : Seq α) (s₂ : Seq β) (f : β → β') :
    s₁.zip (s₂.map f) = (s₁.zip s₂).map (Prod.map id f) := by
  convert zip_map _ _ _ _
  simp

end ZipWith

section Fold

@[simp]
theorem fold_nil (init : β) (f : β → α → β) :
    nil.fold init f = cons init nil := by
  unfold fold
  simp [corec_nil]

@[simp]
theorem fold_cons (init : β) (f : β → α → β) (x : α) (s : Seq α) :
    (cons x s).fold init f = cons init (s.fold (f init x) f) := by
  unfold fold
  dsimp only
  congr
  rw [corec_cons]
  simp

@[simp]
theorem fold_head (init : β) (f : β → α → β) (s : Seq α) :
    (s.fold init f).head = init := by
  simp [fold]

end Fold

section Update

variable (hd x : α) (tl : Seq α) (f : α → α)

theorem get?_update (s : Seq α) (n : ℕ) (m : ℕ) :
    (s.update n f).get? m = if m = n then (s.get? m).map f else s.get? m := by
  simp [update, Function.update]
  split_ifs with h_if
  · simp [h_if]
  · rfl

@[simp]
theorem update_nil (n : ℕ) : update nil n f = nil := by
  ext1 m
  simp [get?_update]

@[simp]
theorem set_nil (n : ℕ) (x : α) : set nil n x = nil := update_nil _ _

@[simp]
theorem update_cons_zero : (cons hd tl).update 0 f = cons (f hd) tl := by
  ext1 n
  cases n <;> simp [get?_update]

@[simp]
theorem set_cons_zero (hd' : α) : (cons hd tl).set 0 hd' = cons hd' tl :=
  update_cons_zero _ _ _

@[simp]
theorem update_cons_succ (n : ℕ) : (cons hd tl).update (n + 1) f = cons hd (tl.update n f) := by
  ext1 n
  cases n <;> simp [get?_update]

@[simp]
theorem set_cons_succ (n : ℕ) : (cons hd tl).set (n + 1) x = cons hd (tl.set n x) :=
  update_cons_succ _ _ _ _

theorem get?_set_of_not_terminatedAt {s : Seq α} {n : ℕ} (h_not_terminated : ¬ s.TerminatedAt n) :
    (s.set n x).get? n = x := by
  simpa [set, update, ← Option.ne_none_iff_exists'] using h_not_terminated

theorem get?_set_of_terminatedAt {s : Seq α} {n : ℕ} (h_terminated : s.TerminatedAt n) :
    (s.set n x).get? n = .none := by
  simpa [set, get?_update] using h_terminated

theorem get?_set_of_ne (s : Seq α) {m n : ℕ} (h : n ≠ m) : (s.set m x).get? n = s.get? n := by
  simp [set, get?_update, h]

theorem drop_set_of_lt (s : Seq α) {m n : ℕ} (h : m < n) : (s.set m x).drop n = s.drop n := by
  ext1 i
  simp [get?_set_of_ne _ _ (show n + i ≠ m by cutsat)]

end Update

section All

theorem all_cons {p : α → Prop} {hd : α} {tl : Seq α} (h_hd : p hd) (h_tl : ∀ x ∈ tl, p x) :
    (∀ x ∈ (cons hd tl), p x) := by
  simp only [mem_cons_iff, forall_eq_or_imp] at *
  exact ⟨h_hd, h_tl⟩

theorem all_get {p : α → Prop} {s : Seq α} (h : ∀ x ∈ s, p x) {n : ℕ} {x : α}
    (hx : s.get? n = .some x) :
    p x := by
  exact h _ (get?_mem hx)

theorem all_of_get {p : α → Prop} {s : Seq α} (h : ∀ n x, s.get? n = .some x → p x) :
    ∀ x ∈ s, p x := by
  simp only [mem_iff_exists_get?]
  grind

private lemma all_coind_drop_motive {s : Seq α} (motive : Seq α → Prop) (base : motive s)
    (step : ∀ hd tl, motive (.cons hd tl) → motive tl) (n : ℕ) :
    motive (s.drop n) := by
  induction n with
  | zero => simpa
  | succ m ih =>
    simp only [drop]
    generalize s.drop m = t at *
    cases t
    · simpa
    · exact step _ _ ih

/-- Coinductive principle for `All`. -/
theorem all_coind {s : Seq α} {p : α → Prop}
    (motive : Seq α → Prop) (base : motive s)
    (step : ∀ hd tl, motive (.cons hd tl) → p hd ∧ motive tl) :
    ∀ x ∈ s, p x := by
  apply all_of_get
  intro n
  have := all_coind_drop_motive motive base (fun hd tl ih ↦ (step hd tl ih).right) n
  rw [← head_dropn]
  generalize s.drop n = s' at this
  cases s' with
  | nil => simp
  | cons hd tl => simp [(step hd tl this).left]

theorem map_all_iff {β : Type u} {f : α → β} {p : β → Prop} {s : Seq α} :
    (∀ x ∈ (s.map f), p x) ↔ (∀ x ∈ s, (p ∘ f) x) := by
  refine ⟨fun _ _ hx ↦ ?_, fun _ _ hx ↦ ?_⟩
  · solve_by_elim [mem_map f hx]
  · obtain ⟨_, _, hx'⟩ := exists_of_mem_map hx
    rw [← hx']
    solve_by_elim

theorem take_all {s : Seq α} {p : α → Prop} (h_all : ∀ x ∈ s, p x) {n : ℕ} {x : α}
    (hx : x ∈ s.take n) : p x := by
  induction n generalizing s with
  | zero => simp [take] at hx
  | succ m ih =>
    cases s with
    | nil => simp at hx
    | cons hd tl =>
      simp only [take_succ_cons, List.mem_cons, mem_cons_iff, forall_eq_or_imp] at hx h_all
      rcases hx with (rfl | hx)
      exacts [h_all.left, ih h_all.right hx]

theorem set_all {p : α → Prop} {s : Seq α} (h_all : ∀ x ∈ s, p x) {n : ℕ} {x : α}
    (hx : p x) : ∀ y ∈ (s.set n x), p y := by
  intro y hy
  simp only [mem_iff_exists_get?] at hy
  obtain ⟨m, hy⟩ := hy
  rcases eq_or_ne n m with (rfl | h_nm)
  · by_cases h_term : s.TerminatedAt n
    · simp [get?_set_of_terminatedAt _ h_term] at hy
    · simp_all [get?_set_of_not_terminatedAt _ h_term]
  · rw [get?_set_of_ne _ _ h_nm.symm] at hy
    apply h_all _ (get?_mem hy.symm)

end All

section Pairwise

@[simp]
theorem Pairwise.nil {R : α → α → Prop} : Pairwise R (@nil α) := by
  simp [Pairwise]

theorem Pairwise.cons {R : α → α → Prop} {hd : α} {tl : Seq α}
    (h_hd : ∀ x ∈ tl, R hd x)
    (h_tl : Pairwise R tl) : Pairwise R (cons hd tl) := by
  simp only [Pairwise] at *
  intro i j h_ij x hx y hy
  cases j with
  | zero => simp at h_ij
  | succ k =>
    simp only [get?_cons_succ] at hy
    cases i with
    | zero =>
      simp only [get?_cons_zero, Option.mem_def, Option.some.injEq] at hx
      exact hx ▸ all_get h_hd hy
    | succ n => exact h_tl n k (by omega) x hx y hy

theorem Pairwise.cons_elim {R : α → α → Prop} {hd : α} {tl : Seq α}
    (h : Pairwise R (.cons hd tl)) : (∀ x ∈ tl, R hd x) ∧ Pairwise R tl := by
  simp only [Pairwise] at *
  refine ⟨?_, fun i j h_ij ↦ h (i + 1) (j + 1) (by omega)⟩
  intro x hx
  rw [mem_iff_exists_get?] at hx
  obtain ⟨n, hx⟩ := hx
  simpa [← hx] using h 0 (n + 1) (by omega)

@[simp]
theorem Pairwise_cons_nil {R : α → α → Prop} {hd : α} : Pairwise R (cons hd nil) := by
  apply Pairwise.cons <;> simp

theorem Pairwise_cons_cons_head {R : α → α → Prop} {hd tl_hd : α} {tl_tl : Seq α}
    (h : Pairwise R (cons hd (cons tl_hd tl_tl))) :
    R hd tl_hd := by
  simp only [Pairwise] at h
  simpa using h 0 1 Nat.one_pos

theorem Pairwise.cons_cons_of_trans {R : α → α → Prop} [IsTrans _ R] {hd tl_hd : α} {tl_tl : Seq α}
    (h_hd : R hd tl_hd)
    (h_tl : Pairwise R (.cons tl_hd tl_tl)) : Pairwise R (.cons hd (.cons tl_hd tl_tl)) := by
  apply Pairwise.cons _ h_tl
  simp only [mem_cons_iff, forall_eq_or_imp]
  exact ⟨h_hd, fun x hx ↦ Trans.simple h_hd ((cons_elim h_tl).left x hx)⟩


/-- Coinductive principle for `Pairwise`. -/
theorem Pairwise.coind {R : α → α → Prop} {s : Seq α}
    (motive : Seq α → Prop) (base : motive s)
    (step : ∀ hd tl, motive (.cons hd tl) → (∀ x ∈ tl, R hd x) ∧ motive tl) : Pairwise R s := by
  simp only [Pairwise]
  intro i j h_ij x hx y hy
  obtain ⟨k, hj⟩ := Nat.exists_eq_add_of_lt h_ij
  rw [← head_dropn] at hx
  rw [hj, ← head_dropn, Nat.add_assoc, dropn_add, head_dropn] at hy
  have := all_coind_drop_motive motive base (fun hd tl ih ↦ (step hd tl ih).right) i
  generalize s.drop i = s' at *
  cases s' with
  | nil => simp at hx
  | cons hd tl =>
    simp at hx hy
    exact hx ▸ all_get (step hd tl this).left hy

/-- Coinductive principle for `Pairwise` that assumes that `R` is transitive. Compared to
`Pairwise.coind`, this allows you to prove `R hd tl.head` instead of `tl.All (R hd ·)` in `step`.
-/
theorem Pairwise.coind_trans {R : α → α → Prop} [IsTrans α R] {s : Seq α}
    (motive : Seq α → Prop) (base : motive s)
    (step : ∀ hd tl, motive (.cons hd tl) → (∀ x ∈ tl.head, R hd x) ∧ motive tl) :
    Pairwise R s := by
  have h_succ {n} {x y} (hx : s.get? n = some x) (hy : s.get? (n + 1) = some y) : R x y := by
    rw [← head_dropn] at hx
    have := all_coind_drop_motive motive base (fun hd tl ih ↦ (step hd tl ih).right)
    exact (step x (s.drop (n + 1)) (head_eq_some hx ▸ this n)).left _ (by simpa)
  simp only [Pairwise]
  intro i j h_ij x hx y hy
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h_ij
  clear h_ij
  induction k generalizing y with
  | zero => exact h_succ hx hy
  | succ k ih =>
    obtain ⟨z, hz⟩ := ge_stable (m := i + k + 1) _ (by omega) hy
    exact _root_.trans (ih z hz) <| h_succ hz hy

theorem Pairwise_tail {R : α → α → Prop} {s : Seq α} (h : s.Pairwise R) :
    s.tail.Pairwise R := by
  cases s
  · simp
  · simp [h.cons_elim.right]

theorem Pairwise_drop {R : α → α → Prop} {s : Seq α} (h : s.Pairwise R) {n : ℕ} :
    (s.drop n).Pairwise R := by
  induction n with
  | zero => simpa
  | succ m ih => simp [drop, Pairwise_tail ih]

end Pairwise

/-- Coinductive principle for proving `b.length' ≤ a.length'` for two sequences `a` and `b`. -/
theorem at_least_as_long_as_coind {a : Seq α} {b : Seq β}
    (motive : Seq α → Seq β → Prop) (base : motive a b)
    (step : ∀ a b, motive a b →
      (∀ b_hd b_tl, (b = .cons b_hd b_tl) → ∃ a_hd a_tl, a = .cons a_hd a_tl ∧ motive a_tl b_tl)) :
    b.length' ≤ a.length' := by
  have (n) (hb : b.drop n ≠ .nil) : motive (a.drop n) (b.drop n) := by
    induction n with
    | zero => simpa
    | succ m ih =>
      simp only [drop] at hb ⊢
      generalize b.drop m = tb at *
      cases tb with
      | nil => simp at hb
      | cons tb_hd tb_tl =>
        simp only [ne_eq, cons_ne_nil, not_false_eq_true, forall_const] at ih
        obtain ⟨a_hd, a_tl, ha, h_tail⟩ := step (a.drop m) (.cons tb_hd tb_tl) ih _ _ rfl
        simpa [ha]
  by_cases ha : a.Terminates; swap
  · simp [length'_of_not_terminates ha]
  simp [length'_of_terminates ha, length'_le_iff]
  by_contra! hb
  have hb_cons : b.drop (a.length ha) ≠ .nil := by
    intro hb'
    simp only [← length'_eq_zero_iff_nil, drop_length', tsub_eq_zero_iff_le, length'_le_iff] at hb'
    contradiction
  specialize this (a.length ha) hb_cons
  generalize b.drop (a.length ha) = b' at *
  cases b' with
  | nil =>
    contradiction
  | cons b_hd b_tl =>
    obtain ⟨a_hd, a_tl, ha', _⟩ := step _ _ this _ _ rfl
    apply_fun length' at ha'
    simp only [drop_length', length'_of_terminates ha, tsub_self, length'_cons] at ha'
    generalize a_tl.length' = u at ha'
    enat_to_nat
    omega

instance : Functor Seq where map := @map

instance : LawfulFunctor Seq where
  id_map := @map_id
  comp_map := @map_comp
  map_const := rfl

end Seq

namespace Seq1

variable {α : Type u} {β : Type v} {γ : Type w}

open Stream'.Seq

/-- Convert a `Seq1` to a sequence. -/
def toSeq : Seq1 α → Seq α
  | (a, s) => Seq.cons a s

instance coeSeq : Coe (Seq1 α) (Seq α) :=
  ⟨toSeq⟩

/-- Map a function on a `Seq1` -/
def map (f : α → β) : Seq1 α → Seq1 β
  | (a, s) => (f a, Seq.map f s)

theorem map_pair {f : α → β} {a s} : map f (a, s) = (f a, Seq.map f s) := rfl

theorem map_id : ∀ s : Seq1 α, map id s = s
  | ⟨a, s⟩ => by simp [map]

/-- Flatten a nonempty sequence of nonempty sequences -/
def join : Seq1 (Seq1 α) → Seq1 α
  | ((a, s), S) =>
    match destruct s with
    | none => (a, Seq.join S)
    | some s' => (a, Seq.join (Seq.cons s' S))

@[simp]
theorem join_nil (a : α) (S) : join ((a, nil), S) = (a, Seq.join S) :=
  rfl

@[simp]
theorem join_cons (a b : α) (s S) :
    join ((a, Seq.cons b s), S) = (a, Seq.join (Seq.cons (b, s) S)) := by
  dsimp [join]; rw [destruct_cons]

/-- The `return` operator for the `Seq1` monad,
  which produces a singleton sequence. -/
def ret (a : α) : Seq1 α :=
  (a, nil)

instance [Inhabited α] : Inhabited (Seq1 α) :=
  ⟨ret default⟩

/-- The `bind` operator for the `Seq1` monad,
  which maps `f` on each element of `s` and appends the results together.
  (Not all of `s` may be evaluated, because the first few elements of `s`
  may already produce an infinite result.) -/
def bind (s : Seq1 α) (f : α → Seq1 β) : Seq1 β :=
  join (map f s)

@[simp]
theorem join_map_ret (s : Seq α) : Seq.join (Seq.map ret s) = s := by
  apply coinduction2 s; intro s; cases s <;> simp [ret]

@[simp]
theorem bind_ret (f : α → β) : ∀ s, bind s (ret ∘ f) = map f s
  | ⟨a, s⟩ => by simp [bind, map, map_comp, ret]

@[simp]
theorem ret_bind (a : α) (f : α → Seq1 β) : bind (ret a) f = f a := by
  simp only [bind, map, ret.eq_1, map_nil]
  obtain ⟨a, s⟩ := f a
  cases s <;> simp

@[simp]
theorem map_join' (f : α → β) (S) : Seq.map f (Seq.join S) = Seq.join (Seq.map (map f) S) := by
  apply
    Seq.eq_of_bisim fun s1 s2 =>
      ∃ s S,
        s1 = Seq.append s (Seq.map f (Seq.join S)) ∧ s2 = append s (Seq.join (Seq.map (map f) S))
  · intro s1 s2 h
    exact
      match s1, s2, h with
      | _, _, ⟨s, S, rfl, rfl⟩ => by
        cases s <;> simp
        case nil =>
          cases S <;> simp
          case cons x S =>
            obtain ⟨a, s⟩ := x
            simpa [map] using ⟨_, _, rfl, rfl⟩
        case cons _ s => exact ⟨s, S, rfl, rfl⟩
  · refine ⟨nil, S, ?_, ?_⟩ <;> simp

@[simp]
theorem map_join (f : α → β) : ∀ S, map f (join S) = join (map (map f) S)
  | ((a, s), S) => by cases s <;> simp [map]

@[simp]
theorem join_join (SS : Seq (Seq1 (Seq1 α))) :
    Seq.join (Seq.join SS) = Seq.join (Seq.map join SS) := by
  apply
    Seq.eq_of_bisim fun s1 s2 =>
      ∃ s SS,
        s1 = Seq.append s (Seq.join (Seq.join SS)) ∧ s2 = Seq.append s (Seq.join (Seq.map join SS))
  · intro s1 s2 h
    exact
      match s1, s2, h with
      | _, _, ⟨s, SS, rfl, rfl⟩ => by
        cases s <;> simp
        case nil =>
          cases SS <;> simp
          case cons S SS =>
            obtain ⟨s, S⟩ := S; obtain ⟨x, s⟩ := s
            simp only [Seq.join_cons, join_append, destruct_cons]
            cases s <;> simp
            case nil => exact ⟨_, _, rfl, rfl⟩
            case cons x s => refine ⟨Seq.cons x (append s (Seq.join S)), SS, ?_, ?_⟩ <;> simp
        case cons _ s => exact ⟨s, SS, rfl, rfl⟩
  · refine ⟨nil, SS, ?_, ?_⟩ <;> simp

@[simp]
theorem bind_assoc (s : Seq1 α) (f : α → Seq1 β) (g : β → Seq1 γ) :
    bind (bind s f) g = bind s fun x : α => bind (f x) g := by
  obtain ⟨a, s⟩ := s
  simp only [bind, map_pair, map_join]
  rw [← map_comp]
  simp only [show (fun x => join (map g (f x))) = join ∘ (map g ∘ f) from rfl]
  rw [map_comp _ join]
  generalize Seq.map (map g ∘ f) s = SS
  rcases map g (f a) with ⟨⟨a, s⟩, S⟩
  induction s using recOn with | nil => ?_ | cons x s_1 => ?_ <;>
  induction S using recOn with | nil => simp | cons x_1 s_2 => ?_
  · obtain ⟨x, t⟩ := x_1
    cases t <;> simp
  · obtain ⟨y, t⟩ := x_1; simp

instance monad : Monad Seq1 where
  map := @map
  pure := @ret
  bind := @bind

instance lawfulMonad : LawfulMonad Seq1 := LawfulMonad.mk'
  (id_map := @map_id)
  (bind_pure_comp := @bind_ret)
  (pure_bind := @ret_bind)
  (bind_assoc := @bind_assoc)

end Seq1

end Stream'
