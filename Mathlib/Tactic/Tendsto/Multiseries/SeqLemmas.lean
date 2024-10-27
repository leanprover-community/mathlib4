import Mathlib.Data.Seq.Seq
import Mathlib.Tactic.ApplyFun
import Mathlib.Tactic.Ring.RingNF

set_option linter.unusedVariables false

namespace Stream'

namespace Seq

universe u v w

@[simp]
theorem recOn_nil {α : Type u} {motive : Seq α → Sort v} {nil : motive .nil}
    {cons : (hd : α) → (tl : Seq α) → motive (.cons hd tl)} : Seq.nil.recOn nil cons = nil := by
  rfl

@[simp]
theorem recOn_cons {α : Type u} {motive : Seq α → Sort v} {nil : motive .nil}
    {cons : (hd : α) → (tl : Seq α) → motive (.cons hd tl)} {hd : α} (tl : Seq α) :
    (Seq.cons hd tl).recOn nil cons = cons hd tl := by
  rfl

@[simp]
theorem noConfusion {α : Type u} {hd : α} {tl : Seq α} : (cons hd tl) ≠ .nil := by
  intro h
  apply_fun head at h
  simp at h

@[simp]
theorem noConfusion' {α : Type u} {hd : α} {tl : Seq α} : .nil ≠ (cons hd tl) := by
  symm
  simp

theorem corec_nil {α : Type u} {β : Type u} (g : β → Option (α × β)) (b : β)
    (h : g b = .none) : corec g b = nil := by
  apply destruct_eq_nil
  simp [h]

theorem corec_cons {α : Type u} {β : Type u} {g : β → Option (α × β)} {b : β} {hd : α} {tl : β}
    (h : g b = .some (hd, tl)) : corec g b = cons hd (corec g tl) := by
  apply destruct_eq_cons
  simp [h]

theorem cons_eq_cons {α : Type u} {hd hd' : α} {tl tl' : Seq α} :
    (cons hd tl = cons hd' tl') ↔ (hd = hd' ∧ tl = tl') := by
  constructor
  · intro h
    constructor
    · apply_fun head at h
      simpa using h
    · apply_fun tail at h
      simpa using h
  · rintro ⟨h_hd, h_tl⟩
    congr

@[simp]
theorem get?_mem {α : Type u} {li : Seq α} {n : ℕ} {x : α} (h : li.get? n = .some x) : x ∈ li := by
  simp [Membership.mem, Seq.Mem, Any]
  exact ⟨n, h.symm⟩

theorem head_eq_some {α : Type u} {li : Seq α} {hd : α} (h : li.head = some hd) :
    li = cons hd li.tail := by
  apply destruct_eq_cons
  simp [destruct, ← head_dropn]
  use hd

theorem head_eq_none {α : Type u} {li : Seq α} (h : li.head = none) : li = nil := by
  revert h
  apply li.recOn
  · intro; rfl
  · intro hd tl h
    simp at h

@[simp]
theorem head_eq_none_iff {α : Type u} {li : Seq α} : li.head = none ↔ li = nil := by
  constructor
  · apply head_eq_none
  · intro h
    simp [h]

@[simp]
theorem val_eq_get {α : Type u} (li : Seq α) (n : ℕ) : li.val n = li.get? n := by
  rfl

section Drop

@[simp]
theorem drop_get? {α : Type u} {n m : ℕ} {li : Seq α} : (li.drop n).get? m = li.get? (n + m) := by
  induction n generalizing m with
  | zero => simp
  | succ k ih =>
    simp [Seq.get?_tail]
    rw [show k + 1 + m = k + (m + 1) by ring]
    apply ih

theorem drop_succ_cons {α : Type u} {hd : α} {tl : Seq α} {n : ℕ} :
    (cons hd tl).drop (n + 1) = tl.drop n := by
  rw [← dropn_tail]
  simp

@[simp]
theorem nil_dropn {α : Type u} {n : ℕ} : (@nil α).drop n = nil := by
  induction n with
  | zero =>
    simp
  | succ m ih =>
    simp [← dropn_tail, ih]

end Drop

section TerminatedAt

@[simp]
theorem nil_TerminatedAt {α : Type u} {n : ℕ} : (@nil α).TerminatedAt n := by
  simp [TerminatedAt]

@[simp]
theorem cons_not_TerminatedAt_zero {α : Type u} {hd : α} {tl : Seq α} :
    ¬(cons hd tl).TerminatedAt 0 := by
  simp [TerminatedAt]

@[simp]
theorem cons_TerminatedAt_succ {α : Type u} {hd : α} {tl : Seq α} {n : ℕ} :
    (cons hd tl).TerminatedAt (n + 1) ↔ tl.TerminatedAt n := by
  simp [TerminatedAt]

end TerminatedAt

section Take

@[simp]
theorem take_nil {α : Type u} {n : ℕ} : (nil (α := α)).take n = List.nil := by
  cases n <;> rfl

@[simp]
theorem take_zero {α : Type u} {li : Seq α} : li.take 0 = [] := by
  apply li.recOn
  · rfl
  · intro hd tl
    rfl

@[simp]
theorem take_succ {α : Type u} {n : ℕ} {hd : α} {tl : Seq α} :
    (cons hd tl).take (n + 1) = hd :: tl.take n := by
  rfl

theorem get_mem_take {α : Type u} {li : Seq α} {m n : ℕ} (h_mn : m < n) {x : α}
    (h_get : li.get? m = .some x) : x ∈ li.take n := by
  induction m generalizing n li with
  | zero =>
    obtain ⟨l, hl⟩ := Nat.exists_add_one_eq.mpr h_mn
    rw [← hl]
    rw [take, head_eq_some h_get]
    simp
  | succ k ih =>
    obtain ⟨l, hl⟩ := Nat.exists_eq_add_of_lt h_mn
    subst hl
    have : ∃ y, li.get? 0 = .some y := by
      apply ge_stable _ _ h_get
      simp
    obtain ⟨y, hy⟩ := this
    rw [take, head_eq_some hy]
    simp
    right
    apply ih (by omega)
    rwa [get?_tail]

theorem take_length_le {α : Type u} {li : Seq α} {n : ℕ} : (li.take n).length ≤ n := by
  induction n generalizing li with
  | zero => simp
  | succ m ih =>
    rw [take]
    cases li.destruct with
    | none => simp
    | some v =>
      obtain ⟨x, r⟩ := v
      simp
      apply ih

theorem take_drop {α : Type u} {li : Seq α} {n m : ℕ} :
    (li.take n).drop m = (li.drop m).take (n - m) := by
  induction m generalizing n li with
  | zero => simp
  | succ k ih =>
    apply li.recOn
    · simp
    intro hd tl
    cases n with
    | zero => simp
    | succ l =>
      simp only [take, destruct_cons, List.drop_succ_cons, Nat.reduceSubDiff]
      rw [ih]
      congr 1
      rw [drop_succ_cons]

end Take

section Fold

/-- Folds and stores intermediate values in Colist
[init, f init li.head, f (f init li.head) li.tail.head, ...]
-/
def fold {α : Type u} {β : Type v} (li : Seq α) (init : β) (f : β → α → β) : Seq β :=
  let g : β × Seq α → Option (β × (β × Seq α)) := fun (acc, x) =>
    match destruct x with
    | none => .none
    | some (hd, tl) => .some (f acc hd, f acc hd, tl)
  cons init <| corec g (init, li)

@[simp]
theorem fold_nil {α : Type u} {β : Type u} (init : β) (f : β → α → β) :
    nil.fold init f = cons init nil := by
  unfold fold
  simp [corec_nil]

@[simp]
theorem fold_cons {α : Type u} {β : Type u} (init : β) (f : β → α → β) (hd : α) (tl : Seq α) :
    (cons hd tl).fold init f = cons init (tl.fold (f init hd) f) := by
  unfold fold
  simp only
  congr
  rw [corec_cons]
  simp

@[simp]
theorem head_fold {α : Type u} {β : Type u} (init : β) (f : β → α → β) (li : Seq α) :
    (li.fold init f).head = init := by
  simp [fold]

end Fold

section Eq

/-- Coinduction principle for proving `a = b`. -/
theorem Eq.coind {α : Type u} {a b : Seq α}
    (motive : Seq α → Seq α → Prop)
    (h_survive : ∀ a b, motive a b →
      (∃ hd a_tl b_tl, a = cons hd a_tl ∧ b = cons hd b_tl ∧ motive a_tl b_tl) ∨
      (a = nil ∧ b = nil))
    (h : motive a b) : a = b := by
  apply Subtype.eq
  ext1 n
  simp [get]
  have : motive (a.drop n) (b.drop n) := by
    induction n with
    | zero =>
      simpa
    | succ m ih =>
      simp only [drop]
      specialize h_survive (a.drop m) (b.drop m) ih
      cases h_survive with
      | inl h =>
        obtain ⟨hd, a_tl, b_tl, h_a_eq, h_b_eq, h_tail⟩ := h
        rw [h_a_eq, h_b_eq]
        simpa
      | inr h =>
        rw [h.1, h.2] at ih ⊢
        simpa
  specialize h_survive _ _ this
  cases h_survive with
  | inl h =>
    obtain ⟨hd, a_tl, b_tl, h_a_eq, h_b_eq, _⟩ := h
    simp [← head_dropn, h_a_eq, h_b_eq]
  | inr h => simp [← head_dropn, h.1, h.2]

-- version where we can finish prove explicitly prove a = b without further coinduction
-- useful for edge cases
theorem Eq.coind_strong {α : Type u} {a b : Seq α}
    (motive : Seq α → Seq α → Prop)
    (h_survive : ∀ a b, motive a b →
      (a = b) ∨
      (∃ hd a_tl b_tl, a = cons hd a_tl ∧ b = cons hd b_tl ∧ (motive a_tl b_tl)))
    (h : motive a b) : a = b := by
  apply Subtype.eq
  ext1 n
  simp [get]
  have : motive (a.drop n) (b.drop n) ∨ (a.drop n) = (b.drop n) := by
    induction n with
    | zero =>
      left
      simpa
    | succ m ih =>
      simp only [drop]
      cases ih with
      | inl ih =>
        specialize h_survive (a.drop m) (b.drop m) ih
        cases h_survive with
        | inl h_eq =>
          right
          congr
        | inr h =>
          left
          obtain ⟨hd, a_tl, b_tl, h_a_eq, h_b_eq, h_tail⟩ := h
          rw [h_a_eq, h_b_eq]
          simpa
      | inr ih =>
        right
        congr
  cases this with
  | inl this =>
    specialize h_survive _ _ this
    cases h_survive with
    | inl h_eq =>
      simp [← head_dropn]
      congr
    | inr h =>
      obtain ⟨hd, a_tl, b_tl, h_a_eq, h_b_eq, _⟩ := h
      simp [← head_dropn, h_a_eq, h_b_eq]
  | inr this =>
    simp [← head_dropn]
    congr

end Eq


section Zip

-- Corecursively defined version
def zip' {α : Type u} {β : Type v} (a : Seq α) (b : Seq β) : Seq (α × β) :=
  let g : Seq α × Seq β → Option ((α × β) × (Seq α × Seq β)) := fun (x, y) =>
    match destruct x with
    | none => none
    | some (x_hd, x_tl) =>
      match destruct y with
      | none => none
      | some (y_hd, y_tl) =>
        some ((x_hd, y_hd), (x_tl, y_tl))
  corec g (a, b)

theorem zip_eq_zip' {α : Type u} {β : Type v} {a : Seq α} {b : Seq β} : zip a b = zip' a b := by
  let motive : Seq (α × β) → Seq (α × β) → Prop := fun x y =>
    ∃ (a : Seq α) (b : Seq β), x = a.zip b ∧ y = a.zip' b
  apply Eq.coind motive
  · intro a b ih
    simp only [motive] at ih ⊢
    obtain ⟨x, y, ha, hb⟩ := ih
    subst ha hb
    apply x.recOn
    · right
      constructor
      · simp [zip, zipWith]
        rfl
      · simp [zip', corec_nil]
    intro x_hd x_tl
    apply y.recOn
    · right
      constructor
      · simp [zip, zipWith]
        rfl
      · simp [zip', corec_nil]
    intro y_hd y_tl
    left
    use (x_hd, y_hd), x_tl.zip y_tl, x_tl.zip' y_tl
    constructor
    · simp [zip, zipWith]
      ext1 n
      cases n <;> simp
    constructor
    · simp [zip']
      rw [corec_cons]
      simp
    use ?_, ?_
    constructor <;> exact Eq.refl _
  · simp [motive]
    use a, b

@[simp]
theorem zip_nil_left {α : Type u} {β : Type v} (a : Seq α) : (nil (α := β)).zip a = .nil := by
  rfl

@[simp]
theorem zip_nil_right {α : Type u} {β : Type v} (a : Seq α) : a.zip (.nil (α := β)) = .nil := by
  rw [zip_eq_zip']
  simp [zip']
  rw [corec_nil]
  simp
  cases a.destruct <;> rfl

@[simp]
theorem cons_zip_cons {α : Type u} {β : Type v} (a_hd : α) (b_hd : β) (a_tl : Seq α) (b_tl : Seq β)
    : (cons a_hd a_tl).zip (cons b_hd b_tl) = cons (a_hd, b_hd) (a_tl.zip b_tl) := by
  rw [zip_eq_zip']
  simp [zip']
  rw [corec_cons, zip_eq_zip', zip']
  simp

theorem map_zip_left {α : Type u} {β : Type v} {γ : Type w} {a : Seq α} {b : Seq β} {f : α → γ} :
    (a.map f).zip b = (a.zip b).map fun (x, y) => (f x, y) := by
  ext1 i
  simp [map_get?, get?_zip]
  cases a.get? i
  · simp
  cases b.get? i
  · simp
  simp

end Zip


section Modify

def modify {α : Type u} (n : ℕ) (li : Seq α) (f : α → α) : Seq α where
  val := fun i =>
    if i = n then
      (li.val i).map f
    else
      li.val i
  property := by
    simp only [IsSeq]
    intro i h
    split_ifs with h_if
    · split_ifs at h
      · omega
      · rw [li.property h]
        rfl
    · split_ifs at h with h_if'
      · simp only [Option.map_eq_none'] at h
        exact li.property h
      · exact li.property h

-- recursively defined version
def modify' {α : Type u} (n : ℕ) (li : Seq α) (f : α → α) : Seq α :=
  match n, head li with
  | 0, .some x => cons (f x) (tail li)
  | _, .none => li
  | m + 1, .some x => cons x (modify m (tail li) f)

def set {α : Type u} (n : ℕ) (li : Seq α) (val : α) : Seq α :=
  modify n li (fun _ ↦ val)

theorem modify_eq_modify' {α : Type u} {n : ℕ} {li : Seq α} {f : α → α} :
    modify n li f = modify' n li f := by
  simp [modify, modify']
  cases n <;> (
    cases h_li : li.head with
    | none =>
      simp at h_li
      simp [h_li]
      rfl
    | some hd =>
      rw [head_eq_some h_li]
      simp
      ext1 i
      cases i <;> simp
  )

@[simp]
theorem cons_modify_zero {α : Type u} {f : α → α} {hd : α} {tl : Seq α} :
    (cons hd tl).modify 0 f = cons (f hd) tl := by
  rw [modify_eq_modify']
  simp [modify']

@[simp]
theorem cons_set_zero {α : Type u} {hd hd' : α} {tl : Seq α} :
    (cons hd tl).set 0 hd' = cons hd' tl := by
  simp [set]

@[simp]
theorem cons_modify_succ {α : Type u} {hd : α} {f : α → α} {n : ℕ} {tl : Seq α} :
    (cons hd tl).modify (n + 1) f = cons hd (tl.modify n f) := by
  rw [modify_eq_modify']
  simp [modify']

@[simp]
theorem cons_set_succ {α : Type u} {hd x : α} {n : ℕ} {tl : Seq α} :
    (cons hd tl).set (n + 1) x = cons hd (tl.set n x) := by
  simp [set]

theorem set_get_of_not_terminated {α : Type u} {li : Seq α} {x : α} {n : ℕ}
    (h_not_terminated : ¬ li.TerminatedAt n) :
    (li.set n x).get? n = x := by
  simp [set, modify]
  simp [TerminatedAt] at h_not_terminated
  cases h : li.get? n with
  | none => simp [h] at h_not_terminated
  | some => simp

theorem set_get_of_terminated {α : Type u} {li : Seq α} {x : α} {n : ℕ}
    (h_terminated : li.TerminatedAt n) :
    (li.set n x).get? n = .none := by
  simp [set, modify]
  simpa [TerminatedAt] using h_terminated

theorem set_get_stable {α : Type u} {li : Seq α} {x : α} {n m : ℕ}
    (h : n ≠ m) :
    (li.set m x).get? n = li.get? n := by
  simp [set, modify]
  intro h'
  exact (h h').elim

theorem set_dropn_stable_of_lt {α : Type u} {li : Seq α} {m n : ℕ} {x : α}
    (h : m < n) :
    (li.set m x).drop n = li.drop n := by
  ext1 i
  simp
  rw [set_get_stable]
  omega

end Modify

section All

-- Note: without `irreducible` attribute it is inconvenient to apply lemmas about it, because Lean
-- eagerly unfolds `All` and unifyes `p x` with the goal (even if the goal is in form `s.All p`).
@[irreducible]
def All {α : Type u} (s : Seq α) (p : α → Prop) : Prop := ∀ x ∈ s, p x

@[simp]
theorem all_nil {α : Type u} {p : α → Prop} : nil.All p := by
  simp [All]

@[simp]
theorem all_cons {α : Type u} {p : α → Prop} {hd : α} {tl : Seq α} :
    ((cons hd tl).All p) ↔ p hd ∧ tl.All p := by
  simp [All]

theorem all_get {α : Type u} {p : α → Prop} {li : Seq α} (h : li.All p) {n : ℕ} :
    (li.get? n).elim True p := by
  cases h_get : li.get? n with
  | none => simp
  | some x =>
    simp
    unfold All at h
    apply h
    exact get?_mem h_get

theorem all_of_get {α : Type u} {p : α → Prop} {li : Seq α} (h : ∀ n, (li.get? n).elim True p) :
    li.All p := by
  simp [All, Membership.mem, Seq.Mem, Any, get]
  intro x i hx
  specialize h i
  simpa [← hx] using h

theorem All.coind {α : Type u} {li : Seq α} {p : α → Prop}
    (motive : Seq α → Prop)
    (h_cons : ∀ hd tl, motive (cons hd tl) → p hd ∧ motive tl)
    (h : motive li) : li.All p := by
  apply all_of_get
  intro n
  have : (li.get? n).elim True p ∧ motive (li.drop n) := by
    induction n with
    | zero =>
      cases h1 : get? li 0 with
      | none =>
        constructor
        · simp
        · simpa
      | some hd =>
        simp
        have := head_eq_some h1
        specialize h_cons hd li.tail (this ▸ h)
        constructor
        · exact h_cons.left
        · exact h
    | succ m ih =>
      simp at ih
      simp only [drop, ← head_dropn]
      revert ih
      generalize li.drop m = t
      apply t.recOn
      · simp
      · intro hd tl
        simp
        intro h1 h2
        have : motive tl := by
          specialize h_cons hd tl h2
          exact h_cons.right
        constructor
        · cases h_head : tl.head with
          | none => simp
          | some tl_hd =>
            have h_tl_cons := head_eq_some h_head
            specialize h_cons tl_hd tl.tail (h_tl_cons ▸ this)
            simp
            exact h_cons.left
        · assumption
  exact this.left

-- Can be easily proved by definition but I want to use coinduction everywhere
theorem all_mp {α : Type u} {p q : α → Prop} (h : ∀ a, p a → q a) {li : Seq α} (hp : li.All p) :
    li.All q := by
  let motive : Seq α → Prop := fun x => x.All p
  apply All.coind motive
  · intro hd tl ih
    simp [motive] at ih
    constructor
    · exact h _ ih.left
    · simp [motive]
      exact ih.right
  · exact hp

theorem map_all_iff {α : Type u} {β : Type u} {f : α → β} {p : β → Prop} {li : Seq α} :
    (li.map f).All p ↔ li.All (p ∘ f) := by
  constructor
  · intro h
    let motive : Seq α → Prop := fun x => (map f x).All p
    apply All.coind motive _ h
    · intro hd tl ih
      simp [motive] at ih
      exact ih
  · intro h
    let motive : Seq β → Prop := fun x => ∃ (y : Seq α), x = y.map f ∧ y.All (p ∘ f)
    apply All.coind motive
    · intro hd tl ih
      simp [motive] at ih
      obtain ⟨y, hx_eq, hy⟩ := ih
      revert hx_eq hy
      apply y.recOn
      · intro hx_eq
        simp at hx_eq
      · intro y_hd y_tl hx_eq hy
        simp [cons_eq_cons] at hx_eq hy
        constructor
        · convert hy.left
          exact hx_eq.left
        · simp [motive]
          use y_tl
          constructor
          · exact hx_eq.right
          · exact hy.right
    · simp [motive]
      use li

theorem take_all {α : Type u} {li : Seq α} {p : α → Prop} (h_all : li.All p) {n : ℕ} :
    ∀ x ∈ li.take n, p x := by
  intro x hx
  induction n generalizing li with
  | zero => simp [take] at hx
  | succ m ih =>
    simp [take] at hx
    revert h_all hx
    apply li.recOn
    · intro _ hx
      simp at hx
    · intro hd tl h_all hx
      simp at hx h_all
      cases hx with
      | inl hx =>
        rw [hx]
        exact h_all.left
      | inr hx =>
        exact ih h_all.right hx

theorem set_all {α : Type u} {p : α → Prop} {li : Seq α} (h_all : li.All p) {n : ℕ} {x : α}
    (hx : p x) : (li.set n x).All p := by
  apply all_of_get
  intro m
  by_cases h_nm : n = m
  · subst h_nm
    by_cases h_term : li.TerminatedAt n
    · rw [set_get_of_terminated h_term]
      simp
    · rw [set_get_of_not_terminated h_term]
      simpa
  · rw [set_get_stable]
    · exact all_get h_all
    · omega

end All

section Sorted

def Sorted {α : Type u} (r : α → α → Prop) (li : Seq α) : Prop :=
  ∀ i j x y, i < j → li.get? i = .some x → li.get? j = .some y → r x y

theorem Sorted.nil {α : Type u} {r : α → α → Prop} : Sorted r (.nil (α := α)) := by
  simp [Sorted]

theorem Sorted.cons {α : Type u} {r : α → α → Prop} [IsTrans _ r] {hd : α} {tl : Seq α}
    (h_lt : tl.head.elim True (r hd ·))
    (h_tl : Sorted r tl) : Sorted r (.cons hd tl) := by
  simp [Sorted] at *
  intro i j x y h_ij hx hy
  cases j with
  | zero =>
    simp at h_ij
  | succ k =>
    simp at hy
    cases i with
    | zero =>
      simp at hx
      subst hx
      revert h_lt h_tl hy
      apply tl.recOn
      · intro _ _ hy
        simp at hy
      · intro tl_hd tl_tl h_lt h_tl hy
        simp at h_lt
        cases k with
        | zero =>
          simp at hy
          rwa [← hy]
        | succ m =>
          simp at hy
          trans tl_hd
          · assumption
          specialize h_tl 0 (m + 1) tl_hd y (by omega)
          solve_by_elim
    | succ n =>
      exact h_tl n k x y (by omega) hx hy

theorem Sorted.coind {α : Type u} {r : α → α → Prop} [IsTrans _ r] (motive : Seq α → Prop)
    (h_survive : ∀ hd tl, motive (.cons hd tl) → tl.head.elim True (r hd ·) ∧ motive tl)
    {li : Seq α} (h : motive li) : Sorted r li := by
  have h_all : ∀ n, motive (li.drop n) := by
    intro n
    induction n with
    | zero => simpa
    | succ m ih =>
      simp only [drop]
      generalize li.drop m = t at *
      revert ih
      apply t.recOn
      · simp
      · intro hd tl ih
        exact (h_survive hd tl ih).right
  simp [Sorted]
  intro i j x y h_ij hx hy
  replace h_ij := Nat.exists_eq_add_of_lt h_ij
  obtain ⟨k, hj⟩ := h_ij
  rw [Nat.add_assoc, Nat.add_comm] at hj
  subst hj
  induction k generalizing y with
  | zero =>
    simp only [Nat.zero_add, Nat.add_comm] at hy
    simp [drop, ← head_dropn] at hx hy
    specialize h_all i
    generalize li.drop i = t at *
    revert hx hy h_all
    apply t.recOn
    · simp
    intro hd tl hx hy h_all
    specialize h_survive hd tl h_all
    simp at hx hy
    simp [hy, hx] at h_survive
    exact h_survive.left
  | succ l ih =>
    simp at hx hy ih
    rw [show l + 1 + 1 + i = l + 1 + i + 1 by omega] at hy
    simp only [drop, ← head_dropn] at hx hy ih
    specialize h_all (l + 1 + i)
    generalize li.drop (l + 1 + i) = t at *
    revert ih hy h_all
    apply t.recOn
    · simp
    intro hd tl hy ih h_all
    specialize h_survive hd tl h_all
    simp at ih hy
    simp [hy] at h_survive
    trans hd
    exacts [ih, h_survive.left]

theorem Sorted_cons {α : Type u} {r : α → α → Prop} {hd : α} {tl : Seq α}
    (h : Sorted r (.cons hd tl)) :
    tl.head.elim True (r hd ·) ∧ Sorted r tl := by
  simp [Sorted] at *
  constructor
  · revert h
    apply tl.recOn
    · simp
    intro tl_hd tl_tl h
    specialize h 0 1 hd tl_hd (by omega)
    simpa using h
  · intro i j
    specialize h (i + 1) (j + 1)
    simpa using h

theorem Sorted_tail {α : Type u} {r : α → α → Prop} {li : Seq α} (h : li.Sorted r) :
    li.tail.Sorted r := by
  revert h
  apply li.recOn
  · simp
  · intro hd tl h
    simp
    exact (Sorted_cons h).right

theorem Sorted_tail' {α : Type u} {r : α → α → Prop} {li : Seq α} (h : li.Sorted r) {n : ℕ} :
    (li.drop n).Sorted r := by
  induction n with
  | zero => simpa
  | succ m ih =>
    simp only [drop]
    exact Sorted_tail ih

end Sorted

section AsLong

-- Meaning: if `a` exhausted then `b` too. Or, equivalentelly, `a` is not exhausted before `b`.
def atLeastAsLongAs {α : Type u} {β : Type v} (a : Seq α) (b : Seq β) : Prop :=
  ∀ n, a.TerminatedAt n → b.TerminatedAt n

-- TODO: prove using coinduction
@[simp]
theorem atLeastAsLongAs_nil {α : Type u} {β : Type v} {a : Seq α} :
    a.atLeastAsLongAs (.nil (α := β)) := by
  unfold atLeastAsLongAs
  simp

theorem atLeastAsLongAs_cons {α : Type u} {β : Type v} {a : Seq α} {hd : β} {tl : Seq β}
    (h : a.atLeastAsLongAs (cons hd tl)) : ∃ hd' tl', a = cons hd' tl' := by
  revert h
  apply a.recOn
  · intro h
    unfold atLeastAsLongAs at h
    simp at h
    specialize h 0
    simp [TerminatedAt] at h
  · intro hd' tl' _
    use hd'
    use tl'

@[simp]
theorem cons_atLeastAsLongAs_cons {α : Type u} {β : Type v} {a_hd : α} {a_tl : Seq α} {b_hd : β}
    {b_tl : Seq β} :
    (cons a_hd a_tl).atLeastAsLongAs (cons b_hd b_tl) ↔ a_tl.atLeastAsLongAs b_tl := by
  constructor
  · intro h
    simp [atLeastAsLongAs] at *
    intro n
    specialize h (n + 1)
    simpa using h
  · intro h
    simp [atLeastAsLongAs] at *
    intro n
    cases n with
    | zero => simp
    | succ m =>
      specialize h m
      simpa

theorem atLeastAsLongAs_map {α : Type v} {β : Type v} {γ : Type w} {f : β → γ} {a : Seq α}
    {b : Seq β} (h : a.atLeastAsLongAs b):
    a.atLeastAsLongAs (b.map f) := by
  simp [atLeastAsLongAs] at h ⊢
  intro n ha
  specialize h n ha
  simpa [TerminatedAt] using h

-- very bad proof. May be possible to do everything in a single induction?
theorem atLeastAsLong.coind {α : Type u} {β : Type v} (motive : Seq α → Seq β → Prop)
    (h_survive : ∀ a b, motive a b →
      (∀ b_hd b_tl, (b = cons b_hd b_tl) → ∃ a_hd a_tl, a = cons a_hd a_tl ∧ motive a_tl b_tl))
    {a : Seq α} {b : Seq β} (h : motive a b) : a.atLeastAsLongAs b := by
  simp only [atLeastAsLongAs]
  intro n
  have : b.drop n ≠ .nil → motive (a.drop n) (b.drop n) := by
    intro hb
    induction n with
    | zero =>
      simpa
    | succ m ih =>
      simp only [drop] at hb ⊢
      generalize a.drop m = ta at *
      generalize b.drop m = tb at *
      revert hb ih
      apply tb.recOn
      · intro hb ih
        simp at hb
      · intro tb_hd tb_tl hb ih
        simp at ih
        specialize h_survive ta (cons tb_hd tb_tl) ih _ _ (by rfl)
        obtain ⟨a_hd, a_tl, ha, h_tail⟩ := h_survive
        subst ha
        simpa
  simp [TerminatedAt, ← head_dropn]
  intro hb
  contrapose hb
  specialize this hb
  specialize h_survive _ _ this
  generalize b.drop n = tb at *
  revert hb h_survive
  apply tb.recOn
  · simp
  · intro tb_hd tb_tl _ h_survive
    specialize h_survive _ _ (by rfl)
    obtain ⟨a_hd, a_tl, ha, _⟩ := h_survive
    rw [ha]
    simp

end AsLong

end Seq

end Stream'
