import Mathlib.Data.Nat.Defs
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.ApplyFun
import Mathlib.Tactic.ExtractLets

universe u v w

namespace TendstoTactic

-- (kernel) invalid nested inductive datatype 'Option', nested inductive datatypes parameters cannot contain local variables.

-- inductive PreMS' : ℕ → Type where
-- | const : ℝ → PreMS' 0
-- | colist {n : ℕ} (fn : ℕ → Option (ℝ × PreMS' n)) : PreMS' (n + 1)

abbrev CoList' (α : Type u) : Type u := ℕ → Option α

def CoListWF {α : Type u} (li : CoList' α) : Prop :=
  ∀ n, li n = .none → li (n + 1) = none

def CoList (α : Type u) : Type u := {x : CoList' α // CoListWF x}

namespace CoList

def nil {α : Type u} : CoList α :=
  ⟨fun _ ↦ .none, by simp [CoListWF]⟩

instance (α : Type u) : Inhabited (CoList α) where
  default := nil

def cons {α : Type u} (hd : α) (tl : CoList α) : CoList α where
  val := fun i => match i with
    | 0 => .some hd
    | j + 1 => tl.val j
  property := by
    sorry

def head {α : Type u} (li : CoList α) : Option α :=
  li.val 0

def tail {α : Type u} (li : CoList α) : CoList α where
  val := fun i => li.val (i + 1)
  property := sorry

def get {α : Type u} (n : ℕ) (li : CoList α) : Option α :=
  match n with
  | 0 => head li
  | m + 1 => get m (tail li)

def take {α : Type u} (n : ℕ) (li : CoList α) : List α :=
  match n, head li with
  | 0, _ => []
  | _, .none => []
  | m + 1, .some x => x :: take m (tail li)

def modify {α : Type u} (n : ℕ) (li : CoList α) (f : α → α) : CoList α :=
  match n, head li with
  | 0, .some x => cons (f x) (tail li)
  | _, .none => li
  | m + 1, _ => modify m (tail li) f

def set {α : Type u} (n : ℕ) (li : CoList α) (val : α) : CoList α :=
  modify n li (fun _ ↦ val)

def casesOn {α : Type u} {motive : CoList α → Sort v} (x : CoList α) (nil : motive .nil)
    (cons : (hd : α) → (tl : CoList α) → motive (.cons hd tl)) : motive x :=
  match h : x.val 0 with
  | .none =>
    have h_nil : x = .nil := by
      apply Subtype.eq
      ext1 i
      have : x.val i = .none := by
        induction i
        · assumption
        · apply x.property
          assumption
      simp [this, CoList.nil]
    h_nil ▸ nil
  | .some hd =>
    let tl := x.tail
    have h_cons : x = .cons hd tl := by
      apply Subtype.eq
      ext1 i
      cases i with
      | zero => simpa [CoList.cons]
      | succ j => simp [CoList.cons, tl, tail]
    h_cons ▸ cons hd tl

/-- nondependendent version of `casesOn` -/
abbrev casesOn' {α : Type u} {motive : Sort v} (x : CoList α) (nil : motive)
    (cons : (hd : α) → (tl : CoList α) → motive) : motive :=
  x.casesOn (motive := fun _ ↦ motive)
    (nil := nil)
    (cons := cons)

@[simp]
theorem casesOn_nil {α : Type u} {motive : CoList α → Sort v} {nil : motive .nil}
    {cons : (hd : α) → (tl : CoList α) → motive (.cons hd tl)} : CoList.nil.casesOn nil cons = nil := by
  rfl

@[simp]
theorem casesOn_cons {α : Type u} {motive : CoList α → Sort v} {nil : motive .nil}
    {cons : (hd : α) → (tl : CoList α) → motive (.cons hd tl)} {hd : α} (tl : CoList α) : (CoList.cons hd tl).casesOn nil cons = cons hd tl := by
  rfl


----- corecursion

inductive OutType (α : Type u) (β : Type v)
| nil
| cons (hd : α) (tl : β)

-- am I reimplementing something?
instance instOutTypeFunctor (α : Type u) : Functor (OutType α) where
  map := fun f a =>
    match a with
    | .nil => .nil
    | .cons hd tl => .cons hd (f tl)

instance (α : Type u) : LawfulFunctor (OutType α) where
  id_map := by
    intro α a
    unfold Functor.map instOutTypeFunctor
    cases a <;> simp
  comp_map := by
    intro α β γ f g a
    unfold Functor.map instOutTypeFunctor
    cases a <;> simp
  map_const := by
    intros
    ext1 a
    simp
    unfold Functor.map instOutTypeFunctor
    simp

def out {α : Type u} : CoList α → (OutType α <| CoList α) := fun li =>
  li.casesOn'
    (nil := .nil)
    (cons := fun hd tl => .cons hd tl)

def corec {α : Type u} {β : Type v} (g : β → OutType α β) (b : β) : CoList α :=
  let next : OutType α β → OutType α β := fun x =>
    match x with
    | .nil => .nil
    | .cons hd tl => g tl
  let after : ℕ → Option α := fun i => match next^[i] (g b) with
    | .nil => .none
    | .cons hd tl => hd
  -- let after' : ℕ → Option α := fun i ↦ (after i).map fun (deg, coef) => (deg, coef.val)
  ⟨after, by sorry⟩
  -- ⟨.colist after', by
  --   constructor
  --   · rintro n ⟨deg, coef'⟩ h
  --     simp [after', after] at h
  --     obtain ⟨_, coef, _, _, h_eq⟩ := h
  --     rw [← h_eq]
  --     exact coef.prop
  --   · intro n h
  --     have next_comm : ∀ t, next^[n] (next t) = next (next^[n] t) := by
  --       intro t
  --       rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
  --     simp [after', after] at h ⊢

  --     have : next^[n] (g b) = .inl () := by
  --       generalize next^[n] (g b) = t at *
  --       cases t with
  --       | inl _ => rfl
  --       | inr _ => simp at h

  --     have : (next^[n] (next (g b))) = .inl () := by
  --       rw [next_comm, this]
  --       simp [next]

  --     rw [this]
  --     rfl
  -- ⟩

def append {α : Type u} (a b : CoList α) : CoList α :=
  b.casesOn'
  (nil := a)
  (cons := fun b_hd b_tl =>
    let T := Bool × CoList α
    let g : T → OutType α T := fun (switched?, li) =>
      li.casesOn'
      (nil :=
        if !switched? then
          .cons b_hd (true, b_tl)
        else
          .nil
      )
      (cons := fun hd tl =>
        .cons hd (switched?, tl)
      )
    corec g (false, a)
  )

def map {α : Type u} {β : Type v} (f : α → β) (li : CoList α) : CoList β :=
  let g : CoList α → OutType β (CoList α) := fun x =>
    x.casesOn'
      (nil := .nil)
      (cons := fun hd tl => .cons (f hd) tl)
  corec g li

def mapIdx {α : Type u} {β : Type v} (f : ℕ → α → β) (li : CoList α) : CoList β :=
  let g : (ℕ × CoList α) → OutType β (ℕ × CoList α) := fun (idx, x) =>
    x.casesOn'
      (nil := .nil)
      (cons := fun hd tl => .cons (f idx hd) (idx + 1, tl))
  corec g (0, li)

def zip {α : Type u} {β : Type v} (a : CoList α) (b : CoList β) : CoList (α × β) :=
  let g : CoList α × CoList β → OutType (α × β) (CoList α × CoList β) := fun (x, y) =>
    x.casesOn'
      (nil := .nil)
      (cons := fun x_hd x_tl =>
        y.casesOn'
        (nil := .nil)
        (cons := fun y_hd y_tl =>
          .cons (x_hd, y_hd) (x_tl, y_tl)
        )
      )
  corec g (a, b)

def enum {α : Type u} (a : CoList α) : CoList (α × ℕ) :=
  let nat : CoList ℕ :=
    let g : ℕ → OutType ℕ ℕ := fun n => .cons n (n + 1)
    corec g 0
  a.zip nat

/-- Folds and stores intermediate values in Colist
[init, f init li.head, f (f init li.head) li.tail.head, ...]
-/
def fold {α : Type u} {β : Type v} (li : CoList α) (init : β) (f : β → α → β) : CoList β :=
  let g : β × CoList α → OutType β (β × CoList α) := fun (acc, x) =>
    x.casesOn'
      (nil := .nil)
      (cons := fun hd tl => .cons (f acc hd) (f acc hd, tl))
  cons init <| corec g (init, li)

/-- Version of `fold` that does not stop when `li` is exhausted. Instead it repeats final accumulated value. -/
def fold' {α : Type u} {β : Type v} (li : CoList α) (init : β) (f : β → α → β) : CoList β :=
  let g : β × CoList α → OutType β (β × CoList α) := fun (acc, x) =>
    x.casesOn'
      (nil := .cons acc (acc, .nil))
      (cons := fun hd tl => .cons (f acc hd) (f acc hd, tl))
  cons init <| corec g (init, li)

/-- `a.atLeastAsLongAs b` means that `a` cannot be exhausted faster than `b`. -/
def atLeastAsLongAs {α : Type u} {β : Type v} (a : CoList α) (b : CoList β) : Prop :=
  ∀ n, b.get n ≠ none → a.get n ≠ none

/--

coinductive all (li : CoList α) (p : α → Prop)
| nil : all nil p
| cons hd tl : (p hd) → all tl p → all (hd :: tl) p

-/
def all {α : Type u} (li : CoList α) (p : α → Prop) : Prop :=
  ∀ n, (li.get n).elim True p

def Sorted {α : Type u} (r : α → α → Prop) (li : CoList α) : Prop :=
  ∀ i j x y, i < j → li.get i = .some x → li.get j = .some y → r x y

------


--- theorems

@[simp]
theorem val_eq_get {α : Type u} (li : CoList α) (n : ℕ) : li.val n = li.get n := by
  induction n generalizing li with
  | zero => rfl
  | succ m ih =>
    unfold get
    rw [← ih]
    rfl

@[simp]
theorem cons_head {α : Type u} (hd : α) (tl : CoList α) : (cons hd tl).head = .some hd :=
  rfl

@[simp]
theorem cons_tail {α : Type u} (hd : α) (tl : CoList α) : (cons hd tl).tail = tl :=
  rfl

@[simp]
theorem nil_head {α : Type u} : (nil (α := α)).head = .none :=
  rfl

theorem head_eq_none {α : Type u} {li : CoList α} (h : li.head = none) : li = nil := by
  revert h
  apply li.casesOn
  · intro; rfl
  · intro hd tl h
    simp at h

@[simp]
theorem head_eq_none_iff {α : Type u} {li : CoList α} : li.head = none ↔ li = nil := by
  constructor
  · apply head_eq_none
  · intro h
    simp [h]

theorem head_eq_some {α : Type u} {li : CoList α} {hd : α} (h : li.head = some hd) : li = cons hd li.tail := by
  sorry

@[simp]
theorem nil_tail {α : Type u} : (nil (α := α)).tail = nil :=
  rfl

@[simp]
theorem nil_tail' {α : Type u} {n : ℕ} : tail^[n] (nil (α := α)) = nil := by
  induction n with
  | zero =>
    simp
  | succ =>
    simpa

@[simp]
theorem noConfusion {α : Type u} {hd : α} {tl : CoList α} : (cons hd tl) ≠ .nil := by
  intro h
  apply_fun head at h
  simp at h

@[simp]
theorem noConfusion' {α : Type u} {hd : α} {tl : CoList α} : .nil ≠ (cons hd tl) := by
  symm
  simp

theorem head_eq_out {α : Type u} {li : CoList α} : li.head = match li.out with
    | .nil => .none
    | .cons hd tl => .some hd := by
  apply li.casesOn <;> simp [out]

theorem tail_eq_out {α : Type u} {li : CoList α} : li.tail = match li.out with
    | .nil => .nil
    | .cons hd tl => tl := by
  apply li.casesOn <;> simp [out]

@[simp]
theorem nil_out {α : Type u} : (nil (α := α)).out = .nil := by
  simp [out]

@[simp]
theorem cons_out {α : Type u} {hd : α} {tl : CoList α} : (cons hd tl).out = .cons hd tl := by
  simp [out]

theorem out_eq_nil {α : Type u} {li : CoList α} (h : li.out = .nil) : li = .nil := by
  apply head_eq_none
  have := h ▸ head_eq_out (li := li)
  simpa using this

theorem out_eq_cons {α : Type u} {li : CoList α} {hd : α} {tl : CoList α} (h : li.out = .cons hd tl) : li = .cons hd tl := by
  revert h
  apply li.casesOn
  · intro h
    simp at h
  · intro hd' tl' h
    simp [out] at h
    congr
    exacts [h.left, h.right]

theorem corec_out {α : Type u} {β : Type u} (g : β → OutType α β) (b : β) :
    out (corec g b) = (corec (α := α) g) <$> (g b) := by
  sorry

@[simp]
theorem corec_nil {α : Type u} {β : Type u} (g : β → OutType α β) (b : β)
    (h : g b = .nil) : corec g b = nil := by
  sorry

@[simp]
theorem corec_cons {α : Type u} {β : Type u} {g : β → OutType α β} {b : β} {hd : α} {tl : β}
    (h : g b = .cons hd tl) : corec g b = cons hd (corec g tl) := by
  sorry

@[simp]
theorem cons_eq_cons {α : Type u} {hd hd' : α} {tl tl' : CoList α} : (cons hd tl = cons hd' tl') ↔ (hd = hd' ∧ tl = tl') := by
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
theorem get_eq_head {α : Type u} (li : CoList α) (n : ℕ) : li.get n = head (tail^[n] li) := by
  induction n generalizing li with
  | zero => rfl
  | succ m ih =>
    simp [get]
    apply ih

theorem get_succ_none {α : Type u} {li : CoList α} {n : ℕ} (h : li.get n = none) : li.get (n + 1) = none := by
  sorry

theorem exists_pred_of_get_some {α : Type u} {li : CoList α} {x : α} {n : ℕ} (h : li.get (n + 1) = .some x)
    : ∃ y, li.get n = .some y := by
  sorry

-- @[simp]
-- theorem get_nil {α : Type u} {n : ℕ} : (nil (α := α)).get n = .none := by
--   simp

@[simp]
theorem take_nil {α : Type u} {n : ℕ} : (nil (α := α)).take n = List.nil := by
  cases n <;> rfl


@[simp]
theorem take_zero {α : Type u} {li : CoList α} : li.take 0 = [] := by
  apply li.casesOn
  · rfl
  · intro hd tl
    rfl

@[simp]
theorem take_succ {α : Type u} {n : ℕ} {hd : α} {tl : CoList α} :
    (cons hd tl).take (n + 1) = hd :: tl.take n := by
  rfl

theorem set_head {α : Type u} {li : CoList α} {x : α} {n : ℕ} :
    (li.set n x).head =
    match n with
    | 0 => .some x
    | _ + 1 => li.head := by
  sorry

theorem set_get_some {α : Type u} {li : CoList α} {x y : α} {n : ℕ}
    (h_some : li.get n = .some y) :
    (li.set n x).get n = x := by
  sorry

theorem set_get_none {α : Type u} {li : CoList α} {x : α} {n : ℕ}
    (h_some : li.get n = .none) :
    (li.set n x).get n = .none := by
  sorry

theorem set_get_stable {α : Type u} {li : CoList α} {x : α} {n m : ℕ}
    (h : n ≠ m) :
    (li.set m x).get n = li.get n := by
  sorry

@[simp]
theorem map_nil {α : Type v} {β : Type v} (f : α → β) : nil.map f = nil := by
  unfold map
  rw [corec_nil]
  simp [casesOn']

@[simp]
theorem map_cons {α : Type v} {β : Type v} (hd : α) (tl : CoList α) (f : α → β) :
    (cons hd tl).map f = cons (f hd) (tl.map f) := by
  unfold map
  rw [corec_cons]
  simp [casesOn']

@[simp]
theorem zip_nil_left {α : Type u} {β : Type v} (a : CoList α) : (nil (α := β)).zip a = .nil := by
  unfold zip
  rw [corec_nil]
  simp [casesOn']

@[simp]
theorem zip_nil_right {α : Type u} {β : Type v} (a : CoList α) : a.zip (.nil (α := β)) = .nil := by
  unfold zip
  rw [corec_nil]
  simp [casesOn']
  apply a.casesOn <;> simp

@[simp]
theorem cons_zip_cons {α : Type u} {β : Type v} (a_hd : α) (b_hd : β) (a_tl : CoList α) (b_tl : CoList β)
    : (cons a_hd a_tl).zip (cons b_hd b_tl) = cons (a_hd, b_hd) (a_tl.zip b_tl) := by
  sorry

theorem map_zip_left {α : Type u} {β : Type v} {γ : Type w} {a : CoList α} {b : CoList β} {f : α → γ} :
    (a.map f).zip b = (a.zip b).map fun (x, y) =>  (f x, y) := by
  sorry

@[simp]
theorem nil_append {α : Type u} (b : CoList α) : nil.append b = b := by
  unfold append
  simp
  conv =>
    arg 1
    arg 3
    ext; ext;
    rw [corec_cons]
    · skip
    · tactic =>
      simp
      constructor
      · rfl
      · rfl
  sorry -- probably cannot prove without bisimulation

@[simp]
theorem cons_append {α : Type u} (hd : α) (tl b : CoList α) :
    (cons hd tl).append b = cons hd (tl.append b) := by
  sorry


@[simp]
theorem fold_nil {α : Type u} {β : Type u} (init : β) (f : β → α → β) :
    nil.fold init f = cons init nil := by
  unfold fold
  simp

@[simp]
theorem fold_cons {α : Type u} {β : Type u} (init : β) (f : β → α → β) (hd : α) (tl : CoList α) :
    (cons hd tl).fold init f = cons init (tl.fold (f init hd) f) := by
  unfold fold
  simp
  sorry

@[simp]
theorem head_fold {α : Type u} {β : Type u} (init : β) (f : β → α → β) (li : CoList α) :
    (li.fold init f).head = init := by
  rfl

-- @[simp]
-- theorem fold_map {α : Type u} {β : Type u} {γ : Type u} (init : β) (f : β → α → β) (g : β → γ) (li : CoList α) :
--     (li.fold init f).map g = li.fold (g init)

-- theorem fold_get {α : Type u} {β : Type u} (init : β) (f : β → α → β) (li : CoList α) (n : ℕ) :
--   (li.fold init f).get (n + 1) = f

theorem fold_idk {α : Type u} {β : Type u} {init init' : β} {f : β → α → β} {li : CoList α} {p p' : β → Prop}
    (h : (li.fold init f).all p) (h_init : p init → p' init')
    (h_trans : ∀ acc acc' hd, (p acc → p' acc') → (p (f acc hd) → p' (f acc' hd)))
    : (li.fold init' f).all p' := by
  unfold all
  unfold all at h
  intro n
  induction n generalizing li with
  | zero =>
    simp
    simp at h
    exact h_init (h 0)
  | succ m ih =>
    sorry
    -- simp only [get_eq_head, Function.iterate_succ, Function.comp_apply] at ih ⊢


-- very bad proof. May be possible to do everything in a single induction?
theorem atLeastAsLong.coind {α : Type u} {β : Type v} (motive : CoList α → CoList β → Prop)
    (h_survive : ∀ a b, motive a b →
      (∀ b_hd b_tl, (b = cons b_hd b_tl) → ∃ a_hd a_tl, a = cons a_hd a_tl ∧ motive a_tl b_tl))
    {a : CoList α} {b : CoList β} (h : motive a b) : a.atLeastAsLongAs b := by
  simp only [atLeastAsLongAs]
  intro n
  have : tail^[n] b ≠ .nil → motive (tail^[n] a) (tail^[n] b) := by
    intro hb
    induction n with
    | zero =>
      simpa
    | succ m ih =>
      simp only [Function.iterate_succ', Function.comp_apply] at hb ⊢
      generalize tail^[m] a = ta at *
      generalize tail^[m] b = tb at *
      revert hb ih
      apply tb.casesOn
      · intro hb ih
        simp at hb
      · intro tb_hd tb_tl hb ih
        simp at ih
        specialize h_survive ta (cons tb_hd tb_tl) ih _ _ (by rfl)
        obtain ⟨a_hd, a_tl, ha, h_tail⟩ := h_survive
        subst ha
        simpa
  simp [get_eq_head]
  intro hb
  specialize this hb
  specialize h_survive _ _ this
  generalize tail^[n] b = tb at *
  revert hb h_survive
  apply tb.casesOn
  · simp
  · intro tb_hd tb_tl _ h_survive
    specialize h_survive _ _ (by rfl)
    obtain ⟨a_hd, a_tl, ha, _⟩ := h_survive
    rw [ha]
    simp

theorem atLeastAsLongAs_cons {α : Type u} {β : Type v} {a : CoList α} {hd : β} {tl : CoList β}
    (h : a.atLeastAsLongAs (cons hd tl)) : ∃ hd' tl', a = cons hd' tl' := by
  revert h
  apply a.casesOn
  · intro h
    unfold atLeastAsLongAs at h
    specialize h 0
    simp at h
  · intro hd' tl' _
    use hd'
    use tl'

-- TODO: prove using coinduction
@[simp]
theorem atLeastAsLongAs_nil {α : Type u} {β : Type v} {a : CoList α} :
    a.atLeastAsLongAs (.nil (α := β)) := by
  unfold atLeastAsLongAs
  intro n
  contrapose
  simp only [ne_eq, not_not]
  intro
  rw [← val_eq_get]
  rfl


@[simp]
theorem cons_atLeastAsLongAs_cons {α : Type u} {β : Type v} {a_hd : α} {a_tl : CoList α} {b_hd : β}
    {b_tl : CoList β} : (cons a_hd a_tl).atLeastAsLongAs (cons b_hd b_tl) ↔ a_tl.atLeastAsLongAs b_tl := by
  sorry

theorem atLeastAsLongAs_map {α : Type v} {β : Type v} {γ : Type w} {f : β → γ} {a : CoList α}
    {b : CoList β} (h : a.atLeastAsLongAs b):
    a.atLeastAsLongAs (b.map f) := by
  sorry

@[simp]
theorem all_nil {α : Type u} {p : α → Prop} : nil.all p := by
  sorry

@[simp]
theorem all_cons {α : Type u} {p : α → Prop} {hd : α} {tl : CoList α} :
    ((cons hd tl).all p) ↔ p hd ∧ tl.all p := by
  sorry

theorem all_get {α : Type  u} {p : α → Prop} {li : CoList α} (h : li.all p) {n : ℕ} : (li.get n).elim True p := by
  sorry --induction n

theorem set_all {α : Type u} {p : α → Prop} {li : CoList α} (h_all : li.all p) {n : ℕ} {x : α}
    (hx : p x) : (li.set n x).all p := by
  sorry

/-- Coinduction principle for proving `a = b`. -/
def Eq.coind {α : Type u} {a b : CoList α}
    (motive : CoList α → CoList α → Prop)
    (h_survive : ∀ a b, motive a b →
      (∃ hd a_tl b_tl, a = cons hd a_tl ∧ b = cons hd b_tl ∧ motive a_tl b_tl) ∨
      (a = nil ∧ b = nil))
    (h : motive a b) : a = b := by
  apply Subtype.eq
  ext1 n
  have : motive (tail^[n] a) (tail^[n] b) := by
    induction n with
    | zero =>
      simpa
    | succ m ih =>
      simp only [Function.iterate_succ', Function.comp_apply]
      specialize h_survive (tail^[m] a) (tail^[m] b) ih
      cases h_survive with
      | inl h =>
        obtain ⟨hd, a_tl, b_tl, h_a_eq, h_b_eq, h_tail⟩ := h
        rw [h_a_eq, h_b_eq]
        simpa
      | inr h =>
        rw [h.1, h.2] at ih ⊢
        simpa
  simp
  specialize h_survive _ _ this
  cases h_survive with
  | inl h =>
    obtain ⟨hd, a_tl, b_tl, h_a_eq, h_b_eq, _⟩ := h
    simp [h_a_eq, h_b_eq]
  | inr h => rw [h.1, h.2]

@[simp]
theorem map_append {α : Type v} {β : Type v} (a b : CoList α) (f : α → β) :
    (a.append b).map f = (a.map f).append (b.map f) := by
  sorry

def all.coind' {α : Type u} {li : CoList α} {p : α → Prop}
    (motive : CoList α → (α → Prop) → Prop)
    (h_cons : ∀ hd tl p, motive (cons hd tl) p → p hd ∧ motive tl p)
    (h : motive li p) : li.all p := by
  unfold all
  -- simp_rw [← aux]
  intro n
  have : (get n li).elim True p ∧ motive (tail^[n] li) p := by
    induction n with
    | zero =>
      cases h1 : get 0 li with
      | none =>
        constructor
        · simp
        · simpa
      | some hd =>
        simp
        have := head_eq_some h1
        specialize h_cons hd li.tail p (this ▸ h)
        constructor
        · exact h_cons.left
        · exact h
    | succ m ih =>
      simp at ih
      simp only [get_eq_head, Function.iterate_succ', Function.comp_apply]
      revert ih
      generalize tail^[m] li = t
      apply t.casesOn
      · simp
      · intro hd tl
        simp
        intro h1 h2
        have : motive tl p := by
          specialize h_cons hd tl p h2
          exact h_cons.right
        constructor
        · cases h_head : tl.head with
          | none => simp
          | some tl_hd =>
            have h_tl_cons := head_eq_some h_head
            specialize h_cons tl_hd tl.tail p (h_tl_cons ▸ this)
            simp
            exact h_cons.left
        · assumption
  exact this.left


-- can I prove using `all.coind` ?
def all.coind {α : Type u} {li : CoList α} {p : α → Prop}
    (motive : CoList α → Prop)
    (h_cons : ∀ hd tl, motive (cons hd tl) → p hd ∧ motive tl)
    (h : motive li) : li.all p := by
  unfold all
  -- simp_rw [← aux]
  intro n
  have : (get n li).elim True p ∧ motive (tail^[n] li) := by
    induction n with
    | zero =>
      cases h1 : get 0 li with
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
      simp only [get_eq_head, Function.iterate_succ', Function.comp_apply]
      revert ih
      generalize tail^[m] li = t
      apply t.casesOn
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
theorem all_mp {α : Type u} {p q : α → Prop} (h : ∀ a, p a → q a) {li : CoList α} (hp : li.all p) :
    li.all q := by
  let motive : CoList α → Prop := fun x => x.all p
  apply all.coind motive
  · intro hd tl ih
    simp [motive] at ih
    constructor
    · exact h _ ih.left
    · simp [motive]
      exact ih.right
  · exact hp

theorem map_all_iff {α : Type u} {β : Type u} {f : α → β} {p : β → Prop} {li : CoList α} :
    (li.map f).all p ↔ li.all (p ∘ f) := by
  constructor
  · intro h
    let motive : CoList α → Prop := fun x => (map f x).all p
    apply all.coind motive _ h
    · intro hd tl ih
      simp [motive] at ih
      exact ih
  · intro h
    let motive : CoList β → Prop := fun x => ∃ (y : CoList α), x = y.map f ∧ y.all (p ∘ f)
    apply all.coind motive
    · intro hd tl ih
      simp [motive] at ih
      obtain ⟨y, hx_eq, hy⟩ := ih
      revert hx_eq hy
      apply y.casesOn
      · intro hx_eq
        simp at hx_eq
      · intro y_hd y_tl hx_eq hy
        simp at hx_eq hy
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

theorem take_length_le {α : Type u} {li : CoList α} {n : ℕ} : (li.take n).length ≤ n := by
  sorry

theorem take_tail' {α : Type u} {li : CoList α} {n m : ℕ} : List.tail^[m] (li.take n) = (tail^[m] li).take (n - m) := by
  sorry

theorem mem_take_iff {α : Type u} {x : α} {li : CoList α} {n : ℕ} :
    x ∈ li.take n ↔ ∃ m < n, li.get m = .some x := by
  sorry

theorem get_mem_take {α : Type u} {li : CoList α} {m n : ℕ} (h_mn : m < n) {x : α}
    (h_get : li.get m = .some x) : x ∈ li.take n := by
  sorry

theorem head_mem_take_succ {α : Type u} {hd : α} {tl : CoList α} {n : ℕ} :
    hd ∈ (cons hd tl).take (n + 1) := by
  sorry

theorem take_all {α : Type u} {li : CoList α} {p : α → Prop} (h : li.all p) {n : ℕ} :
    ∀ x ∈ li.take n, p x := by
  sorry

theorem map_comp {α β γ : Type u} {f : α → β} {g : β → γ} {li : CoList α} :
    (li.map f).map g = li.map (g ∘ f) := by
  let motive : CoList γ → CoList γ → Prop := fun x y =>
    ∃ a : CoList α, x = (a.map f).map g ∧ y = a.map (g ∘ f)
  apply Eq.coind motive
  · intro x y ih
    simp [motive] at ih
    obtain ⟨a, h_x_eq, h_y_eq⟩ := ih
    revert h_x_eq h_y_eq
    apply a.casesOn
    · simp
      intro h_x_eq h_y_eq
      right
      exact ⟨h_x_eq, h_y_eq⟩
    · intro hd tl
      intro h_x_eq h_y_eq
      simp at h_x_eq h_y_eq
      left
      use (g (f hd))
      use (map g (map f tl))
      use (map (g ∘ f) tl)
      constructor
      · assumption
      constructor
      · assumption
      simp [motive]
      use tl
  · simp [motive]
    use li

@[simp]
theorem cons_set_zero {α : Type u} {hd hd' : α} {tl : CoList α} :
    (cons hd tl).set 0 hd' = cons hd' tl := by
  simp [set, modify]

@[simp]
theorem cons_set_succ {α : Type u} {hd x : α} {n : ℕ} {tl : CoList α} :
    (cons hd tl).set (n + 1) x = cons hd (tl.set n x) := by
  sorry

theorem set_tail_stable_of_lt {α : Type u} {li : CoList α} {m n : ℕ} {x : α}
    (h : m < n) :
    tail^[n] (li.set m x) = tail^[n] li := by
  sorry

theorem Sorted.nil {α : Type u} {r : α → α → Prop} : Sorted r (.nil (α := α)) := by
  simp [Sorted]

theorem Sorted.cons {α : Type u} {r : α → α → Prop} [IsTrans _ r] {hd : α} {tl : CoList α}
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
      apply tl.casesOn
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

theorem Sorted.coind {α : Type u} {r : α → α → Prop} [IsTrans _ r] (motive : CoList α → Prop)
    (h_survive : ∀ hd tl, motive (.cons hd tl) → tl.head.elim True (r hd ·) ∧ motive tl)
    {li : CoList α} (h : motive li) : Sorted r li := by
  have h_all : ∀ n, motive (CoList.tail^[n] li) := by
    intro n
    induction n with
    | zero => simpa
    | succ m ih =>
      simp only [Function.iterate_succ', Function.comp_apply]
      generalize tail^[m] li = t at *
      revert ih
      apply t.casesOn
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
    simp [CoList.get_eq_head, Function.iterate_add, Function.comp_apply] at hy
    specialize h_all i
    generalize tail^[i] li = t at *
    revert hx hy h_all
    apply t.casesOn
    · simp
    intro hd tl hx hy h_all
    specialize h_survive hd tl h_all
    simp at hx hy
    simp [hy, hx] at h_survive
    exact h_survive.left
  | succ l ih =>
    simp at hx hy ih
    rw [show l + 1 + 1 + i = l + 1 + i + 1 by omega] at hy
    simp only [Function.iterate_succ', Function.comp_apply] at hy
    specialize h_all (l + 1 + i)
    generalize tail^[l + 1 + i] li = t at *
    revert ih hy h_all
    apply t.casesOn
    · simp
    intro hd tl ih hy h_all
    specialize h_survive hd tl h_all
    simp at ih hy
    simp [hy] at h_survive
    trans hd
    exacts [ih, h_survive.left]

theorem Sorted_cons {α : Type u} {r : α → α → Prop} {hd : α} {tl : CoList α}
    (h : Sorted r (.cons hd tl)) :
    tl.head.elim True (r hd ·) ∧ Sorted r tl := by
  simp [Sorted] at *
  constructor
  · revert h
    apply tl.casesOn
    · simp
    intro tl_hd tl_tl h
    specialize h 0 1 hd tl_hd (by omega)
    simpa using h
  · intro i j
    specialize h (i + 1) (j + 1)
    simpa using h

theorem Sorted_tail {α : Type u} {r : α → α → Prop} {li : CoList α} (h : li.Sorted r) :
    li.tail.Sorted r := by
  revert h
  apply li.casesOn
  · simp
  · intro hd tl h
    simp
    exact (Sorted_cons h).right

theorem Sorted_tail' {α : Type u} {r : α → α → Prop} {li : CoList α} (h : li.Sorted r) {n : ℕ} :
    (CoList.tail^[n] li).Sorted r := by
  induction n with
  | zero => simpa
  | succ m ih =>
    simp only [Function.iterate_succ', Function.comp_apply]
    exact Sorted_tail ih

end CoList

end TendstoTactic
