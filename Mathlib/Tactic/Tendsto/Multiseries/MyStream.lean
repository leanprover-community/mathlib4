import Mathlib.Data.ENat.Basic

namespace TendstoTactic

universe u v

def CoList (α : Type u) : Type u := {fn : ℕ → Option α // ∀ n, fn n = none → fn (n + 1) = none}

def CoList.get {α : Type u} (li : CoList α) (n : ℕ) := li.val n

def CoList.nil (α : Type u) : CoList α :=
  ⟨fun _ ↦ none, by simp⟩

def CoList.cons {α : Type u} (hd : α) (tl : CoList α) : CoList α :=
  ⟨fun i ↦ match i with
  | 0 => .some hd
  | j + 1 => tl.val j, by
    intro n
    cases n with
    | zero => simp
    | succ m => simp; exact tl.property m
  ⟩

def CoList.tail {α : Type u} (li : CoList α) : CoList α :=
  ⟨fun i ↦ li.val (i + 1), fun i ↦ li.prop (i + 1)⟩

def CoList.casesOn {α : Type u} {β : Type v} (nil : β) (cons : α → CoList α → β) (li : CoList α) : β :=
  match li.val 0 with
  | .none => nil
  | .some hd =>
    let tl := li.tail
    cons hd tl

def CoList.corec {α : Type u} {β : Type v} (g : β → Unit ⊕ (α × β)) (b : β) : CoList α :=
  let next : Unit ⊕ (α × β) → Unit ⊕ (α × β) := fun x =>
    x.elim (fun () => .inl ()) fun (_, y) => g y
  let after : ℕ → Option α := fun i ↦ next^[i] (g b) |>.elim (fun () => .none) (fun (hd, _) => hd)
  ⟨after, by
    intro n h
    have next_comm : ∀ t, next^[n] (next t) = next (next^[n] t) := by
      intro t
      rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
    simp [after] at h ⊢

    have : next^[n] (g b) = .inl () := by
      generalize next^[n] (g b) = t at *
      cases t with
      | inl _ => rfl
      | inr _ => simp at h

    have : (next^[n] (next (g b))) = .inl () := by
      rw [next_comm, this]
      simp [next]

    rw [this]
    rfl
  ⟩

theorem CoList.corec_correct {α : Type u} {β : Type v} {g : β → Unit ⊕ (α × β)} (b : β) :
    CoList.corec g b = match g b with | .inl () => CoList.nil α | .inr (hd, tlIdx) => CoList.cons hd <| CoList.corec g tlIdx := by
  cases hb : g b with
  | inl _ =>
    simp [corec, nil]
    congr
    ext i
    induction i with
    | zero => simp [hb]
    | succ j ih => simpa [hb] using ih
  | inr v =>
    obtain ⟨hd, tlIdx⟩ := v
    simp [corec, nil]
    congr
    ext i
    cases i <;> simp [hb]

#eval CoList.corec (fun (n : ℕ) ↦ .inr (n, n + 1)) 1 |>.get 4 -- natural numbers

def collatz (n : ℕ) : ℕ :=
  if n % 2 == 0 then
    n / 2
  else
    3 * n + 1

#eval CoList.corec (fun (n : ℕ) ↦ .inr (n, collatz n)) 1234556 |>.get 100001 -- collatz


-- Let's try to define Infinte

/-
coinductive CoList.Infinite : CoList α → Prop
| inf hd tl : tl.Infinite → (hd :: tl).Infinite
    α → CoList α → (Infinite tl) → Infinite (hd :: tl)

g : Π li : Colist γ, α li → Π hd : γ, tl : Colist γ →
-/
def CoList.Infinite {α : Type u} (li : CoList α) : Prop :=
  ∀ n, li.val n ≠ .none

theorem CoList.Infinite.principle' {α : Type u} {β : Type v} (g : β → Unit ⊕ (α × β)) (b : β)
    ()
    : CoList.Infinite (CoList.corec g b) := by
  sorry

theorem CoList.Infinite.principle {α : Type u} {β : Type v} (g : β → Unit ⊕ (α × β)) (b : β)
    (nil : (b : β) → g b = .inl () → False)
    (cons : (b : β) → (hd : α) → (b' : β) → g b = .inr (hd, b') → (CoList.Infinite (CoList.corec g b')) → (CoList.Infinite (CoList.corec g b))) :
    CoList.Infinite (CoList.corec g b) := by
  unfold CoList.Infinite
  intro n
  by_contra hn
  simp [corec] at hn
  cases n with
  | zero =>
    simp at hn
    have : g b = .inl () := by
      generalize g b = gb at *
      cases gb
      · rfl
      · simp at hn
    exact nil _ this
  | succ m =>
    simp_rw [Function.iterate_succ_apply'] at hn
    have : ((fun x ↦ Sum.elim (fun x ↦ Sum.inl ()) (fun x ↦ g x.2) x)^[m] (g b)) = .inl () := by
      generalize ((fun x ↦ Sum.elim (fun x ↦ Sum.inl ()) (fun x ↦ g x.2) x)^[m] (g b)) = t at *
      cases t
      · rfl
      · rename_i val
        simp at hn
        have : g val.2 = .inl () := by
          generalize g val.2 = s at *
          cases s
          · rfl
          · simp at hn
        simp [nil _ this]
    rw [this] at hn
    simp at hn





  -- rw [CoList.corec_correct]
  -- cases hgb : g b with
  -- | inl _ => specialize nil b hgb; exact nil.elim
  -- | inr v =>
  --   obtain ⟨hd, b'⟩ := v
  --   simp
  --   specialize cons b hd b' hgb
  --   conv at cons =>
  --     rhs
  --     rw [CoList.corec_correct, hgb]
  --     simp


def merge (a b : CoList ℕ) : CoList ℕ :=
  let p := (a, b)
  CoList.corec (fun (left, right) =>
    left.casesOn
      (nil := .inl ())
      (cons := fun left_hd left_tl =>
        right.casesOn
        (nil := .inl ())
        (cons := fun right_hd right_tl =>
          if left_hd <= right_hd then
            .inr (left_hd, (left_tl, right))
          else
            .inr (right_hd, (left, right_tl))
        )
      )
  ) p

def ones : CoList ℕ := CoList.corec (fun _ ↦ .inr (1, ())) ()

def flipflop : CoList ℕ := CoList.corec (fun b ↦ .inr (b.toNat, !b)) false

#reduce ones.val 4

#reduce flipflop.val 101


def merged := merge flipflop flipflop

#reduce Array.ofFn (fun (x : Fin 10) ↦ merged.val x)

end TendstoTactic


def f (n : ℕ) : ℕ := n + 10

theorem t : ∃ n : ℕ, n * n > n := by
  use 5
  decide

@[implemented_by f]
noncomputable def ff (n : ℕ) : ℕ := n + t.choose

def g (n : ℕ) : ℕ := ff n + 20

#eval g 3

namespace hidden
mutual
  inductive Even where
    | zero : Even
    | succ : Odd → Even

  inductive Odd where
    | one : Odd
    | succ : Even → Odd
end


inductive MyEvenOdd : Bool → Type
| zero : MyEvenOdd false
| one : MyEvenOdd true
| even_succ : MyEvenOdd true → MyEvenOdd false
| odd_succ : MyEvenOdd false → MyEvenOdd true

#check Even.rec

#check MyEvenOdd.rec

def MyEven := MyEvenOdd false

/-

mutual
  coinductive PreMS_CoList
  | nil : PreMS_CoList
  | cons : ℝ → PreMS → PreMS_CoList → PreMS_CoList

  inductive PreMS
  | const : ℝ → PreMS
  | colist : PreMS_CoList → PreMS
end

rec
{motive_1 : PreMS → Sort u} →
  {motive_2 : PreMS_CoList → Sort u} →
    ((c : ℝ) → motive_1 (.const c)) →
      ((li : PreMS_CoList) → motive_2 li → motive_1 (.colist li)) →
        motive_2 .nil → ((deg : ℝ) → (coef : PreMS) → (tl : PreMS_CoList) → motive_1 coef → motive_2 (.cons deg coef tl)) →
          (t : PreMS) → motive_1 t

corec
{α : Type u} →
  (g : α → Unit ⊕ (ℝ × PreMS × α)) →
    (a : α) : PreMS_CoList

neg :=
  rec
  (motive_1 := PreMS)
  (motive_2 li :=
    match li with
    | nil => PUnit
    | cons deg coef tl => motive_1 coef
  )
  (const c := .const -c)
  (colist li li_ih :=
    .colist <| corec (li, li_ih)
      (nil, () => .nil)
      (cons deg coef tl, coef_neg =>
        ((deg, coef_neg), (tl_neg, ?))
      )
  )


углубиться в теорию типов и категорий и понять

-/

end hidden
