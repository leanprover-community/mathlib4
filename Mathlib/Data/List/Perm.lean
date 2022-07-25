import Mathlib.Init.Set
import Mathlib.Data.List.EraseDup

namespace List

/-- `Perm l₁ l₂` or `l₁ ~ l₂` asserts that `l₁` and `l₂` are Permutations
  of each other. This is defined by induction using pairwise swaps. -/
inductive Perm {α} : List α → List α → Prop
| nil   : Perm [] []
| cons  : ∀ (x : α) {l₁ l₂ : List α}, Perm l₁ l₂ → Perm (x::l₁) (x::l₂)
| swap  : ∀ (x y : α) (l : List α), Perm (y::x::l) (x::y::l)
| trans : ∀ {l₁ l₂ l₃ : List α}, Perm l₁ l₂ → Perm l₂ l₃ → Perm l₁ l₃

open Perm

infixl:50 " ~ " => Perm

protected theorem Perm.refl : ∀ (l : List α), l ~ l
  | []      => Perm.nil
  | (x::xs) => (Perm.refl xs).cons x

protected theorem Perm.symm {l₁ l₂ : List α} (p : l₁ ~ l₂) : l₂ ~ l₁ := by
  induction p with
  | nil => exact Perm.nil
  | cons x _ ih => exact Perm.cons x ih
  | swap x y l => exact Perm.swap y x l
  | trans _ _ ih₁ ih₂ => exact Perm.trans ih₂ ih₁

theorem Perm_comm {l₁ l₂ : List α} : l₁ ~ l₂ ↔ l₂ ~ l₁ := ⟨Perm.symm, Perm.symm⟩

theorem Perm.swap' (x y : α) {l₁ l₂ : List α} (p : l₁ ~ l₂) : y::x::l₁ ~ x::y::l₂ :=
  have h1 : y :: l₁ ~ y :: l₂ := Perm.cons y p
  have h2 : x :: y :: l₁ ~ x :: y :: l₂ := Perm.cons x h1
  have h3 : y :: x :: l₁ ~ x :: y :: l₁ := Perm.swap x y l₁
  Perm.trans h3 h2

theorem Perm.Equivalence : Equivalence (@Perm α) := ⟨Perm.refl, Perm.symm, Perm.trans⟩

instance (α : Type u) : Setoid (List α) := ⟨Perm, Perm.Equivalence⟩

theorem Perm.subset {α : Type u} {l₁ l₂ : List α} (p : l₁ ~ l₂) : l₁ ⊆ l₂ := by
  induction p with
  | nil => exact nil_subset _
  | cons _ _ ih => exact cons_subset_cons _ ih
  | swap x y l =>
    intro a
    rw [mem_cons]
    exact fun
    | Or.inl rfl => Mem.tail _ (Mem.head ..)
    | Or.inr (Mem.head ..) => Mem.head ..
    | Or.inr (Mem.tail _ a_mem_l) => Mem.tail _ (Mem.tail _ a_mem_l)
  | trans _ _ ih₁ ih₂ => exact subset.trans ih₁ ih₂

theorem Perm.mem_iff {a : α} {l₁ l₂ : List α} (h : l₁ ~ l₂) : a ∈ l₁ ↔ a ∈ l₂ :=
Iff.intro (λ m => h.subset m) (λ m=> h.symm.subset m)

theorem Perm.append_right
  {l₁ l₂ : List α} (t₁ : List α) (p : l₁ ~ l₂) : l₁ ++ t₁ ~ l₂ ++ t₁ :=
by
  induction p with
  | nil => exact Perm.refl $ [] ++ t₁
  | cons _ _ ih => exact Perm.cons _ ih
  | swap x y l => exact Perm.swap x y _
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem perm_middle {a : α} : ∀ {l₁ l₂ : List α}, l₁ ++ a :: l₂ ~ a :: (l₁ ++ l₂)
| [], _ => Perm.refl _
| b::l₁, l₂ =>
  let h2 := @perm_middle α a l₁ l₂
  (h2.cons _).trans (swap a b _)

theorem Perm.length_eq {l₁ l₂ : List α} (p : l₁ ~ l₂) : length l₁ = length l₂ := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap _ _ l => simp
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem Perm.eq_nil {l : List α} (p : l ~ []) : l = [] :=
eq_nil_of_length_eq_zero p.length_eq

theorem Perm.nil_eq {l : List α} (p : [] ~ l) : [] = l :=
p.symm.eq_nil.symm

@[simp] theorem perm_nil {l₁ : List α} : l₁ ~ [] ↔ l₁ = [] :=
⟨λ p => p.eq_nil, λ e => e ▸ Perm.refl _⟩

theorem perm_inv_core {a : α} {l₁ l₂ r₁ r₂ : List α} :
  l₁ ++ a::r₁ ~ l₂ ++ a::r₂ → l₁ ++ r₁ ~ l₂ ++ r₂ :=
by
  generalize e₁ : l₁ ++ a::r₁ = s₁; generalize e₂ : l₂ ++ a::r₂ = s₂
  intro p
  induction p generalizing l₁ l₂ r₁ r₂ with
  | nil =>
    apply (not_mem_nil a).elim
    rw [← e₁]; simp
  | cons t₁ t₂ ih =>
    sorry
  | swap _ _ l => sorry
  | trans _ _ ih₁ ih₂ => sorry
  -- refine perm_induction_on p _ (λ x t₁ t₂ p IH, _) (λ x y t₁ t₂ p IH, _)
  --   (λ t₁ t₂ t₃ p₁ p₂ IH₁ IH₂, _); intros l₁ l₂ r₁ r₂ e₁ e₂,
  -- { apply (not_mem_nil a).elim, rw ← e₁, simp },
  -- { cases l₁ with y l₁; cases l₂ with z l₂;
  --     dsimp at e₁ e₂; injections; subst x,
  --   { substs t₁ t₂,     exact p },
  --   { substs z t₁ t₂,   exact p.trans perm_middle },
  --   { substs y t₁ t₂,   exact perm_middle.symm.trans p },
  --   { substs z t₁ t₂,   exact (IH rfl rfl).cons y } },
  -- { rcases l₁ with _|⟨y, _|⟨z, l₁⟩⟩; rcases l₂ with _|⟨u, _|⟨v, l₂⟩⟩;
  --     dsimp at e₁ e₂; injections; substs x y,
  --   { substs r₁ r₂,     exact p.cons a },
  --   { substs r₁ r₂,     exact p.cons u },
  --   { substs r₁ v t₂,   exact (p.trans perm_middle).cons u },
  --   { substs r₁ r₂,     exact p.cons y },
  --   { substs r₁ r₂ y u, exact p.cons a },
  --   { substs r₁ u v t₂, exact ((p.trans perm_middle).cons y).trans (swap _ _ _) },
  --   { substs r₂ z t₁,   exact (perm_middle.symm.trans p).cons y },
  --   { substs r₂ y z t₁, exact (swap _ _ _).trans ((perm_middle.symm.trans p).cons u) },
  --   { substs u v t₁ t₂, exact (IH rfl rfl).swap' _ _ } },
  -- { substs t₁ t₃,
  --   have : a ∈ t₂ := p₁.subset (by simp),
  --   rcases mem_split this with ⟨l₂, r₂, e₂⟩,
  --   subst t₂, exact (IH₁ rfl rfl).trans (IH₂ rfl rfl) }

theorem Perm.cons_inv {a : α} {l₁ l₂ : List α} : a::l₁ ~ a::l₂ → l₁ ~ l₂ :=
@perm_inv_core _ _ [] [] _ _

theorem perm_cons_erase [DecidableEq α] {a : α} {l : List α} (h : a ∈ l) :
  l ~ a :: l.erase a :=
let ⟨_, _, _, e₁, e₂⟩ := exists_erase_eq h
e₂.symm ▸ e₁.symm ▸ perm_middle

theorem cons_perm_iff_perm_erase [DecidableEq α] {a : α} {l₁ l₂ : List α} :
  a::l₁ ~ l₂ ↔ a ∈ l₂ ∧ l₁ ~ l₂.erase a :=
by
  constructor
  · intro h
    have : a ∈ l₂ := h.subset (mem_cons_self a l₁)
    exact ⟨this, (h.trans $ perm_cons_erase this).cons_inv⟩
  · exact λ ⟨m, h⟩ => (h.cons a).trans (perm_cons_erase m).symm

theorem perm_iff_count [DecidableEq α] {l₁ l₂ : List α} :
  l₁ ~ l₂ ↔ ∀ a, count a l₁ = count a l₂ :=
by
  constructor
  · exact sorry
  · intro H
    induction l₁ with
    | nil =>
      cases l₂ with
      | nil => exact Perm.refl []
      | cons b l₂ =>
        sorry
    | cons x xs ih =>
    sorry

-- ⟨perm.count_eq, λ H => begin
--   induction l₁ with a l₁ IH generalizing l₂,
--   { cases l₂ with b l₂, {refl},
--     specialize H b, simp at H, contradiction },
--   { have : a ∈ l₂ := count_pos.1 (by rw ← H; simp; apply nat.succ_pos),
--     refine ((IH $ λ b, _).cons a).trans (perm_cons_erase this).symm,
--     specialize H b,
--     rw (perm_cons_erase this).count_eq at H,
--     by_cases b = a; simp [h] at H ⊢; assumption }
-- end⟩


-- TODO: Fix with `haveI`
instance decidable_perm [DecidableEq α] : ∀ (l₁ l₂ : List α), Decidable (l₁ ~ l₂)
  | [],    []    => isTrue $ Perm.refl _
  | [],    b::l₂ => isFalse $ λ h => by have := h.nil_eq; contradiction
  | a::l₁, l₂    => by
    have h₁ := decidable_perm l₁ (l₂.erase a)
    have h₂ : Decidable (a ∈ l₁) := inferInstance
    have this := @instDecidableAnd _ _ h₂ h₁
    have := @decidable_of_iff' _ (a ∈ l₂ ∧ l₁ ~ List.erase l₂ a) cons_perm_iff_perm_erase _
    exact this

-- @[congr]
theorem Perm.eraseDup [DecidableEq α] {l₁ l₂ : List α} (p : l₁ ~ l₂) :
  eraseDup l₁ ~ eraseDup l₂ :=
by
  refine perm_iff_count.2 fun a => ?_
  by_cases h : a ∈ l₁
  · simp [nodup_eraseDup, h]
    sorry
  ·
    sorry
  -- if h : a ∈ l₁
  -- then by simp [nodup_dedup, h, p.subset h]
  -- else by simp [h, mt p.mem_iff.2 h]

-- line 820
set_option linter.unusedVariables false in -- FIXME: lean4#1214
theorem perm_insertNth {x : α} : ∀ {l : List α} {n : Nat}, n ≤ l.length →
  insertNth n x l ~ x :: l
| [], 0, _ => Perm.refl _
| [], _ + 1, h => False.elim (Nat.not_succ_le_zero _ h)
| _ :: _, 0, _ => Perm.refl _
| _ :: _, _ + 1, h =>
  Perm.trans
    (Perm.cons _ (perm_insertNth (Nat.le_of_succ_le_succ h)))
    (Perm.swap _ _ _)

theorem Perm.pairwise_iff {R : α → α → Prop} (S : ∀ a₁ a₂, R a₁ a₂ → R a₂ a₁) :
  ∀ {l₁ l₂ : List α} (p : l₁ ~ l₂), Pairwise R l₁ ↔ Pairwise R l₂ :=
by
  suffices ∀ {l₁ l₂}, l₁ ~ l₂ → Pairwise R l₁ → Pairwise R l₂
    from λ l₁ l₂ p => ⟨this p, this p.symm⟩
  intro l₁ l₂ p d
  induction d generalizing l₂ with
  | nil =>
    rw [← p.nil_eq]
    exact Pairwise.nil
  | @cons a l ha hp ih =>
-- λ l₁ l₂ p d => by

  -- induction d with a l₁ h d IH generalizing l₂
  -- { rw ← p.nil_eq, constructor }
  -- { have : a ∈ l₂ := p.subset (mem_cons_self _ _),
  --   rcases mem_split this with ⟨s₂, t₂, rfl⟩,
  --   have p' := (p.trans perm_middle).cons_inv,
  --   refine (pairwise_middle S).2 (pairwise_cons.2 ⟨λ b m, _, IH _ p'⟩),
  --   exact h _ (p'.symm.subset m) }
    sorry

lemma Pairwise.perm {R : α → α → Prop} {l l' : List α} (hR : l.Pairwise R)
  (hl : l ~ l') (hsymm : ∀ a₁ a₂, R a₁ a₂ → R a₂ a₁) : l'.Pairwise R :=
(hl.pairwise_iff hsymm).mp hR

lemma Perm.pairwise {R : α → α → Prop} {l l' : List α}
  (hl : l ~ l') (hR : l.Pairwise R) (hsymm : ∀ a₁ a₂, R a₁ a₂ → R a₂ a₁) : l'.Pairwise R :=
hR.perm hl hsymm

theorem Perm.nodup_iff {l₁ l₂ : List α} : l₁ ~ l₂ → (Nodup l₁ ↔ Nodup l₂) :=
Perm.pairwise_iff $ fun _ _ => Ne.symm
