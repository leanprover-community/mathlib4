import Mathlib.Data.List.Sort
import Mathlib.Data.List.Lex
import Mathlib.Data.List.MinMax
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.OrderIsoNat

variable (α : Type _) [LinearOrder α]

lemma Antitone.eventually_constant [WellFoundedLT α] (f : ℕ → α) (h : Antitone f) :
    ∃ N a, ∀ n, N ≤ n → f n = a := by
  sorry

theorem wellFoundedLT_iff_not_strictAnti : WellFoundedLT α ↔ ∀ f : ℕ → α, ¬ StrictAnti f := by
  dsimp [WellFoundedLT]
  rw [IsWellFounded_iff, RelEmbedding.wellFounded_iff_no_descending_seq]
  constructor
  <;> intro h
  · intro f hf
    rw [isEmpty_iff] at h
    apply h
    refine' ⟨⟨f, hf.injective⟩,_⟩
    intro a b
    refine' ⟨_, fun h ↦ hf h⟩
    intro hfab
    dsimp at hfab
    by_contra hab
    simp only [gt_iff_lt, not_lt] at hab
    have := hf.antitone hab
    rw [← not_lt] at this
    exact this hfab
  · rw [isEmpty_iff]
    intro f
    apply h f.toEmbedding
    intro a b hab
    rwa [f.map_rel_iff']



variable {α}

@[simp] theorem List.cons_lt (a : α) (x y : List α) : a :: x < a :: y ↔ x < y := by
  constructor
  · intro h
    cases h
    case cons h =>
      exact h
    case rel h =>
      simp at h
  · intro h
    apply Lex.cons h

@[simp] theorem List.append_lt (x y z : List α) : x ++ y < x ++ z ↔ y < z := by
  induction x
  · case nil => rfl
  · case cons h t ih =>
      simpa

@[simp]
theorem List.head?_isNone_iff : l.head?.isNone ↔ l = [] := by cases l <;> simp

@[simp] theorem List.lt_nil_iff (l : List α) : ¬ l < [] := by
  cases l
  · simp
  · exact of_decide_eq_false rfl

theorem List.take_one_eq_singleton_iff (l : List α) : l.take 1 = [a] ↔ l.head? = some a := by
  cases l <;> simp

theorem Option.get?_eq_some (o : Option α) (w : o.isSome) : o.get w = a ↔ o = some a := by
  cases o
  · simp at w
  · simp

theorem List.maximum_of_length_pos_mem (l : List α) (h : 0 < l.length) :
    l.maximum_of_length_pos h ∈ l := by
  apply maximum_mem
  simp

theorem List.exists_mem_eq_maximum_of_length_pos (l : List α) (h : 0 < l.length) :
    ∃ a, a ∈ l ∧ a = l.maximum_of_length_pos h := by
  simp only [exists_eq_right]
  exact maximum_of_length_pos_mem l h

theorem List.some_get_eq_get? (l : List α) (x : Fin l.length) : some (l.get x) = l.get? x.1 := by
  rw [List.get?_eq_get]

theorem List.get_eq_get_of_take_eq_take (la lb : List α) (n : ℕ)
    (ha : n < la.length) (hb : n < lb.length) (lt : n < m) (w : la.take m = lb.take m) :
    la.get ⟨n, ha⟩ = lb.get ⟨n, hb⟩ := by
  rw [List.get_eq_iff]
  simp only [some_get_eq_get?]
  rw [← List.take_append_drop m la, ← List.take_append_drop m lb]
  rw [List.get?_append, List.get?_append, w]
  · aesop
  · aesop

/--
Constructs the smallest monotone function larger than a given function,
defined by `leastOrderHom f n = [f 0, f 1, ..., f n].maximum_of_length_pos (by simp)`.
-/
-- One could prove `leastOrderHom_le (f : ℕ → α) (g : ℕ →o α) (w : f ≤ g) : leastOrderHom f ≤ g`,
-- and that this is a Galois connection.
-- One could generalize from `ℕ` to any `LocallyFiniteOrderBot`.
def leastOrderHom (f : ℕ → α) : ℕ →o α where
  toFun n := (List.range (n + 1)).map f |>.maximum_of_length_pos (by simp)
  monotone' n m h := by
    apply List.le_maximum_of_length_pos_of_mem
    dsimp
    obtain ⟨a, m, w⟩ :=
      List.exists_mem_eq_maximum_of_length_pos ((List.range (n + 1)).map f) (by simp)
    rw [← w]
    simp at m
    obtain ⟨b, w', rfl⟩ := m
    simp only [List.mem_map, List.mem_range]
    exact ⟨b, (lt_of_lt_of_le w' (Nat.add_le_add_right h 1)), rfl⟩

theorem le_leastOrderHom (f : ℕ → α) : f ≤ leastOrderHom f := by
  intro n
  dsimp [leastOrderHom]
  apply List.le_maximum_of_length_pos_of_mem
  simp only [List.mem_map, List.mem_range]
  exact ⟨n, Nat.lt_succ_self _, rfl⟩

namespace wellFoundedLT_sorted

variable (α)
variable [WellFoundedLT α]

def IncreasingList := { l : List α // l.Sorted (· > · ) }

instance : LinearOrder (IncreasingList α) := inferInstanceAs <| LinearOrder { _l : List α // _ }

@[simp] lemma IncreasingList.lt_iff (x y : IncreasingList α) : x < y ↔ x.1 < y.1 := Iff.rfl

def SDS := { f : ℕ → IncreasingList α // StrictAnti f }

variable {α}

def Q (n : ℕ) (L : SDS α) :=
  Σ' N, Σ' S : List α, S.length = n ∧ ∀ (m), N ≤ m → (L.1 m).1.take n = S

def P (L : SDS α) := ∀ n, Q n L

def IncreasingList.drop (l : IncreasingList α) (m : ℕ) : IncreasingList α :=
  ⟨l.1.drop m, l.2.drop⟩

def SDS.drop₁ (L : SDS α) (m : ℕ) : SDS α :=
  ⟨fun n => L.1 (n + m), fun _ _ h => L.2 (Nat.add_lt_add_right h m)⟩

def SDS.drop₂ (L : SDS α) (S : List α) (m : ℕ) (w : ∀ n, (L.1 n).1.take m = S) : SDS α :=
  ⟨fun n => (L.1 n).drop m, by
    intro a b h
    have := L.2 h
    change (L.1 b).1 < (L.1 a).1 at this
    rw [← List.take_append_drop m (L.1 a).1, ← List.take_append_drop m (L.1 b).1, w, w] at this
    simpa using this⟩

def SDS.dropQ (L : SDS α) (w : Q n L) : SDS α := by
  obtain ⟨N, S, w⟩ := w
  refine (L.drop₁ N).drop₂ S n ?_
  intro m
  exact (w.2 (m + N) (Nat.le_add_left N m))

theorem SDS.dropQ_apply (L : SDS α) (w : Q n L) : ((L.dropQ w).1 m).1 = (L.1 (m + w.1)).1.drop n :=
  rfl

variable {L : SDS α}

theorem Q_succ (L : SDS α) (w' : Q n L) (w₁ : Q 1 (L.dropQ w')) : Q (n+1) L := by
  obtain ⟨N', S', s', w'⟩ := w'
  obtain ⟨N₁, S₁, s₁, w₁⟩ := w₁
  use N' + N₁
  use S' ++ S₁
  constructor
  · simp [s', s₁]
  intro m h
  specialize w' m (le_of_add_le_left h)
  specialize w₁ (m - N') (le_tsub_of_add_le_left h)
  simp only [SDS.dropQ_apply] at w₁
  rw [Nat.sub_add_cancel (le_of_add_le_left h)] at w₁
  rw [List.take_add]
  rw [w', w₁]

def SDS.head? (L : SDS α) : ℕ → Option α := fun n => (L.1 n).1.head?

lemma SDS.head?_isSome (L : SDS α) (n : ℕ) : (L.head? n).isSome := by
  by_contra h
  simp [SDS.head?] at h
  have := L.2 (Nat.lt_succ_self n)
  simp [h] at this

def SDS.head (L : SDS α) : ℕ → α := fun n => (L.head? n).get (L.head?_isSome n)

lemma aux (l₁ l₂ : List α) (h₁ : l₁.head?.isSome) (h₂ : l₂.head?.isSome) : l₁ < l₂ →
    l₁.head?.get h₁ ≤ l₂.head?.get h₂ := by
  match l₁, h₁, l₂, h₂ with
  | x₁ :: t₁, _, x₂ :: t₂, _ =>
    intro h
    cases h
    case cons => rfl
    case rel h =>
      exact h.le

lemma SDS.head_antitone (L : SDS α) : Antitone L.head := by
  intro a b h
  rcases lt_or_eq_of_le h with (h | rfl)
  · have := L.2 h
    simp [SDS.head, SDS.head?]
    apply aux _ _ _ _ this
  · rfl

lemma SDS.head_eventually_constant (L : SDS α) : ∃ N a, ∀ n, N ≤ n → L.head n = a :=
  Antitone.eventually_constant α _ L.head_antitone

theorem Q_one : Nonempty (Q 1 L) := by
  obtain ⟨N, a, w⟩ := L.head_eventually_constant
  apply Nonempty.intro
  use N
  use [a]
  use rfl
  intro m h
  specialize w m h
  simp [SDS.head, SDS.head?, Option.get?_eq_some] at w
  simpa [List.take_one_eq_singleton_iff]

theorem main (L : SDS α) : P L := by
  intro n
  apply Nonempty.some
  induction n using Nat.strong_induction_on generalizing L
  case h n a =>
    cases n
    case zero =>
      use 0
      use []
      use rfl
      intro m _
      simp
    case succ n =>
      cases n
      case zero =>
        apply Q_one
      case succ n =>
        apply Nonempty.intro
        apply Q_succ
        · apply Nonempty.some
          apply a
          exact Nat.one_lt_succ_succ n
        · apply Nonempty.some
          apply a
          exact Nat.lt_succ_self _

def P' (L : SDS α) :=
  ∃ g : ℕ →o ℕ, ∀ n, ∃ S : List α, S.length = n ∧ ∀ (m), g n ≤ m → (L.1 m).1.take n = S

theorem main' (L : SDS α) : P' L := by
  let this := main L
  use leastOrderHom fun n => (this n).1
  intro n
  use (this n).2.1
  use (this n).2.2.1
  intro m h
  apply (this n).2.2.2
  exact (le_leastOrderHom _ _).trans h

def P'' (L : SDS α) :=
  ∃ g : ℕ →o ℕ, ∀ (n : ℕ), ∀ (m₁ : ℕ), g n ≤ m₁ → n ≤ (L.1 m₁).1.length ∧
    ∀ m₂, g n ≤ m₂ → ∀ x, x < n → (h₁ : _) → (h₂ : _) →
      (L.1 m₁).1.get ⟨x, h₁⟩ = (L.1 m₂).1.get ⟨x, h₂⟩

theorem main'' (L : SDS α) : P'' L := by
  obtain ⟨g, w⟩ := main' L
  use g
  intro n m₁ mh₁
  constructor
  · obtain ⟨S, s, w⟩ := w n
    specialize w m₁ mh₁
    rw [←List.take_append_drop n (L.1 m₁).1]
    simp [s, w]
  · intro m₂ mh₂ x lt h₁ h₂
    obtain ⟨S, _, w⟩ := w n
    have w₁ := w m₁ mh₁
    have w₂ := w m₂ mh₂
    apply List.get_eq_get_of_take_eq_take _ _ _ _ _ lt
    simp [w₁, w₂]

end wellFoundedLT_sorted

open wellFoundedLT_sorted

instance wellFoundedLT_sorted [WellFoundedLT α] :
    WellFoundedLT { l : List α // l.Sorted (· > · ) } :=
  (wellFoundedLT_iff_not_strictAnti _).mpr (fun f w => by
    obtain ⟨g, h⟩ := main'' ⟨f, w⟩
    have lt_length : ∀ n, n < (f (g (n + 1))).1.length :=
      fun n => lt_of_lt_of_le (Nat.lt_succ_self n) (h (n + 1) (g (n + 1)) (le_refl _)).1
    let z : ℕ → α := fun n => (f (g (n + 1))).1.get ⟨n, lt_length n⟩
    apply (wellFoundedLT_iff_not_strictAnti α).mp ‹_› z
    intro a b lt
    calc
      z b = (f (g (b + 1))).1.get ⟨b, lt_length b⟩ := rfl
      _   < (f (g (b + 1))).1.get ⟨a, lt.trans (lt_length _)⟩ :=
              List.pairwise_iff_get.mp (f (g (b + 1))).2 _ _ lt
      _   = (f (g (a + 1))).1.get ⟨a, lt_length a⟩ :=
              ((h (a + 1) (g (a + 1)) (le_refl _)).2
                (g (b + 1)) (g.2 (Nat.succ_le_succ lt.le)) a (Nat.lt_succ_self _) _ _).symm
      _   = z a := rfl)
