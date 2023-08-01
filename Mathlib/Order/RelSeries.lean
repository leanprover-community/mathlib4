/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.Logic.Equiv.Fin
import Mathlib.Data.List.Indexes
import Mathlib.Data.Rel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Series of a relation

If `r` is a relation on `α` then a relation series of length `n` is a series
`a_0, a_1, ..., a_n` such that `r a_i a_{i+1}` for all `i < n`

-/

variable {α : Type _} (r : Rel α α)

/--
Let `r` be a relation on `α`, a relation series of `r` of length `n` is a series
`a_0, a_1, ..., a_n` such that `r a_i a_{i+1}` for all `i < n`
-/
structure RelSeries where
/-- The number of inequalities in the series -/
length : ℕ
/-- The underlying function of a relation series -/
toFun : Fin (length + 1) → α
/-- Adjacent elements are related -/
step : ∀ (i : Fin length), r (toFun (Fin.castSucc i)) (toFun i.succ)

namespace RelSeries

-- TODO : change to `FunLike`
instance : CoeFun (RelSeries r) (fun x ↦ Fin (x.length + 1) → α) :=
{ coe := RelSeries.toFun }

instance : Preorder (RelSeries r) :=
  Preorder.lift fun x => x.length

lemma le_def (x y : RelSeries r) : x ≤ y ↔ x.length ≤ y.length :=
  Iff.rfl

lemma lt_def (x y : RelSeries r) : x < y ↔ x.length < y.length :=
  Iff.rfl

/--
For any type `α`, each term of `α` gives a relation series with the right most index to be 0.
-/
@[simps!] def singleton (a : α) : RelSeries r where
  length := 0
  toFun := fun _ => a
  step := fun i => Fin.elim0 i

instance [IsEmpty α] : IsEmpty (RelSeries r) where
  false := fun x ↦ IsEmpty.false (x 0)

instance [Inhabited α] : Inhabited (RelSeries r) where
  default := singleton r default

instance [Nonempty α] : Nonempty (RelSeries r) :=
  Nonempty.map (singleton r) inferInstance

variable {r}

@[ext]
lemma ext {x y : RelSeries r} (length_eq : x.length = y.length)
    (toFun_eq : x.toFun = y.toFun ∘ Fin.cast (by rw [length_eq])) : x = y := by
  rcases x with ⟨nx, fx⟩
  rcases y with ⟨ny, fy⟩
  dsimp at length_eq toFun_eq
  subst length_eq
  rw [Fin.cast_refl, Function.comp.right_id] at toFun_eq
  subst toFun_eq
  rfl

lemma rel_of_lt [IsTrans α r] (x : RelSeries r) {i j : Fin (x.length + 1)} (h : i < j) :
    r (x i) (x j) := by
  induction i using Fin.inductionOn generalizing j with
  | zero => induction j using Fin.inductionOn with
    | zero => cases lt_irrefl _ h
    | succ j ihj =>
      by_cases H : 0 < Fin.castSucc j
      · exact IsTrans.trans _ _ _ (ihj H) (x.step _)
      · simp only [not_lt, Fin.le_zero_iff] at H
        rw [← H]
        exact x.step _
  | succ i _ => induction j using Fin.inductionOn with
    | zero => cases not_lt_of_lt (Fin.succ_pos i) h
    | succ j ihj =>
      obtain (H|H) : i.succ = Fin.castSucc j ∨ i.succ < Fin.castSucc j
      · change (i + 1 : ℕ) < (j + 1 : ℕ) at h
        rw [Nat.lt_succ_iff, le_iff_lt_or_eq] at h
        rcases h with (h|h)
        · exact Or.inr h
        · left
          ext
          exact h
      · rw [H]
        exact x.step _
      · exact IsTrans.trans _ _ _ (ihj H) (x.step _)

lemma rel_or_eq_of_le [IsTrans α r] (x : RelSeries r) {i j : Fin (x.length + 1)} (h : i ≤ j) :
    r (x i) (x j) ∨ x i = x j :=
  (le_iff_lt_or_eq.mp h).by_cases (Or.intro_left _ $ x.rel_of_lt .) (Or.intro_right _ $ . ▸ rfl)

/--
Given two relations `r, s` on `α` such that `r ≤ s`, any relation series of `r` induces a relation
series of `s`
-/
@[simps!]
def OfLE (x : RelSeries r) {s : Rel α α} (h : r ≤ s) : RelSeries s where
  length := x.length
  toFun := x
  step := fun _ => h _ _ <| x.step _

lemma ofLE_length (x : RelSeries r) {s : Rel α α} (h : r ≤ s) :
    (x.OfLE h).length = x.length := rfl

lemma coe_ofLE (x : RelSeries r) {s : Rel α α} (h : r ≤ s) :
  (x.OfLE h : _ → _) = x := rfl

/-- Every relation series gives a list -/
abbrev toList (x : RelSeries r) : List α := List.ofFn x

lemma toList_chain' (x : RelSeries r) : x.toList.Chain' r := by
  rw [List.chain'_iff_get]
  intros i h
  have h' : i < x.length := by simpa [List.length_ofFn] using h
  convert x.step ⟨i, h'⟩ <;>
  · rw [List.get_ofFn]; congr 1

lemma toList_ne_empty (x : RelSeries r) : x.toList ≠ ∅ := fun m =>
  List.eq_nil_iff_forall_not_mem.mp m (x 0) <| (List.mem_ofFn _ _).mpr ⟨_, rfl⟩

/-- Every nonempty list satisfying the chain condition gives a relation series-/
@[simps]
def fromListChain' (x : List α) (x_ne_empty : x ≠ ∅) (hx : x.Chain' r) : RelSeries r where
  length := x.length.pred
  toFun := x.get ∘ Fin.cast (Nat.succ_pred_eq_of_pos <| List.length_pos.mpr x_ne_empty)
  step := fun i => List.chain'_iff_get.mp hx i i.2

/-- Relation series of `r` and nonempty list of `α` satisfying `r`-chain condition bijectively
corresponds to each other.-/
protected def Equiv : RelSeries r ≃ {x : List α | x ≠ ∅ ∧ x.Chain' r} where
  toFun := fun x => ⟨_, x.toList_ne_empty, x.toList_chain'⟩
  invFun := fun x => fromListChain' _ x.2.1 x.2.2
  left_inv := fun x => ext (by dsimp; rw [List.length_ofFn, Nat.pred_succ]) <| by
    ext f
    simp only [fromListChain'_toFun, Function.comp_apply, List.get_ofFn]
    rfl
  right_inv := by
    intro x
    refine Subtype.ext (List.ext_get ?_ <| fun n hn1 hn2 => ?_)
    · dsimp
      rw [List.length_ofFn, fromListChain'_length, ←Nat.succ_eq_add_one, Nat.succ_pred_eq_of_pos]
      rw [List.length_pos]
      exact x.2.1
    · rw [List.get_ofFn, fromListChain'_toFun, Function.comp_apply]
      congr

-- TODO : build a similar bijection between `RelSeries α` and `Quiver.Path`

/--
If `a_0 < a_1 < ... < a_n` and `b_0 < b_1 < ... < b_m` are two strict series such that `a_n < b_0`,
then there is a chain of length `n + m + 1` given by
`a_0 < a_1 < ... < a_n < b_0 < b_1 < ... < b_m`.
-/
@[simps]
def append (p q : RelSeries r) (h : r (p (Fin.last _)) (q 0)) : RelSeries r where
  length := p.length + q.length + 1
  toFun := Fin.append p q ∘ Fin.cast (by ring)
  step := fun i => by
    obtain (hi|rfl|hi) := lt_trichotomy i (Fin.castLE (by linarith) (Fin.last _ : Fin (p.length + 1)))
    -- StrictMono.comp (by
    -- refine Fin.addCases (fun i ↦ Fin.addCases (fun j H ↦ ?_) (fun j _ ↦ ?_))
    --   (fun i ↦ (Fin.addCases (fun j H ↦ ?_) (fun j H ↦ ?_)))
    -- . rw [Fin.append_left, Fin.append_left]
    --   exact p.StrictMono H
    -- . rw [Fin.append_left, Fin.append_right]
    --   refine lt_of_lt_of_le (lt_of_le_of_lt (p.StrictMono.monotone ?_) h) (q.StrictMono.monotone ?_)
    --   . show (i : ℕ) ≤ p.length
    --     linarith [i.2]
    --   . norm_num
    -- . rw [Fin.append_right, Fin.append_left]
    --   change (p.length + 1 + i : ℕ) < (j : ℕ) at H
    --   exfalso
    --   linarith [j.2]
    -- . rw [Fin.append_right, Fin.append_right]
    --   refine q.StrictMono (?_ : (i : ℕ) < (j : ℕ))
    --   change p.length + 1 + ↑i < p.length + 1 + ↑j at H
    --   linarith ) (OrderIso.strictMono _)

/--
If `a_0 < a_1 < ... < a_n` is a strict series and `a` is such that `a_i < a < a_{i + 1}`, then
`a_0 < a_1 < ... < a_i < a < a_{i + 1} < ... < a_n` is another strict series
-/
@[simps]
def insert_nth (p : StrictSeries α) (i : Fin p.length) (a : α) (a_lt : p (Fin.castSucc i) < a)
  (lt_a : a < p i.succ) : StrictSeries α :=
{ length := p.length + 1
  toFun :=  (Fin.castSucc i.succ).insertNth a p
  StrictMono := by
    intros m n h
    obtain (hm|rfl|hm) := lt_trichotomy m (Fin.castSucc i.succ)
    . rw [Fin.insertNth_apply_below hm]
      obtain (hn|rfl|hn) := lt_trichotomy n (Fin.castSucc i.succ)
      . rw [Fin.insertNth_apply_below hn]
        simpa only [Fin.coe_castSucc, eq_rec_constant] using p.StrictMono h
      . rw [Fin.insertNth_apply_same]
        simp only [Fin.coe_castSucc, eq_rec_constant]
        refine lt_of_le_of_lt (p.StrictMono.monotone $ Nat.lt_succ_iff.mp ?_) a_lt
        exact h
      . rw [Fin.insertNth_apply_above hn]
        simp only [Fin.coe_castSucc, eq_rec_constant]
        generalize_proofs h1 h2
        refine lt_trans (lt_of_le_of_lt (p.StrictMono.monotone ?_) a_lt)
          (lt_of_lt_of_le lt_a $ p.StrictMono.monotone $ show (i : ℕ) + 1 ≤ (n : ℕ) - 1 from ?_)
        . change (m : ℕ) ≤ _
          change (m : ℕ) < _ at hm
          simp only [Fin.coe_castSucc] at hm ⊢
          linarith [show (m : ℕ) < i + 1 from hm]
        rwa [Nat.succ_le_iff, ←Nat.pred_eq_sub_one, Nat.lt_pred_iff, Nat.succ_eq_add_one]
    . rw [Fin.insertNth_apply_same, Fin.insertNth_apply_above h]
      simp only [Fin.coe_castSucc, eq_rec_constant]
      refine lt_of_lt_of_le lt_a (p.StrictMono.monotone $ show ↑i + 1 ≤ ↑n - 1 from ?_)
      change (_ : ℕ) < _ at h
      simp only [Fin.coe_castSucc, Fin.val_succ] at h
      rwa [Nat.succ_le_iff, ←Nat.pred_eq_sub_one, Nat.lt_pred_iff, Nat.succ_eq_add_one]
    . rw [Fin.insertNth_apply_above hm, Fin.insertNth_apply_above (lt_trans hm h)]
      simp only [Fin.coe_castSucc, eq_rec_constant]
      refine p.StrictMono ?_
      change (_ : ℕ) < _ at hm h ⊢
      simp only [Fin.coe_castSucc, Fin.val_succ, Fin.val_fin_lt, Fin.coe_pred, ge_iff_le] at hm h ⊢
      refine Nat.pred_lt_pred (?_ : (m : ℕ) ≠ 0) h
      linarith }

variable {β}

/--
For two pre-ordered sets `α, β`, if `f : α → β` is strictly monotonic, then a strict series of `α`
can be pushed out to a strict series of `β` by
`a₀ < a₁ < ... < aₙ ↦ f a₀ < f a₁ < ... < f aₙ`
-/
@[simps]
def map (p : StrictSeries α) (f : α → β) (hf : _root_.StrictMono f) : StrictSeries β :=
{ length := p.length
  toFun := f.comp p
  StrictMono := hf.comp p.StrictMono }

/--
For two pre-ordered sets `α, β`, if `f : α → β` is surjective and strictly comonotonic, then a
strict series of `β` can be pulled back to a strict chain of `α` by
`b₀ < b₁ < ... < bₙ ↦ f⁻¹ b₀ < f⁻¹ b₁ < ... < f⁻¹ bₙ` where `f⁻¹ bᵢ` is an arbitrary element in the
preimage of `f⁻¹ {bᵢ}`.
-/
@[simps]
noncomputable def comap (p : StrictSeries β) (f : α → β)
  (hf1 : ∀ ⦃x y⦄, f x < f y → x < y)
  (hf2 : Function.Surjective f) :
  StrictSeries α :=
{ length := p.length
  toFun := fun i ↦ (hf2 (p i)).choose
  StrictMono := fun i j h ↦ hf1 (by simpa only [(hf2 _).choose_spec] using p.StrictMono h) }

end RelSeries

section LTSeries

variable (α) [Preorder α]
/--
If `α` is a preordered set, a series ordered by less than is a relation series of the less than
relation.
-/
abbrev LTSeries := RelSeries ((. < .) : Rel α α)

namespace LTSeries

variable {α}

lemma top_len_unique [OrderTop (LTSeries α)] (p : LTSeries α) (hp : IsTop p) :
    p.length = (⊤ : LTSeries α).length :=
  le_antisymm (@le_top (LTSeries α) _ _ _) (hp ⊤)

lemma top_len_unique' (H1 H2 : OrderTop (LTSeries α)) : H1.top.length = H2.top.length :=
  le_antisymm (H2.le_top H1.top) (H1.le_top H2.top)

lemma StrictMono (x : LTSeries α) : StrictMono x :=
  fun _ _ h => x.rel_of_lt h

section PartialOrder

variable {β : Type _} [PartialOrder β]

lemma Monotone (x : LTSeries β) : Monotone x :=
  fun _ _ h => le_iff_lt_or_eq.mpr $ x.rel_or_eq_of_le h

end PartialOrder

end LTSeries

end LTSeries
