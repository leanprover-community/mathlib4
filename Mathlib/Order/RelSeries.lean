/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Fangming Li
-/
import Mathlib.Logic.Equiv.Fin
import Mathlib.Data.List.Indexes
import Mathlib.Data.Rel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

/-!
# Series of a relation

If `r` is a relation on `α` then a relation series of length `n` is a series
`a_0, a_1, ..., a_n` such that `r a_i a_{i+1}` for all `i < n`

-/

variable {α : Type*} (r : Rel α α)
variable {β : Type*} (s : Rel β β)

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

instance : CoeFun (RelSeries r) (fun x ↦ Fin (x.length + 1) → α) :=
{ coe := RelSeries.toFun }

/--
For any type `α`, each term of `α` gives a relation series with the right most index to be 0.
-/
@[simps!] def singleton (a : α) : RelSeries r where
  length := 0
  toFun _ := a
  step := Fin.elim0

instance [IsEmpty α] : IsEmpty (RelSeries r) where
  false x := IsEmpty.false (x 0)

instance [Inhabited α] : Inhabited (RelSeries r) where
  default := singleton r default

instance [Nonempty α] : Nonempty (RelSeries r) :=
  Nonempty.map (singleton r) inferInstance

variable {r}

@[ext]
lemma ext {x y : RelSeries r} (length_eq : x.length = y.length)
    (toFun_eq : x.toFun = y.toFun ∘ Fin.cast (by rw [length_eq])) : x = y := by
  rcases x with ⟨nx, fx⟩
  dsimp only at length_eq toFun_eq
  subst length_eq toFun_eq
  rfl

lemma rel_of_lt [IsTrans α r] (x : RelSeries r) {i j : Fin (x.length + 1)} (h : i < j) :
    r (x i) (x j) :=
  (Fin.liftFun_iff_succ r).mpr x.step h

lemma rel_or_eq_of_le [IsTrans α r] (x : RelSeries r) {i j : Fin (x.length + 1)} (h : i ≤ j) :
    r (x i) (x j) ∨ x i = x j :=
  h.lt_or_eq.imp (x.rel_of_lt ·) (by rw [·])

/--
Given two relations `r, s` on `α` such that `r ≤ s`, any relation series of `r` induces a relation
series of `s`
-/
@[simps!]
def ofLE (x : RelSeries r) {s : Rel α α} (h : r ≤ s) : RelSeries s where
  length := x.length
  toFun := x
  step _ := h _ _ <| x.step _

lemma coe_ofLE (x : RelSeries r) {s : Rel α α} (h : r ≤ s) :
    (x.ofLE h : _ → _) = x := rfl

/-- Every relation series gives a list -/
abbrev toList (x : RelSeries r) : List α := List.ofFn x

lemma toList_chain' (x : RelSeries r) : x.toList.Chain' r := by
  rw [List.chain'_iff_get]
  intros i h
  convert x.step ⟨i, by simpa using h⟩ <;> apply List.get_ofFn

lemma toList_ne_empty (x : RelSeries r) : x.toList ≠ [] := fun m =>
  List.eq_nil_iff_forall_not_mem.mp m (x 0) <| (List.mem_ofFn _ _).mpr ⟨_, rfl⟩

/-- Every nonempty list satisfying the chain condition gives a relation series-/
@[simps]
def fromListChain' (x : List α) (x_ne_empty : x ≠ []) (hx : x.Chain' r) : RelSeries r where
  length := x.length.pred
  toFun := x.get ∘ Fin.cast (Nat.succ_pred_eq_of_pos <| List.length_pos.mpr x_ne_empty)
  step i := List.chain'_iff_get.mp hx i i.2

/-- Relation series of `r` and nonempty list of `α` satisfying `r`-chain condition bijectively
corresponds to each other.-/
protected def Equiv : RelSeries r ≃ {x : List α | x ≠ [] ∧ x.Chain' r} where
  toFun x := ⟨_, x.toList_ne_empty, x.toList_chain'⟩
  invFun x := fromListChain' _ x.2.1 x.2.2
  left_inv x := ext (by simp) <| by ext; apply List.get_ofFn
  right_inv x := by
    refine Subtype.ext (List.ext_get ?_ fun n hn1 _ => List.get_ofFn _ _)
    simp [Nat.succ_pred_eq_of_pos <| List.length_pos.mpr x.2.1]

-- TODO : build a similar bijection between `RelSeries α` and `Quiver.Path`

end RelSeries

namespace Rel

/-- A relation `r` is said to be finite dimensional iff there is a relation series of `r` with the
  maximum length. -/
class FiniteDimensional : Prop where
  /-- A relation `r` is said to be finite dimensional iff there is a relation series of `r` with the
    maximum length. -/
  exists_longest_relSeries : ∃ (x : RelSeries r), ∀ (y : RelSeries r), y.length ≤ x.length

/-- A relation `r` is said to be infinite dimensional iff there exists relation series of arbitrary
  length. -/
class InfiniteDimensional : Prop where
  /-- A relation `r` is said to be infinite dimensional iff there exists relation series of
    arbitrary length. -/
  exists_relSeries_with_length : ∀ (n : ℕ), ∃ (x : RelSeries r), x.length = n

end Rel

namespace RelSeries

/-- The longest relational series when a relation is finite dimensional -/
protected noncomputable def longestOf [r.FiniteDimensional] : RelSeries r :=
  Rel.FiniteDimensional.exists_longest_relSeries.choose

lemma length_le_length_longestOf [r.FiniteDimensional] (x : RelSeries r) :
    x.length ≤ (RelSeries.longestOf r).length :=
  Rel.FiniteDimensional.exists_longest_relSeries.choose_spec _

/-- A relation series with length `n` if the relation is infinite dimensional -/
protected noncomputable def withLength [r.InfiniteDimensional] (n : ℕ) : RelSeries r :=
  (Rel.InfiniteDimensional.exists_relSeries_with_length n).choose

@[simp] lemma length_withLength [r.InfiniteDimensional] (n : ℕ) :
    (RelSeries.withLength r n).length = n :=
  (Rel.InfiniteDimensional.exists_relSeries_with_length n).choose_spec

/-- If a relation on `α` is infinite dimensional, then `α` is nonempty. -/
lemma nonempty_of_infiniteDimensional [r.InfiniteDimensional] : Nonempty α :=
  ⟨RelSeries.withLength r 0 0⟩

instance membership : Membership α (RelSeries r) :=
  ⟨(· ∈ Set.range ·)⟩

theorem mem_def {x : α} {s : RelSeries r} : x ∈ s ↔ x ∈ Set.range s :=
  Iff.rfl

/-- Start of a series, i.e. for `a₀ -r→ a₁ -r→ ... -r→ aₙ`, its head is `a₀`.

Since a relation series is assumed to be non-empty, this is well defined. -/
def head (x : RelSeries r) : α := x 0

/-- End of a series, i.e. for `a₀ -r→ a₁ -r→ ... -r→ aₙ`, its last element is `aₙ`.

Since a relation series is assumed to be non-empty, this is well defined. -/
def last (x : RelSeries r) : α := x <| Fin.last _

lemma head_mem (x : RelSeries r) : x.head ∈ x := ⟨_, rfl⟩

lemma last_mem (x : RelSeries r) : x.last ∈ x := ⟨_, rfl⟩

/--
If `a₀ -r→ a₁ -r→ ... -r→ aₙ` and `b₀ -r→ b₁ -r→ ... -r→ bₘ` are two strict series
such that `r aₙ b₀`, then there is a chain of length `n + m + 1` given by
`a₀ -r→ a₁ -r→ ... -r→ aₙ -r→ b₀ -r→ b₁ -r→ ... -r→ bₘ`.
-/
@[simps]
def append (p q : RelSeries r) (connect : r p.last q.head) : RelSeries r where
  length := p.length + q.length + 1
  toFun := Fin.append p q ∘ Fin.cast (by abel)
  step i := by
    obtain hi | rfl | hi :=
      lt_trichotomy i (Fin.castLE (by linarith) (Fin.last _ : Fin (p.length + 1)))
    · convert p.step ⟨i.1, hi⟩ <;> convert Fin.append_left p q _ <;> rfl
    · convert connect
      · convert Fin.append_left p q _; rfl
      · convert Fin.append_right p q _; rfl
    · set x := _; set y := _
      change r (Fin.append p q x) (Fin.append p q y)
      have hx : x = Fin.natAdd _ ⟨i - (p.length + 1), Nat.sub_lt_left_of_lt_add hi <|
        i.2.trans <| by linarith!⟩
      · ext; dsimp; rw [Nat.add_sub_cancel']; exact hi
      have hy : y = Fin.natAdd _ ⟨i - p.length, Nat.sub_lt_left_of_lt_add (le_of_lt hi)
        (by exact i.2)⟩
      · ext
        dsimp
        conv_rhs => rw [Nat.add_comm p.length 1, add_assoc,
          Nat.add_sub_cancel' <| le_of_lt (show p.length < i.1 from hi), add_comm]
      rw [hx, Fin.append_right, hy, Fin.append_right]
      convert q.step ⟨i - (p.length + 1), Nat.sub_lt_left_of_lt_add hi <|
        by convert i.2 using 1; abel⟩
      rw [Fin.succ_mk, Nat.sub_eq_iff_eq_add (le_of_lt hi : p.length ≤ i),
        Nat.add_assoc _ 1, add_comm 1, Nat.sub_add_cancel]
      exact hi

/--
For two types `α, β` and relation on them `r, s`, if `f : α → β` preserves relation `r`, then an
`r`-series can be pushed out to an `s`-series by
`a₀ -r→ a₁ -r→ ... -r→ aₙ ↦ f a₀ -s→ f a₁ -s→ ... -s→ f aₙ`
-/
@[simps]
def map (p : RelSeries r)
    (f : α → β) (hf : ∀ ⦃x y : α⦄, r x y → s (f x) (f y)) : RelSeries s where
  length := p.length
  toFun := f.comp p
  step := (hf <| p.step .)

/--
If `a₀ -r→ a₁ -r→ ... -r→ aₙ` is an `r`-series and `a` is such that
`aᵢ -r→ a -r→ a_ᵢ₊₁`, then
`a₀ -r→ a₁ -r→ ... -r→ a_i -r→ a -r→ aᵢ₊₁ -r→ ... -r→ aₙ`
is another `r`-series
-/
@[simps]
def insertNth (p : RelSeries r) (i : Fin p.length) (a : α)
    (prev_connect : r (p (Fin.castSucc i)) a) (connect_next : r a (p i.succ)) : RelSeries r where
  toFun := (Fin.castSucc i.succ).insertNth a p
  step m := by
    set x := _; set y := _; change r x y
    obtain hm | hm | hm := lt_trichotomy m.1 i.1
    · convert p.step ⟨m, hm.trans i.2⟩
      · show Fin.insertNth _ _ _ _ = _
        rw [Fin.insertNth_apply_below]
        pick_goal 2; exact hm.trans (lt_add_one _)
        simp
      · show Fin.insertNth _ _ _ _ = _
        rw [Fin.insertNth_apply_below]
        pick_goal 2; change m.1 + 1 < i.1 + 1; rwa [add_lt_add_iff_right]
        simp; rfl
    · rw [show x = p m from show Fin.insertNth _ _ _ _ = _ by
        rw [Fin.insertNth_apply_below]
        pick_goal 2; show m.1 < i.1 + 1; exact hm ▸ lt_add_one _
        simp]
      convert prev_connect
      · ext; exact hm
      · change Fin.insertNth _ _ _ _ = _
        rw [show m.succ = i.succ.castSucc by ext; change _ + 1 = _ + 1; rw [hm],
          Fin.insertNth_apply_same]
    · rw [Nat.lt_iff_add_one_le, le_iff_lt_or_eq] at hm
      obtain hm | hm := hm
      · convert p.step ⟨m.1 - 1, Nat.sub_lt_right_of_lt_add (by linarith) m.2⟩
        · change Fin.insertNth _ _ _ _ = _
          rw [Fin.insertNth_apply_above (h := hm)]
          aesop
        · change Fin.insertNth _ _ _ _ = _
          rw [Fin.insertNth_apply_above]
          swap; exact hm.trans (lt_add_one _)
          simp only [Fin.val_succ, Nat.zero_eq, Fin.pred_succ, eq_rec_constant, ge_iff_le,
            Fin.succ_mk]
          congr
          exact Fin.ext <| Eq.symm <| Nat.succ_pred_eq_of_pos (lt_trans (Nat.zero_lt_succ _) hm)
      · convert connect_next
        · change Fin.insertNth _ _ _ _ = _
          rw [show m.castSucc = i.succ.castSucc from Fin.ext hm.symm, Fin.insertNth_apply_same]
        · change Fin.insertNth _ _ _ _ = _
          rw [Fin.insertNth_apply_above]
          swap; change i.1 + 1 < m.1 + 1; rw [hm]; exact lt_add_one _
          simp only [Fin.pred_succ, eq_rec_constant]
          congr; ext; exact hm.symm

end RelSeries

/-- A type is finite dimensional if its `LTSeries` has bounded length. -/
abbrev FiniteDimensionalOrder (γ : Type*) [Preorder γ] :=
  Rel.FiniteDimensional ((. < .) : γ → γ → Prop)

/-- A type is infinite dimensional if it has `LTSeries` of at least arbitrary length -/
abbrev InfiniteDimensionalOrder (γ : Type*) [Preorder γ] :=
  Rel.InfiniteDimensional ((. < .) : γ → γ → Prop)

section LTSeries

variable (α) [Preorder α] [Preorder β]
/--
If `α` is a preorder, a LTSeries is a relation series of the less than relation.
-/
abbrev LTSeries := RelSeries ((. < .) : Rel α α)

namespace LTSeries

/-- The longest `<`-series when a type is finite dimensional -/
protected noncomputable def longestOf [FiniteDimensionalOrder α] : LTSeries α :=
  RelSeries.longestOf _

/-- A `<`-series with length `n` if the relation is infinite dimensional -/
protected noncomputable def withLength [InfiniteDimensionalOrder α] (n : ℕ) : LTSeries α :=
  RelSeries.withLength _ n

@[simp] lemma length_withLength [InfiniteDimensionalOrder α] (n : ℕ) :
    (LTSeries.withLength α n).length = n :=
  RelSeries.length_withLength _ _

/-- if `α` is infinite dimensional, then `α` is nonempty. -/
lemma nonempty_of_infiniteDimensionalType [InfiniteDimensionalOrder α] : Nonempty α :=
  ⟨LTSeries.withLength α 0 0⟩

variable {α}

lemma longestOf_is_longest [FiniteDimensionalOrder α] (x : LTSeries α) :
    x.length ≤ (LTSeries.longestOf α).length :=
  RelSeries.length_le_length_longestOf _ _

lemma longestOf_len_unique [FiniteDimensionalOrder α] (p : LTSeries α)
    (is_longest : ∀ (q : LTSeries α), q.length ≤ p.length) :
    p.length = (LTSeries.longestOf α).length :=
  le_antisymm (longestOf_is_longest _) (is_longest _)


lemma strictMono (x : LTSeries α) : StrictMono x :=
  fun _ _ h => x.rel_of_lt h

lemma monotone (x : LTSeries α) : Monotone x :=
  x.strictMono.monotone


/-- An alternative constructor of `LTSeries` from a strictly monotone function. -/
@[simps]
def mk (length : ℕ) (toFun : Fin (length + 1) → α) (strictMono : StrictMono toFun) :
    LTSeries α where
  toFun := toFun
  step i := strictMono <| lt_add_one i.1

/--
For two preorders `α, β`, if `f : α → β` is strictly monotonic, then a strict chain of `α`
can be pushed out to a strict chain of `β` by
`a₀ < a₁ < ... < aₙ ↦ f a₀ < f a₁ < ... < f aₙ`
-/
@[simps!]
def map (p : LTSeries α) (f : α → β) (hf : StrictMono f) : LTSeries β :=
  LTSeries.mk p.length (f.comp p) (hf.comp p.strictMono)

/--
For two preorders `α, β`, if `f : α → β` is surjective and strictly comonotonic, then a
strict series of `β` can be pulled back to a strict chain of `α` by
`b₀ < b₁ < ... < bₙ ↦ f⁻¹ b₀ < f⁻¹ b₁ < ... < f⁻¹ bₙ` where `f⁻¹ bᵢ` is an arbitrary element in the
preimage of `f⁻¹ {bᵢ}`.
-/
@[simps!]
noncomputable def comap (p : LTSeries β) (f : α → β)
  (comap : ∀ ⦃x y⦄, f x < f y → x < y)
  (surjective : Function.Surjective f) :
  LTSeries α := mk p.length (fun i ↦ (surjective (p i)).choose)
    (fun i j h ↦ comap (by simpa only [(surjective _).choose_spec] using p.strictMono h))

end LTSeries

end LTSeries
