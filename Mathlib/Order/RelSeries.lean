/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Fangming Li
-/
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Rel
import Mathlib.Data.Fin.VecNotation

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

@[ext (iff := false)]
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
  (Fin.lt_or_eq_of_le h).imp (x.rel_of_lt ·) (by rw [·])

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
def toList (x : RelSeries r) : List α := List.ofFn x

@[simp]
lemma length_toList (x : RelSeries r) : x.toList.length = x.length + 1 :=
  List.length_ofFn _

@[simp]
lemma toList_singleton (x : α) : (singleton r x).toList = [x] :=
  rfl

lemma toList_chain' (x : RelSeries r) : x.toList.Chain' r := by
  rw [List.chain'_iff_get]
  intros i h
  convert x.step ⟨i, by simpa [toList] using h⟩ <;> apply List.get_ofFn

lemma toList_ne_nil (x : RelSeries r) : x.toList ≠ [] := fun m =>
  List.eq_nil_iff_forall_not_mem.mp m (x 0) <| (List.mem_ofFn _ _).mpr ⟨_, rfl⟩

/-- Every nonempty list satisfying the chain condition gives a relation series -/
@[simps]
def fromListChain' (x : List α) (x_ne_nil : x ≠ []) (hx : x.Chain' r) : RelSeries r where
  length := x.length - 1
  toFun i := x[Fin.cast (Nat.succ_pred_eq_of_pos <| List.length_pos_iff.mpr x_ne_nil) i]
  step i := List.chain'_iff_get.mp hx i i.2

/-- Relation series of `r` and nonempty list of `α` satisfying `r`-chain condition bijectively
corresponds to each other. -/
protected def Equiv : RelSeries r ≃ {x : List α | x ≠ [] ∧ x.Chain' r} where
  toFun x := ⟨_, x.toList_ne_nil, x.toList_chain'⟩
  invFun x := fromListChain' _ x.2.1 x.2.2
  left_inv x := ext (by simp [toList]) <| by ext; dsimp; apply List.get_ofFn
  right_inv x := by
    refine Subtype.ext (List.ext_get ?_ fun n hn1 _ => by dsimp; apply List.get_ofFn)
    have := Nat.succ_pred_eq_of_pos <| List.length_pos_iff.mpr x.2.1
    simp_all [toList]

lemma toList_injective : Function.Injective (RelSeries.toList (r := r)) :=
  fun _ _ h ↦ (RelSeries.Equiv).injective <| Subtype.ext h

-- TODO : build a similar bijection between `RelSeries α` and `Quiver.Path`

end RelSeries

namespace Rel

/-- A relation `r` is said to be finite dimensional iff there is a relation series of `r` with the
  maximum length. -/
@[mk_iff]
class FiniteDimensional : Prop where
  /-- A relation `r` is said to be finite dimensional iff there is a relation series of `r` with the
    maximum length. -/
  exists_longest_relSeries : ∃ x : RelSeries r, ∀ y : RelSeries r, y.length ≤ x.length

/-- A relation `r` is said to be infinite dimensional iff there exists relation series of arbitrary
  length. -/
@[mk_iff]
class InfiniteDimensional : Prop where
  /-- A relation `r` is said to be infinite dimensional iff there exists relation series of
    arbitrary length. -/
  exists_relSeries_with_length : ∀ n : ℕ, ∃ x : RelSeries r, x.length = n

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

section
variable {r} {s : RelSeries r} {x : α}

/-- If a relation on `α` is infinite dimensional, then `α` is nonempty. -/
lemma nonempty_of_infiniteDimensional [r.InfiniteDimensional] : Nonempty α :=
  ⟨RelSeries.withLength r 0 0⟩

lemma nonempty_of_finiteDimensional [r.FiniteDimensional] : Nonempty α := by
  obtain ⟨p, _⟩ := (Rel.finiteDimensional_iff r).mp ‹_›
  exact ⟨p 0⟩

instance membership : Membership α (RelSeries r) :=
  ⟨Function.swap (· ∈ Set.range ·)⟩

theorem mem_def : x ∈ s ↔ x ∈ Set.range s := Iff.rfl

@[simp] theorem mem_toList : x ∈ s.toList ↔ x ∈ s := by
  rw [RelSeries.toList, List.mem_ofFn', RelSeries.mem_def]

theorem subsingleton_of_length_eq_zero (hs : s.length = 0) : {x | x ∈ s}.Subsingleton := by
  rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩
  congr!
  exact finCongr (by rw [hs, zero_add]) |>.injective <| Subsingleton.elim (α := Fin 1) _ _

theorem length_ne_zero_of_nontrivial (h : {x | x ∈ s}.Nontrivial) : s.length ≠ 0 :=
  fun hs ↦ h.not_subsingleton <| subsingleton_of_length_eq_zero hs

theorem length_pos_of_nontrivial (h : {x | x ∈ s}.Nontrivial) : 0 < s.length :=
  Nat.pos_iff_ne_zero.mpr <| length_ne_zero_of_nontrivial h

theorem length_ne_zero (irrefl : Irreflexive r) : s.length ≠ 0 ↔ {x | x ∈ s}.Nontrivial := by
  refine ⟨fun h ↦ ⟨s 0, by simp [mem_def], s 1, by simp [mem_def], fun rid ↦ irrefl (s 0) ?_⟩,
    length_ne_zero_of_nontrivial⟩
  nth_rw 2 [rid]
  convert s.step ⟨0, by omega⟩
  ext
  simpa [Nat.pos_iff_ne_zero]

theorem length_pos (irrefl : Irreflexive r) : 0 < s.length ↔ {x | x ∈ s}.Nontrivial :=
  Nat.pos_iff_ne_zero.trans <| length_ne_zero irrefl

lemma length_eq_zero (irrefl : Irreflexive r) : s.length = 0 ↔ {x | x ∈ s}.Subsingleton := by
  rw [← not_ne_iff, length_ne_zero irrefl, Set.not_nontrivial_iff]

/-- Start of a series, i.e. for `a₀ -r→ a₁ -r→ ... -r→ aₙ`, its head is `a₀`.

Since a relation series is assumed to be non-empty, this is well defined. -/
def head (x : RelSeries r) : α := x 0

/-- End of a series, i.e. for `a₀ -r→ a₁ -r→ ... -r→ aₙ`, its last element is `aₙ`.

Since a relation series is assumed to be non-empty, this is well defined. -/
def last (x : RelSeries r) : α := x <| Fin.last _

lemma apply_zero (p : RelSeries r) : p 0 = p.head := rfl

lemma apply_last (x : RelSeries r) : x (Fin.last <| x.length) = x.last := rfl

lemma head_mem (x : RelSeries r) : x.head ∈ x := ⟨_, rfl⟩

lemma last_mem (x : RelSeries r) : x.last ∈ x := ⟨_, rfl⟩

@[simp]
lemma head_singleton {r : Rel α α} (x : α) : (singleton r x).head = x := by simp [singleton, head]

@[simp]
lemma last_singleton {r : Rel α α} (x : α) : (singleton r x).last = x := by simp [singleton, last]

@[simp]
lemma head_toList (p : RelSeries r) : p.toList.head p.toList_ne_nil = p.head := by
  simp [toList, apply_zero]

@[simp]
lemma toList_getElem_eq_apply (p : RelSeries r) (i : Fin (p.length + 1)) :
    p.toList[(i : ℕ)] = p i := by
  simp only [Fin.getElem_fin, toList, List.getElem_ofFn p.toFun]

@[simp]
lemma toList_getElem_zero_eq_head (p : RelSeries r) : p.toList[0] = p.head := by
  simp [head, ← toList_getElem_eq_apply]

@[simp]
lemma toList_fromListChain' (l : List α) (l_ne_nil : l ≠ []) (hl : l.Chain' r) :
    (fromListChain' l l_ne_nil hl).toList = l :=
  Subtype.ext_iff.mp <| RelSeries.Equiv.right_inv ⟨l, ⟨l_ne_nil, hl⟩⟩

@[simp]
lemma head_fromListChain' (l : List α) (l_ne_nil : l ≠ [])
    (hl : l.Chain' r) :
    (fromListChain' l l_ne_nil hl).head = l.head l_ne_nil := by
  simp [← toList_getElem_zero_eq_head, List.getElem_zero_eq_head]

end

variable {r s}

/--
If `a₀ -r→ a₁ -r→ ... -r→ aₙ` and `b₀ -r→ b₁ -r→ ... -r→ bₘ` are two strict series
such that `r aₙ b₀`, then there is a chain of length `n + m + 1` given by
`a₀ -r→ a₁ -r→ ... -r→ aₙ -r→ b₀ -r→ b₁ -r→ ... -r→ bₘ`.
-/
@[simps length]
def append (p q : RelSeries r) (connect : r p.last q.head) : RelSeries r where
  length := p.length + q.length + 1
  toFun := Fin.append p q ∘ Fin.cast (by omega)
  step i := by
    obtain hi | rfl | hi :=
      lt_trichotomy i (Fin.castLE (by omega) (Fin.last _ : Fin (p.length + 1)))
    · convert p.step ⟨i.1, hi⟩ <;> convert Fin.append_left p q _ <;> rfl
    · convert connect
      · convert Fin.append_left p q _
      · convert Fin.append_right p q _; rfl
    · set x := _; set y := _
      change r (Fin.append p q x) (Fin.append p q y)
      have hx : x = Fin.natAdd _ ⟨i - (p.length + 1), Nat.sub_lt_left_of_lt_add hi <|
          i.2.trans <| by omega⟩ := by
        ext; dsimp [x, y]; rw [Nat.add_sub_cancel']; exact hi
      have hy : y = Fin.natAdd _ ⟨i - p.length, Nat.sub_lt_left_of_lt_add (le_of_lt hi)
          (by exact i.2)⟩ := by
        ext
        dsimp
        conv_rhs => rw [Nat.add_comm p.length 1, add_assoc,
          Nat.add_sub_cancel' <| le_of_lt (show p.length < i.1 from hi), add_comm]
        rfl
      rw [hx, Fin.append_right, hy, Fin.append_right]
      convert q.step ⟨i - (p.length + 1), Nat.sub_lt_left_of_lt_add hi <| by omega⟩
      rw [Fin.succ_mk, Nat.sub_eq_iff_eq_add (le_of_lt hi : p.length ≤ i),
        Nat.add_assoc _ 1, add_comm 1, Nat.sub_add_cancel]
      exact hi

lemma append_apply_left (p q : RelSeries r) (connect : r p.last q.head)
    (i : Fin (p.length + 1)) :
    p.append q connect ((i.castAdd (q.length + 1)).cast (by dsimp; omega)) = p i := by
  delta append
  simp only [Function.comp_apply]
  convert Fin.append_left _ _ _

lemma append_apply_right (p q : RelSeries r) (connect : r p.last q.head)
    (i : Fin (q.length + 1)) :
    p.append q connect (i.natAdd p.length + 1) = q i := by
  delta append
  simp only [Fin.coe_natAdd, Nat.cast_add, Function.comp_apply]
  convert Fin.append_right _ _ _
  ext
  simp only [Fin.coe_cast, Fin.coe_natAdd]
  conv_rhs => rw [add_assoc, add_comm 1, ← add_assoc]
  change _ % _ = _
  simp only [Nat.add_mod_mod, Nat.mod_add_mod, Nat.one_mod, Nat.mod_succ_eq_iff_lt]
  omega

@[simp] lemma head_append (p q : RelSeries r) (connect : r p.last q.head) :
    (p.append q connect).head = p.head :=
  append_apply_left p q connect 0

@[simp] lemma last_append (p q : RelSeries r) (connect : r p.last q.head) :
    (p.append q connect).last = q.last := by
  delta last
  convert append_apply_right p q connect (Fin.last _)
  ext
  change _ = _ % _
  simp only [append_length, Fin.val_last, Fin.natAdd_last, Nat.one_mod, Nat.mod_add_mod,
    Nat.mod_succ]

/--
For two types `α, β` and relation on them `r, s`, if `f : α → β` preserves relation `r`, then an
`r`-series can be pushed out to an `s`-series by
`a₀ -r→ a₁ -r→ ... -r→ aₙ ↦ f a₀ -s→ f a₁ -s→ ... -s→ f aₙ`
-/
@[simps length]
def map (p : RelSeries r) (f : r →r s) : RelSeries s where
  length := p.length
  toFun := f.1.comp p
  step := (f.2 <| p.step ·)

@[simp] lemma map_apply (p : RelSeries r) (f : r →r s) (i : Fin (p.length + 1)) :
    p.map f i = f (p i) := rfl

@[simp] lemma head_map (p : RelSeries r) (f : r →r s) : (p.map f).head = f p.head := rfl

@[simp] lemma last_map (p : RelSeries r) (f : r →r s) : (p.map f).last = f p.last := rfl

/--
If `a₀ -r→ a₁ -r→ ... -r→ aₙ` is an `r`-series and `a` is such that
`aᵢ -r→ a -r→ a_ᵢ₊₁`, then
`a₀ -r→ a₁ -r→ ... -r→ aᵢ -r→ a -r→ aᵢ₊₁ -r→ ... -r→ aₙ`
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
        pick_goal 2
        · exact hm.trans (lt_add_one _)
        simp
      · show Fin.insertNth _ _ _ _ = _
        rw [Fin.insertNth_apply_below]
        pick_goal 2
        · change m.1 + 1 < i.1 + 1; rwa [add_lt_add_iff_right]
        simp; rfl
    · rw [show x = p m from show Fin.insertNth _ _ _ _ = _ by
        rw [Fin.insertNth_apply_below]
        pick_goal 2
        · show m.1 < i.1 + 1; exact hm ▸ lt_add_one _
        simp]
      convert prev_connect
      · ext; exact hm
      · change Fin.insertNth _ _ _ _ = _
        rw [show m.succ = i.succ.castSucc by ext; change _ + 1 = _ + 1; rw [hm],
          Fin.insertNth_apply_same]
    · rw [Nat.lt_iff_add_one_le, le_iff_lt_or_eq] at hm
      obtain hm | hm := hm
      · convert p.step ⟨m.1 - 1, Nat.sub_lt_right_of_lt_add (by omega) m.2⟩
        · change Fin.insertNth _ _ _ _ = _
          rw [Fin.insertNth_apply_above (h := hm)]
          aesop
        · change Fin.insertNth _ _ _ _ = _
          rw [Fin.insertNth_apply_above]
          swap
          · exact hm.trans (lt_add_one _)
          simp only [Fin.val_succ, Fin.pred_succ, eq_rec_constant, Fin.succ_mk]
          congr
          exact Fin.ext <| Eq.symm <| Nat.succ_pred_eq_of_pos (lt_trans (Nat.zero_lt_succ _) hm)
      · convert connect_next
        · change Fin.insertNth _ _ _ _ = _
          rw [show m.castSucc = i.succ.castSucc from Fin.ext hm.symm, Fin.insertNth_apply_same]
        · change Fin.insertNth _ _ _ _ = _
          rw [Fin.insertNth_apply_above]
          swap
          · change i.1 + 1 < m.1 + 1; omega
          simp only [Fin.pred_succ, eq_rec_constant]
          congr; ext; exact hm.symm

/--
A relation series `a₀ -r→ a₁ -r→ ... -r→ aₙ` of `r` gives a relation series of the reverse of `r`
by reversing the series `aₙ ←r- aₙ₋₁ ←r- ... ←r- a₁ ←r- a₀`.
-/
@[simps length]
def reverse (p : RelSeries r) : RelSeries (fun (a b : α) ↦ r b a) where
  length := p.length
  toFun := p ∘ Fin.rev
  step i := by
    rw [Function.comp_apply, Function.comp_apply]
    have hi : i.1 + 1 ≤ p.length := by omega
    convert p.step ⟨p.length - (i.1 + 1), Nat.sub_lt_self (by omega) hi⟩
    · ext; simp
    · ext
      simp only [Fin.val_rev, Fin.coe_castSucc, Fin.val_succ]
      omega

@[simp] lemma reverse_apply (p : RelSeries r) (i : Fin (p.length + 1)) :
    p.reverse i = p i.rev := rfl

@[simp] lemma last_reverse (p : RelSeries r) : p.reverse.last = p.head := by
  simp [RelSeries.last, RelSeries.head]

@[simp] lemma head_reverse (p : RelSeries r) : p.reverse.head = p.last := by
  simp [RelSeries.last, RelSeries.head]

@[simp] lemma reverse_reverse {r : Rel α α} (p : RelSeries r) : p.reverse.reverse = p := by
  ext <;> simp

/--
Given a series `a₀ -r→ a₁ -r→ ... -r→ aₙ` and an `a` such that `a₀ -r→ a` holds, there is
a series of length `n+1`: `a -r→ a₀ -r→ a₁ -r→ ... -r→ aₙ`.
-/
@[simps! length]
def cons (p : RelSeries r) (newHead : α) (rel : r newHead p.head) : RelSeries r :=
  (singleton r newHead).append p rel

@[simp] lemma head_cons (p : RelSeries r) (newHead : α) (rel : r newHead p.head) :
    (p.cons newHead rel).head = newHead := rfl

@[simp] lemma last_cons (p : RelSeries r) (newHead : α) (rel : r newHead p.head) :
    (p.cons newHead rel).last = p.last := by
  delta cons
  rw [last_append]

@[simp]
lemma append_singleton_left (p : RelSeries r) (x : α) (hx : r x p.head) :
    (singleton r x).append p hx = p.cons x hx :=
  rfl

@[simp]
lemma toList_cons (p : RelSeries r) (x : α) (hx : r x p.head) :
    (p.cons x hx).toList = x :: p.toList := by
  simp only [toList, cons_length, List.ofFn_succ, Fin.cast_zero, apply_zero, head_cons,
    Fin.cast_succ_eq, singleton_length, List.cons.injEq, List.ofFn_inj, true_and]
  refine ⟨rfl, ?_⟩
  ext i
  simp [cons, append, singleton, Fin.append, Fin.addCases, Fin.subNat, Fin.succ]

lemma fromListChain'_cons (l : List α) (l_ne_nil : l ≠ [])
    (hl : l.Chain' r) (x : α) (hx : r x (l.head l_ne_nil)) :
    fromListChain' (x :: l) (by simp) (hl.cons_of_ne_nil l_ne_nil hx) =
      (fromListChain' l l_ne_nil hl).cons x (by simpa) := by
  apply toList_injective
  simp

lemma append_cons {p q : RelSeries r} {x : α} (hx : r x p.head) (hq : r p.last q.head) :
    (p.cons x hx).append q (by simpa) = (p.append q hq).cons x (by simpa) := by
  simp only [cons]
  ext n
  · simp
    omega
  · simp only [singleton, Nat.reduceAdd, append, Fin.append, cons, id_eq, eq_mpr_eq_cast,
      Function.comp_apply, Fin.addCases, Fin.coe_cast, zero_add, Fin.coe_castLT, Nat.lt_one_iff,
      Fin.cast_trans, Fin.subNat, Fin.natAdd_mk, eq_rec_constant, Int.reduceNeg,
      Int.Nat.cast_ofNat_Int, Fin.cast_mk, Fin.castLT_mk, Fin.subNat_mk]
    split_ifs <;> try rfl; <;> try omega
    congr 2
    omega

/--
Given a series `a₀ -r→ a₁ -r→ ... -r→ aₙ` and an `a` such that `aₙ -r→ a` holds, there is
a series of length `n+1`: `a₀ -r→ a₁ -r→ ... -r→ aₙ -r→ a`.
-/
@[simps! length]
def snoc (p : RelSeries r) (newLast : α) (rel : r p.last newLast) : RelSeries r :=
  p.append (singleton r newLast) rel

@[simp] lemma head_snoc (p : RelSeries r) (newLast : α) (rel : r p.last newLast) :
    (p.snoc newLast rel).head = p.head := by
  delta snoc; rw [head_append]

@[simp] lemma last_snoc (p : RelSeries r) (newLast : α) (rel : r p.last newLast) :
    (p.snoc newLast rel).last = newLast := last_append _ _ _

-- This lemma is useful because `last_snoc` is about `Fin.last (p.snoc _ _).length`, but we often
-- see `Fin.last (p.length + 1)` in practice. They are equal by definition, but sometimes simplifier
-- does not pick up `last_snoc`
@[simp] lemma last_snoc' (p : RelSeries r) (newLast : α) (rel : r p.last newLast) :
    p.snoc newLast rel (Fin.last (p.length + 1)) = newLast := last_append _ _ _

@[simp] lemma snoc_castSucc (s : RelSeries r) (a : α) (connect : r s.last a)
    (i : Fin (s.length + 1)) : snoc s a connect (Fin.castSucc i) = s i :=
  Fin.append_left _ _ i

lemma mem_snoc {p : RelSeries r} {newLast : α} {rel : r p.last newLast} {x : α} :
    x ∈ p.snoc newLast rel ↔ x ∈ p ∨ x = newLast := by
  simp only [snoc, append, singleton_length, Nat.add_zero, Nat.reduceAdd, Fin.cast_refl,
    Function.comp_id, mem_def, id_eq, Set.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    exact Fin.lastCases (Or.inr <| Fin.append_right _ _ 0) (fun i => Or.inl ⟨⟨i.1, i.2⟩,
      (Fin.append_left _ _ _).symm⟩) i
  · intro h
    rcases h with (⟨i, rfl⟩ | rfl)
    · exact ⟨i.castSucc, Fin.append_left _ _ _⟩
    · exact ⟨Fin.last _, Fin.append_right _ _ 0⟩

/--
If a series `a₀ -r→ a₁ -r→ ...` has positive length, then `a₁ -r→ ...` is another series
-/
@[simps]
def tail (p : RelSeries r) (len_pos : p.length ≠ 0) : RelSeries r where
  length := p.length - 1
  toFun := Fin.tail p ∘ (Fin.cast <| Nat.succ_pred_eq_of_pos <| Nat.pos_of_ne_zero len_pos)
  step i := p.step ⟨i.1 + 1, Nat.lt_pred_iff.mp i.2⟩

@[simp] lemma head_tail (p : RelSeries r) (len_pos : p.length ≠ 0) :
    (p.tail len_pos).head = p 1 := by
  show p (Fin.succ _) = p 1
  congr
  ext
  show (1 : ℕ) = (1 : ℕ) % _
  rw [Nat.mod_eq_of_lt]
  simpa only [lt_add_iff_pos_left, Nat.pos_iff_ne_zero]

@[simp] lemma last_tail (p : RelSeries r) (len_pos : p.length ≠ 0) :
    (p.tail len_pos).last = p.last := by
  show p _ = p _
  congr
  ext
  simp only [tail_length, Fin.val_succ, Fin.coe_cast, Fin.val_last]
  exact Nat.succ_pred_eq_of_pos (by simpa [Nat.pos_iff_ne_zero] using len_pos)

@[simp]
lemma tail_cons (p : RelSeries r) (x : α) (hx : r x p.head) :
    (p.cons x hx).tail (by simp) = p := by
  ext n
  · simp
  · simp [-append_singleton_left, Fin.tail, cons, append, Fin.append, Fin.addCases,
      Fin.subNat, Fin.cast]

lemma cons_self_tail {p : RelSeries r} (hp : p.length ≠ 0) :
    (p.tail hp).cons p.head (p.3 ⟨0, Nat.zero_lt_of_ne_zero hp⟩) = p := by
  ext n
  · rw [cons_length, tail_length]
    exact (Nat.succ_pred_eq_of_ne_zero hp)
  unfold cons append Fin.append Fin.addCases
  by_cases h : n.1 = 0
  · have : n = 0 := Fin.eq_of_val_eq h
    simp [this, apply_zero]
  · simp only [singleton_length, Nat.reduceAdd, Nat.lt_one_iff,
      tail_toFun, Function.comp_apply, Fin.tail, eq_rec_constant, Fin.coe_cast, dif_neg h]
    congr
    exact Fin.val_inj.mp (Nat.succ_pred_eq_of_ne_zero h)

/--
To show a proposition `p` for `xs : RelSeries r` it suffices to show it for all singletons
and to show that when `p` holds for `xs` it also holds for `xs` prepended with one element.

Note: This can also be used to construct data, but it does not have good definitional properties,
since `(p.cons x hx).tail _ = p` is not a definitional equality.
-/
@[elab_as_elim]
def inductionOn (motive : RelSeries r → Sort*)
    (singleton : (x : α) → motive (RelSeries.singleton r x))
    (cons : (p : RelSeries r) → (x : α) → (hx : r x p.head) → (hp : motive p) →
      motive (p.cons x hx)) (p : RelSeries r) :
    motive p := by
  let this {n : ℕ} (heq : p.length = n) : motive p := by
    induction' n with d hd generalizing p
    · convert singleton p.head
      ext n
      exact heq
      simp [show n = 0 by omega, apply_zero]
    · have lq := p.tail_length (heq ▸ d.zero_ne_add_one.symm)
      nth_rw 3 [heq] at lq
      convert cons (p.tail (heq ▸ d.zero_ne_add_one.symm)) p.head
        (p.3 ⟨0, heq ▸ d.zero_lt_succ⟩) (hd _ lq)
      exact (p.cons_self_tail (heq ▸ d.zero_ne_add_one.symm)).symm
  exact this rfl

@[simp]
lemma toList_tail (p : RelSeries r) (hp : p.length ≠ 0) :
    (p.tail hp).toList = p.toList.tail := by
  induction p using inductionOn
  · simp at hp
  · simp

lemma append_toList (p q : RelSeries r) (rel : r p.last q.head) :
    (p.append q rel).toList = p.toList ++ q.toList := by
  induction p using RelSeries.inductionOn with
  | singleton => simp
  | cons p x hx hp =>
    simp only [last_cons] at rel
    simpa [toList_cons, List.cons_append, append_cons _ rel] using hp rel

/--
If a series ``a₀ -r→ a₁ -r→ ... -r→ aₙ``, then `a₀ -r→ a₁ -r→ ... -r→ aₙ₋₁` is
another series -/
@[simps]
def eraseLast (p : RelSeries r) : RelSeries r where
  length := p.length - 1
  toFun i := p ⟨i, lt_of_lt_of_le i.2 (Nat.succ_le_succ (Nat.sub_le _ _))⟩
  step i := p.step ⟨i, lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩

@[simp] lemma head_eraseLast (p : RelSeries r) : p.eraseLast.head = p.head := rfl

@[simp] lemma last_eraseLast (p : RelSeries r) :
    p.eraseLast.last = p ⟨p.length.pred, Nat.lt_succ_iff.2 (Nat.pred_le _)⟩ := rfl

/-- In a non-trivial series `p`, the last element of `p.eraseLast` is related to `p.last` -/
lemma eraseLast_last_rel_last (p : RelSeries r) (h : p.length ≠ 0) :
    r p.eraseLast.last p.last := by
  simp only [last, Fin.last, eraseLast_length, eraseLast_toFun]
  convert p.step ⟨p.length - 1, by omega⟩
  simp only [Nat.succ_eq_add_one, Fin.succ_mk]; omega

/--
Given two series of the form `a₀ -r→ ... -r→ X` and `X -r→ b ---> ...`,
then `a₀ -r→ ... -r→ X -r→ b ...` is another series obtained by combining the given two.
-/
@[simps]
def smash (p q : RelSeries r) (connect : p.last = q.head) : RelSeries r where
  length := p.length + q.length
  toFun i :=
    if H : i.1 < p.length
    then p ⟨i.1, H.trans (lt_add_one _)⟩
    else q ⟨i.1 - p.length,
      Nat.sub_lt_left_of_lt_add (by rwa [not_lt] at H) (by rw [← add_assoc]; exact i.2)⟩
  step i := by
    dsimp only
    by_cases h₂ : i.1 + 1 < p.length
    · have h₁ : i.1 < p.length := lt_trans (lt_add_one _) h₂
      simp only [Fin.coe_castSucc, Fin.val_succ]
      rw [dif_pos h₁, dif_pos h₂]
      convert p.step ⟨i, h₁⟩ using 1
    · simp only [Fin.coe_castSucc, Fin.val_succ]
      rw [dif_neg h₂]
      by_cases h₁ : i.1 < p.length
      · rw [dif_pos h₁]
        have h₃ : p.length = i.1 + 1 := by omega
        convert p.step ⟨i, h₁⟩ using 1
        convert connect.symm
        · aesop
        · congr; aesop
      · rw [dif_neg h₁]
        convert q.step ⟨i.1 - p.length, _⟩ using 1
        · congr
          change (i.1 + 1) - _ = _
          rw [Nat.sub_add_comm]
          rwa [not_lt] at h₁
        · refine Nat.sub_lt_left_of_lt_add ?_ i.2
          rwa [not_lt] at h₁

lemma smash_castAdd {p q : RelSeries r} (connect : p.last = q.head) (i : Fin p.length) :
    p.smash q connect (Fin.castSucc <| i.castAdd q.length) = p (Fin.castSucc i) := by
  unfold smash
  dsimp
  rw [dif_pos i.2]
  rfl

lemma smash_succ_castAdd {p q : RelSeries r} (h : p.last = q.head)
    (i : Fin p.length) : p.smash q h (i.castAdd q.length).succ = p i.succ := by
  rw [smash_toFun]
  split_ifs with H
  · congr
  · simp only [Fin.val_succ, Fin.coe_castAdd] at H
    convert h.symm
    · congr
      simp only [Fin.val_succ, Fin.coe_castAdd, Nat.zero_mod, Nat.sub_eq_zero_iff_le]
      omega
    · congr
      ext
      change i.1 + 1 = p.length
      omega

lemma smash_natAdd {p q : RelSeries r} (h : p.last = q.head) (i : Fin q.length) :
    smash p q h (Fin.castSucc <| i.natAdd p.length) = q (Fin.castSucc i) := by
  rw [smash_toFun, dif_neg (by simp)]
  congr
  exact Nat.add_sub_self_left _ _

lemma smash_succ_natAdd {p q : RelSeries r} (h : p.last = q.head) (i : Fin q.length) :
    smash p q h (i.natAdd p.length).succ = q i.succ := by
  rw [smash_toFun]
  split_ifs with H
  · have H' : p.length < p.length + (i.1 + 1) := by omega
    exact (lt_irrefl _ (H.trans H')).elim
  · congr
    simp only [Fin.val_succ, Fin.coe_natAdd]
    rw [add_assoc, Nat.add_sub_cancel_left]

@[simp] lemma head_smash {p q : RelSeries r} (h : p.last = q.head) :
    (smash p q h).head = p.head := by
  delta head smash
  simp only [Fin.val_zero, Fin.zero_eta, zero_le, Nat.sub_eq_zero_of_le, dite_eq_ite,
    ite_eq_left_iff, not_lt, nonpos_iff_eq_zero]
  intro H; convert h.symm; congr; aesop

@[simp] lemma last_smash {p q : RelSeries r} (h : p.last = q.head) :
    (smash p q h).last = q.last := by
  delta smash last; aesop

/-- Given the series `a₀ -r→ … -r→ aᵢ -r→ … -r→ aₙ`, the series `a₀ -r→ … -r→ aᵢ`. -/
@[simps! length]
def take {r : Rel α α} (p : RelSeries r) (i : Fin (p.length + 1)) : RelSeries r where
  length := i
  toFun := fun ⟨j, h⟩ => p.toFun ⟨j, by omega⟩
  step := fun ⟨j, h⟩ => p.step ⟨j, by omega⟩

@[simp]
lemma head_take (p : RelSeries r) (i : Fin (p.length + 1)) :
    (p.take i).head = p.head := by simp [take, head]

@[simp]
lemma last_take (p : RelSeries r) (i : Fin (p.length + 1)) :
    (p.take i).last = p i := by simp [take, last, Fin.last]

/-- Given the series `a₀ -r→ … -r→ aᵢ -r→ … -r→ aₙ`, the series `aᵢ₊₁ -r→ … -r→ aᵢ`. -/
@[simps! length]
def drop (p : RelSeries r) (i : Fin (p.length + 1)) : RelSeries r where
  length := p.length - i
  toFun := fun ⟨j, h⟩ => p.toFun ⟨j+i, by omega⟩
  step := fun ⟨j, h⟩ => by
    convert p.step ⟨j+i.1, by omega⟩
    simp only [Nat.succ_eq_add_one, Fin.succ_mk]; omega

@[simp]
lemma head_drop (p : RelSeries r) (i : Fin (p.length + 1)) : (p.drop i).head = p.toFun i := by
  simp [drop, head]

@[simp]
lemma last_drop (p : RelSeries r) (i : Fin (p.length + 1)) : (p.drop i).last = p.last := by
  simp only [last, drop, Fin.last]
  congr
  omega

end RelSeries

variable {r} in
lemma Rel.not_finiteDimensional_iff [Nonempty α] :
    ¬ r.FiniteDimensional ↔ r.InfiniteDimensional := by
  rw [finiteDimensional_iff, infiniteDimensional_iff]
  push_neg
  constructor
  · intro H n
    induction n with
    | zero => refine ⟨⟨0, ![Nonempty.some ‹_›], by simp⟩, by simp⟩
    | succ n IH =>
      obtain ⟨l, hl⟩ := IH
      obtain ⟨l', hl'⟩ := H l
      exact ⟨l'.take ⟨n + 1, by simpa [hl] using hl'⟩, rfl⟩
  · intro H l
    obtain ⟨l', hl'⟩ := H (l.length + 1)
    exact ⟨l', by simp [hl']⟩

variable {r} in
lemma Rel.not_infiniteDimensional_iff [Nonempty α] :
    ¬ r.InfiniteDimensional ↔ r.FiniteDimensional := by
  rw [← not_finiteDimensional_iff, not_not]

lemma Rel.finiteDimensional_or_infiniteDimensional [Nonempty α] :
    r.FiniteDimensional ∨ r.InfiniteDimensional := by
  rw [← not_finiteDimensional_iff]
  exact em r.FiniteDimensional

/-- A type is finite dimensional if its `LTSeries` has bounded length. -/
abbrev FiniteDimensionalOrder (γ : Type*) [Preorder γ] :=
  Rel.FiniteDimensional ((· < ·) : γ → γ → Prop)

instance FiniteDimensionalOrder.ofUnique (γ : Type*) [Preorder γ] [Unique γ] :
    FiniteDimensionalOrder γ where
  exists_longest_relSeries := ⟨.singleton _ default, fun x ↦ by
    by_contra! r
    exact (ne_of_lt <| x.step ⟨0, by omega⟩) <| Subsingleton.elim _ _⟩

/-- A type is infinite dimensional if it has `LTSeries` of at least arbitrary length -/
abbrev InfiniteDimensionalOrder (γ : Type*) [Preorder γ] :=
  Rel.InfiniteDimensional ((· < ·) : γ → γ → Prop)

section LTSeries

variable (α) [Preorder α] [Preorder β]
/--
If `α` is a preorder, a LTSeries is a relation series of the less than relation.
-/
abbrev LTSeries := RelSeries ((· < ·) : Rel α α)

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
lemma nonempty_of_infiniteDimensionalOrder [InfiniteDimensionalOrder α] : Nonempty α :=
  ⟨LTSeries.withLength α 0 0⟩

@[deprecated (since := "2025-03-01")]
alias nonempty_of_infiniteDimensionalType := nonempty_of_infiniteDimensionalOrder

lemma nonempty_of_finiteDimensionalOrder [FiniteDimensionalOrder α] : Nonempty α := by
  obtain ⟨p, _⟩ := (Rel.finiteDimensional_iff _).mp ‹_›
  exact ⟨p 0⟩

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

lemma head_le_last (x : LTSeries α) : x.head ≤ x.last :=
  LTSeries.monotone x (Fin.zero_le _)

/-- An alternative constructor of `LTSeries` from a strictly monotone function. -/
@[simps]
def mk (length : ℕ) (toFun : Fin (length + 1) → α) (strictMono : StrictMono toFun) :
    LTSeries α where
  toFun := toFun
  step i := strictMono <| lt_add_one i.1

/-- An injection from the type of strictly monotone functions with limited length to `LTSeries`. -/
def injStrictMono (n : ℕ) :
    {f : (l : Fin n) × (Fin (l + 1) → α) // StrictMono f.2} ↪ LTSeries α where
  toFun f := mk f.1.1 f.1.2 f.2
  inj' f g e := by
    obtain ⟨⟨lf, f⟩, mf⟩ := f
    obtain ⟨⟨lg, g⟩, mg⟩ := g
    dsimp only at mf mg e
    have leq := congr($(e).length)
    rw [mk_length lf f mf, mk_length lg g mg, Fin.val_eq_val] at leq
    subst leq
    simp_rw [Subtype.mk_eq_mk, Sigma.mk.inj_iff, heq_eq_eq, true_and]
    have feq := fun i ↦ congr($(e).toFun i)
    simp_rw [mk_toFun lf f mf, mk_toFun lf g mg, mk_length lf f mf] at feq
    rwa [funext_iff]

/--
For two preorders `α, β`, if `f : α → β` is strictly monotonic, then a strict chain of `α`
can be pushed out to a strict chain of `β` by
`a₀ < a₁ < ... < aₙ ↦ f a₀ < f a₁ < ... < f aₙ`
-/
@[simps!]
def map (p : LTSeries α) (f : α → β) (hf : StrictMono f) : LTSeries β :=
  LTSeries.mk p.length (f.comp p) (hf.comp p.strictMono)

@[simp] lemma head_map (p : LTSeries α) (f : α → β) (hf : StrictMono f) :
  (p.map f hf).head = f p.head := rfl

@[simp] lemma last_map (p : LTSeries α) (f : α → β) (hf : StrictMono f) :
  (p.map f hf).last = f p.last := rfl

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

/-- The strict series `0 < … < n` in `ℕ`. -/
def range (n : ℕ) : LTSeries ℕ where
  length := n
  toFun := fun i => i
  step i := Nat.lt_add_one i

@[simp] lemma length_range (n : ℕ) : (range n).length = n := rfl

@[simp] lemma range_apply (n : ℕ) (i : Fin (n+1)) : (range n) i = i := rfl

@[simp] lemma head_range (n : ℕ) : (range n).head = 0 := rfl

@[simp] lemma last_range (n : ℕ) : (range n).last = n := rfl

/--
In ℕ, two entries in an `LTSeries` differ by at least the difference of their indices.
(Expressed in a way that avoids subtraction).
-/
lemma apply_add_index_le_apply_add_index_nat (p : LTSeries ℕ) (i j : Fin (p.length + 1))
    (hij : i ≤ j) : p i + j ≤ p j + i := by
  have ⟨i, hi⟩ := i
  have ⟨j, hj⟩ := j
  simp only [Fin.mk_le_mk] at hij
  simp only at *
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j _hij ih =>
    specialize ih (Nat.lt_of_succ_lt hj)
    have step : p ⟨j, _⟩ < p ⟨j + 1, _⟩ := p.step ⟨j, by omega⟩
    norm_cast at *; omega

/--
In ℤ, two entries in an `LTSeries` differ by at least the difference of their indices.
(Expressed in a way that avoids subtraction).
-/
lemma apply_add_index_le_apply_add_index_int (p : LTSeries ℤ) (i j : Fin (p.length + 1))
    (hij : i ≤ j) : p i + j ≤ p j + i := by
  -- The proof is identical to `LTSeries.apply_add_index_le_apply_add_index_nat`, but seemed easier
  -- to copy rather than to abstract
  have ⟨i, hi⟩ := i
  have ⟨j, hj⟩ := j
  simp only [Fin.mk_le_mk] at hij
  simp only at *
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j _hij ih =>
    specialize ih (Nat.lt_of_succ_lt hj)
    have step : p ⟨j, _⟩ < p ⟨j + 1, _⟩:= p.step ⟨j, by omega⟩
    norm_cast at *; omega

/-- In ℕ, the head and tail of an `LTSeries` differ at least by the length of the series -/
lemma head_add_length_le_nat (p : LTSeries ℕ) : p.head + p.length ≤ p.last :=
  LTSeries.apply_add_index_le_apply_add_index_nat _ _ (Fin.last _) (Fin.zero_le _)

/-- In ℤ, the head and tail of an `LTSeries` differ at least by the length of the series -/
lemma head_add_length_le_int (p : LTSeries ℤ) : p.head + p.length ≤ p.last := by
  simpa using LTSeries.apply_add_index_le_apply_add_index_int _ _ (Fin.last _) (Fin.zero_le _)

section Fintype

variable [Fintype α]

lemma length_lt_card (s : LTSeries α) : s.length < Fintype.card α := by
  by_contra! h
  obtain ⟨i, j, hn, he⟩ := Fintype.exists_ne_map_eq_of_card_lt s (by rw [Fintype.card_fin]; omega)
  wlog hl : i < j generalizing i j
  · exact this j i hn.symm he.symm (by omega)
  exact absurd he (s.strictMono hl).ne

instance [DecidableRel ((· < ·) : α → α → Prop)] : Fintype (LTSeries α) where
  elems := Finset.univ.map (injStrictMono (Fintype.card α))
  complete s := by
    have bl := s.length_lt_card
    obtain ⟨l, f, mf⟩ := s
    simp_rw [Finset.mem_map, Finset.mem_univ, true_and, Subtype.exists]
    use ⟨⟨l, bl⟩, f⟩, Fin.strictMono_iff_lt_succ.mpr mf; rfl

end Fintype

end LTSeries

end LTSeries

lemma not_finiteDimensionalOrder_iff [Preorder α] [Nonempty α] :
    ¬ FiniteDimensionalOrder α ↔ InfiniteDimensionalOrder α :=
  Rel.not_finiteDimensional_iff

lemma not_infiniteDimensionalOrder_iff [Preorder α] [Nonempty α] :
    ¬ InfiniteDimensionalOrder α ↔ FiniteDimensionalOrder α :=
  Rel.not_infiniteDimensional_iff

variable (α) in
lemma finiteDimensionalOrder_or_infiniteDimensionalOrder [Preorder α] [Nonempty α] :
    FiniteDimensionalOrder α ∨ InfiniteDimensionalOrder α :=
  Rel.finiteDimensional_or_infiniteDimensional _

/-- If `f : α → β` is a strictly monotonic function and `α` is an infinite dimensional type then so
  is `β`. -/
lemma infiniteDimensionalOrder_of_strictMono [Preorder α] [Preorder β]
    (f : α → β) (hf : StrictMono f) [InfiniteDimensionalOrder α] :
    InfiniteDimensionalOrder β :=
  ⟨fun n ↦ ⟨(LTSeries.withLength _ n).map f hf, LTSeries.length_withLength α n⟩⟩
