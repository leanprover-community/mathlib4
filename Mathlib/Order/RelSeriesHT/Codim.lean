import Mathlib.Order.RelSeriesHT.Defs
import Mathlib.Data.ENat.Lattice

variable {α : Type*} {r : Rel α α}
namespace RelSeriesHT

@[mk_iff]
class IsReduced {a b : α} (x : a -[r]→* b) : Prop where
  isReduced (y : a -[r]→* b) : x ≤ y → x.length ≤ y.length

@[simp]
instance isReduced_singleton (a : α) : (singleton (r := r) a).IsReduced := by
  simp only [singleton_le, length_singleton, zero_le, imp_self, implies_true, isReduced_iff]

@[simp]
lemma isReduced_cons (a : α) {b c : α} (x : b -[r]→* c) (hr : r a b) :
    (cons a x hr).IsReduced ↔ a ≠ b ∧ x.IsReduced := by
  simp only [isReduced_iff, length_cons, ne_eq]
  constructor
  · intro h
    have : a ≠ b := by
      rintro rfl
      specialize h x (cons_le_append a hr (singleton a) (le_refl _))
      simp at h
    use this
    intro y hy
    specialize h (cons a y hr) (cons_le_append a hr (ofRel hr) hy)
    simpa using h
  · rintro ⟨hne,h⟩
    intro y hy
    cases hy with
    | ofSubstCons hr hseries hle =>
      specialize h _ hle
      simp only [length_append]
      have := length_pos_of_ne hne hseries
      omega

noncomputable def reduce {a b : α} (x : a -[r]→* b) : a -[r]→* b :=
  open Classical in
  match x with
  | .singleton a => .singleton a
  | @cons _ _ a b c l hr => if h: a = b then copy (reduce l) (h.symm) rfl else .cons a (reduce l) hr

@[simp]
lemma reduce_singleton (a : α) : reduce (.singleton (r := r) a) = .singleton a := rfl

lemma reduce_cons_of_eq (a : α) {b c : α} (x : b -[r]→* c) (hr : r a b) (hab : a = b) :
    reduce (cons a x hr) = copy (reduce x) (hab.symm) rfl := by
  rw [reduce,dif_pos hab]

lemma reduce_cons_of_ne (a : α) {b c : α} (x : b -[r]→* c) (hr : r a b) (hab : a ≠ b) :
    reduce (cons a x hr) = cons a (reduce x) hr := by
  rw [reduce,dif_neg hab]

@[simp]
lemma reduce_cons [DecidableEq α] (a : α) {b c : α} (x : b -[r]→* c) (hr : r a b) :
    reduce (cons a x hr) =
      if h : a = b then copy (reduce x) (h.symm) rfl else cons a (reduce x) hr := by
  rw [reduce]
  congr

@[simp]
lemma toList_reduce [DecidableEq α] {a b : α} (x : a -[r]→* b) :
    toList (reduce x) = x.toList.destutter (· ≠ ·) := by
  induction x with
  | singleton a =>
    simp
  | cons a l hab ih =>
    simp only [reduce_cons, ne_eq, toList_cons]
    cases l with
    | singleton a =>
      simp only [reduce_singleton, toList_singleton, List.destutter_pair, ite_not]
      split <;> simp_all
    | cons a l hab =>
      simp only [toList_cons]
      split <;> simp_all only [ne_eq, toList_cons, toList_copy]
      · rw [List.destutter_cons_cons]
        simp_all only [not_true_eq_false, ite_false, reduce_cons]
        rfl
      · rw [List.destutter_cons_cons]
        simp_all only [not_false_eq_true, ite_true, List.cons.injEq, true_and]
        rw [← List.destutter_cons']

@[simp]
lemma length_reduce_le_length_self {a b : α} (x : a -[r]→* b) : x.reduce.length ≤ x.length := by
  induction x with
  | singleton a => simp
  | cons a l hab ih =>
    rw [reduce]
    split <;> simp_all ; omega



@[simp]
lemma self_le_reduce {a b : α} (x : a -[r]→* b) : x ≤ x.reduce := by
  induction x with
  | singleton a => simp
  | cons a l hab ih =>
    rw [reduce]
    split
    · rename_i h
      cases h
      exact cons_le_append a hab (singleton a) ih
    · rename_i h
      exact cons_le_append a hab (ofRel hab) ih

lemma reduce_le_self {a b : α} (x : a -[r]→* b) : x.reduce ≤ x := by
  induction x with
  | singleton a => simp
  | cons a l hab ih =>
    rw [reduce]
    split <;> rename_i h
    · cases h
      apply le_trans ih
      exact append_left_mono l (singleton_le (ofRel hab))
    · exact append_right_mono (ofRel hab) (ih)



@[simp]
lemma reduce_isReduced {a b : α} (x : a -[r]→* b) : x.reduce.IsReduced := by
  induction x with
  | singleton a => simp
  | cons a l hab ih =>
    rw [reduce]
    split <;> rename_i h
    · cases h; simp_all
    · simp_all

lemma reduce_eq_self_of_isReduced {a b : α} (x : a -[r]→* b) (hx : x.IsReduced) :
    x.reduce = x := by
  induction x with
  | singleton a => simp_all
  | cons a l hab ih =>
    simp_all
    rw [reduce_cons_of_ne a l hab hx.left, ih]

@[simp]
lemma reduce_reduce {a b : α} (x : a -[r]→* b) : x.reduce.reduce = x.reduce := by
  rw [reduce_eq_self_of_isReduced _ (reduce_isReduced x)]

@[simp]
lemma isReduced_of_irrefl [IsIrrefl α r] {a b : α} (x : a -[r]→* b) : x.IsReduced := by
  induction x with
  | singleton a => simp
  | cons a l hab ih =>
    simp_all only [isReduced_cons, ne_eq, and_true]
    rintro rfl
    exact irrefl _ hab

end RelSeriesHT


namespace Rel
/-
Of note in this section, we don't assume the existance of `r`-series between all pairs of points.
Instead we assume that *if any exist*, the relevant property holds.
This allows the notions to (mostly) coincide with those for transitive orders.
-/
open scoped RelSeriesHT

/-- A relation `r` is said to be discrete iff for all points `a`, `b`,
  there is length of `r`-series such that every series is less than a `r`-series of such length -/
@[mk_iff]
class IsDiscrete (r : Rel α α) : Prop where
  /-- A relation `r` is said to be discrete iff for all points `a`, `b`,
    every `r`-series essentially has a maximum length -/
  isDiscrete (r) (a b : α) : ∃ n, ∀ (x : a -[r]→* b), ∃ (y : a -[r]→* b),
    y.IsReduced ∧ x ≤ y ∧ y.length ≤ n

/-- A relation `r` is said to be dense iff for every two points `a` and `b` and a `r`-series
  between them, there is another r-series which is strictly larger. For transitive `· < ·`,
  equivalent to DenselyOrdered. -/
@[mk_iff]
class IsDense (r : Rel α α) : Prop where
  /-- A relation `r` is said to be dense iff for every two points `a` and `b` and a `r`-series
    between them, there is another r-series which is strictly larger. For transitive `· < ·`,
    equivalent to DenselyOrdered. -/
  isDense (r) (a b : α) : ∀ (x : a -[r]→* b), ∃ (y : a -[r]→* b),
    x < y

/-- A relation `r` is said to be catenary iff for every two points `a` and `b`,
  any `r`-series extends to a reduced `r`-series of length `n`. -/
class IsCatenary (r : Rel α α) : Prop where
  /-- A relation `r` is said to be catenary iff for every two points `a` and `b`,
    any `r`-series extends to a reduced `r`-series of length `n`. -/
  isCatenary (r) (a b : α) : ∃ n, ∀ (x : a -[r]→* b),
    ∃ (y : a -[r]→* b), y.IsReduced ∧ x ≤ y ∧ y.length = n

end Rel

namespace RelSeriesHT

section ecodim

variable (r) in

noncomputable def eCodim (a b : α) : ℕ∞ := ⨆ (x : a -[r]→* b), (x.reduce.length : ℕ∞)

lemma eCodim_def (a b : α) : eCodim r a b = ⨆ (x : a -[r]→* b), (x.reduce.length : ℕ∞) := rfl

lemma length_le_eCodim_of_isReduced (a b : α) (x : a -[r]→* b) (hx : x.IsReduced) :
    x.length ≤ eCodim r a b := by
  rw [← reduce_eq_self_of_isReduced x hx, eCodim_def]
  exact le_iSup_iff.mpr fun b_1 a ↦ a x


lemma eCodim_eq_sSup_length_reduce (a b : α) :
    eCodim r a b = ⨅ (n : ℕ∞), ⨅ (_ : ∀ (x : a -[r]→* b), ∃ y, x ≤ y ∧ y.length ≤ n), n:= by
  rw [eCodim_def]
  apply le_antisymm
  · simp_rw [le_iInf_iff,iSup_le_iff]
    intro d hd i
    obtain ⟨z,hz⟩ := hd i.reduce
    trans (z.length : ℕ∞)
    · simp only [Nat.cast_le]
      apply (reduce_isReduced i).isReduced _ hz.left
    exact hz.right
  · simp_rw [iInf_le_iff, le_iSup_iff]
    intro d hd e he
    specialize hd e
    simp_rw [le_iInf_iff] at hd
    apply hd
    intro i
    use i.reduce, self_le_reduce i, (he i)

lemma eCodim_lt_top [inst:r.IsDiscrete] (a b : α) : eCodim r a b < ⊤ := by
  rw [eCodim_def]
  rw [iSup_lt_iff]
  obtain ⟨z,hz⟩ := inst.isDiscrete a b
  use z
  simp only [ENat.coe_lt_top, Nat.cast_le, true_and]
  intro i
  obtain ⟨y,hyr,hiy,hyl⟩ := hz i
  trans y.length
  · apply (reduce_isReduced i).isReduced
    apply le_trans (reduce_le_self i) hiy
  exact hyl

lemma isDiscrete_iff_forall_eCodim_lt_top : r.IsDiscrete ↔ ∀ a b, eCodim r a b < ⊤ := by
  refine ⟨@eCodim_lt_top _ _,?_⟩
  rw [Rel.isDiscrete_iff]
  intro h a b
  specialize h a b
  use (eCodim r a b).toNat
  intro x
  use x.reduce, reduce_isReduced x, self_le_reduce x
  rw [← ENat.toNat_coe x.reduce.length]
  apply ENat.toNat_le_toNat _ h.ne
  exact length_le_eCodim_of_isReduced a b _ (reduce_isReduced x)


@[simp]
lemma reduce_length_le_eCodim {a b : α} (x : a -[r]→* b) : x.reduce.length ≤ eCodim r a b := by
  rw [eCodim_def]
  exact le_iSup_iff.mpr fun b_1 a ↦ a x

lemma eCodim_le_iff {a b : α} (n : ℕ∞) : eCodim r a b ≤ n ↔
    ∀ (x : a -[r]→* b), x.reduce.length ≤ n := by
  rw [eCodim_def]
  exact iSup_le_iff

lemma eCodim_eq_top [r.IsDense] (a b : α) [Nonempty (a -[r]→* b)]: eCodim r a b = ⊤ := by
  have := ‹r.IsDense›.isDense a b
  rw [eCodim_eq_sSup_length_reduce]
  -- rw [← ]
  -- rw [ENat.iInf_coe_eq_top]
  sorry

end ecodim

section codim
variable (r) in
noncomputable def codim (a b : α) : ℕ := (eCodim r a b).toNat

lemma codim_def (a b : α) : codim r a b = (eCodim r a b).toNat := rfl

-- lemma eCodim_eq_cast_codim [r.IsDiscrete]

end codim


-- lemma isDiscrete_iff_exists_longest_of_nonempty : r.IsDiscrete ↔ ∀ a b,
--     Nonempty (a -[r]→* b) →
--       ∃ z: a -[r]→* b, ∀ y : a -[r]→* b, y.length ≤ z.length := by
--   sorry
  -- refine ⟨?_,fun h => ⟨(· -[r]→* · |> Nonempty|> em |>.elim
  --     (h _ _ · |>.elim (⟨·.length,·⟩)) (.intro 0 ∘ (· ⟨·⟩ |>.elim)))⟩⟩
  -- rintro discrete a b ⟨x⟩
  -- obtain ⟨n,hn⟩ := discrete.isDiscrete a b
  -- contrapose! hn
  -- induction n with
  -- | zero =>
  --   apply (hn x).imp
  --   omega
  -- | succ n ih =>
  --   obtain ⟨x',hx'⟩ := ih
  --   apply (hn x').imp
  --   omega

-- variable (r) in
-- noncomputable def longestBetween [r.IsDiscrete] (a b : α) [Nonempty (a -[r]→* b)] :
--     a -[r]→* b :=
--   (isDiscrete_iff_exists_longest_of_nonempty.mp (by assumption) a b (by assumption)).choose

-- lemma length_le_length_longestBetween [r.IsDiscrete] (a b : α) (y : a -[r]→* b)
--     (z : Nonempty (a -[r]→* b) := ⟨y⟩) : y.length ≤ (@longestBetween _ r _ a b).length :=
--   (isDiscrete_iff_exists_longest_of_nonempty.mp (by assumption) a b
--     (by assumption)).choose_spec y

-- -- variable (r) in
-- noncomputable def longerBetween [r.IsDense] {a b : α} (y : a -[r]→* b) : a -[r]→* b :=
--   (‹r.IsDense›.isDense a b y).choose

-- lemma length_lt_length_longerBetween [r.IsDense] {a b : α} (y : a -[r]→* b) :
--   y < (longerBetween y) :=
--   (‹r.IsDense›.isDense a b y).choose_spec

-- instance [r.IsDense] : Rel.IsDense (Function.swap r) where
--   isDense a b x := (Rel.IsDense.isDense r b a x.reverse).elim (fun h => ⟨·.reverse,by

--     simp_all⟩)

-- instance [r.IsDiscrete] : Rel.IsDiscrete (Function.swap r) where
--   isDiscrete a b := (Rel.IsDiscrete.isDiscrete r b a).elim (fun h => ⟨·,(by
--     specialize h ·.reverse
--     simp_all)⟩)

-- section
-- variable {a b : α} {s : a -[r]→* b} {x : α}

-- theorem subsingleton_of_length_eq_zero (hs : s.length = 0) : {x | x ∈ s}.Subsingleton := by
--   rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩
--   congr!
--   exact finCongr (by rw [hs, zero_add]) |>.injective <| Subsingleton.elim (α := Fin 1) _ _

-- theorem length_ne_zero_of_nontrivial (h : {x | x ∈ s}.Nontrivial) : s.length ≠ 0 :=
--   fun hs ↦ h.not_subsingleton <| subsingleton_of_length_eq_zero hs

-- theorem length_pos_of_nontrivial (h : {x | x ∈ s}.Nontrivial) : 0 < s.length :=
--   Nat.pos_iff_ne_zero.mpr <| length_ne_zero_of_nontrivial h

-- theorem length_ne_zero (irrefl : Irreflexive r) : s.length ≠ 0 ↔ {x | x ∈ s}.Nontrivial := by
--   refine ⟨?_,length_ne_zero_of_nontrivial⟩
--   intro h
--   contrapose! h
--   simp only [Set.not_nontrivial_iff] at h
--   cases s with
--   | singleton a => rfl
--   | @cons a c _ l hab =>
--     apply (irrefl a).elim
--     convert hab
--     apply h <;> simp

-- theorem length_pos (irrefl : Irreflexive r) : 0 < s.length ↔ {x | x ∈ s}.Nontrivial :=
--   Nat.pos_iff_ne_zero.trans <| length_ne_zero irrefl

-- lemma length_eq_zero (irrefl : Irreflexive r) : s.length = 0 ↔ {x | x ∈ s}.Subsingleton := by
--   rw [← not_ne_iff, length_ne_zero irrefl, Set.not_nontrivial_iff]

-- end
end RelSeriesHT
