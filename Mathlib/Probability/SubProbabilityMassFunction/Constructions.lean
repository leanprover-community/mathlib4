import Mathlib.Probability.SubProbabilityMassFunction.Monad

noncomputable section

namespace SPMF

universe u

open scoped Classical
open BigOperators ENNReal

variable {α β γ : Type*}

section Map

/-- The functorial action of a function on a `SPMF`. -/
def map (f : α → β) (d : SPMF α) : SPMF β := bind d (pure ∘ f)

variable (f : α → β) (d : SPMF α) (b : β)

theorem monad_map_eq_map {α β : Type u} (f : α → β) (d : SPMF α) : f <$> d = d.map f := rfl

@[simp]
theorem map_apply : (map f d) b = ∑' a, if b = f a then d a else 0 := by simp [map]

@[simp]
theorem support_map : (map f d).support = f '' d.support :=
  Set.ext fun b => by simp [map, @eq_comm β b]

theorem mem_support_map_iff : b ∈ (map f d).support ↔ ∃ a ∈ d.support, f a = b := by simp

theorem bind_pure_comp : bind d (pure ∘ f) = map f d := rfl

theorem map_id : map id d = d := bind_pure _

theorem map_comp (g : β → γ) : (d.map f).map g = d.map (g ∘ f) := by simp [map, Function.comp]

theorem pure_map (a : α) : (pure a).map f = pure (f a) := pure_bind _ _

theorem map_bind (q : α → SPMF β) (f : β → γ) : (d.bind q).map f = d.bind fun a => (q a).map f :=
  bind_bind _ _ _

@[simp]
theorem bind_map (d : SPMF α) (f : α → β) (q : β → SPMF γ) : (d.map f).bind q = d.bind (q ∘ f) :=
  (bind_bind _ _ _).trans (congr_arg _ (funext fun _ => pure_bind _ _))

@[simp]
theorem map_const : d.map (Function.const α b) = mass d • pure b := by
  simp only [map, Function.comp, bind_const, Function.const]



end Map

section Seq

/-- The monadic sequencing operation for `SPMF`. -/
def seq (q : SPMF (α → β)) (d : SPMF α) : SPMF β :=
  q.bind fun m => d.bind fun a => pure (m a)

variable (q : SPMF (α → β)) (d : SPMF α) (b : β)

theorem monad_seq_eq_seq {α β : Type u} (q : SPMF (α → β)) (d : SPMF α) : q <*> d = q.seq d := rfl

@[simp]
theorem seq_apply : (seq q d) b = ∑' (f : α → β) (a : α), if b = f a then q f * d a else 0 := by
  simp only [seq, mul_boole, bind_apply, pure_apply]
  refine' tsum_congr fun f => ENNReal.tsum_mul_left.symm.trans (tsum_congr fun a => _)
  simpa only [mul_zero] using mul_ite (b = f a) (q f) (d a) 0

@[simp]
theorem support_seq : (seq q d).support = ⋃ f ∈ q.support, f '' d.support :=
  Set.ext fun b => by simp [-mem_support_iff, seq, @eq_comm β b]

theorem mem_support_seq_iff : b ∈ (seq q d).support ↔ ∃ f ∈ q.support, b ∈ f '' d.support := by simp

end Seq

instance : LawfulFunctor SPMF where
  map_const := rfl
  id_map := bind_pure
  comp_map _ _ _ := (map_comp _ _ _).symm

instance : LawfulMonad SPMF := LawfulMonad.mk'
  (bind_pure_comp := fun f x => rfl)
  (id_map := id_map)
  (pure_bind := pure_bind)
  (bind_assoc := bind_bind)

section OfFinset

/-- Given a finset `s` and a function `f : α → ℝ≥0∞` with sum `1` on `s`,
  such that `f a = 0` for `a ∉ s`, we get a `SPMF`. -/
def ofFinset (f : α → ℝ≥0∞) (s : Finset α) (h : ∑ a in s, f a ≤ 1)
    (h' : ∀ (a) (_ : a ∉ s), f a = 0) : SPMF α :=
  ⟨f, by rwa [HasSum.tsum_eq (hasSum_sum_of_ne_finset_zero h')]⟩

variable {f : α → ℝ≥0∞} {s : Finset α} (h : ∑ a in s, f a ≤ 1) (h' : ∀ (a) (_ : a ∉ s), f a = 0)

@[simp]
theorem ofFinset_apply (a : α) : ofFinset f s h h' a = f a := rfl

@[simp]
theorem support_ofFinset : (ofFinset f s h h').support = ↑s ∩ Function.support f :=
  Set.ext fun a => by simpa [mem_support_iff] using mt (h' a)

theorem mem_support_ofFinset_iff (a : α) : a ∈ (ofFinset f s h h').support ↔ a ∈ s ∧ f a ≠ 0 := by
  simp

theorem ofFinset_apply_of_not_mem {a : α} (ha : a ∉ s) : ofFinset f s h h' a = 0 :=
  h' a ha

end OfFinset

section OfFintype

def ofFintype [Fintype α] (f : α → ℝ≥0∞) (h : ∑ a, f a ≤ 1) : SPMF α :=
  ofFinset f Finset.univ h fun a ha => absurd (Finset.mem_univ a) ha

variable [Fintype α] {f : α → ℝ≥0∞} (h : ∑ a, f a ≤ 1)

@[simp]
theorem ofFintype_apply (a : α) : ofFintype f h a = f a := rfl

@[simp]
theorem support_ofFintype : (ofFintype f h).support = Function.support f := rfl

theorem mem_support_ofFintype_iff (a : α) : a ∈ (ofFintype f h).support ↔ f a ≠ 0 := Iff.rfl

end OfFintype

section Filter

def filter (d : SPMF α) (s : Set α) : SPMF α :=
  d.bind (fun a => if a ∈ s then pure a else 0)

variable {d : SPMF α} {s : Set α}

@[simp]
theorem filter_apply (a : α) : (d.filter s) a = s.indicator d a := by
  simp_rw [filter, bind_apply]
  by_cases ha : a ∈ s
  · rw [tsum_eq_single a, if_pos ha, pure_apply_self, Set.indicator_of_mem ha, mul_one]
    intro b hab
    refine' mul_eq_zero_of_right _ _
    by_cases hb : b ∈ s
    · rw [if_pos hb, pure_apply_of_ne _ _ hab.symm]
    · rw [if_neg hb, zero_apply]
  · rw [Set.indicator_of_not_mem ha, ENNReal.tsum_eq_zero]
    intro b
    by_cases hb : b ∈ s
    · rw [if_pos hb, pure_apply_of_ne _ _ (ne_of_mem_of_not_mem hb ha).symm, mul_zero]
    · rw [if_neg hb, zero_apply, mul_zero]

theorem filter_apply_eq_zero_of_not_mem {a : α} (ha : a ∉ s) : (d.filter s) a = 0 := by
  rw [filter_apply, Set.indicator_apply_eq_zero.mpr fun ha' => absurd ha' ha]

theorem mem_support_filter_iff {a : α} : a ∈ (d.filter s).support ↔ a ∈ s ∧ a ∈ d.support := by
  rw [mem_support_iff, filter_apply, Set.indicator_apply_ne_zero, Set.mem_inter_iff, support_def]

@[simp]
theorem support_filter : (d.filter s).support = s ∩ d.support :=
  Set.ext fun _ => mem_support_filter_iff

theorem filter_apply_eq_zero_iff (a : α) : (d.filter s) a = 0 ↔ a ∉ s ∨ a ∉ d.support := by
  erw [← nmem_support_iff, support_filter, Set.mem_inter_iff, not_and_or]

theorem filter_apply_ne_zero_iff (a : α) : (d.filter s) a ≠ 0 ↔ a ∈ s ∧ a ∈ d.support := by
  rw [Ne, filter_apply_eq_zero_iff, not_or, Classical.not_not, Classical.not_not]

end Filter

section bernoulli

/-- A `SPMF` which assigns probability `p` to `true` and `1 - p` to `false`. -/
def bernoulli (p : ℝ≥0∞) (h : p ≤ 1) : SPMF Bool :=
  ofFintype (fun b => cond b p (1 - p)) (by simp [h])

variable {p : ℝ≥0∞} (h : p ≤ 1) (b : Bool)

@[simp]
theorem bernoulli_apply : bernoulli p h b = cond b p (1 - p) := rfl

@[simp]
theorem support_bernoulli : (bernoulli p h).support = { b | cond b (p ≠ 0) (p ≠ 1) } := by
  refine' Set.ext fun b => _
  induction b
  · simp_rw [mem_support_iff, bernoulli_apply, Bool.cond_false, Ne, tsub_eq_zero_iff_le, not_le]
    exact ⟨ne_of_lt, lt_of_le_of_ne h⟩
  · simp only [mem_support_iff, bernoulli_apply, Bool.cond_true, Set.mem_setOf_eq]

theorem mem_support_bernoulli_iff : b ∈ (bernoulli p h).support ↔ cond b (p ≠ 0) (p ≠ 1) := by simp

end bernoulli

end SPMF
