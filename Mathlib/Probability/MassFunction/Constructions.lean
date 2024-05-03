import Mathlib.Probability.MassFunction.Monad

open BigOperators ENNReal

universe u

variable {α β γ : Type*}

namespace SPMF

section Map

/-- The functorial action of a function on a `SPMF`. -/
noncomputable def map (f : α → β) (d : SPMF α) : SPMF β := bind d (pure ∘ f)

variable {f : α → β} {g : β → γ} {d : SPMF α} {b : β}

theorem monad_map_eq_map {α β : Type u} (f : α → β) (d : SPMF α) : f <$> d = d.map f := rfl

theorem map_def : (map f d) b = ∑' a, d a * Set.indicator {f a} 1 b := rfl

@[simp]
theorem massSupport_map : massSupport (map f d) = f '' massSupport d :=
  Set.ext fun b => by simp [map, @eq_comm β b]

theorem mem_massSupport_map_iff :
  b ∈ massSupport (map f d) ↔ ∃ a ∈ massSupport d, f a = b := by simp only [massSupport_map,
    Set.mem_image, mem_massSupport_iff, ne_eq]

theorem bind_pure_comp : bind d (pure ∘ f) = map f d := rfl

@[simp]
theorem mass_map : mass (map f d) = mass d := by
  simp_rw [← bind_pure_comp, mass_bind, Function.comp_apply, mass_pure, mul_one, tsum_eq_mass]

theorem map_id : map id d = d := bind_pure

theorem map_comp  : (d.map f).map g = d.map (g ∘ f) := by simp [map, Function.comp]

theorem pure_map {a : α} : (pure a).map f = pure (f a) := pure_bind

theorem map_bind {q : α → SPMF β} {f : β → γ} :
    (d.bind q).map f = d.bind fun a => (q a).map f := bind_bind

@[simp]
theorem bind_map (d : SPMF α) (f : α → β) (q : β → SPMF γ) : (d.map f).bind q = d.bind (q ∘ f) :=
  (bind_bind).trans (congr_arg _ (funext fun _ => pure_bind))

@[simp]
theorem map_const_apply (b' : β) :
  d.map (Function.const α b) b' = mass d * pure b b' :=
  bind_apply.trans (by simp_rw [Function.comp_apply, Function.const_apply,
    ENNReal.tsum_mul_right, tsum_eq_mass])

@[simp]
theorem map_apply [DecidableEq β] : (map f d) b = ∑' a, if b = f a then d a else 0 :=
  bind_apply.trans (by simp_rw [Function.comp_apply, pure_apply, mul_ite, mul_one, mul_zero])

end Map

section Seq

/-- The monadic sequencing operation for `SPMF`. -/
noncomputable def seq (q : SPMF (α → β)) (d : SPMF α) : SPMF β :=
  q.bind fun m => d.bind fun a => pure (m a)

variable {q : SPMF (α → β)} {d : SPMF α} {b : β}

theorem monad_seq_eq_seq {α β : Type u} (q : SPMF (α → β)) (d : SPMF α) : q <*> d = q.seq d := rfl

@[simp]
theorem massSupport_seq : massSupport (seq q d) = ⋃ f ∈ massSupport q, f '' massSupport d :=
  Set.ext fun b => by simp [-mem_massSupport_iff, seq, @eq_comm β b]

theorem mem_massSupport_seq_iff :
  b ∈ massSupport (seq q d) ↔ ∃ f ∈ massSupport q, b ∈ f '' massSupport d := by simp

theorem seq_def :
    (seq q d) b = ∑' (f : α → β) (a : α), q f * (d a * Set.indicator {f a} 1 b) :=
  bind_apply.trans (by simp_rw [bind_apply, ←ENNReal.tsum_mul_left, pure_def])

@[simp]
theorem mass_seq : mass (seq q d) = ∑' (a : α → β), q a * mass d := by
  simp_rw [seq, mass_bind, mass_pure, mul_one, tsum_eq_mass]

@[simp]
theorem seq_apply [DecidableEq β] :
    (seq q d) b = ∑' (f : α → β) (a : α), if b = f a then q f * d a else 0 :=
  bind_apply.trans (by simp_rw [bind_apply, ←ENNReal.tsum_mul_left, pure_apply,
  mul_ite, mul_one, mul_zero])

end Seq

instance : LawfulFunctor SPMF where
  map_const := rfl
  id_map _ := bind_pure
  comp_map _ _ _ := (map_comp).symm

instance : LawfulMonad SPMF := LawfulMonad.mk'
  (bind_pure_comp := fun f x => rfl)
  (id_map := id_map)
  (pure_bind := fun _ _ => pure_bind)
  (bind_assoc := fun _ _ _ => bind_bind)

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
theorem support_ofFinset : massSupport (ofFinset f s h h') = ↑s ∩ Function.support f :=
  Set.ext fun a => by simpa [mem_massSupport_iff] using mt (h' a)

theorem mem_massSupport_ofFinset_iff (a : α) :
  a ∈ massSupport (ofFinset f s h h') ↔ a ∈ s ∧ f a ≠ 0 := by
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
theorem massSupport_ofFintype : massSupport (ofFintype f h) = Function.support f := rfl

theorem mem_massSupport_ofFintype_iff (a : α) :
  a ∈ massSupport (ofFintype f h) ↔ f a ≠ 0 := Iff.rfl

end OfFintype

section Filter

noncomputable def filter (d : SPMF α) (s : Set α) : SPMF α :=
  d.bind (fun a => s.indicator pure a)

variable {d : SPMF α} {s : Set α} {a a' : α}

theorem filter_apply_of_mem (ha : a ∈ s) : (d.filter s) a = d a :=
  bind_apply.trans (by
  simp_rw [indicator_pure_apply]
  refine' (tsum_eq_single a _).trans _
  · intros b' h
    rw [Set.indicator_of_not_mem (s := s ∩ {b'}) (Set.mem_of_mem_inter_right.mt h.symm), mul_zero]
  · rw [Set.indicator_of_mem (Set.mem_inter ha (Set.mem_singleton _)), Pi.one_apply, mul_one])

theorem filter_apply_of_not_mem (ha : a ∉ s) : (d.filter s) a = 0 :=
  bind_apply.trans (by
  simp_rw [ENNReal.tsum_eq_zero, indicator_pure_apply, mul_eq_zero, Set.indicator_apply_eq_zero,
    Set.mem_inter_iff, Set.mem_singleton_iff, Pi.one_apply, one_ne_zero, and_imp, imp_false]
  exact fun _ => Or.inr (fun h => (ha h).elim))

@[simp]
theorem filter_apply (a : α) : (d.filter s) a = s.indicator d a := by
  by_cases ha : a ∈ s
  · rw [filter_apply_of_mem ha, Set.indicator_of_mem ha]
  · rw [filter_apply_of_not_mem ha, Set.indicator_of_not_mem ha]

@[simp]
theorem mass_filter : mass (d.filter s) = massOf d s := by
  simp_rw [← tsum_eq_mass, filter_apply, ← tsum_coe_indicator_eq_massOf]

theorem mem_massSupport_filter_iff {a : α} :
  a ∈ massSupport (d.filter s) ↔ a ∈ s ∧ a ∈ massSupport d := by
  rw [mem_massSupport_iff, filter_apply, Set.indicator_apply_ne_zero,
  Set.mem_inter_iff, coe_support_eq_massSupport]

@[simp]
theorem massSupport_filter : massSupport (d.filter s) = s ∩ massSupport d :=
  Set.ext fun _ => mem_massSupport_filter_iff

theorem filter_apply_eq_zero_iff (a : α) :
  (d.filter s) a = 0 ↔ a ∉ s ∨ a ∉ massSupport d := by
  erw [← nmem_massSupport_iff, massSupport_filter, Set.mem_inter_iff, not_and_or]

theorem filter_apply_ne_zero_iff (a : α) :
  (d.filter s) a ≠ 0 ↔ a ∈ s ∧ a ∈ massSupport d := by
  rw [Ne, filter_apply_eq_zero_iff, not_or, Classical.not_not, Classical.not_not]

end Filter

section Bernoulli

/-- A `SPMF` which assigns probability `p` to `true` and `1 - p` to `false`. -/
noncomputable def bernoulli (p : ℝ≥0∞) (h : p ≤ 1) : SPMF Bool :=
  ofFintype (fun b => cond b p (1 - p)) (by simp [h])

variable {p : ℝ≥0∞} (h : p ≤ 1) (b : Bool)

@[simp]
theorem bernoulli_apply : bernoulli p h b = cond b p (1 - p) := rfl

theorem mass_bernoulli : mass (bernoulli p h) = 1 := by
  simp_rw [← tsum_eq_mass, tsum_bool, bernoulli_apply,
  cond_false, cond_true, tsub_add_cancel_of_le h]

@[simp]
theorem massSupport_bernoulli : massSupport (bernoulli p h) = { b | cond b (p ≠ 0) (p ≠ 1) } := by
  refine' Set.ext fun b => _
  cases b
  · simp_rw [mem_massSupport_iff, bernoulli_apply, Bool.cond_false, Ne, tsub_eq_zero_iff_le, not_le]
    exact ⟨ne_of_lt, lt_of_le_of_ne h⟩
  · simp only [mem_massSupport_iff, bernoulli_apply, Bool.cond_true, Set.mem_setOf_eq]

theorem mem_massSupport_bernoulli_iff :
  b ∈ massSupport (bernoulli p h) ↔ cond b (p ≠ 0) (p ≠ 1) := by simp

end Bernoulli

end SPMF


namespace PMF

section Map

/-- The functorial action of a function on a `SPMF`. -/
noncomputable def map (f : α → β) (d : PMF α) : PMF β := bind d (pure ∘ f)

variable {f : α → β} {g : β → γ} {d : PMF α} {b : β}

theorem monad_map_eq_map {α β : Type u} (f : α → β) (d : PMF α) : f <$> d = d.map f := rfl

theorem map_def : (map f d) b = ∑' a, d a * Set.indicator {f a} 1 b := rfl

@[simp]
theorem massSupport_map : massSupport (map f d) = f '' massSupport d :=
  Set.ext fun b => by simp [map, @eq_comm β b]

theorem mem_massSupport_map_iff :
  b ∈ massSupport (map f d) ↔ ∃ a ∈ massSupport d, f a = b := by simp only [massSupport_map,
    Set.mem_image, mem_massSupport_iff, ne_eq]

theorem bind_pure_comp : bind d (pure ∘ f) = map f d := rfl

theorem map_id : map id d = d := bind_pure

theorem map_comp  : (d.map f).map g = d.map (g ∘ f) := by simp [map, Function.comp]

theorem pure_map {a : α} : (pure a).map f = pure (f a) := pure_bind

theorem map_bind {q : α → PMF β} {f : β → γ} :
    (d.bind q).map f = d.bind fun a => (q a).map f := bind_bind

@[simp]
theorem bind_map (d : PMF α) (f : α → β) (q : β → PMF γ) : (d.map f).bind q = d.bind (q ∘ f) :=
  (bind_bind).trans (congr_arg _ (funext fun _ => pure_bind))

@[simp]
theorem map_const_apply (b' : β) :
  d.map (Function.const α b) b' = mass d * pure b b' :=
  bind_apply.trans (by simp_rw [Function.comp_apply, Function.const_apply,
    ENNReal.tsum_mul_right, tsum_eq_mass])

@[simp]
theorem map_apply [DecidableEq β] : (map f d) b = ∑' a, if b = f a then d a else 0 :=
  bind_apply.trans (by simp_rw [Function.comp_apply, pure_apply, mul_ite, mul_one, mul_zero])

end Map

section Seq

/-- The monadic sequencing operation for `PMF`. -/
noncomputable def seq (q : PMF (α → β)) (d : PMF α) : PMF β :=
  q.bind fun m => d.bind fun a => pure (m a)

variable {q : PMF (α → β)} {d : PMF α} {b : β}

theorem monad_seq_eq_seq {α β : Type u} (q : PMF (α → β)) (d : PMF α) : q <*> d = q.seq d := rfl

@[simp]
theorem massSupport_seq : massSupport (seq q d) = ⋃ f ∈ massSupport q, f '' massSupport d :=
  Set.ext fun b => by simp [-mem_massSupport_iff, seq, @eq_comm β b]

theorem mem_massSupport_seq_iff :
  b ∈ massSupport (seq q d) ↔ ∃ f ∈ massSupport q, b ∈ f '' massSupport d := by simp

theorem seq_def :
    (seq q d) b = ∑' (f : α → β) (a : α), q f * (d a * Set.indicator {f a} 1 b) :=
  bind_apply.trans (by simp_rw [bind_apply, ←ENNReal.tsum_mul_left, pure_def])

@[simp]
theorem seq_apply [DecidableEq β] :
    (seq q d) b = ∑' (f : α → β) (a : α), if b = f a then q f * d a else 0 :=
  bind_apply.trans (by simp_rw [bind_apply, ←ENNReal.tsum_mul_left, pure_apply,
  mul_ite, mul_one, mul_zero])

end Seq

instance : LawfulFunctor PMF where
  map_const := rfl
  id_map _ := bind_pure
  comp_map _ _ _ := (map_comp).symm

instance : LawfulMonad PMF := LawfulMonad.mk'
  (bind_pure_comp := fun f x => rfl)
  (id_map := id_map)
  (pure_bind := fun _ _ => pure_bind)
  (bind_assoc := fun _ _ _ => bind_bind)

section OfFinset

/-- Given a finset `s` and a function `f : α → ℝ≥0∞` with sum `1` on `s`,
  such that `f a = 0` for `a ∉ s`, we get a `PMF`. -/
def ofFinset (f : α → ℝ≥0∞) (s : Finset α) (h : ∑ a in s, f a = 1)
    (h' : ∀ (a) (_ : a ∉ s), f a = 0) : PMF α :=
  ⟨f, by rwa [HasSum.tsum_eq (hasSum_sum_of_ne_finset_zero h')]⟩

variable {f : α → ℝ≥0∞} {s : Finset α} (h : ∑ a in s, f a = 1) (h' : ∀ (a) (_ : a ∉ s), f a = 0)

@[simp]
theorem ofFinset_apply (a : α) : ofFinset f s h h' a = f a := rfl

@[simp]
theorem support_ofFinset : massSupport (ofFinset f s h h') = ↑s ∩ Function.support f :=
  Set.ext fun a => by simpa [mem_massSupport_iff] using mt (h' a)

theorem mem_massSupport_ofFinset_iff (a : α) :
  a ∈ massSupport (ofFinset f s h h') ↔ a ∈ s ∧ f a ≠ 0 := by
  simp

theorem ofFinset_apply_of_not_mem {a : α} (ha : a ∉ s) : ofFinset f s h h' a = 0 :=
  h' a ha

end OfFinset

section OfFintype

def ofFintype [Fintype α] (f : α → ℝ≥0∞) (h : ∑ a, f a = 1) : PMF α :=
  ofFinset f Finset.univ h fun a ha => absurd (Finset.mem_univ a) ha

variable [Fintype α] {f : α → ℝ≥0∞} (h : ∑ a, f a = 1)

@[simp]
theorem ofFintype_apply (a : α) : ofFintype f h a = f a := rfl

@[simp]
theorem massSupport_ofFintype : massSupport (ofFintype f h) = Function.support f := rfl

theorem mem_massSupport_ofFintype_iff (a : α) :
  a ∈ massSupport (ofFintype f h) ↔ f a ≠ 0 := Iff.rfl

end OfFintype

section Normalize

variable {F : Sort*} {α : Type*} [MFLike F α] [FMFClass F α] {f : F} {a : α} {hf : mass f ≠ 0}

noncomputable def normalize (f : F) (hf : mass f ≠ 0) : PMF α :=
  ⟨fun a => f a * (mass f)⁻¹, by simp_rw [ENNReal.tsum_mul_right,
  tsum_eq_mass, ENNReal.mul_inv_cancel hf mass_ne_top]⟩

@[simp]
theorem normalize_apply : (normalize f hf) a = f a * (mass f)⁻¹ := rfl

@[simp]
theorem massSupport_normalize : massSupport (normalize f hf) = Function.support f :=
  Set.ext fun a => by simp [mass_ne_top, mem_massSupport_iff]

theorem mem_massSupport_normalize_iff :
    a ∈ massSupport (normalize f hf) ↔ f a ≠ 0 := by simp

end Normalize

section Filter

noncomputable def filter (d : PMF α) (s : Set α) (h : (s ∩ massSupport d).Nonempty) : PMF α :=
  normalize (SPMF.filter d s) (by rwa [SPMF.mass_filter, massOf_ne_zero_iff_disjoint_massSupport])

variable {d : PMF α} {s : Set α} {a a' : α} {h : (s ∩ massSupport d).Nonempty}

@[simp]
theorem filter_apply (a : α) : (d.filter s) h a = s.indicator d a * (massOf d s)⁻¹ := by
  exact (normalize_apply).trans
    (by rw [SPMF.filter_apply, SPMF.mass_filter, SPMFClass.coe_eq_coe, SPMFClass.coe_massOf])

theorem filter_apply_of_mem (ha : a ∈ s) : (d.filter s) h a = d a * (massOf d s)⁻¹ := by
  rw [filter_apply, Set.indicator_of_mem ha]

theorem filter_apply_of_not_mem (ha : a ∉ s) : (d.filter s) h a = 0 := by
    rw [filter_apply, Set.indicator_of_not_mem ha, zero_mul]

theorem mem_massSupport_filter_iff {a : α} :
  a ∈ massSupport (d.filter s h) ↔ a ∈ s ∧ a ∈ massSupport d := by
  simp_rw [mem_massSupport_iff, filter_apply, mul_ne_zero_iff, Set.indicator_apply_ne_zero,
  Set.mem_inter_iff, coe_support_eq_massSupport, mem_massSupport_iff, ENNReal.inv_ne_zero,
  and_iff_left (massOf_ne_top)]

@[simp]
theorem massSupport_filter : massSupport (d.filter s h) = s ∩ massSupport d :=
  Set.ext fun _ => mem_massSupport_filter_iff

theorem filter_apply_eq_zero_iff :
  (d.filter s h) a = 0 ↔ a ∉ s ∨ a ∉ massSupport d := by
  erw [← nmem_massSupport_iff, massSupport_filter, Set.mem_inter_iff, not_and_or]

theorem filter_apply_ne_zero_iff (a : α) :
  (d.filter s h) a ≠ 0 ↔ a ∈ s ∧ a ∈ massSupport d := by
  rw [Ne, filter_apply_eq_zero_iff, not_or, Classical.not_not, Classical.not_not]

end Filter

section Bernoulli

/-- A `PMF` which assigns probability `p` to `true` and `1 - p` to `false`. -/
noncomputable def bernoulli (p : ℝ≥0∞) (h : p ≤ 1) : PMF Bool :=
  ofFintype (fun b => cond b p (1 - p)) (by simp [h])

variable {p : ℝ≥0∞} (h : p ≤ 1) (b : Bool)

@[simp]
theorem bernoulli_apply : bernoulli p h b = cond b p (1 - p) := rfl

@[simp]
theorem massSupport_bernoulli : massSupport (bernoulli p h) = { b | cond b (p ≠ 0) (p ≠ 1) } := by
  refine' Set.ext fun b => _
  cases b
  · simp_rw [mem_massSupport_iff, bernoulli_apply, Bool.cond_false, Ne, tsub_eq_zero_iff_le, not_le]
    exact ⟨ne_of_lt, lt_of_le_of_ne h⟩
  · simp only [mem_massSupport_iff, bernoulli_apply, Bool.cond_true, Set.mem_setOf_eq]

theorem mem_massSupport_bernoulli_iff :
  b ∈ massSupport (bernoulli p h) ↔ cond b (p ≠ 0) (p ≠ 1) := by simp

end Bernoulli

end PMF
