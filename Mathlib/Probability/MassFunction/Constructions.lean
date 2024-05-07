import Mathlib.Probability.MassFunction.Monad

open BigOperators ENNReal

namespace MassFunction

universe u

section Map

variable {M : Type u → Type*} [MFLike M] [DiracPure M] [WeightedSumBind M]
{α β γ : Type u} {f : α → β} {g : β → γ} {μ : M α} {φ : α → M β} {ξ : β → M γ} {b b' : β}

open DiracPure WeightedSumBind

noncomputable def map (f : α → β) (μ : M α) : M β := bind μ (pure ∘ f)

theorem monad_map_eq_map : f <$> μ = map f μ := rfl

theorem map_def : map f μ = bind μ (pure ∘ f) := rfl

theorem coeFn_map : ⇑(map f μ) = fun b => ∑' a, μ a * Set.indicator {f a} 1 b := by
  simp_rw [map_def, coeFn_bind, Function.comp_apply, coeFn_pure]

theorem map_apply : map f μ b = ∑' a, μ a * Set.indicator {f a} 1 b := by rw [coeFn_map]

@[simp]
theorem support_map : support (map f μ) = f '' support μ := Set.ext fun b => by
  simp_rw [mem_support_iff, ne_eq, Set.mem_image, coeFn_map, ENNReal.tsum_eq_zero, not_forall,
  mul_eq_zero, Set.indicator_apply_eq_zero, Set.mem_singleton_iff, @eq_comm β b, Pi.one_apply,
  one_ne_zero, imp_false, mem_support_iff, not_or, not_not]

theorem mem_support_map_iff :
    b ∈ support (map f μ) ↔ ∃ a ∈ support μ, f a = b := by
  simp only [support_map, Set.mem_image, mem_support_iff, ne_eq]

theorem bind_pure_comp : bind μ (pure ∘ f) = map f μ := rfl

@[simp]
theorem mass_map : mass (map f μ) = mass μ := by
  simp_rw [← bind_pure_comp, WeightedSumBind.mass_bind, Function.comp_apply,
  DiracPure.mass_pure, mul_one, mass_eq_tsum_coeFn]

theorem map_id : map id μ = μ := bind_pure

theorem map_comp : map g (map f μ) = map (g ∘ f) μ := by simp [map_def, Function.comp]

theorem pure_map {a : α} : map f (pure a) = (pure (f a) : M β) := pure_bind

theorem map_bind : map g (bind μ φ) = bind μ fun a => map g (φ a) := bind_bind

@[simp]
theorem bind_map : bind (map f μ) ξ = bind μ (ξ ∘ f) :=
  (bind_bind).trans (congr_arg _ (funext fun _ => pure_bind))

@[simp]
theorem map_const_apply :
  map (Function.const α b) μ b' = mass μ * (pure b : M β) b' :=
  bind_apply.trans (by simp_rw [Function.comp_apply, Function.const_apply,
    ENNReal.tsum_mul_right, mass_eq_tsum_coeFn])

@[simp]
theorem map_apply' [DecidableEq β] : map f μ b = ∑' a, if b = f a then μ a else 0 :=
  bind_apply.trans (by simp_rw [Function.comp_apply, pure_apply', mul_ite, mul_one, mul_zero])

end Map

section Seq

variable {M : Type u → Type*} [MFLike M] [DiracPure M] [WeightedSumBind M]
{α β γ : Type u} {κ : M (α → β)} {μ : M α} {b : β}

open DiracPure WeightedSumBind

noncomputable def seq (κ : M (α → β)) (μ : M α) : M β :=
  bind κ fun f => bind μ fun a => pure (f a)

theorem monad_seq_eq_seq : κ <*> μ = seq κ μ := rfl

theorem seq_def : seq κ μ = bind κ fun f => bind μ fun a => pure (f a) := rfl

theorem seq_apply : seq κ μ b = ∑' (f : α → β) (a : α), κ f * (μ a * Set.indicator {f a} 1 b) := by
  simp_rw [seq_def, bind_apply, pure_apply, ENNReal.tsum_mul_left]

theorem coeFn_seq : ⇑(seq κ μ) =
    fun b => ∑' (f : α → β) (a : α), κ f * (μ a * Set.indicator {f a} 1 b) := by
    simp_rw [Function.funext_iff, seq_apply, implies_true]

@[simp]
theorem support_seq : support (seq κ μ) = ⋃ f ∈ support κ, f '' support μ := by
  simp_rw [seq_def, support_bind, support_pure, Set.image_eq_iUnion]

theorem mem_support_seq_iff : b ∈ support (seq κ μ) ↔ ∃ f ∈ support κ, b ∈ f '' support μ := by
  simp_rw [support_seq, mem_support_iff, ne_eq, Set.mem_iUnion, Set.mem_image, exists_prop]

@[simp]
theorem mass_seq : mass (seq κ μ) = ∑' (a : α → β), κ a * mass μ := by
  simp_rw [seq, mass_bind, mass_pure, mul_one, mass_eq_tsum_coeFn]

@[simp]
theorem seq_apply' [DecidableEq β] :
    (seq κ μ) b = ∑' (f : α → β) (a : α), if b = f a then κ f * μ a else 0 :=
  bind_apply.trans (by simp_rw [bind_apply, ←ENNReal.tsum_mul_left, pure_apply',
  mul_ite, mul_one, mul_zero])

end Seq

section Lawful

variable {M : Type u → Type*} [MFLike M] [DiracPure M] [WeightedSumBind M]

open DiracPure WeightedSumBind

instance : LawfulFunctor M where
  map_const := rfl
  id_map _ := bind_pure
  comp_map _ _ _ := (map_comp).symm

instance : LawfulMonad M := LawfulMonad.mk'
  (bind_pure_comp := fun f x => rfl)
  (id_map := id_map)
  (pure_bind := fun _ _ => pure_bind)
  (bind_assoc := fun _ _ _ => bind_bind)

end Lawful

section Filter

variable {M : Type u → Type*} [MFLike M] [DiracPure M] [WeightedSumBind M]
[∀ α, Zero (M α)] [ZeroNull M] {α β γ : Type u} {μ : M α} {s : Set α} {a a' : α}

open DiracPure WeightedSumBind

noncomputable def filter (μ : M α) (s : Set α) : M α := bind μ (fun a => s.indicator pure a)

theorem filter_apply_of_mem (ha : a ∈ s) : (filter μ s) a = μ a :=
  bind_apply.trans (by
  simp_rw [indicator_pure_apply]
  refine' (tsum_eq_single a _).trans _
  · intros b' h
    rw [Set.indicator_of_not_mem (s := s ∩ {b'}) (Set.mem_of_mem_inter_right.mt h.symm), mul_zero]
  · rw [Set.indicator_of_mem (Set.mem_inter ha (Set.mem_singleton _)), Pi.one_apply, mul_one])

theorem filter_apply_of_not_mem (ha : a ∉ s) : (filter μ s) a = 0 :=
  bind_apply.trans (by
  simp_rw [ENNReal.tsum_eq_zero, indicator_pure_apply, mul_eq_zero, Set.indicator_apply_eq_zero,
    Set.mem_inter_iff, Set.mem_singleton_iff, Pi.one_apply, one_ne_zero, and_imp, imp_false]
  exact fun _ => Or.inr (fun h => (ha h).elim))

@[simp]
theorem filter_apply (a : α) : (filter μ s) a = s.indicator μ a := by
  by_cases ha : a ∈ s
  · rw [filter_apply_of_mem ha, Set.indicator_of_mem ha]
  · rw [filter_apply_of_not_mem ha, Set.indicator_of_not_mem ha]

@[simp]
theorem mass_filter : mass (filter μ s) = massOf μ s := by
  simp_rw [mass_eq_tsum_coeFn, filter_apply, massOf_eq_tsum_indicator_coeFn]

theorem mem_support_filter_iff {a : α} : a ∈ support (filter μ s) ↔ a ∈ s ∧ a ∈ support μ := by
  simp_rw [mem_support_iff, filter_apply, Set.indicator_apply_ne_zero,
  Set.mem_inter_iff, Function.mem_support]

@[simp]
theorem support_filter : support (filter μ s) = s ∩ support μ :=
  Set.ext fun _ => mem_support_filter_iff

theorem filter_apply_eq_zero_iff (a : α) :
  (filter μ s) a = 0 ↔ a ∉ s ∨ a ∉ support μ := by
  erw [← nmem_support_iff, support_filter, Set.mem_inter_iff, not_and_or]

theorem filter_apply_ne_zero_iff (a : α) :
  (filter μ s) a ≠ 0 ↔ a ∈ s ∧ a ∈ support μ := by
  rw [Ne, filter_apply_eq_zero_iff, not_or, Classical.not_not, Classical.not_not]

end Filter

namespace SPMF

section OfFinset

variable {α : Type*}

/-- Given a finset `s` and a function `f : α → ℝ≥0∞` with sum `1` on `s`,
  such that `f a = 0` for `a ∉ s`, we get a `SPMF`. -/
def ofFinset (f : α → ℝ≥0∞) (s : Finset α) (h : ∑ a in s, f a ≤ 1)
    (h' : ∀ (a) (_ : a ∉ s), f a = 0) : SPMF α :=
  ⟨f, by rwa [HasSum.tsum_eq (hasSum_sum_of_ne_finset_zero h')]⟩

variable {f : α → ℝ≥0∞} {s : Finset α} (h : ∑ a in s, f a ≤ 1) (h' : ∀ (a) (_ : a ∉ s), f a = 0)

@[simp]
theorem ofFinset_apply (a : α) : ofFinset f s h h' a = f a := rfl

@[simp]
theorem support_ofFinset : support (ofFinset f s h h') = ↑s ∩ Function.support f :=
  Set.ext fun a => by simpa [mem_support_iff] using mt (h' a)

theorem mem_support_ofFinset_iff (a : α) :
  a ∈ support (ofFinset f s h h') ↔ a ∈ s ∧ f a ≠ 0 := by
  simp

theorem ofFinset_apply_of_not_mem {a : α} (ha : a ∉ s) : ofFinset f s h h' a = 0 :=
  h' a ha

end OfFinset

section OfFintype

variable {α : Type*}

def ofFintype [Fintype α] (f : α → ℝ≥0∞) (h : ∑ a, f a ≤ 1) : SPMF α :=
  ofFinset f Finset.univ h fun a ha => absurd (Finset.mem_univ a) ha

variable [Fintype α] {f : α → ℝ≥0∞} (h : ∑ a, f a ≤ 1)

@[simp]
theorem ofFintype_apply (a : α) : ofFintype f h a = f a := rfl

@[simp]
theorem support_ofFintype : support (ofFintype f h) = Function.support f := rfl

theorem mem_support_ofFintype_iff (a : α) :
  a ∈ support (ofFintype f h) ↔ f a ≠ 0 := Iff.rfl

end OfFintype

section Bernoulli

/-- A `SPMF` which assigns probability `p` to `true` and `1 - p` to `false`. -/
noncomputable def bernoulli (p : ℝ≥0∞) (h : p ≤ 1) : SPMF Bool :=
  ofFintype (fun b => cond b p (1 - p)) (by simp [h])

variable {p : ℝ≥0∞} (h : p ≤ 1) (b : Bool)

@[simp]
theorem bernoulli_apply : bernoulli p h b = cond b p (1 - p) := rfl

theorem mass_bernoulli : mass (bernoulli p h) = 1 := by
  simp_rw [mass_eq_tsum_coeFn, tsum_bool, bernoulli_apply,
  cond_false, cond_true, tsub_add_cancel_of_le h]

@[simp]
theorem support_bernoulli : support (bernoulli p h) = { b | cond b (p ≠ 0) (p ≠ 1) } := by
  refine' Set.ext fun b => _
  cases b
  · simp_rw [mem_support_iff, bernoulli_apply, Bool.cond_false, Ne, tsub_eq_zero_iff_le, not_le]
    exact ⟨ne_of_lt, lt_of_le_of_ne h⟩
  · simp only [mem_support_iff, bernoulli_apply, Bool.cond_true, Set.mem_setOf_eq]

theorem mem_support_bernoulli_iff :
  b ∈ support (bernoulli p h) ↔ cond b (p ≠ 0) (p ≠ 1) := by simp

end Bernoulli

end SPMF


namespace PMF

section OfFinset

variable {α : Type*}

/-- Given a finset `s` and a function `f : α → ℝ≥0∞` with sum `1` on `s`,
  such that `f a = 0` for `a ∉ s`, we get a `PMF`. -/
def ofFinset (f : α → ℝ≥0∞) (s : Finset α) (h : ∑ a in s, f a = 1)
    (h' : ∀ (a) (_ : a ∉ s), f a = 0) : PMF α :=
  ⟨f, by rwa [HasSum.tsum_eq (hasSum_sum_of_ne_finset_zero h')]⟩

variable {f : α → ℝ≥0∞} {s : Finset α} (h : ∑ a in s, f a = 1) (h' : ∀ (a) (_ : a ∉ s), f a = 0)

@[simp]
theorem ofFinset_apply (a : α) : ofFinset f s h h' a = f a := rfl

@[simp]
theorem support_ofFinset : support (ofFinset f s h h') = ↑s ∩ Function.support f :=
  Set.ext fun a => by simpa [mem_support_iff] using mt (h' a)

theorem mem_support_ofFinset_iff (a : α) :
  a ∈ support (ofFinset f s h h') ↔ a ∈ s ∧ f a ≠ 0 := by
  simp

theorem ofFinset_apply_of_not_mem {a : α} (ha : a ∉ s) : ofFinset f s h h' a = 0 :=
  h' a ha

end OfFinset

section OfFintype

variable {α : Type*}

def ofFintype [Fintype α] (f : α → ℝ≥0∞) (h : ∑ a, f a = 1) : PMF α :=
  ofFinset f Finset.univ h fun a ha => absurd (Finset.mem_univ a) ha

variable [Fintype α] {f : α → ℝ≥0∞} (h : ∑ a, f a = 1)

@[simp]
theorem ofFintype_apply (a : α) : ofFintype f h a = f a := rfl

@[simp]
theorem support_ofFintype : support (ofFintype f h) = Function.support f := rfl

theorem mem_support_ofFintype_iff (a : α) :
  a ∈ support (ofFintype f h) ↔ f a ≠ 0 := Iff.rfl

end OfFintype

section Normalize

variable {M : Type u → Type*} {α : Type u} [MFLike M] [FMFClass M] {μ : M α} {a : α}
{hf : mass μ ≠ 0}

noncomputable def normalize (μ : M α) (hf : mass μ ≠ 0) : PMF α :=
  ⟨fun a => μ a * (mass μ)⁻¹, by
    simp_rw [ENNReal.tsum_mul_right, ← mass_eq_tsum_coeFn,
    ENNReal.mul_inv_cancel hf mass_ne_top]⟩

@[simp]
theorem normalize_apply : (normalize μ hf) a = μ a * (mass μ)⁻¹ := rfl

@[simp]
theorem support_normalize : support (normalize μ hf) = Function.support μ :=
  Set.ext fun a => by simp [mass_ne_top, mem_support_iff]

theorem mem_support_normalize_iff :
    a ∈ support (normalize μ hf) ↔ μ a ≠ 0 := by simp

end Normalize

section Bernoulli

/-- A `PMF` which assigns probability `p` to `true` and `1 - p` to `false`. -/
noncomputable def bernoulli (p : ℝ≥0∞) (h : p ≤ 1) : PMF Bool :=
  ofFintype (fun b => cond b p (1 - p)) (by simp [h])

variable {p : ℝ≥0∞} (h : p ≤ 1) (b : Bool)

@[simp]
theorem bernoulli_apply : bernoulli p h b = cond b p (1 - p) := rfl

@[simp]
theorem support_bernoulli : support (bernoulli p h) = { b | cond b (p ≠ 0) (p ≠ 1) } := by
  refine' Set.ext fun b => _
  cases b
  · simp_rw [mem_support_iff, bernoulli_apply, Bool.cond_false, Ne, tsub_eq_zero_iff_le, not_le]
    exact ⟨ne_of_lt, lt_of_le_of_ne h⟩
  · simp only [mem_support_iff, bernoulli_apply, Bool.cond_true, Set.mem_setOf_eq]

theorem mem_support_bernoulli_iff :
  b ∈ support (bernoulli p h) ↔ cond b (p ≠ 0) (p ≠ 1) := by simp

end Bernoulli

end PMF

end MassFunction
