import Mathlib.Probability.MassFunction.Monad
import Mathlib.Data.Finset.Card

open BigOperators ENNReal

namespace MassFunction

universe u v

section Map

open Functor

variable {M : Type u → Type v} [∀ α, MFLike M α] [DiracPure M] [WeightedSumBind M]
{α β γ : Type u} {f : α → β} {g : β → γ} {μ : M α} {φ : α → M β} {ξ : β → M γ} {b b' : β}

theorem map_eq_monad_map : map f μ = f <$> μ := rfl

theorem map_def : map f μ = bind μ (pure ∘ f) := rfl

theorem map_eq_pure_bind : map f μ = (do let x ← μ; pure (f x)) := rfl

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
  simp_rw [← bind_pure_comp, mass_bind, Function.comp_apply,
  mass_pure, mul_one, mass_eq_tsum_coeFn]

theorem map_id : map id μ = μ := bind_pure _

theorem map_comp : map g (map f μ) = map (g ∘ f) μ := (LawfulFunctor.comp_map _ _ _).symm

theorem pure_map {a : α} : map f (pure a) = (pure (f a) : M β) := pure_bind _ _

theorem map_bind : map g (bind μ φ) = bind μ fun a => map g (φ a) := bind_assoc _ _ _

@[simp]
theorem bind_map : (do let g ← (f <$> μ); ξ g) = (do let x ← μ; (ξ ∘ f) x) := by
  simp_rw [map_eq_pure_bind, bind_assoc, pure_bind, Function.comp_apply]

@[simp]
theorem map_const_apply :
  (map (Function.const α b) μ) b' = mass μ * (pure b : M β) b' :=
  bind_apply.trans (by simp_rw [Function.comp_apply, Function.const_apply,
    ENNReal.tsum_mul_right, mass_eq_tsum_coeFn])

@[simp]
theorem map_apply' [DecidableEq β] : map f μ b = ∑' a, if b = f a then μ a else 0 :=
  bind_apply.trans (by simp_rw [Function.comp_apply, pure_apply', mul_ite, mul_one, mul_zero])

end Map

section Seq

noncomputable def seq {M : Type u → Type v} [∀ α, MFLike M α] [Pure M] [Bind M]
    {α β : Type u} (κ : M (α → β)) (μ : M α) : M β := do
  let f ← κ ; let x ← μ ; return (f x)

variable {M : Type u → Type v} [∀ α, MFLike M α] [DiracPure M] [WeightedSumBind M]
{α β γ : Type u} {κ : M (α → β)} {μ : M α} {b : β}

open DiracPure WeightedSumBind

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
  bind_apply.trans (by simp_rw [bind_apply, ← ENNReal.tsum_mul_left, pure_apply',
  mul_ite, mul_one, mul_zero])

end Seq

section Filter

noncomputable def filter {M : Type u → Type v} [∀ α, MFLike M α] [Pure M] [Bind M]
    {α : Type u} [Zero (M α)] (μ : M α) (s : Set α) : M α := do
  let x ← μ
  s.indicator pure x

variable {M : Type u → Type v} [∀ α, MFLike M α] [DiracPure M] [WeightedSumBind M]
{α β γ : Type u} {μ : M α} {s : Set α} {a a' : α}

open DiracPure WeightedSumBind

theorem filter_eq_ite [Zero (M α)] [∀ a, Decidable (a ∈ s)] : filter μ s = (do
    let x ← μ
    if x ∈ s then pure x else 0) := by
  simp_rw [filter, Set.indicator_apply]

variable [ZeroNull M α]

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

variable {α : Type u}

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

variable {α : Type u}

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

variable {α : Type u}

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

variable {α : Type u}

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

section UniformOn

variable {α : Type u} [DecidableEq α] {s : Finset α} {a : α}

noncomputable def uniformOn (s : Finset α) (hs : s.Nonempty) : PMF α :=
    ofFinset (fun a => if a ∈ s then (s.card)⁻¹ else 0) s (by
  rw [Finset.sum_ite_of_true _ _ (fun _ => id), Finset.sum_const, nsmul_eq_mul]
  exact ENNReal.mul_inv_cancel
    (Nat.cast_ne_zero.mpr (hs.card_ne_zero)) (ENNReal.natCast_ne_top _)) (fun _ h => if_neg h)

@[simp]
theorem uniformOn_apply (hs : s.Nonempty) :
    uniformOn s hs a = if a ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0 := ofFinset_apply _ _ _

@[simp]
theorem uniformOn_apply_of_mem (ha : a ∈ s) (hs : s.Nonempty := ⟨a, ha⟩) :
    uniformOn s hs a = (s.card : ℝ≥0∞)⁻¹ := by
  rw [uniformOn_apply, if_pos ha]

@[simp]
theorem uniformOn_apply_of_not_mem (hs : s.Nonempty) (ha : a ∉ s) :
    uniformOn s hs a = 0 := by
  rw [uniformOn_apply, if_neg ha]

@[simp]
theorem support_uniformOn (hs : s.Nonempty) : support (uniformOn s hs) = s := Set.ext fun _ => by
  simp_rw [mem_support_iff, uniformOn_apply, ite_ne_right_iff,ENNReal.inv_ne_zero,
  and_iff_left (natCast_ne_top _), Finset.mem_coe]

theorem mem_support_uniformOn_iff (hs : s.Nonempty) :
    a ∈ support (uniformOn s hs) ↔ a ∈ s := by rw [support_uniformOn, Finset.mem_coe]

theorem nmem_support_uniformOn_iff (hs : s.Nonempty) :
    a ∉ support (uniformOn s hs) ↔ a ∉ s := (mem_support_uniformOn_iff hs).not

end UniformOn

section Uniform

variable {α : Type u}

noncomputable def uniform (α : Type u) [DecidableEq α] [Fintype α] [Nonempty α] : PMF α :=
  uniformOn Finset.univ Finset.univ_nonempty

variable [DecidableEq α] [Fintype α] [Nonempty α] {a : α}

@[simp]
theorem uniform_apply : uniform α a = (Fintype.card α : ℝ≥0∞)⁻¹ :=
  uniformOn_apply_of_mem (Finset.mem_univ _)

@[simp]
theorem support_uniform : support (uniform α) = Set.univ :=
  (support_uniformOn _).trans Finset.coe_univ

theorem mem_support_uniform (a : α) : a ∈ support (uniform α) :=
  support_uniform (α := α) ▸ Set.mem_univ _

end Uniform

section Normalize

variable {M : Type u → Type v} {α : Type u} [∀ α, MFLike M α] {μ : M α} {a : α}
{hμ : mass μ ≠ 0}

noncomputable def normalize [FMFClass M] (μ : M α) (hμ : mass μ ≠ 0) : PMF α :=
  ⟨fun a => μ a * (mass μ)⁻¹, by
    simp_rw [ENNReal.tsum_mul_right, ← mass_eq_tsum_coeFn,
    ENNReal.mul_inv_cancel hμ mass_ne_top]⟩

@[simp]
theorem normalize_apply [FMFClass M] : (normalize μ hμ) a = μ a * (mass μ)⁻¹ := rfl

@[simp]
theorem support_normalize [FMFClass M] : support (normalize μ hμ) = Function.support μ :=
  Set.ext fun a => by simp [mass_ne_top, mem_support_iff]

theorem mem_support_normalize_iff [FMFClass M] :
    a ∈ support (normalize μ hμ) ↔ μ a ≠ 0 := by simp

theorem normalize_pmf [PMFClass M] (μ : M α) (hμ : mass μ ≠ 0 := mass_ne_zero) :
    normalize μ hμ = (μ : PMF α) := by
  ext
  rw [normalize_apply, mass_eq_one, inv_one, mul_one, castPMF_apply]

@[simp]
theorem normalize_normalize [FMFClass M] (μ : M α) (hμ : mass μ ≠ 0)
    (hμ' : mass (normalize μ hμ) ≠ 0 := mass_ne_zero) :
  normalize (normalize μ hμ) hμ' = normalize μ hμ := by rw [normalize_pmf, castPMF_PMF_eq]

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
