import Mathlib.Probability.MassFunction.Basic

open BigOperators ENNReal

namespace MassFunction

universe u

section DiracPure

class DiracPure (M : Type u → Type*) [MFLike M] extends Pure M :=
(coeFn' : ∀ {α} {a : α}, ⇑(pure a : M α) = Set.indicator {a} 1)

namespace DiracPure

variable {M : Type u → Type*} [MFLike M] [DiracPure M] {α : Type u} {a a' : α} {s : Set α}

theorem coeFn_pure : ⇑(pure a : M α) = Set.indicator {a} 1 := coeFn'

theorem pure_apply : (pure a : M α) a' = Set.indicator {a} 1 a' := by rw [coeFn_pure]

theorem support_pure : support (pure a : M α) = {a} := by
  simp_rw [Set.ext_iff, mem_support_iff, coeFn_pure, Set.indicator_apply_ne_zero,
  Function.support_one, Set.inter_univ, implies_true]

@[simp]
theorem pure_apply_self : (pure a : M α) a = 1 := by
  rw [coeFn_pure, Set.indicator_singleton_apply_self, Pi.one_apply]

theorem mem_support_pure_iff : a' ∈ support (pure a : M α) ↔ a' = a := by
  rw [support_pure, Set.mem_singleton_iff]

theorem nmem_support_pure_iff : a' ∉ support (pure a : M α) ↔ a' ≠ a := mem_support_pure_iff.not

@[simp]
theorem pure_apply_of_ne (h : a' ≠ a) : (pure a : M α) a' = 0 :=
  apply_eq_zero_of_nmem_support (by rwa [support_pure])

theorem mass_pure : mass (pure a : M α) = 1 := by
  rw [mass_eq_tsum_coeFn, tsum_eq_single a (fun _ h => pure_apply_of_ne h), pure_apply_self]

theorem pure_apply' [DecidableEq α] : (pure a : M α) a' = if a' = a then 1 else 0 := by
  rcases eq_or_ne a' a with (rfl | h)
  · rw [if_pos rfl, pure_apply_self]
  · rw [if_neg h, pure_apply_of_ne h]

theorem indicator_pure_apply [∀ α, Zero (M α)] [ZeroNull M] :
    (s.indicator (pure : α → M α) a') a = (s ∩ {a'}).indicator 1 a := by
  by_cases ha' : a' ∈ s
  · rw [s.indicator_of_mem ha', pure_apply]
    congr
    rwa [Set.right_eq_inter, Set.singleton_subset_iff]
  · rw [s.indicator_of_not_mem ha', Set.inter_singleton_eq_empty.mpr ha',
    Set.indicator_empty, ZeroNull.zero_apply]

end DiracPure

noncomputable instance MF.instDiracPure : DiracPure MF where
  pure a := ⟨Set.indicator {a} 1⟩
  coeFn' := rfl

noncomputable instance FMF.instDiracPure : DiracPure FMF where
  pure a := ⟨Set.indicator {a} 1, (DiracPure.mass_pure (M := MF)).trans_lt one_lt_top⟩
  coeFn' := rfl

noncomputable instance SPMF.instDiracPure : DiracPure SPMF where
  pure a := ⟨Set.indicator {a} 1, (DiracPure.mass_pure (M := MF)).le⟩
  coeFn' := rfl

noncomputable instance PMF.instDiracPure : DiracPure PMF where
  pure a := ⟨Set.indicator {a} 1, DiracPure.mass_pure (M := MF)⟩
  coeFn' := rfl

end DiracPure

section WeightedSumBind

class WeightedSumBind (M : Type u → Type*) [MFLike M] extends Bind M :=
(coeFn' : ∀ {α β} {μ : M α} {φ : α → M β}, ⇑(bind μ φ : M β) = fun b => ∑' a, μ a * φ a b)

namespace WeightedSumBind

open DiracPure

variable {M : Type u → Type*} [MFLike M] [WeightedSumBind M] {α β γ : Type u}
{μ : M α} {ν : M β} {φ : α → M β} {ξ : β → M γ} {ψ : α → M α} {υ : α → β → M γ} {a : α} {b : β}

theorem coeFn_bind : ⇑(bind μ φ) = fun b => ∑' a, μ a * φ a b := coeFn'

theorem bind_apply : (bind μ φ) b = ∑' a, μ a * φ a b := by rw [coeFn_bind]

@[simp]
theorem mass_bind : mass (bind μ φ) = ∑' a, μ a * mass (φ a) := by
  simp_rw [mass_eq_tsum_coeFn, bind_apply, ENNReal.tsum_comm (α := β), ENNReal.tsum_mul_left]

@[simp]
theorem support_bind : support (bind μ φ) = ⋃ a ∈ support μ, support (φ a) :=
  Set.ext fun b => by
    simp_rw [mem_support_iff, Set.mem_iUnion, exists_prop, bind_apply,
    tsum_ne_zero_iff ENNReal.summable, mul_ne_zero_iff, mem_support_iff]

theorem mem_support_bind_iff : b ∈ support (bind μ φ) ↔ ∃ a ∈ support μ, b ∈ support (φ a) := by
  simp only [support_bind, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]

theorem nmem_support_bind_iff : b ∉ support (bind μ φ) ↔ ∀ a ∈ support μ, b ∉ support (φ a) := by
  simp_rw [mem_support_bind_iff.not, not_exists, not_and]

@[simp]
theorem pure_bind [DiracPure M] : bind (pure a) φ = φ a := DFunLike.ext _ _ fun _ => by
  rw [bind_apply, coeFn_pure]
  exact (tsum_eq_single a
    (fun a' h => by rw [Set.indicator_singleton_apply_of_ne h, zero_mul])).trans
    (by rw [Set.indicator_singleton_apply_self, Pi.one_apply, one_mul])

@[simp]
theorem bind_pure [DiracPure M] : bind μ pure = μ := DFunLike.ext _ _ fun _ => by
  rw [bind_apply]
  exact (tsum_eq_single _
    (fun a' h => by rw [pure_apply_of_ne h.symm, mul_zero])).trans
    (by rw [pure_apply_self, mul_one])

@[simp]
theorem bind_bind : bind (bind μ φ) ξ = bind μ fun a => bind (φ a) ξ :=
  DFunLike.ext _ _ fun _ => by
  simp_rw [bind_apply, ENNReal.tsum_mul_right.symm, ENNReal.tsum_mul_left.symm,
  ENNReal.tsum_comm (α := β), mul_assoc]

theorem bind_comm : (bind μ fun a => bind ν (υ a)) = bind ν fun b => bind μ fun a => υ a b :=
  DFunLike.ext _ _ fun _ => by
  simp_rw [bind_apply, ENNReal.tsum_mul_left.symm, ENNReal.tsum_comm (α := β), mul_left_comm]

@[simp]
theorem bind_const_apply : (bind μ fun _ => ν) b = mass μ * ν b := by
  rw [bind_apply, ENNReal.tsum_mul_right]
  rfl

end WeightedSumBind

noncomputable instance MF.instWeightedSumBind : WeightedSumBind MF where
  bind μ φ := ⟨fun b => ∑' a, μ a * φ a b⟩
  coeFn' := rfl

noncomputable instance SPNF.instWeightedSumBind : WeightedSumBind SPMF where
  bind μ φ := ⟨fun b => ∑' a, μ a * φ a b, by
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left]
    exact (ENNReal.tsum_le_tsum (fun a => mul_le_of_le_one_right' mass_le_one)).trans mass_le_one⟩
  coeFn' := rfl

noncomputable instance PMF.instWeightedSumBind : WeightedSumBind PMF where
  bind μ φ := ⟨fun b => ∑' a, μ a * φ a b, by
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left, ← mass_eq_tsum_coeFn, mass_eq_one, mul_one,
    ← mass_eq_tsum_coeFn, mass_eq_one]⟩
  coeFn' := rfl

end WeightedSumBind

section BindOnSupport

variable {M : Type u → Type*} [MFLike M] [WeightedSumBind M] {α β γ : Type u}

def IsBindOnSupport (ρ : {α β : Type u} → (μ : M α) → ((a : α) → a ∈ support μ → M β) → M β) :=
    ∀ {α β} {μ : M α} {φ : (a : α) → a ∈ support μ → M β},
    ⇑(ρ μ φ) = fun b => ∑' a, μ a * if h : μ a = 0 then 0 else φ a h b

variable {ρ : {α β : Type u} → (μ : M α) → ((a : α) → a ∈ support μ → M β) → M β}
{α β γ : Type u} {μ : M α} {ν : M β} {φ : (a : α) → a ∈ support μ → M β} {Φ : α → M β} {a : α}
{b : β} {ξ : (b : β) → b ∈ support (ρ μ φ) → M γ}
{υ : (a : α) → a ∈ support μ → (b : β) → b ∈ support ν → M γ}

namespace IsBindOnSupport

open DiracPure WeightedSumBind

variable (hρ : IsBindOnSupport ρ)

@[simp]
theorem coeFn : ρ μ φ = fun b => ∑' a, μ a * if h : μ a = 0 then 0 else φ a h b := hρ

@[simp]
theorem apply :
    ρ μ φ b = ∑' a, μ a * if h : μ a = 0 then 0 else φ a h b := hρ.coeFn ▸ rfl

theorem mass_eq [DecidablePred (· ∈ support μ)] :
    mass (ρ μ φ) =
    ∑' a, μ a * if h : a ∈ support μ then mass (φ a h) else 0 := by
  simp_rw [mass_eq_tsum_coeFn, hρ.apply, ENNReal.tsum_comm (α := β),
  ENNReal.tsum_mul_left, mem_support_iff, dite_not, tsum_dite_right]

@[simp]
theorem support_eq :
    support (ρ μ φ) = ⋃ (a : α) (h : a ∈ support μ), support (φ a h) := by
  refine' Set.ext fun b => _
  simp only [ENNReal.tsum_eq_zero, not_or, mem_support_iff,
    hρ.apply, Ne, not_forall, mul_eq_zero, Set.mem_iUnion]
  exact
    ⟨fun hb =>
      let ⟨a, ⟨ha, ha'⟩⟩ := hb
      ⟨a, ha, by simpa [ha] using ha'⟩,
      fun hb =>
      let ⟨a, ha, ha'⟩ := hb
      ⟨a, ⟨ha, by simpa [(mem_support_iff).1 ha] using ha'⟩⟩⟩

theorem mem_support_iff :
    b ∈ support (ρ μ φ) ↔
    ∃ (a : α) (h : a ∈ support μ), b ∈ support (φ a h) := by
  simp only [hρ.support_eq, Set.mem_setOf_eq, Set.mem_iUnion]

theorem nmem_support_iff :
    b ∉ support (ρ μ φ) ↔
    ∀ (a : α) (h : a ∈ support μ), b ∉ support (φ a h) := by
  simp only [hρ.mem_support_iff, not_exists]

@[simp]
theorem eq_bind [WeightedSumBind M] : (ρ μ fun a _ => Φ a) = bind μ Φ :=
  DFunLike.ext _ _ fun b => by
  have : ∀ a, ite (μ a = 0) 0 (μ a * Φ a b) = μ a * Φ a b :=
    fun a => ite_eq_right_iff.2 fun h => h.symm ▸ symm (zero_mul <| Φ a b)
  simp only [hρ.apply, bind_apply, dite_eq_ite, mul_ite, mul_zero, this]

theorem eq_zero_iff : ρ μ φ b = 0 ↔
    ∀ (a) (ha : μ a ≠ 0), φ a ha b = 0 := by
  simp only [hρ.apply, ENNReal.tsum_eq_zero, mul_eq_zero, or_iff_not_imp_left]
  exact ⟨fun h a ha => Trans.trans (dif_neg ha).symm (h a ha),
    fun h a ha => Trans.trans (dif_neg ha) (h a ha)⟩

@[simp]
theorem map_pure_left [DiracPure M] {ς : (a' : α) → a' ∈ support (pure a) → M β} :
    ρ (pure a) ς = ς a (mem_support_pure_iff.mpr rfl) := DFunLike.ext _ _ fun b => by
  classical
  simp only [hρ.apply, pure_apply]
  refine' _root_.trans (tsum_congr fun a' => _) (tsum_ite_eq a _)
  by_cases h : a' = a <;> simp [h]

theorem map_pure_right [WeightedSumBind M] [DiracPure M] : (ρ μ fun a _ => pure a) = μ := by
  rw [hρ.eq_bind, WeightedSumBind.bind_pure]

@[simp]
theorem map_map_left :
    ρ (ρ μ φ) ξ = ρ μ fun a ha => ρ (φ a ha) fun b hb =>
    ξ b (hρ.mem_support_iff.mpr ⟨a, ha, hb⟩) := DFunLike.ext _ _ fun b => by
  classical
  simp only [hρ.apply]
  simp only [← tsum_dite_right, ENNReal.tsum_mul_left.symm, ENNReal.tsum_mul_right.symm]
  simp only [ENNReal.tsum_eq_zero, dite_eq_left_iff]
  refine' ENNReal.tsum_comm.trans (tsum_congr fun a' => tsum_congr fun b => _)
  split_ifs with h _ h_1 _ h_2
  any_goals ring1
  · have := h_1 a'
    simp? [h]  at this  says simp only [h, ↓reduceDite, mul_eq_zero, false_or] at this
    contradiction
  · simp [h_2]

theorem bindOnSupport_comm :
    (ρ μ fun a ha => ρ ν (υ a ha)) = ρ ν fun b hb => ρ μ fun a ha => υ a ha b hb :=
  DFunLike.ext _ _ fun b => by
    simp only [ENNReal.coe_inj.symm, hρ.apply, ← tsum_dite_right,
      ENNReal.tsum_mul_left.symm, ENNReal.tsum_mul_right.symm]
    refine' _root_.trans ENNReal.tsum_comm (tsum_congr fun b => tsum_congr fun a => _)
    split_ifs with h1 h2 h2 <;> ring

end IsBindOnSupport

namespace MF

noncomputable def bindOnSupport (μ : MF α) (φ : ∀ a ∈ support μ, MF β) : MF β:=
  ⟨fun b => ∑' a, μ a * if h : μ a = 0 then 0 else φ a h b⟩

theorem bindOnSupport_isBindOnSupport : IsBindOnSupport bindOnSupport := rfl

end MF

namespace SPMF

noncomputable def bindOnSupport (μ : SPMF α) (φ : ∀ a ∈ support μ, SPMF β) : SPMF β:=
  ⟨fun b => ∑' a, μ a * if h : μ a = 0 then 0 else φ a h b, by
    rw [ENNReal.tsum_comm ]
    simp_rw [ENNReal.tsum_mul_left, tsum_dite_right]
    exact (ENNReal.tsum_le_tsum (fun _ => mul_le_of_le_one_right' (dite_le_one
      (fun _ => zero_le_one) (fun _ => mass_le_one)))).trans mass_le_one⟩

theorem bindOnSupport_isBindOnSupport : IsBindOnSupport bindOnSupport := rfl

end SPMF

namespace PMF

noncomputable def bindOnSupport (μ : PMF α) (φ : ∀ a ∈ support μ, PMF β) : PMF β:=
  ⟨fun b => ∑' a, μ a * if h : μ a = 0 then 0 else φ a h b, by
    rw [ENNReal.tsum_comm ]
    simp_rw [ENNReal.tsum_mul_left, tsum_dite_right, ← mass_eq_tsum_coeFn, mass_eq_one,
    dite_eq_ite, mul_ite, mul_zero, mul_one, ← mass_eq_one (μ := μ)]
    exact tsum_congr (fun _ => ite_eq_right_iff.mpr (fun h => h.symm))⟩

end PMF

end BindOnSupport

section Monad

variable {M : Type u → Type*}

instance [MFLike M] [DiracPure M] [WeightedSumBind M] : Monad M where

end Monad

end MassFunction
