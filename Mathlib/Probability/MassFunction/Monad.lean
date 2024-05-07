import Mathlib.Probability.MassFunction.Basic

open BigOperators ENNReal

namespace MassFunction

universe u

variable {M : Type u → Type*} [∀ α, MFLike (M α) α]

section Pure

def IsPure (π : {α : Type u} → α → M α) :=
  ∀ {α} {a : α}, (π a) a = 1 ∧ support (π a) = {a}

variable {π : {α : Type u} → α → M α} {α : Type u} {a a' : α}

namespace IsPure

variable (hπ : IsPure π)

theorem support_eq : support (π a) = {a} := hπ.right

theorem mem_support_iff : a' ∈ support (π a) ↔ a' = a := by
  simp only [hπ.support_eq, Set.mem_singleton_iff]

theorem nmem_support_iff : a' ∉ support (π a) ↔ a' ≠ a := hπ.mem_support_iff.not

@[simp]
theorem apply_self : (π a) a = 1 := hπ.left

@[simp]
theorem apply_of_ne (h : a' ≠ a) : (π a) a' = 0 :=
  apply_eq_zero_of_nmem_support (hπ.support_eq ▸ h)

theorem mass_eq : mass (π a) = 1 := by
  rw [mass_eq_tsum_coeFn, tsum_eq_single a (fun _ h => hπ.apply_of_ne h), hπ.apply_self]

theorem apply [DecidableEq α] : (π a) a' = if a' = a then 1 else 0 := by
  rcases eq_or_ne a' a with (rfl | h)
  · rw [if_pos rfl, hπ.apply_self]
  · rw [if_neg h, hπ.apply_of_ne h]

theorem coeFn : ⇑(π a) = Set.indicator {a} 1 := by
  ext a'
  rcases (eq_or_ne a' a) with (rfl | h)
  · rw [hπ.apply_self, Set.indicator_singleton_apply_self, Pi.one_apply]
  · rw [hπ.apply_of_ne h, Set.indicator_singleton_apply_of_ne h]

end IsPure

theorem isPure_iff_coeFn_indicator_singleton_one :
    IsPure π ↔ ∀ {α} {a : α}, ⇑(π a) = Set.indicator {a} 1 := by
  refine' ⟨fun hπ => hπ.coeFn, fun hπ _ _ => _⟩
  simp_rw [Set.ext_iff, mem_support_iff, hπ, Set.indicator_singleton_apply_self, Pi.one_apply,
  Set.indicator_apply_ne_zero, Function.support_one, Set.inter_univ, implies_true, and_self]

namespace MF

noncomputable instance : Pure MF where
  pure a := ⟨Set.indicator {a} 1⟩

theorem pure_isPure : IsPure (pure : {α : Type*} → α → MF α) :=
  isPure_iff_coeFn_indicator_singleton_one.mpr (by exact rfl)

end MF

namespace FMF

noncomputable instance : Pure FMF where
  pure a := ⟨Set.indicator {a} 1, MF.pure_isPure.mass_eq.trans_lt one_lt_top⟩

theorem pure_isPure : IsPure (pure : {α : Type*} → α → FMF α) := MF.pure_isPure

end FMF

namespace SPMF

noncomputable instance : Pure SPMF where
  pure a := ⟨Set.indicator {a} 1, MF.pure_isPure.mass_eq.le⟩

theorem pure_isPure : IsPure (pure : {α : Type*} → α → SPMF α) := MF.pure_isPure

end SPMF

namespace PMF

noncomputable instance : Pure PMF where
  pure a := ⟨Set.indicator {a} 1, MF.pure_isPure.mass_eq⟩

theorem pure_isPure : IsPure (pure : {α : Type*} → α → PMF α) := MF.pure_isPure

end PMF

end Pure

section Bind

def IsBind (ρ : {α β : Type u} → M α → (α → M β) → M β) := ∀ {α β} {μ : M α} {φ : α → M β},
  ⇑(ρ μ φ) = fun b => ∑' a, μ a * φ a b

variable {ρ : {α β : Type u} → M α → (α → M β) → M β} {π : {α : Type u} → α → M α} {α β γ : Type u}
{μ : M α} {ν : M β} {φ : α → M β} {ξ : β → M γ} {ψ : α → M α} {υ : α → β → M γ} {a : α} {b : β}

namespace IsBind

variable (hρ : IsBind ρ) (hπ : IsPure π)

theorem coeFn : ⇑(ρ μ φ) = fun b => ∑' a, μ a * φ a b := hρ

theorem apply : (ρ μ φ) b = ∑' a, μ a * φ a b := hρ.coeFn ▸ rfl

@[simp]
theorem mass_eq : mass (ρ μ φ) = ∑' a, μ a * mass (φ a) := by
  simp_rw [mass_eq_tsum_coeFn, hρ.apply, ENNReal.tsum_comm (α := β), ENNReal.tsum_mul_left]

@[simp]
theorem support_eq : support (ρ μ φ) = ⋃ a ∈ support μ, support (φ a) :=
  Set.ext fun b => by
    simp_rw [mem_support_iff, Set.mem_iUnion, exists_prop, hρ.apply,
    tsum_ne_zero_iff ENNReal.summable, mul_ne_zero_iff, mem_support_iff]

theorem mem_support_iff : b ∈ support (ρ μ φ) ↔ ∃ a ∈ support μ, b ∈ support (φ a) := by
  simp only [hρ.support_eq, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]

theorem nmem_support_iff : b ∉ support (ρ μ φ) ↔ ∀ a ∈ support μ, b ∉ support (φ a) := by
  simp_rw [hρ.mem_support_iff.not, not_exists, not_and]

@[simp]
theorem map_pure_left : ρ (π a) φ = φ a := DFunLike.ext _ _ fun _ => by
  rw [hρ.apply, hπ.coeFn]
  exact (tsum_eq_single a
    (fun a' h => by rw [Set.indicator_singleton_apply_of_ne h, zero_mul])).trans
    (by rw [Set.indicator_singleton_apply_self, Pi.one_apply, one_mul])

@[simp]
theorem map_pure_right : ρ μ π = μ := DFunLike.ext _ _ fun _ => by
  rw [hρ.apply]
  exact (tsum_eq_single _
    (fun a' h => by rw [hπ.apply_of_ne h.symm, mul_zero])).trans
    (by rw [hπ.apply_self, mul_one])

@[simp]
theorem map_map_left : ρ (ρ μ φ) ξ = ρ μ fun a => ρ (φ a) ξ := DFunLike.ext _ _ fun _ => by
  simp_rw [hρ.apply, ENNReal.tsum_mul_right.symm, ENNReal.tsum_mul_left.symm,
  ENNReal.tsum_comm (α := β), mul_assoc]

theorem comm : (ρ μ fun a => ρ ν (υ a)) = ρ ν fun b => ρ μ fun a => υ a b :=
  DFunLike.ext _ _ fun _ => by
  simp_rw [hρ.apply, ENNReal.tsum_mul_left.symm, ENNReal.tsum_comm (α := β), mul_left_comm]

@[simp]
theorem const_apply : (ρ μ fun _ => ν) b = mass μ * ν b := by
  rw [hρ.apply, ENNReal.tsum_mul_right]
  rfl

end IsBind

namespace MF

noncomputable instance : Monad MF where
  bind μ φ := ⟨fun b => ∑' a, μ a * φ a b⟩

theorem bind_isBind : IsBind ((· >>= ·) : {α β : Type u} → MF α → _ → MF β) := rfl

end MF

namespace SPMF

noncomputable instance : Monad SPMF where
  bind μ φ := ⟨fun b => ∑' a, μ a * φ a b, by
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left]
    exact (ENNReal.tsum_le_tsum (fun a => mul_le_of_le_one_right' mass_le_one)).trans mass_le_one⟩

theorem bind_isBind : IsBind ((· >>= ·) : {α β : Type u} → SPMF α → _ → SPMF β) := rfl

end SPMF

namespace PMF

noncomputable instance : Monad PMF where
  bind μ φ := ⟨fun b => ∑' a, μ a * φ a b, by
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left, ← mass_eq_tsum_coeFn, mass_eq_one, mul_one,
    ← mass_eq_tsum_coeFn, mass_eq_one]⟩

theorem bind_isBind : IsBind ((· >>= ·) : {α β : Type u} → PMF α → _ → PMF β) := rfl

end PMF

end Bind

section BindOnSupport

def IsBindOnSupport (ρ : {α β : Type u} → (μ : M α) → ((a : α) → a ∈ support μ → M β) → M β) :=
    ∀ {α β} {μ : M α} {φ : (a : α) → a ∈ support μ → M β},
    ⇑(ρ μ φ) = fun b => ∑' a, μ a * if h : μ a = 0 then 0 else φ a h b

/-
variable {ρ : {α β : Type u} → (μ : M α) → ((a : α) → a ∈ support μ → M β) → M β} {π : {α : Type u} → α → M α} {α β γ : Type u}
{μ : M α} {ν : M β} {φ : α → M β} {ξ : β → M γ} {ψ : α → M α} {υ : α → β → M γ} {a : α} {b : β}

-/

variable {ρ : {α β : Type u} → (μ : M α) → ((a : α) → a ∈ support μ → M β) → M β}
{Ρ : {α β : Type u} → M α → (α → M β) → M β} {π : {α : Type u} → α → M α} {α β γ : Type u}
{μ : M α} {ν : M β} {φ : (a : α) → a ∈ support μ → M β} {Φ : α → M β} {a : α} {b : β}
{ς : (a' : α) → a' ∈ support (π a) → M β} {ξ : (b : β) → b ∈ support (ρ μ φ) → M γ}
{υ : (a : α) → a ∈ support μ → (b : β) → b ∈ support ν → M γ}

namespace IsBindOnSupport

variable (hρ : IsBindOnSupport ρ) (hΡ : IsBind Ρ) (hπ : IsPure π)

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
theorem eq_bind : (ρ μ fun a _ => Φ a) = Ρ μ Φ := DFunLike.ext _ _ fun b => by
  have : ∀ a, ite (μ a = 0) 0 (μ a * Φ a b) = μ a * Φ a b :=
    fun a => ite_eq_right_iff.2 fun h => h.symm ▸ symm (zero_mul <| Φ a b)
  simp only [hρ.apply, hΡ.apply, dite_eq_ite, mul_ite, mul_zero, this]

theorem eq_zero_iff : ρ μ φ b = 0 ↔
    ∀ (a) (ha : μ a ≠ 0), φ a ha b = 0 := by
  simp only [hρ.apply, ENNReal.tsum_eq_zero, mul_eq_zero, or_iff_not_imp_left]
  exact ⟨fun h a ha => Trans.trans (dif_neg ha).symm (h a ha),
    fun h a ha => Trans.trans (dif_neg ha) (h a ha)⟩

@[simp]
theorem map_pure_left :
    ρ (π a) ς = ς a (hπ.mem_support_iff.mpr rfl) := DFunLike.ext _ _ fun b => by
  classical
  simp only [hρ.apply, hπ.apply]
  refine' _root_.trans (tsum_congr fun a' => _) (tsum_ite_eq a _)
  by_cases h : a' = a <;> simp [h]

theorem map_pure_right : (ρ μ fun a _ => π a) = μ := by
  rw [hρ.eq_bind hΡ, hΡ.map_pure_right hπ]

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

end MassFunction
