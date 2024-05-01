import Mathlib.Probability.SubProbabilityMassFunction.Basic

noncomputable section

namespace SPMF

open scoped Classical
open BigOperators ENNReal

variable {α β γ : Type*}

section Pure

/-- The pure `SPMF` is the `SPMF` where all the mass lies in one point.
  The value of `pure a` is `1` at `a` and `0` elsewhere. -/
noncomputable def pure (a : α) : SPMF α :=
  ⟨fun a' => if a' = a then 1 else 0, by rw [tsum_ite_eq]⟩

variable (a a' : α)

@[simp]
theorem pure_apply : pure a a' = if a' = a then 1 else 0 := rfl

@[simp]
theorem support_pure : (pure a).support = {a} :=
  Set.ext fun a' => by simp [mem_support_iff]

theorem mem_support_pure_iff : a' ∈ (pure a).support ↔ a' = a := by simp

-- @[simp] -- Porting note (#10618): simp can prove this
theorem pure_apply_self : pure a a = 1 :=
  if_pos rfl

theorem pure_apply_of_ne (h : a' ≠ a) : pure a a' = 0 :=
  if_neg h

instance [Inhabited α] : Inhabited (SPMF α) :=
  ⟨pure default⟩

end Pure

section Bind

/-- The monadic bind operation for `SPMF`. -/
def bind (d : SPMF α) (f : α → SPMF β) : SPMF β :=
  ⟨fun b => ∑' a, d a * f a b, by
    simp_rw [ENNReal.tsum_comm (α := β), ENNReal.tsum_mul_left]
    refine' le_trans (ENNReal.tsum_le_tsum (fun a => _)) d.mass_le_one
    nth_rewrite 2 [← mul_one (d a)]
    exact ENNReal.mul_left_mono (f a).mass_le_one⟩

variable (d : SPMF α) (f : α → SPMF β) (g : β → SPMF γ)

@[simp]
theorem bind_apply (b : β) : d.bind f b = ∑' a, d a * f a b := rfl

@[simp]
theorem support_bind : (d.bind f).support = ⋃ a ∈ d.support, (f a).support :=
  Set.ext fun b => by simp [mem_support_iff, ENNReal.tsum_eq_zero, not_or]

theorem mem_support_bind_iff (b : β) :
    b ∈ (d.bind f).support ↔ ∃ a ∈ d.support, b ∈ (f a).support := by
  simp only [support_bind, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]

@[simp]
theorem pure_bind (a : α) (f : α → SPMF β) : (pure a).bind f = f a := by
  have : ∀ b a', ite (a' = a) (f a' b) 0 = ite (a' = a) (f a b) 0 := fun b a' => by
    split_ifs with h <;> simp [h]
  ext b
  simp [this]

@[simp]
theorem bind_pure : d.bind pure = d :=
  SPMF.ext fun x => (bind_apply _ _ _).trans (_root_.trans
    (tsum_eq_single x fun y hy => by rw [pure_apply_of_ne _ _ hy.symm, mul_zero]) <|
    by rw [pure_apply_self, mul_one])

@[simp]
theorem bind_bind : (d.bind f).bind g = d.bind fun a => (f a).bind g :=
  SPMF.ext fun b => by
    simpa only [ENNReal.coe_inj.symm, bind_apply, ENNReal.tsum_mul_left.symm,
      ENNReal.tsum_mul_right.symm, mul_assoc, mul_left_comm, mul_comm] using ENNReal.tsum_comm

theorem bind_comm (p : SPMF α) (q : SPMF β) (f : α → β → SPMF γ) :
    (p.bind fun a => q.bind (f a)) = q.bind fun b => p.bind fun a => f a b :=
  SPMF.ext fun b => by
    simpa only [ENNReal.coe_inj.symm, bind_apply, ENNReal.tsum_mul_left.symm,
      ENNReal.tsum_mul_right.symm, mul_assoc, mul_left_comm, mul_comm] using ENNReal.tsum_comm

@[simp]
theorem bind_const (p : SPMF α) (q : SPMF β) : (p.bind fun _ => q) = p.mass • q :=
  SPMF.ext fun x => by rw [bind_apply, ENNReal.tsum_mul_right,
  smul_apply_of_le_one (p.mass_le_one), mass_def]

end Bind

instance : Monad SPMF where
  pure a := pure a
  bind pa pb := pa.bind pb

section BindOnSupport

/-- Generalized version of `bind` allowing `f` to only be defined on the support of `p`.
  `p.bind f` is equivalent to `p.bindOnSupport (fun a _ ↦ f a)`, see `bindOnSupport_eq_bind`. -/
def bindOnSupport (d : SPMF α) (f : ∀ a ∈ d.support, SPMF β) : SPMF β :=
  ⟨fun b => ∑' a, d a * if h : d a = 0 then 0 else f a h b, by
    simp_rw [ENNReal.tsum_comm (α := β), ENNReal.tsum_mul_left, tsum_dite_right]
    refine' le_trans (ENNReal.tsum_le_tsum (fun a => _)) d.mass_le_one
    by_cases h : d a = 0
    · simp_rw [dif_pos h, mul_zero]
      exact zero_le _
    · simp_rw [dif_neg h]
      nth_rewrite 2 [← mul_one (d a)]
      exact ENNReal.mul_left_mono (f a h).mass_le_one⟩

variable {d : SPMF α} (f : ∀ a ∈ d.support, SPMF β)

@[simp]
theorem bindOnSupport_apply (b : β) :
    d.bindOnSupport f b = ∑' a, d a * if h : d a = 0 then 0 else f a h b := rfl

@[simp]
theorem support_bindOnSupport :
    (d.bindOnSupport f).support = ⋃ (a : α) (h : a ∈ d.support), (f a h).support := by
  refine' Set.ext fun b => _
  simp only [ENNReal.tsum_eq_zero, not_or, mem_support_iff, bindOnSupport_apply, Ne, not_forall,
    mul_eq_zero, Set.mem_iUnion]
  exact
    ⟨fun hb =>
      let ⟨a, ⟨ha, ha'⟩⟩ := hb
      ⟨a, ha, by simpa [ha] using ha'⟩,
      fun hb =>
      let ⟨a, ha, ha'⟩ := hb
      ⟨a, ⟨ha, by simpa [(mem_support_iff _ a).1 ha] using ha'⟩⟩⟩

theorem mem_support_bindOnSupport_iff (b : β) :
    b ∈ (d.bindOnSupport f).support ↔ ∃ (a : α) (h : a ∈ d.support), b ∈ (f a h).support := by
  simp only [support_bindOnSupport, Set.mem_setOf_eq, Set.mem_iUnion]

/-- `bindOnSupport` reduces to `bind` if `f` doesn't depend on the additional hypothesis. -/
@[simp]
theorem bindOnSupport_eq_bind (d : SPMF α) (f : α → SPMF β) :
    (d.bindOnSupport fun a _ => f a) = d.bind f := by
  ext b
  have : ∀ a, ite (d a = 0) 0 (d a * f a b) = d a * f a b :=
    fun a => ite_eq_right_iff.2 fun h => h.symm ▸ symm (zero_mul <| f a b)
  simp only [bindOnSupport_apply fun a _ => f a, d.bind_apply f, dite_eq_ite, mul_ite,
    mul_zero, this]

theorem bindOnSupport_eq_zero_iff (b : β) :
    d.bindOnSupport f b = 0 ↔ ∀ (a) (ha : d a ≠ 0), f a ha b = 0 := by
  simp only [bindOnSupport_apply, ENNReal.tsum_eq_zero, mul_eq_zero, or_iff_not_imp_left]
  exact ⟨fun h a ha => Trans.trans (dif_neg ha).symm (h a ha),
    fun h a ha => Trans.trans (dif_neg ha) (h a ha)⟩

@[simp]
theorem pure_bindOnSupport (a : α) (f : ∀ (a' : α) (_ : a' ∈ (pure a).support), SPMF β) :
    (pure a).bindOnSupport f = f a ((mem_support_pure_iff a a).mpr rfl) := by
  refine' SPMF.ext fun b => _
  simp only [bindOnSupport_apply, pure_apply]
  refine' _root_.trans (tsum_congr fun a' => _) (tsum_ite_eq a _)
  by_cases h : a' = a <;> simp [h]

theorem bindOnSupport_pure (p : SPMF α) : (p.bindOnSupport fun a _ => pure a) = p := by
  simp only [SPMF.bind_pure, SPMF.bindOnSupport_eq_bind]

@[simp]
theorem bindOnSupport_bindOnSupport (d : SPMF α) (f : ∀ a ∈ d.support, SPMF β)
    (g : ∀ b ∈ (d.bindOnSupport f).support, SPMF γ) :
    (d.bindOnSupport f).bindOnSupport g =
      d.bindOnSupport fun a ha =>
        (f a ha).bindOnSupport fun b hb =>
          g b ((mem_support_bindOnSupport_iff f b).mpr ⟨a, ha, hb⟩) := by
  refine' SPMF.ext fun a => _
  dsimp only [bindOnSupport_apply]
  simp only [← tsum_dite_right, ENNReal.tsum_mul_left.symm, ENNReal.tsum_mul_right.symm]
  simp only [ENNReal.tsum_eq_zero, dite_eq_left_iff]
  refine' ENNReal.tsum_comm.trans (tsum_congr fun a' => tsum_congr fun b => _)
  split_ifs with h _ h_1 _ h_2
  any_goals ring1
  · have := h_1 a'
    simp? [h]  at this  says simp only [h, ↓reduceDite, mul_eq_zero, false_or] at this
    contradiction
  · simp [h_2]

theorem bindOnSupport_comm (p : SPMF α) (q : SPMF β) (f : ∀ a ∈ p.support, ∀ b ∈ q.support, SPMF γ) :
    (p.bindOnSupport fun a ha => q.bindOnSupport (f a ha)) =
      q.bindOnSupport fun b hb => p.bindOnSupport fun a ha => f a ha b hb := by
  apply SPMF.ext; rintro c
  simp only [ENNReal.coe_inj.symm, bindOnSupport_apply, ← tsum_dite_right,
    ENNReal.tsum_mul_left.symm, ENNReal.tsum_mul_right.symm]
  refine' _root_.trans ENNReal.tsum_comm (tsum_congr fun b => tsum_congr fun a => _)
  split_ifs with h1 h2 h2 <;> ring

end BindOnSupport

end SPMF

end
