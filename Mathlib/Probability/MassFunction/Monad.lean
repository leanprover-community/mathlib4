import Mathlib.Probability.MassFunction.Basic

open BigOperators ENNReal

namespace MassFunction

section Pure

variable {α : Type*} {F : Sort*} [MFLike F α]

def IsPure (f : F) (a : α) := ⇑f = Set.indicator {a} 1

namespace IsPure



end IsPure

variable {α : Type*} {a a' : α} {s : Set α} {F : Sort*} [MFLike F α] {f : F}

noncomputable def pure (a : α) : MF α := ⟨Set.indicator {a} 1⟩

theorem pure_def : pure a a' = Set.indicator {a} 1 a' := rfl

@[simp]
theorem mass_pure : mass (pure a) = 1 :=
  (tsum_subtype _ _).symm.trans (tsum_singleton _ _)

@[simp]
theorem support_pure : support (pure a) = {a} :=
  Set.support_indicator.trans (by rw [Function.support_one, Set.inter_univ])

theorem mem_support_pure_iff : a' ∈ support (pure a) ↔ a' = a := by
  simp only [support_pure, Set.mem_singleton_iff]

@[simp]
theorem pure_apply_self : pure a a = 1 := if_pos rfl

@[simp]
theorem pure_apply_of_ne (h : a' ≠ a) : pure a a' = 0 := if_neg h

theorem pure_apply [DecidableEq α] : pure a a' = if a' = a then 1 else 0 := by
  rcases eq_or_ne a' a with (rfl | h)
  · rw [if_pos rfl, pure_apply_self]
  · rw [if_neg h, pure_apply_of_ne h]

theorem indicator_pure_apply {F : Type*} [MFLike F α] [Zero F] [Coe (PMF α) F] :
    (s.indicator pure a') a = (s ∩ {a'}).indicator 1 a := by
  by_cases ha' : a' ∈ s
  · rw [s.indicator_of_mem ha', pure_def]
    congr
    rwa [Set.right_eq_inter, Set.singleton_subset_iff]
  · rw [s.indicator_of_not_mem ha', Set.inter_singleton_eq_empty.mpr ha',
    Set.indicator_empty, MF.zero_apply]

theorem coe_eq_pure_of_eq_one_support_singleton (ha : f a = 1) (hf : support f = {a}) :
    f = pure a := by
  ext a'
  rw [MFLike.coe_apply]
  rcases (eq_or_ne a' a) with (rfl | ha')
  · rw [pure_apply_self, ha]
  · rw [pure_apply_of_ne ha']
    exact apply_eq_zero_of_nmem_support (hf ▸ ha')

theorem coe_eq_pure_iff : f = pure a ↔ (f a = 1 ∧ support f = {a}) := by
  refine' ⟨fun hf => _, fun ⟨ha, hf⟩ => coe_eq_pure_of_eq_one_support_singleton ha hf⟩
  rw [← MFLike.coe_apply, ← MFLike.coe_support, hf, pure_apply_self, support_pure]
  exact ⟨rfl, rfl⟩

end Pure

section Bind

variable {α β γ : Type*} {F G : Sort*} [MFLike F α] [MFLike G β]
  {P : α → Sort*} [∀ a, MFLike (P a) β] {Q : β → Sort*} [∀ b, MFLike (Q b) γ]
  {W : α → β → Sort*} [∀ a b, MFLike (W a b) γ]
  {f : F} {g : G} {p : (a : α) → P a} {a : α} {b : β} {q : (b : β) → Q b}
  {w : (a : α) → (b : β) → W a b}

noncomputable def bind (f : F) (p : (a : α) → P a) : MF β := ⟨fun b => ∑' a, f a * p a b⟩
/-
variable {α β γ : Type*} {a a' : α} {s : Set α}

variable {f : MF α} {g : MF β} {p : α → MF β} {q : β → MF γ} {w : α → β → MF γ} {b : β}

noncomputable def bind (f : MF α) (g : α → MF β) : MF β := ⟨fun b => ∑' a, f a * g a b⟩
-/
theorem bind_apply : bind f p b = ∑' a, f a * p a b := rfl

@[simp]
theorem mass_bind : mass (bind f p) = ∑' a, f a * mass (p a) := by
  simp_rw [mass_eq_tsum, bind_apply, ENNReal.tsum_comm (α := β), ENNReal.tsum_mul_left]

theorem mass_bind_le_one : mass (bind f p) = ∑' a, f a * mass (p a) := by
  simp_rw [mass_eq_tsum, bind_apply, ENNReal.tsum_comm (α := β), ENNReal.tsum_mul_left]

@[simp]
theorem support_bind :
    support (bind f p) = ⋃ a ∈ support f, support (p a) :=
  Set.ext fun b => by
    simp_rw [mem_support_iff, Set.mem_iUnion, exists_prop, bind_apply,
    tsum_ne_zero_iff ENNReal.summable, mul_ne_zero_iff, mem_support_iff]

theorem mem_support_bind_iff :
    b ∈ support (bind f p) ↔ ∃ a ∈ support f, b ∈ support (p a) := by
  simp only [support_bind, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]

@[simp]
theorem pure_bind : bind (pure a) p = p a := by
  classical
  have ha : ∀ b a', ite (a' = a) (p a' b) 0 = ite (a' = a) (p a b) 0 := fun b a' => by
    split_ifs with H
    · congr
    · rfl
  simp_rw [DFunLike.ext_iff, bind_apply, MFLike.coe_apply, pure_apply,
    ite_mul, one_mul, zero_mul, ha, tsum_ite_eq, implies_true]

@[simp]
theorem bind_pure : bind f pure = f :=
  MF.ext fun x => bind_apply.trans (_root_.trans
    (tsum_eq_single x fun y hy => by rw [pure_apply_of_ne hy.symm, mul_zero]) <|
    by rw [pure_apply_self, mul_one, MFLike.coe_apply])

@[simp]
theorem bind_bind : bind (bind f p) q = bind f fun a => bind (p a) q :=
  MF.ext fun b => by
    simpa only [ENNReal.coe_inj.symm, bind_apply, ENNReal.tsum_mul_left.symm,
      ENNReal.tsum_mul_right.symm, mul_assoc, mul_left_comm, mul_comm] using ENNReal.tsum_comm

theorem bind_comm :
    (bind f fun a => bind g (w a)) = bind g fun b => bind f fun a => w a b :=
  MF.ext fun b => by
    simpa only [ENNReal.coe_inj.symm, bind_apply, ENNReal.tsum_mul_left.symm,
      ENNReal.tsum_mul_right.symm, mul_assoc, mul_left_comm, mul_comm] using ENNReal.tsum_comm

@[simp]
theorem bind_const_apply : (bind f fun _ => g) b = (mass f) * g b := by
    rw [bind_apply, ENNReal.tsum_mul_right, mass_eq_tsum]

end Bind

noncomputable instance instMonad : Monad MF where
  pure a := pure a
  bind pa pb := bind pa pb

section BindOnMassSupport

variable {f : MF α} {q : MF β} {g : ∀ a ∈ support f, MF β} {p : α → MF β} {a : α}
  {b : β} {w : ∀ (a' : α) (_ : a' ∈ support (pure a)), MF β}

noncomputable def bindOnMassSupport (f : MF α) (g : ∀ a ∈ support f, MF β) : MF β :=
  ⟨fun b => ∑' a, f a * if h : f a = 0 then 0 else g a h b⟩

@[simp]
theorem bindOnMassSupport_apply :
    bindOnMassSupport f g b = ∑' a, f a * if h : f a = 0 then 0 else g a h b := rfl

theorem mass_bindOnMassSupport [DecidablePred (· ∈ support f)] :
    mass (bindOnMassSupport f g) =
    ∑' a, f a * if h : a ∈ support f then mass (g a h) else 0 := by
  simp_rw [ ← tsum_eq_mass, bindOnMassSupport_apply, ENNReal.tsum_comm (α := β),
  ENNReal.tsum_mul_left, mem_support_iff, dite_not, tsum_dite_right]


@[simp]
theorem support_bindOnMassSupport :
    support (bindOnMassSupport f g) = ⋃ (a : α)
    (h : a ∈ support f), support (g a h) := by
  refine' Set.ext fun b => _
  simp only [ENNReal.tsum_eq_zero, not_or, mem_support_iff,
    bindOnMassSupport_apply, Ne, not_forall, mul_eq_zero, Set.mem_iUnion]
  exact
    ⟨fun hb =>
      let ⟨a, ⟨ha, ha'⟩⟩ := hb
      ⟨a, ha, by simpa [ha] using ha'⟩,
      fun hb =>
      let ⟨a, ha, ha'⟩ := hb
      ⟨a, ⟨ha, by simpa [(mem_support_iff).1 ha] using ha'⟩⟩⟩

theorem mem_support_bindOnMassSupport_iff :
    b ∈ support (bindOnMassSupport f g) ↔
    ∃ (a : α) (h : a ∈ support f), b ∈ support (g a h) := by
  simp only [support_bindOnMassSupport, Set.mem_setOf_eq, Set.mem_iUnion]

@[simp]
theorem bindOnMassSupport_eq_bind : (bindOnMassSupport f fun a _ => p a) = bind f p := by
  ext b
  have : ∀ a, ite (f a = 0) 0 (f a * p a b) = f a * p a b :=
    fun a => ite_eq_right_iff.2 fun h => h.symm ▸ symm (zero_mul <| p a b)
  simp only [bindOnMassSupport_apply, bind_apply, dite_eq_ite, mul_ite,
    mul_zero, this]

theorem bindOnMassSupport_eq_zero_iff : bindOnMassSupport f g b = 0 ↔
    ∀ (a) (ha : f a ≠ 0), g a ha b = 0 := by
  simp only [bindOnMassSupport_apply, ENNReal.tsum_eq_zero, mul_eq_zero, or_iff_not_imp_left]
  exact ⟨fun h a ha => Trans.trans (dif_neg ha).symm (h a ha),
    fun h a ha => Trans.trans (dif_neg ha) (h a ha)⟩

@[simp]
theorem pure_bindOnMassSupport :
    (pure a).bindOnMassSupport w = w a ((mem_support_pure_iff).mpr rfl) := by
  classical
  refine' MF.ext fun b => _
  simp only [bindOnMassSupport_apply, pure_apply]
  refine' _root_.trans (tsum_congr fun a' => _) (tsum_ite_eq a _)
  by_cases h : a' = a <;> simp [h]

theorem bindOnMassSupport_pure : (f.bindOnMassSupport fun a _ => pure a) = f := by
  simp only [bind_pure, bindOnMassSupport_eq_bind]

@[simp]
theorem bindOnsupport_bindOnMassSupport {h : ∀ b ∈ support (bindOnMassSupport f g), MF γ}:
    (f.bindOnMassSupport g).bindOnMassSupport h =
      f.bindOnMassSupport fun a ha =>
        (g a ha).bindOnMassSupport fun b hb =>
          h b ((mem_support_bindOnMassSupport_iff).mpr ⟨a, ha, hb⟩) := by
  classical
  refine' MF.ext fun a => _
  dsimp only [bindOnMassSupport_apply]
  simp only [← tsum_dite_right, ENNReal.tsum_mul_left.symm, ENNReal.tsum_mul_right.symm]
  simp only [ENNReal.tsum_eq_zero, dite_eq_left_iff]
  refine' ENNReal.tsum_comm.trans (tsum_congr fun a' => tsum_congr fun b => _)
  split_ifs with h _ h_1 _ h_2
  any_goals ring1
  · have := h_1 a'
    simp? [h]  at this  says simp only [h, ↓reduceDite, mul_eq_zero, false_or] at this
    contradiction
  · simp [h_2]

theorem bindOnMassSupport_comm {h : ∀ a ∈ support f, ∀ b ∈ support q, MF γ} :
    (f.bindOnMassSupport fun a ha => q.bindOnMassSupport (h a ha)) =
      q.bindOnMassSupport fun b hb => f.bindOnMassSupport fun a ha => h a ha b hb := by
  apply MF.ext; rintro c
  simp only [ENNReal.coe_inj.symm, bindOnMassSupport_apply, ← tsum_dite_right,
    ENNReal.tsum_mul_left.symm, ENNReal.tsum_mul_right.symm]
  refine' _root_.trans ENNReal.tsum_comm (tsum_congr fun b => tsum_congr fun a => _)
  split_ifs with h1 h2 h2 <;> ring

end BindOnMassSupport



namespace MF

variable {α β γ : Type*} {a a' : α} {s : Set α}

section Pure

noncomputable def pure (a : α) : MF α := ⟨Set.indicator {a} 1⟩

theorem pure_def : pure a a' = Set.indicator {a} 1 a' := rfl

@[simp]
theorem mass_pure : mass (pure a) = 1 := by
  simp_rw [← tsum_eq_mass, pure_def, ← tsum_subtype, tsum_singleton, Pi.one_apply]

@[simp]
theorem support_pure : support (pure a) = {a} :=
  Set.ext fun b => by
    rw [mem_support_iff, pure_def, Set.indicator_apply_ne_zero,
    Function.support_one, Set.inter_univ]

theorem mem_support_pure_iff : a' ∈ support (pure a) ↔ a' = a := by
  simp only [support_pure, Set.mem_singleton_iff]

@[simp]
theorem pure_apply_self : pure a a = 1 := if_pos rfl

@[simp]
theorem pure_apply_of_ne (h : a' ≠ a) : pure a a' = 0 := if_neg h

theorem pure_apply [DecidableEq α] : pure a a' = if a' = a then 1 else 0 := by
  rcases eq_or_ne a' a with (rfl | h)
  · rw [if_pos rfl, pure_apply_self]
  · rw [if_neg h, pure_apply_of_ne h]

theorem indicator_pure_apply : (s.indicator pure a') a = (s ∩ {a'}).indicator 1 a := by
  by_cases ha' : a' ∈ s
  · rw [s.indicator_of_mem ha', pure_def]
    congr
    rwa [Set.right_eq_inter, Set.singleton_subset_iff]
  · rw [s.indicator_of_not_mem ha', Set.inter_singleton_eq_empty.mpr ha',
    Set.indicator_empty, zero_apply]

end Pure

section Bind

variable {f : MF α} {g : MF β} {p : α → MF β} {q : β → MF γ} {w : α → β → MF γ} {b : β}

noncomputable def bind (f : MF α) (g : α → MF β) : MF β :=
  fun b => ∑' a, f a * g a b

theorem bind_apply : bind f p b = ∑' a, f a * p a b := rfl

@[simp]
theorem mass_bind : mass (bind f p) = ∑' a, f a * mass (p a) := by
  simp_rw [mass_eq_tsum, bind_apply, ENNReal.tsum_comm (α := β), ENNReal.tsum_mul_left]

@[simp]
theorem support_bind :
    support (bind f p) = ⋃ a ∈ support f, support (p a) :=
  Set.ext fun b => by
    simp_rw [mem_support_iff, Set.mem_iUnion, exists_prop, bind_apply,
    tsum_ne_zero_iff ENNReal.summable, mul_ne_zero_iff, mem_support_iff]

theorem mem_support_bind_iff :
    b ∈ support (bind f p) ↔ ∃ a ∈ support f, b ∈ support (p a) := by
  simp only [support_bind, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]

@[simp]
theorem pure_bind : (pure a).bind p = p a := by
  classical
  have ha : ∀ b a', ite (a' = a) (p a' b) 0 = ite (a' = a) (p a b) 0 := fun b a' => by
    split_ifs with H <;> simp [H]
  simp_rw [DFunLike.ext_iff, bind_apply, pure_apply, ite_mul, one_mul, zero_mul,
    ha, tsum_ite_eq, implies_true]

@[simp]
theorem bind_pure : bind f pure = f :=
  MF.ext fun x => bind_apply.trans (_root_.trans
    (tsum_eq_single x fun y hy => by rw [pure_apply_of_ne hy.symm, mul_zero]) <|
    by rw [pure_apply_self, mul_one])

@[simp]
theorem bind_bind : (bind f p).bind q = bind f fun a => (p a).bind q :=
  MF.ext fun b => by
    simpa only [ENNReal.coe_inj.symm, bind_apply, ENNReal.tsum_mul_left.symm,
      ENNReal.tsum_mul_right.symm, mul_assoc, mul_left_comm, mul_comm] using ENNReal.tsum_comm

theorem bind_comm :
    (bind f fun a => bind g (w a)) = bind g fun b => bind f fun a => w a b :=
  MF.ext fun b => by
    simpa only [ENNReal.coe_inj.symm, bind_apply, ENNReal.tsum_mul_left.symm,
      ENNReal.tsum_mul_right.symm, mul_assoc, mul_left_comm, mul_comm] using ENNReal.tsum_comm

@[simp]
theorem bind_const_apply : (bind f fun _ => g) b = (mass f) * g b := by
    rw [bind_apply, ENNReal.tsum_mul_right, tsum_eq_mass]

end Bind

noncomputable instance instMonad : Monad MF where
  pure a := pure a
  bind pa pb := pa.bind pb

section BindOnMassSupport

variable {f : MF α} {q : MF β} {g : ∀ a ∈ support f, MF β} {p : α → MF β} {a : α}
  {b : β} {w : ∀ (a' : α) (_ : a' ∈ support (pure a)), MF β}

noncomputable def bindOnMassSupport (f : MF α) (g : ∀ a ∈ support f, MF β) : MF β :=
  ⟨fun b => ∑' a, f a * if h : f a = 0 then 0 else g a h b⟩

@[simp]
theorem bindOnMassSupport_apply :
    bindOnMassSupport f g b = ∑' a, f a * if h : f a = 0 then 0 else g a h b := rfl

theorem mass_bindOnMassSupport [DecidablePred (· ∈ support f)] :
    mass (bindOnMassSupport f g) =
    ∑' a, f a * if h : a ∈ support f then mass (g a h) else 0 := by
  simp_rw [ ← tsum_eq_mass, bindOnMassSupport_apply, ENNReal.tsum_comm (α := β),
  ENNReal.tsum_mul_left, mem_support_iff, dite_not, tsum_dite_right]


@[simp]
theorem support_bindOnMassSupport :
    support (bindOnMassSupport f g) = ⋃ (a : α)
    (h : a ∈ support f), support (g a h) := by
  refine' Set.ext fun b => _
  simp only [ENNReal.tsum_eq_zero, not_or, mem_support_iff,
    bindOnMassSupport_apply, Ne, not_forall, mul_eq_zero, Set.mem_iUnion]
  exact
    ⟨fun hb =>
      let ⟨a, ⟨ha, ha'⟩⟩ := hb
      ⟨a, ha, by simpa [ha] using ha'⟩,
      fun hb =>
      let ⟨a, ha, ha'⟩ := hb
      ⟨a, ⟨ha, by simpa [(mem_support_iff).1 ha] using ha'⟩⟩⟩

theorem mem_support_bindOnMassSupport_iff :
    b ∈ support (bindOnMassSupport f g) ↔
    ∃ (a : α) (h : a ∈ support f), b ∈ support (g a h) := by
  simp only [support_bindOnMassSupport, Set.mem_setOf_eq, Set.mem_iUnion]

@[simp]
theorem bindOnMassSupport_eq_bind : (bindOnMassSupport f fun a _ => p a) = bind f p := by
  ext b
  have : ∀ a, ite (f a = 0) 0 (f a * p a b) = f a * p a b :=
    fun a => ite_eq_right_iff.2 fun h => h.symm ▸ symm (zero_mul <| p a b)
  simp only [bindOnMassSupport_apply, bind_apply, dite_eq_ite, mul_ite,
    mul_zero, this]

theorem bindOnMassSupport_eq_zero_iff : bindOnMassSupport f g b = 0 ↔
    ∀ (a) (ha : f a ≠ 0), g a ha b = 0 := by
  simp only [bindOnMassSupport_apply, ENNReal.tsum_eq_zero, mul_eq_zero, or_iff_not_imp_left]
  exact ⟨fun h a ha => Trans.trans (dif_neg ha).symm (h a ha),
    fun h a ha => Trans.trans (dif_neg ha) (h a ha)⟩

@[simp]
theorem pure_bindOnMassSupport :
    (pure a).bindOnMassSupport w = w a ((mem_support_pure_iff).mpr rfl) := by
  classical
  refine' MF.ext fun b => _
  simp only [bindOnMassSupport_apply, pure_apply]
  refine' _root_.trans (tsum_congr fun a' => _) (tsum_ite_eq a _)
  by_cases h : a' = a <;> simp [h]

theorem bindOnMassSupport_pure : (f.bindOnMassSupport fun a _ => pure a) = f := by
  simp only [bind_pure, bindOnMassSupport_eq_bind]

@[simp]
theorem bindOnsupport_bindOnMassSupport {h : ∀ b ∈ support (bindOnMassSupport f g), MF γ}:
    (f.bindOnMassSupport g).bindOnMassSupport h =
      f.bindOnMassSupport fun a ha =>
        (g a ha).bindOnMassSupport fun b hb =>
          h b ((mem_support_bindOnMassSupport_iff).mpr ⟨a, ha, hb⟩) := by
  classical
  refine' MF.ext fun a => _
  dsimp only [bindOnMassSupport_apply]
  simp only [← tsum_dite_right, ENNReal.tsum_mul_left.symm, ENNReal.tsum_mul_right.symm]
  simp only [ENNReal.tsum_eq_zero, dite_eq_left_iff]
  refine' ENNReal.tsum_comm.trans (tsum_congr fun a' => tsum_congr fun b => _)
  split_ifs with h _ h_1 _ h_2
  any_goals ring1
  · have := h_1 a'
    simp? [h]  at this  says simp only [h, ↓reduceDite, mul_eq_zero, false_or] at this
    contradiction
  · simp [h_2]

theorem bindOnMassSupport_comm {h : ∀ a ∈ support f, ∀ b ∈ support q, MF γ} :
    (f.bindOnMassSupport fun a ha => q.bindOnMassSupport (h a ha)) =
      q.bindOnMassSupport fun b hb => f.bindOnMassSupport fun a ha => h a ha b hb := by
  apply MF.ext; rintro c
  simp only [ENNReal.coe_inj.symm, bindOnMassSupport_apply, ← tsum_dite_right,
    ENNReal.tsum_mul_left.symm, ENNReal.tsum_mul_right.symm]
  refine' _root_.trans ENNReal.tsum_comm (tsum_congr fun b => tsum_congr fun a => _)
  split_ifs with h1 h2 h2 <;> ring

end BindOnMassSupport

end MF

namespace SPMF

variable {α β γ : Type*} {a a' : α} {s : Set α}

section Pure

noncomputable def pure (a : α) : SPMF α := ⟨MF.pure a, MF.mass_pure.le⟩

theorem pure_def : pure a a' = Set.indicator {a} 1 a' := MF.pure_def

@[simp]
theorem mass_pure : mass (pure a) = 1 := MF.mass_pure

@[simp]
theorem support_pure : support (pure a) = {a} := MF.support_pure

theorem mem_support_pure_iff : a' ∈ support (pure a) ↔ a' = a :=
  MF.mem_support_pure_iff

@[simp]
theorem pure_apply_self : pure a a = 1 := MF.pure_apply_self

@[simp]
theorem pure_apply_of_ne (h : a' ≠ a) : pure a a' = 0 := MF.pure_apply_of_ne h

theorem pure_apply [DecidableEq α] : pure a a' = if a' = a then 1 else 0 := by
  rcases eq_or_ne a' a with (rfl | h)
  · rw [if_pos rfl, pure_apply_self]
  · rw [if_neg h, pure_apply_of_ne h]

theorem indicator_pure_apply : (s.indicator pure a') a = (s ∩ {a'}).indicator 1 a := by
  by_cases ha' : a' ∈ s
  · rw [s.indicator_of_mem ha', pure_def]
    congr
    rwa [Set.right_eq_inter, Set.singleton_subset_iff]
  · rw [s.indicator_of_not_mem ha', Set.inter_singleton_eq_empty.mpr ha',
    Set.indicator_empty, zero_apply]

end Pure

section Bind

variable {f : SPMF α} {g : SPMF β} {p : α → SPMF β} {q : β → SPMF γ} {w : α → β → SPMF γ} {b : β}

noncomputable def bind (f : SPMF α) (g : α → SPMF β) : SPMF β :=
  ⟨fun b => ∑' a, f a * g a b, by
    simp [mass_eq_tsum, ENNReal.tsum_comm (α := β), ENNReal.tsum_mul_left]
    exact (ENNReal.tsum_le_tsum (fun a => mul_le_of_le_one_right' mass_le_one)).trans mass_le_one⟩

theorem bind_apply : bind f p b = ∑' a, f a * p a b := rfl

@[simp]
theorem mass_bind : mass (bind f p) = ∑' a, f a * mass (p a) := by
  simp_rw [mass_eq_tsum, bind_apply, ENNReal.tsum_comm (α := β), ENNReal.tsum_mul_left]

@[simp]
theorem support_bind : support (bind f p) = ⋃ a ∈ support f, support (p a) :=
  Set.ext fun b => by
    simp_rw [mem_support_iff, Set.mem_iUnion, exists_prop, bind_apply,
    tsum_ne_zero_iff ENNReal.summable, mul_ne_zero_iff, mem_support_iff]

theorem mem_support_bind_iff :
    b ∈ support (bind f p) ↔ ∃ a ∈ support f, b ∈ support (p a) := by
  simp only [support_bind, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]

@[simp]
theorem pure_bind : (pure a).bind p = p a := by
  classical
  have ha : ∀ b a', ite (a' = a) (p a' b) 0 = ite (a' = a) (p a b) 0 := fun b a' => by
    split_ifs with H <;> simp [H]
  simp_rw [DFunLike.ext_iff, bind_apply, pure_apply, ite_mul, one_mul, zero_mul,
    ha, tsum_ite_eq, implies_true]

@[simp]
theorem bind_pure : bind f pure = f :=
  SPMF.ext fun x => bind_apply.trans (_root_.trans
    (tsum_eq_single x fun y hy => by rw [pure_apply_of_ne hy.symm, mul_zero]) <|
    by rw [pure_apply_self, mul_one])

@[simp]
theorem bind_bind : (bind f p).bind q = bind f fun a => (p a).bind q :=
  SPMF.ext fun b => by
    simpa only [ENNReal.coe_inj.symm, bind_apply, ENNReal.tsum_mul_left.symm,
      ENNReal.tsum_mul_right.symm, mul_assoc, mul_left_comm, mul_comm] using ENNReal.tsum_comm

theorem bind_comm :
    (bind f fun a => bind g (w a)) = bind g fun b => bind f fun a => w a b :=
  SPMF.ext fun b => by
    simpa only [ENNReal.coe_inj.symm, bind_apply, ENNReal.tsum_mul_left.symm,
      ENNReal.tsum_mul_right.symm, mul_assoc, mul_left_comm, mul_comm] using ENNReal.tsum_comm

@[simp]
theorem bind_const_apply : (bind f fun _ => g) b = (mass f) * g b := by
    rw [bind_apply, ENNReal.tsum_mul_right, tsum_eq_mass]

end Bind

noncomputable instance instMonad : Monad SPMF where
  pure a := pure a
  bind pa pb := pa.bind pb

section BindOnMassSupport

variable {f : SPMF α} {q : SPMF β} {g : ∀ a ∈ support f, SPMF β} {p : α → SPMF β} {a : α}
  {b : β} {w : ∀ (a' : α) (_ : a' ∈ support (pure a)), SPMF β}

noncomputable def bindOnMassSupport (f : SPMF α) (g : ∀ a ∈ support f, SPMF β) : SPMF β :=
  ⟨fun b => ∑' a, f a * if h : f a = 0 then 0 else g a h b, by
    simp_rw [ENNReal.tsum_comm (α := β), ENNReal.tsum_mul_left, tsum_dite_right]
    exact (ENNReal.tsum_le_tsum (fun _ => mul_le_of_le_one_right' (dite_le_one
      (fun _ => zero_le_one) (fun _ => mass_le_one)))).trans mass_le_one⟩

@[simp]
theorem bindOnMassSupport_apply :
    bindOnMassSupport f g b = ∑' a, f a * if h : f a = 0 then 0 else g a h b := rfl

theorem mass_bindOnMassSupport [DecidablePred (· ∈ support f)] :
    mass (bindOnMassSupport f g) =
    ∑' a, f a * if h : a ∈ support f then mass (g a h) else 0 := by
  simp_rw [ ← tsum_eq_mass, bindOnMassSupport_apply, ENNReal.tsum_comm (α := β),
  ENNReal.tsum_mul_left, mem_support_iff, dite_not, tsum_dite_right]


@[simp]
theorem support_bindOnMassSupport :
    support (bindOnMassSupport f g) = ⋃ (a : α)
    (h : a ∈ support f), support (g a h) := by
  refine' Set.ext fun b => _
  simp only [ENNReal.tsum_eq_zero, not_or, mem_support_iff,
    bindOnMassSupport_apply, Ne, not_forall, mul_eq_zero, Set.mem_iUnion]
  exact
    ⟨fun hb =>
      let ⟨a, ⟨ha, ha'⟩⟩ := hb
      ⟨a, ha, by simpa [ha] using ha'⟩,
      fun hb =>
      let ⟨a, ha, ha'⟩ := hb
      ⟨a, ⟨ha, by simpa [(mem_support_iff).1 ha] using ha'⟩⟩⟩

theorem mem_support_bindOnMassSupport_iff :
    b ∈ support (bindOnMassSupport f g) ↔
    ∃ (a : α) (h : a ∈ support f), b ∈ support (g a h) := by
  simp only [support_bindOnMassSupport, Set.mem_setOf_eq, Set.mem_iUnion]

@[simp]
theorem bindOnMassSupport_eq_bind : (bindOnMassSupport f fun a _ => p a) = bind f p := by
  ext b
  have : ∀ a, ite (f a = 0) 0 (f a * p a b) = f a * p a b :=
    fun a => ite_eq_right_iff.2 fun h => h.symm ▸ symm (zero_mul <| p a b)
  simp only [bindOnMassSupport_apply, bind_apply, dite_eq_ite, mul_ite,
    mul_zero, this]

theorem bindOnMassSupport_eq_zero_iff : bindOnMassSupport f g b = 0 ↔
    ∀ (a) (ha : f a ≠ 0), g a ha b = 0 := by
  simp only [bindOnMassSupport_apply, ENNReal.tsum_eq_zero, mul_eq_zero, or_iff_not_imp_left]
  exact ⟨fun h a ha => Trans.trans (dif_neg ha).symm (h a ha),
    fun h a ha => Trans.trans (dif_neg ha) (h a ha)⟩

@[simp]
theorem pure_bindOnMassSupport :
    (pure a).bindOnMassSupport w = w a ((mem_support_pure_iff).mpr rfl) := by
  classical
  refine' SPMF.ext fun b => _
  simp only [bindOnMassSupport_apply, pure_apply]
  refine' _root_.trans (tsum_congr fun a' => _) (tsum_ite_eq a _)
  by_cases h : a' = a <;> simp [h]

theorem bindOnMassSupport_pure : (f.bindOnMassSupport fun a _ => pure a) = f := by
  simp only [SPMF.bind_pure, SPMF.bindOnMassSupport_eq_bind]

@[simp]
theorem bindOnsupport_bindOnMassSupport {h : ∀ b ∈ support (bindOnMassSupport f g), SPMF γ}:
    (f.bindOnMassSupport g).bindOnMassSupport h =
      f.bindOnMassSupport fun a ha =>
        (g a ha).bindOnMassSupport fun b hb =>
          h b ((mem_support_bindOnMassSupport_iff).mpr ⟨a, ha, hb⟩) := by
  classical
  refine' SPMF.ext fun a => _
  dsimp only [bindOnMassSupport_apply]
  simp only [← tsum_dite_right, ENNReal.tsum_mul_left.symm, ENNReal.tsum_mul_right.symm]
  simp only [ENNReal.tsum_eq_zero, dite_eq_left_iff]
  refine' ENNReal.tsum_comm.trans (tsum_congr fun a' => tsum_congr fun b => _)
  split_ifs with h _ h_1 _ h_2
  any_goals ring1
  · have := h_1 a'
    simp? [h]  at this  says simp only [h, ↓reduceDite, mul_eq_zero, false_or] at this
    contradiction
  · simp [h_2]

theorem bindOnMassSupport_comm {h : ∀ a ∈ support f, ∀ b ∈ support q, SPMF γ} :
    (f.bindOnMassSupport fun a ha => q.bindOnMassSupport (h a ha)) =
      q.bindOnMassSupport fun b hb => f.bindOnMassSupport fun a ha => h a ha b hb := by
  apply SPMF.ext; rintro c
  simp only [ENNReal.coe_inj.symm, bindOnMassSupport_apply, ← tsum_dite_right,
    ENNReal.tsum_mul_left.symm, ENNReal.tsum_mul_right.symm]
  refine' _root_.trans ENNReal.tsum_comm (tsum_congr fun b => tsum_congr fun a => _)
  split_ifs with h1 h2 h2 <;> ring

end BindOnMassSupport

end SPMF

namespace PMF

variable {α β γ : Type*} {a a' : α} {s : Set α}

section Pure

noncomputable def pure (a : α) : PMF α := ⟨MF.pure a, MF.mass_pure⟩

theorem pure_def : pure a a' = Set.indicator {a} 1 a' := MF.pure_def

@[simp]
theorem coe_pure : (pure a : SPMF α) = SPMF.pure a := rfl

@[simp]
theorem support_pure : support (pure a) = {a} := SPMF.support_pure

theorem mem_support_pure_iff : a' ∈ support (pure a) ↔ a' = a := SPMF.mem_support_pure_iff

@[simp]
theorem pure_apply_self : pure a a = 1 := SPMF.pure_apply_self

theorem pure_apply_of_ne (h : a' ≠ a) : pure a a' = 0 := SPMF.pure_apply_of_ne h

noncomputable instance [Inhabited α] : Inhabited (PMF α) := ⟨pure default⟩

theorem pure_apply [DecidableEq α] : pure a a' = if a' = a then 1 else 0 := SPMF.pure_apply

theorem indicator_pure_apply : (s.indicator pure a') a = (s ∩ {a'}).indicator 1 a := by
  by_cases ha' : a' ∈ s
  · rw [s.indicator_of_mem ha', pure_def]
    congr
    rwa [Set.right_eq_inter, Set.singleton_subset_iff]
  · rw [s.indicator_of_not_mem ha', Set.inter_singleton_eq_empty.mpr ha',
    Set.indicator_empty, zero_apply]

end Pure

section Bind

variable {f : PMF α} {g : PMF β} {p : α → PMF β} {q : β → PMF γ} {w : α → β → PMF γ} {b : β}

noncomputable def bind (f : PMF α) (g : α → PMF β) : PMF β :=
  ⟨fun b => ∑' a, f a * g a b, by
    simp only [ENNReal.tsum_comm (α := β), ENNReal.tsum_mul_left, tsum_eq_mass,
    mass_eq_one, mul_one]⟩

theorem bind_apply : bind f p b = ∑' a, f a * p a b := rfl

@[simp]
theorem coe_bind : (bind f p : SPMF β) = SPMF.bind f (fun a => (p a)) := rfl

@[simp]
theorem support_bind : support (bind f p) = ⋃ a ∈ support f, support (p a) := by
  simp_rw [← SPMFClass.coe_support (bind f p), coe_bind, SPMF.support_bind,
  SPMFClass.coe_support]

theorem mem_support_bind_iff : b ∈ support (bind f p) ↔
    ∃ a ∈ support f, b ∈ support (p a) := by
  simp_rw [← SPMFClass.coe_support (bind f p), coe_bind, SPMF.mem_support_bind_iff,
  SPMFClass.coe_support]

@[simp]
theorem pure_bind : (pure a).bind p = p a := by
  rw [← SPMFClass.coe_fn_coe, coe_bind, coe_pure, SPMF.pure_bind]

@[simp]
theorem bind_pure : bind f pure = f := by
  simp_rw [← SPMFClass.coe_fn_coe (bind f pure), coe_bind, coe_pure, SPMF.bind_pure]

@[simp]
theorem bind_bind : (bind f p).bind q = bind f fun a => (p a).bind q := by
  simp_rw [← SPMFClass.coe_fn_coe ((bind f p).bind q), coe_bind, SPMF.bind_bind]

theorem bind_comm :
    (bind f fun a => bind g (w a)) = bind g fun b => bind f fun a => w a b := by
  simp_rw [← SPMFClass.coe_fn_coe ((bind f fun a => bind g (w a))), coe_bind,
  SPMF.bind_comm (f := (f : SPMF α))]

@[simp]
theorem bind_const : (bind f fun _ => g) = g := by
  simp_rw [← SPMFClass.coe_fn_coe _ g, coe_bind, DFunLike.ext_iff, SPMF.bind_const_apply,
  SPMFClass.coe_mass, mass_eq_one, one_mul, implies_true]

end Bind

noncomputable instance instMonad : Monad PMF where
  pure a := pure a
  bind pa pb := pa.bind pb

section BindOnMassSupport

variable {f : PMF α} {q : PMF β} {g : ∀ a ∈ support f, PMF β} {p : α → PMF β} {a : α}
  {b : β} {w : ∀ (a' : α) (_ : a' ∈ support (pure a)), PMF β}

noncomputable def bindOnMassSupport (f : PMF α) (g : ∀ a ∈ support f, PMF β) : PMF β :=
  ⟨fun b => ∑' a, f a * if h : f a = 0 then 0 else g a h b, by
    simp_rw [ENNReal.tsum_comm (α := β), ENNReal.tsum_mul_left, tsum_dite_right,
    tsum_eq_mass, mass_eq_one, dite_eq_ite, mul_ite, mul_zero, mul_one, ← mass_eq_one (f := f)]
    exact tsum_congr (fun _ => ite_eq_right_iff.mpr (fun h => h.symm))⟩

@[simp]
theorem bindOnMassSupport_apply :
    bindOnMassSupport f g b = ∑' a, f a * if h : f a = 0 then 0 else g a h b := rfl

@[simp]
theorem coe_bindOnMassSupport :
  (bindOnMassSupport f g : SPMF β) = SPMF.bindOnMassSupport f (fun a h => (g a h : SPMF β)) := rfl

@[simp]
theorem support_bindOnMassSupport :
    support (bindOnMassSupport f g) = ⋃ (a : α)
    (h : a ∈ support f), support (g a h) := by
  simp_rw [← SPMFClass.coe_support (bindOnMassSupport f g), coe_bindOnMassSupport,
  SPMF.support_bindOnMassSupport, SPMFClass.coe_support]

theorem mem_support_bindOnMassSupport_iff :
    b ∈ support (bindOnMassSupport f g) ↔
    ∃ (a : α) (h : a ∈ support f), b ∈ support (g a h) := by
    simp_rw [← SPMFClass.coe_support (bindOnMassSupport f g), coe_bindOnMassSupport,
    SPMF.mem_support_bindOnMassSupport_iff, SPMFClass.coe_support]

@[simp]
theorem bindOnMassSupport_eq_bind : (bindOnMassSupport f fun a _ => p a) = bind f p := by
  rw [← SPMFClass.coe_fn_coe, coe_bind, coe_bindOnMassSupport, SPMF.bindOnMassSupport_eq_bind]

theorem bindOnMassSupport_eq_zero_iff : bindOnMassSupport f g b = 0 ↔
    ∀ (a) (ha : f a ≠ 0), g a ha b = 0 := by
  simp_rw [← SPMFClass.coe_apply (bindOnMassSupport f g), coe_bindOnMassSupport,
  SPMF.bindOnMassSupport_eq_zero_iff, SPMFClass.coe_apply]

@[simp]
theorem pure_bindOnMassSupport :
    (pure a).bindOnMassSupport w = w a ((mem_support_pure_iff).mpr rfl) := by
  simp_rw [← SPMFClass.coe_fn_coe ((pure a).bindOnMassSupport w), coe_bindOnMassSupport, coe_pure,
  SPMF.pure_bindOnMassSupport]

theorem bindOnMassSupport_pure : (f.bindOnMassSupport fun a _ => pure a) = f := by
  simp_rw [← SPMFClass.coe_fn_coe _ f, coe_bindOnMassSupport, coe_pure, SPMF.bindOnMassSupport_pure]

@[simp]
theorem bindOnsupport_bindOnMassSupport {h : ∀ b ∈ support (bindOnMassSupport f g), PMF γ}:
    (f.bindOnMassSupport g).bindOnMassSupport h =
      f.bindOnMassSupport fun a ha =>
        (g a ha).bindOnMassSupport fun b hb =>
          h b ((mem_support_bindOnMassSupport_iff).mpr ⟨a, ha, hb⟩) := by
  simp_rw [← SPMFClass.coe_fn_coe ((f.bindOnMassSupport g).bindOnMassSupport h),
  coe_bindOnMassSupport, SPMF.bindOnsupport_bindOnMassSupport]

theorem bindOnMassSupport_comm {h : ∀ a ∈ support f, ∀ b ∈ support q, PMF γ} :
    (f.bindOnMassSupport fun a ha => q.bindOnMassSupport (h a ha)) =
      q.bindOnMassSupport fun b hb => f.bindOnMassSupport fun a ha => h a ha b hb := by
  simp_rw [← SPMFClass.coe_fn_coe ((f.bindOnMassSupport fun a ha => q.bindOnMassSupport (h a ha))),
  coe_bindOnMassSupport, SPMF.bindOnMassSupport_comm (f := (f : SPMF α))]

end BindOnMassSupport


end PMF

end MassFunction
