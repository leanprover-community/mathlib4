import Mathlib.Probability.MassFunction.Constructions

open BigOperators ENNReal

universe u

theorem Prod.mk_injective {α β : Type*} [Nonempty β] :
    Function.Injective (α := α) (β := β → α × β) Prod.mk :=
  fun _ _ h' => Prod.mk.inj_right (Classical.arbitrary _) (congrFun h' _)

theorem Prod.mk_injective_of_nonempty {α β : Type*} (h : Nonempty β) :
    Function.Injective (α := α) (β := β → α × β) Prod.mk :=
  fun _ _ h' => Prod.mk.inj_right h.some (congrFun h' _)

theorem Prod.mk_injective_of_snd {α β : Type*} (b : β) :
    Function.Injective (α := α) (β := β → α × β) Prod.mk :=
  fun _ _ h' => Prod.mk.inj_right (by assumption) (congrFun h' _)

theorem Prod.swap_mk_injective {α β : Type*} [Nonempty α] :
    Function.Injective (α := β) (β := α → α × β) (Function.swap Prod.mk) :=
  fun _ _ h' => Prod.mk.inj_left (Classical.arbitrary _) (congrFun h' _)

theorem Prod.swap_mk_injective_of_nonempty {α β : Type*} (h : Nonempty α) :
    Function.Injective (α := β) (β := α → α × β) (Function.swap Prod.mk) :=
  fun _ _ h' => Prod.mk.inj_left h.some (congrFun h' _)

theorem Prod.swap_mk_injective_of_snd {α β : Type*} (a : α) :
    Function.Injective (α := β) (β := α → α × β) (Function.swap Prod.mk) :=
  fun _ _ h' => Prod.mk.inj_left (by assumption) (congrFun h' _)

namespace MassFunction

section Sum

variable {M : Type u → Type*} [∀ α, MFLike M α]
{α β : Type u}

open Functor

noncomputable abbrev inl [Pure M] [Bind M] (β) (μ₁ : M α) : M (α ⊕ β) := do
  let x ← μ₁
  return Sum.inl x

noncomputable abbrev inr [Pure M] [Bind M] (α) (μ₂ : M β) : M (α ⊕ β) := do
  let y ← μ₂
  pure (Sum.inr y)


variable [DiracPure M] [WeightedSumBind M] {μ : M (α × β)} {μ₁ : M α} {μ₂ : M β}
{a : α} {b : β} {t : α ⊕ β} {μ : M (α ⊕ β)}

@[simp]
theorem inl_apply_inl : inl β μ₁ (Sum.inl a) = μ₁ a := by
  simp_rw [inl, bind_apply, pure_apply]
  classical simp only [Set.indicator_singleton_apply, Sum.inl.injEq,
    Pi.one_apply, mul_ite, mul_one, mul_zero, tsum_ite_eq_dep']

@[simp]
theorem inl_apply_inr : inl β μ₁ (Sum.inr b) = 0 := by
  simp_rw [inl, bind_apply, pure_apply]
  classical simp only [Set.mem_singleton_iff, not_false_eq_true,
    Set.indicator_of_not_mem, mul_zero, tsum_zero]

theorem inl_apply : inl β μ₁ t = if h : Sum.isLeft t then μ₁ (Sum.getLeft t h) else 0 := by
  cases t
  · simp_rw [inl_apply_inl, Sum.isLeft_inl, Sum.getLeft_inl, dite_true]
  · simp_rw [inl_apply_inr, Sum.isLeft_inr, dite_false]

@[simp]
theorem inr_apply_inr : inr α μ₂ (Sum.inr b) = μ₂ b := by
  simp_rw [inr, bind_apply, pure_apply]
  classical simp only [Set.indicator_singleton_apply, Sum.inr.injEq,
    Pi.one_apply, mul_ite, mul_one, mul_zero, tsum_ite_eq_dep']

@[simp]
theorem inr_apply_inl : inr α μ₂ (Sum.inl a) = 0 := by
  simp_rw [inr, bind_apply, pure_apply]
  classical simp only [Set.mem_singleton_iff, not_false_eq_true,
    Set.indicator_of_not_mem, mul_zero, tsum_zero]

theorem inr_apply : inr α μ₂ t = if h : Sum.isRight t then μ₂ (Sum.getRight t h) else 0 := by
  cases t
  · simp_rw [inr_apply_inl, Sum.isRight_inl, dite_false]
  · simp_rw [inr_apply_inr, Sum.isRight_inr, dite_true, Sum.getRight_inr]

theorem mass_inl : mass (inl β μ₁) = mass μ₁ := by
  simp_rw [mass_eq_tsum_coeFn, ENNReal.tsum_sum_type,
  inl_apply_inl, inl_apply_inr, tsum_zero, add_zero]

theorem mass_inr : mass (inr α μ₂) = mass μ₂ := by
  simp_rw [mass_eq_tsum_coeFn, ENNReal.tsum_sum_type,
  inr_apply_inl, inr_apply_inr, tsum_zero, zero_add]

theorem support_inl : support (inl β μ₁) = Sum.inl '' support μ₁ := by
  ext (x | x)
  · simp_rw [Set.mem_image, mem_support_iff, inl_apply_inl, Sum.inl.injEq,
    exists_eq_right]
  · simp_rw [Set.mem_image, mem_support_iff, inl_apply_inr, and_false,
    exists_false, ne_eq, not_true_eq_false]

theorem support_inr : support (inr α μ₂) = Sum.inr '' support μ₂ := by
  ext (x | x)
  · simp_rw [Set.mem_image, mem_support_iff, inr_apply_inl, and_false,
    exists_false, ne_eq, not_true_eq_false]
  · simp_rw [Set.mem_image, mem_support_iff, inr_apply_inr, Sum.inr.injEq,
    exists_eq_right]

section

@[simp]
theorem inl_zero_apply [ZeroNull M α] : inl β (0 : M α) t = 0 := by
  cases t
  · rw [inl_apply_inl, ZeroNull.zero_apply]
  · rw [inl_apply_inr]

@[simp]
theorem coe_inl_zero [ZeroNull M α] : ⇑(inl β (0 : M α)) = 0 := by
  ext
  rw [inl_zero_apply, Pi.zero_apply]

@[simp]
theorem inr_zero_apply [ZeroNull M β] : inr α (0 : M β) t = 0 := by
  cases t
  · rw [inr_apply_inl]
  · rw [inr_apply_inr, ZeroNull.zero_apply]

@[simp]
theorem coe_inr_zero [ZeroNull M β] : ⇑(inr α (0 : M β)) = 0 := by
  ext
  rw [inr_zero_apply, Pi.zero_apply]

theorem inl_zero_eq_inr_zero [ZeroNull M α] [ZeroNull M β] : inl β 0 = inr α (0 : M β) := by
  ext
  rw [inl_zero_apply, inr_zero_apply]

noncomputable abbrev elim_left [Pure M] [Bind M] [Zero (M α)] (μ : M (α ⊕ β)) :
    M α ⊕ M β := Sum.inl <| do
  let x ← μ
  match x with
  | Sum.inl x => pure x
  | Sum.inr _ => 0

noncomputable abbrev elim_right [Pure M] [Bind M] [Zero (M β)] (μ : M (α ⊕ β)) :
    M α ⊕ M β := Sum.inr <| do
  let x ← μ
  match x with
  | Sum.inl _ => 0
  | Sum.inr x => pure x

@[simp]
theorem elim_left_isLeft [Zero (M α)] : Sum.isLeft (elim_left μ) := rfl

@[simp]
theorem elim_left_eq [Zero (M α)] :
    elim_left μ = Sum.inl (bind μ (Sum.elim pure 0)) := by
  rw [elim_left, Sum.inl.injEq]
  congr
  ext (a | b)
  · rw [Sum.elim_inl]
  · simp_rw [Sum.elim_inr, Pi.zero_apply]

@[simp]
theorem bind_elim_pure_zero [ZeroNull M α] : (bind μ (Sum.elim pure 0)) a = μ (Sum.inl a) := by
  rw [bind_apply, tsum_eq_single (Sum.inl a)]
  · rw [Sum.elim_inl, pure_apply_self, mul_one]
  · simp_rw [Sum.forall, Sum.inl.inj_iff.not, ne_eq, mul_eq_zero]
    refine' ⟨fun a ha => Or.inr (pure_apply_of_ne fun h => ha h.symm),
    fun b _ => Or.inr ZeroNull.zero_apply⟩

@[simp]
theorem bind_elim_zero_pure [ZeroNull M β] : (bind μ (Sum.elim 0 pure)) b = μ (Sum.inr b) := by
  rw [bind_apply, tsum_eq_single (Sum.inr b), Sum.elim_inr]
  · rw [pure_apply_self, mul_one]
  · simp_rw [Sum.forall, Sum.inr.inj_iff.not, ne_eq, mul_eq_zero]
    refine' ⟨fun a _ => Or.inr ZeroNull.zero_apply,
    fun b hb => Or.inr (pure_apply_of_ne fun h => hb h.symm)⟩

@[simp]
theorem elim_left_getLeft [ZeroNull M α] (h := elim_left_isLeft (μ := μ)) :
    ((elim_left μ).getLeft h) a = μ (Sum.inl a) := by
  simp_rw [elim_left_eq , Sum.getLeft_inl, bind_elim_pure_zero]

@[simp]
theorem elim_right_isRight [Zero (M β)] : Sum.isRight (elim_right μ) := rfl

@[simp]
theorem elim_right_eq [Zero (M β)] :
    elim_right μ = Sum.inr (bind μ (Sum.elim 0 pure)):= by
  rw [elim_right, Sum.inr.injEq]
  congr
  ext (a | b)
  · simp_rw [Sum.elim_inl, Pi.zero_apply]
  · rw [Sum.elim_inr]

@[simp]
theorem elim_right_getRight [ZeroNull M β] (h := elim_right_isRight (μ := μ)) :
    ((elim_right μ).getRight h) b = μ (Sum.inr b) := by
  simp_rw [elim_right_eq , Sum.getRight_inr, bind_elim_zero_pure]

end

@[simp]
theorem elim_inl_inr_inl [∀ α, ZeroNull M α] :
    Sum.elim (inl β) (inr α) (Sum.inl μ₁) = inl β μ₁ := by
  ext (a | b)
  · rw [Sum.elim_inl, inl_apply_inl]
  · rw [Sum.elim_inl, inl_apply_inr]

@[simp]
theorem elim_inl_inr_inr [∀ α, ZeroNull M α] :
    Sum.elim (inl β) (inr α) (Sum.inr μ₂) = inr α μ₂ := by
  ext (a | b)
  · rw [Sum.elim_inr, inr_apply_inl]
  · rw [Sum.elim_inr, inr_apply_inr]

theorem elim_elim_left [∀ α, ZeroNull M α] :
    Sum.elim (inl β) (inr α) (elim_left μ) = filter μ (Set.range Sum.inl) := by
  rw [elim_left_eq, elim_inl_inr_inl]
  ext (a | b)
  · simp_rw [filter_apply, inl_apply_inl,
    Set.indicator_of_mem (Set.mem_range.mpr ⟨a, rfl⟩), bind_elim_pure_zero]
  · simp_rw [filter_apply, inl_apply_inr]
    rw [Set.indicator_of_not_mem (Set.mem_range.not.mpr
      (not_exists.mpr (fun _ => Sum.inl_ne_inr)))]

theorem elim_elim_right [∀ α, ZeroNull M α] :
    Sum.elim (inl β) (inr α) (elim_right μ) = filter μ (Set.range Sum.inr) := by
  rw [elim_right_eq, elim_inl_inr_inr]
  ext (a | b)
  · simp_rw [filter_apply, inr_apply_inl]
    rw [Set.indicator_of_not_mem (Set.mem_range.not.mpr
      (not_exists.mpr (fun _ => Sum.inr_ne_inl)))]
  · simp_rw [filter_apply, inr_apply_inr,
    Set.indicator_of_mem (Set.mem_range.mpr ⟨b, rfl⟩), bind_elim_zero_pure]

def IsUplingOf (μ : M (α ⊕ β)) (μ₁₂ : M α ⊕ M β) : Prop := μ = Sum.elim (inl β) (inr α) μ₁₂

example [∀ α, ZeroNull M α] : IsUplingOf (filter μ (Set.range Sum.inl)) (elim_left μ) :=
  elim_elim_left.symm

example [∀ α, ZeroNull M α] : IsUplingOf (filter μ (Set.range Sum.inr)) (elim_right μ) :=
  elim_elim_right.symm

example [∀ α, ZeroNull M α] : IsUplingOf (inr α μ₂) (Sum.inr μ₂) := elim_inl_inr_inr

example [∀ α, ZeroNull M α] : IsUplingOf (inl β μ₁) (Sum.inl μ₁) := elim_inl_inr_inl

end Sum

section Prod

variable {M : Type u → Type*} [∀ α, MFLike M α] {α β γ δ : Type u}

noncomputable abbrev fst [Pure M] [Bind M] (μ : M (α × β)) : M α :=
  do let (a, _) ← μ ; return a

noncomputable abbrev snd [Pure M] [Bind M] (μ : M (α × β)) : M β :=
  do let (_, b) ← μ ; return b

noncomputable abbrev prod [Pure M] [Bind M] (μ₁ : M α) (μ₂ : M β) : M (α × β) :=
  do let a ← μ₁ ; let b ← μ₂ ; return (a, b)

variable [DiracPure M] [WeightedSumBind M] {μ : M (α × β)} {μ₁ : M α} {μ₂ : M β}
{a : α} {b : β} {p : α × β} {ρ : α × β → M (γ × δ)} {ν : α → M γ} {ξ : β → M δ}

theorem fst_eq [Pure M] [Bind M] : fst μ = bind μ (fun (a, _) => pure a) := rfl
theorem snd_eq [Pure M] [Bind M] : snd μ = bind μ (fun (_, b) => pure b) := rfl
theorem prod_eq [Pure M] [Bind M] :
  prod μ₁ μ₂ = bind μ₁ (fun a => bind μ₂ fun b => pure (a, b)) := rfl

theorem prod_comm [Pure M] [WeightedSumBind M] :
    prod μ₁ μ₂ = bind μ₂ (fun b => bind μ₁ fun a => pure (a, b)) := bind_comm

theorem prod_apply : prod μ₁ μ₂ (a, b) = μ₁ a * μ₂ b := by
  simp_rw [prod, bind_apply, pure_apply]
  refine' (tsum_eq_single a (fun a' ha => _)).trans _
  · refine' mul_eq_zero_of_right _ (ENNReal.tsum_eq_zero.mpr (fun b' =>
      mul_eq_zero_of_right _ (Set.indicator_singleton_apply_of_ne (by
      simp_rw [ne_eq, Prod.mk.inj_iff, not_and, ha.symm, false_implies]))))
  · refine' congrArg (μ₁ a  * ·) ((tsum_eq_single b (fun b' hb => _)).trans
      (by rw [Set.indicator_singleton_apply_self, Pi.one_apply, mul_one]))
    · rw [Set.indicator_singleton_apply_of_ne (ne_eq _ _ ▸ ((Prod.mk.inj_left a).mt hb.symm)),
      mul_zero]

theorem prod_apply' : prod μ₁ μ₂ p = μ₁ p.1 * μ₂ p.2 := by
  rcases p with ⟨_, _⟩
  exact prod_apply

theorem fst_apply : fst μ a = ∑' b, μ (a, b) := by
  classical
  refine' map_apply'.trans _
  simp_rw [ENNReal.tsum_prod', ENNReal.tsum_comm (α := α),
  fun b' a' => ite_eq_comm a a' (μ (a', b')),
  fun b' a' => ite_eq_apply_subst (fun a' => μ (a', b')) a', tsum_ite_eq]

theorem snd_apply : snd μ b = ∑' a, μ (a, b) := by
  classical
  refine' map_apply'.trans _
  simp_rw [ENNReal.tsum_prod',
  fun a' b' => ite_eq_comm b b' (μ (a', b')),
  fun a' b' => ite_eq_apply_subst (fun b' => μ (a', b')) b', tsum_ite_eq]

@[simp]
theorem fst_prod_apply : fst (prod μ₁ μ₂) a = μ₁ a * mass μ₂ := by
  simp_rw [mass_eq_tsum_coeFn, fst_apply, prod_apply, ENNReal.tsum_mul_left]

@[simp]
theorem snd_prod_apply : snd (prod μ₁ μ₂) b = mass μ₁ * μ₂ b := by
  simp_rw [mass_eq_tsum_coeFn, snd_apply, prod_apply, ENNReal.tsum_mul_right]

theorem prod_fst_snd_apply : prod (fst μ) (snd μ) (a, b) =
    ∑' (a' : α) (b' : β), μ (a, b') * μ (a', b) := by
  simp_rw [prod_apply, fst_apply, snd_apply]
  simp_rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]

theorem prod_fst_snd_apply' : prod (fst μ) (snd μ) p =
    ∑' (q : α × β), μ (p.1, q.2) * μ (q.1, p.2) := by
  rcases p with ⟨_, _⟩
  simp_rw [prod_fst_snd_apply, ENNReal.tsum_prod']

@[simp]
theorem mass_fst : mass (fst μ) = mass μ := by
  simp_rw [mass_eq_tsum_coeFn, fst_apply, ENNReal.tsum_prod']

@[simp]
theorem mass_snd : mass (snd μ) = mass μ := by
  simp_rw [mass_eq_tsum_coeFn, snd_apply, ENNReal.tsum_prod', ENNReal.tsum_comm (α := α)]

@[simp]
theorem mass_prod : mass (prod μ₁ μ₂) = mass μ₁ * mass μ₂ := by
  simp_rw [mass_eq_tsum_coeFn, prod_apply', ENNReal.tsum_prod',
  ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]

theorem fst_mass_eq_snd_mass : mass (fst μ) = mass (snd μ) := by
  rw [mass_fst, mass_snd]

@[simp]
theorem mass_prod_fst_snd : mass (prod (fst μ) (snd μ)) = mass μ * mass μ := by
  simp_rw [mass_prod, mass_fst, mass_snd]

theorem prod_eq_prod (hμ₁ : mass μ₁ = 1) (hμ₂ : mass μ₂ = 1) :
    (μ₁, μ₂) = (fst (prod μ₁ μ₂), snd (prod μ₁ μ₂)) := by
  simp_rw [Prod.ext_iff, DFunLike.ext_iff, fst_prod_apply, snd_prod_apply,
  hμ₁, hμ₂, mul_one, one_mul, implies_true, and_self]

theorem prod_eq_prod' (μ : M α × M β) (hμ₁ : mass μ.fst = 1) (hμ₂ : mass μ.snd = 1) :
    μ = (fst (prod μ.fst μ.snd), snd (prod μ.fst μ.snd)) := by
  rcases μ with ⟨μ₁, μ₂⟩
  exact prod_eq_prod hμ₁ hμ₂

theorem fst_pure : fst (pure (f := M) (a, b)) = pure a := pure_bind _ _

theorem snd_pure : snd (pure (f := M) (a, b)) = pure b := pure_bind _ _

theorem fst_bind (h : ∀ a b, (a, b) ∈ support μ → ν a = fst (ρ (a, b))) :
  fst (bind μ ρ) = bind (fst μ) ν := by
  simp_rw [fst_eq] at h ⊢
  simp_rw [bind_assoc, pure_bind]
  ext c : 1
  simp_rw [bind_apply, pure_apply, ]
  refine' tsum_congr (fun ⟨a, b⟩ => _)
  by_cases hsupp : (a, b) ∈ support μ
  · simp_rw [(h a b hsupp), bind_apply, pure_apply]
  · rw [nmem_support_iff] at hsupp
    simp_rw [hsupp, zero_mul]

theorem snd_bind (h : ∀ a b, (a, b) ∈ support μ → ξ b = snd (ρ (a, b))) :
  snd (bind μ ρ) = bind (snd μ) ξ := by
  simp_rw [snd_eq] at h ⊢
  simp_rw [bind_assoc, pure_bind]
  ext c : 1
  simp_rw [bind_apply, pure_apply, ]
  refine' tsum_congr (fun ⟨a, b⟩ => _)
  by_cases hsupp : (a, b) ∈ support μ
  · simp_rw [(h a b hsupp), bind_apply, pure_apply]
  · rw [nmem_support_iff] at hsupp
    simp_rw [hsupp, zero_mul]


end Prod

section Coupling

variable {M : Type u → Type*} [∀ α, MFLike M α] {α β γ δ : Type u}

structure Coupling {α β} [Pure M] [Bind M] (μ₁ : M α) (μ₂ : M β) where
  massFunction : M (α × β)
  fst_eq : μ₁ = fst massFunction
  snd_eq : μ₂ = snd massFunction

variable [DiracPure M] [WeightedSumBind M] {μ : M (α × β)} {μ₁ : M α} {μ₂ : M β}
{a : α} {b : β} {p : α × β} {ρ : α × β → M (γ × δ)} {ν : α → M γ} {ξ : β → M δ}

theorem mass_eq_of_coupling (μ : Coupling μ₁ μ₂) : mass μ₁ = mass μ₂ := by
  rcases μ with ⟨μ, rfl, rfl⟩
  exact fst_mass_eq_snd_mass

noncomputable example (hμ₁ : mass μ₁ = 1) (hμ₂ : mass μ₂ = 1) : Coupling μ₁ μ₂ where
    massFunction := prod μ₁ μ₂
    fst_eq := by ext ; rw [fst_prod_apply, hμ₂, mul_one]
    snd_eq := by ext ; rw [snd_prod_apply, hμ₁, one_mul]

example : Coupling μ₁ μ₁ where
  massFunction := do let a ← μ₁; return (a, a)
  fst_eq := by simp only [bind_assoc, pure_bind, bind_pure]
  snd_eq := by simp only [bind_assoc, pure_bind, bind_pure]

noncomputable example [Fintype α] [DecidableEq α] [Nonempty α] (e : α ≃ α) :
    Coupling (PMF.uniform α) (PMF.uniform α) where
  massFunction := do let a ← PMF.uniform α; return (a, e a)
  fst_eq := by simp only [bind_assoc, pure_bind, bind_pure]
  snd_eq := by simp only [bind_assoc, pure_bind, DFunLike.ext_iff, PMF.uniform_apply, bind_apply,
    pure_apply, Set.indicator_singleton_apply, e.symm_apply_eq.symm, Pi.one_apply, mul_ite, mul_one,
    mul_zero, tsum_fintype, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, implies_true]

structure Lifting (r : α → β → Prop) (μ₁ : M α) (μ₂ : M β) where
  witness : Coupling μ₁ μ₂
  witnessRelation : ∀ a b, (a, b) ∈ support witness.massFunction → r a b

variable {r : α → β → Prop} {s : γ → δ → Prop}

def Lifting.massFunction (l : Lifting r μ₁ μ₂) := l.witness.massFunction

noncomputable abbrev lift_pure (h : r a b) : Lifting r (pure a : M α) (pure b : M β) where
  witness := {
    massFunction := pure (a, b)
    fst_eq := by simp_rw [pure_bind]
    snd_eq := by simp_rw [pure_bind]}
  witnessRelation := by simp only [support_pure, Set.mem_singleton_iff,
    Prod.mk.injEq, and_imp, forall_eq_apply_imp_iff, forall_eq, h]

 -- {ρ : α × β → M (γ × δ)} {ν : α → M γ} {ξ : β → M δ}
noncomputable abbrev lift_bind (l : Lifting r μ₁ μ₂)
    (rtos : (a : α) → (b : β) → r a b → Lifting s (ν a) (ξ b))
    (hrtos : ∀ a b h, ρ (a, b) = (rtos a b h).massFunction) :
    Lifting s (bind μ₁ ν) (bind μ₂ ξ) where
  witness := _
  witnessRelation := _


end Coupling

namespace SPMF

section Flip

noncomputable def flip := bernoulli (1/2) (by norm_num)

theorem support_flip : support flip = {false, true} := by
  refine' (support_bernoulli _).trans _
  norm_num

@[simp]
theorem flip_apply (a : Bool) : flip a = 1/2 := (bernoulli_apply _ _).trans (by norm_num)

noncomputable def couple_flip_id : SPMF (Bool × Bool) :=
    ofFintype (fun (a, b) => if a = b then 1/2 else 0)
  (by norm_num [(ENNReal.mul_inv_cancel two_ne_zero two_ne_top).le])

@[simp]
theorem couple_flip_id_apply (ab : (Bool × Bool)) :
  couple_flip_id ab = if ab.fst = ab.snd then 1/2 else 0 := rfl

@[simp]
theorem couple_flip_id_apply' (a : Bool) (b : Bool) :
  couple_flip_id (a, b) = if a = b then 1/2 else 0 := rfl

noncomputable def couple_flip_neg : SPMF (Bool × Bool) :=
    ofFintype (fun (a, b) => if a = !b then 1/2 else 0)
  (by norm_num [(ENNReal.inv_two_add_inv_two).le])

@[simp]
theorem couple_flip_neg_apply (ab : (Bool × Bool)) :
  couple_flip_neg ab = if ab.fst = !ab.snd then 1/2 else 0 := rfl

@[simp]
theorem couple_flip_neg_apply' (a : Bool) (b : Bool) :
  couple_flip_neg (a, b) = if a = !b then 1/2 else 0 := rfl

/-
example : IsCouplingOf flip flip couple_flip_id := by
  rw [IsCouplingOf]
  constructor <;>
  ext b <;> cases b <;>
  simp only [flip_apply, one_div, fst_apply, snd_apply, couple_flip_id_apply, tsum_bool,
    ↓reduceIte, zero_add, add_zero]

example : IsCouplingOf flip flip couple_flip_neg := by
  rw [IsCouplingOf]
  constructor <;>
  ext b <;> cases b <;>
  simp only [flip_apply, one_div, fst_apply, snd_apply, couple_flip_neg_apply, tsum_bool,
    ↓reduceIte, zero_add, add_zero, Bool.not_false, Bool.not_true]
-/

end Flip

end SPMF

end MassFunction
