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

variable {M : Type u → Type*} [MFLike M]
{α β : Type u}

open Functor

noncomputable def inl [Pure M] [Bind M] (β) (μ : M α) : M (α ⊕ β) :=
  do let x ← μ; pure (Sum.inl x)

noncomputable def inr [Pure M] [Bind M] (α) (μ : M β) : M (α ⊕ β) :=
  do let y ← μ; pure (Sum.inr y)

noncomputable def summ_left [Pure M] [Bind M] [Zero (M α)] (μ : M (α ⊕ β)) : M α :=
  do let x ← μ; match x with | Sum.inl x => pure x | Sum.inr _ => 0

noncomputable def summ_lright [Pure M] [Bind M] [Zero (M β)] (μ : M (α ⊕ β)) : M β :=
  do let x ← μ; match x with | Sum.inl _ => 0 | Sum.inr x => pure x

variable [DiracPure M] [WeightedSumBind M] {μ : M (α × β)} {μ₁ : M α} {μ₂ : M β}
{a : α} {b : β} {t : α ⊕ β}

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

end Sum

section Prod

variable {M : Type u → Type*} [MFLike M] {α β : Type u}

noncomputable def prod [Pure M] [Bind M] (μ₁ : M α) (μ₂ : M β) : M (α × β) :=
  do let a ← μ₁ ; let b ← μ₂ ; return (a, b)

noncomputable def fst [Pure M] [Bind M] (μ : M (α × β)) : M α :=
  do let (a, _) ← μ ; return a

noncomputable def snd [Pure M] [Bind M] (μ : M (α × β)) : M β :=
  do let (_, b) ← μ ; return b

variable [DiracPure M] [WeightedSumBind M] {μ : M (α × β)} {μ₁ : M α} {μ₂ : M β}
{a : α} {b : β} {p : α × β}

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

theorem fst_prod_apply : fst (prod μ₁ μ₂) a = μ₁ a * mass μ₂ := by
  simp_rw [mass_eq_tsum_coeFn, fst_apply, prod_apply, ENNReal.tsum_mul_left]

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
theorem mass_prod : mass (prod μ₁ μ₂) = mass μ₁ * mass μ₂ := by
  simp_rw [mass_eq_tsum_coeFn, prod_apply', ENNReal.tsum_prod',
  ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]

@[simp]
theorem mass_fst : mass (fst μ) = mass μ := by
  simp_rw [mass_eq_tsum_coeFn, fst_apply, ENNReal.tsum_prod']

@[simp]
theorem mass_snd : mass (snd μ) = mass μ := by
  simp_rw [mass_eq_tsum_coeFn, snd_apply, ENNReal.tsum_prod', ENNReal.tsum_comm (α := α)]

@[simp]
theorem mass_prod_fst_snd : mass (prod (fst μ) (snd μ)) = mass μ * mass μ := by
  simp_rw [mass_prod, mass_fst, mass_snd]

theorem fst_mass_eq_snd_mass : mass (fst μ) = mass (snd μ) := by
  rw [mass_fst, mass_snd]

def couplings (μ₁ : M α) (μ₂ : M β) : Set (M (α × β)) := {μ | fst μ = μ₁ ∧ snd μ = μ₂}

end Prod

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

example : couple_flip_id ∈ couplings flip flip  := by
  rw [couplings]
  constructor <;>
  ext b <;> cases b <;>
  simp only [flip_apply, one_div, fst_apply, snd_apply, couple_flip_id_apply, tsum_bool,
    ↓reduceIte, zero_add, add_zero]

example : couple_flip_neg ∈ couplings flip flip  := by
  rw [couplings]
  constructor <;>
  ext b <;> cases b <;>
  simp only [flip_apply, one_div, fst_apply, snd_apply, couple_flip_neg_apply, tsum_bool,
    ↓reduceIte, zero_add, add_zero, Bool.not_false, Bool.not_true]

end Flip

end SPMF

end MassFunction
