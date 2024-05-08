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

variable {M : Type u → Type*} [MFLike M] [DiracPure M] [WeightedSumBind M]
{α β : Type u}

noncomputable def inl : M α → M (α ⊕ β) := map Sum.inl

noncomputable def inr : M β → M (α ⊕ β) := map Sum.inr

end Sum

section Prod

variable {M : Type u → Type*} [MFLike M] {α β : Type u}

noncomputable def prod [Pure M] [Bind M] (μ₁ : M α) (μ₂ : M β) : M (α × β) := do
  let a ← μ₁
  let b ← μ₂
  return (a, b)

noncomputable def fst [Pure M] [Bind M] (μ : M (α × β)) : M α := do
  let (a, _) ← μ
  return a

noncomputable def snd [Pure M] [Bind M] (μ : M (α × β)) : M β := do
  let (_, b) ← μ
  return b

variable [DiracPure M] [WeightedSumBind M] {μ : M (α × β)} {μ₁ : M α} {μ₂ : M β} {a : α} {b : β}
{p : α × β}

open DiracPure WeightedSumBind

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
  fun b => ite_eq_apply_right (fun a => μ (a, b)) a,
  fun b => ite_eq_comm_apply_left (fun a => μ (a, b)) a, tsum_ite_eq]

theorem snd_apply : snd μ b = ∑' a, μ (a, b) := by
  classical
  refine' map_apply'.trans _
  simp_rw [ENNReal.tsum_prod',
  fun a => ite_eq_apply_right (fun b => μ (a, b)) b,
  fun a => ite_eq_comm_apply_left (fun b => μ (a, b)) b, tsum_ite_eq]

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


end MassFunction

namespace SPMF

variable {α β : Type*}

section Coupling

noncomputable def fst (μ : SPMF (α × β)) : SPMF α :=
  ⟨λ a => ∑' b, μ (a, b), by rw [←ENNReal.tsum_prod'] ; exact mass_le_one⟩

noncomputable def snd (μ : SPMF (α × β)) : SPMF β :=
  ⟨λ b => ∑' a, μ (a, b), by rw [ENNReal.tsum_comm, ←ENNReal.tsum_prod'] ; exact mass_le_one⟩

theorem fst_def (μ : SPMF (α × β)) (a : α) : μ.fst a = ∑' b, μ (a, b) := rfl

theorem snd_def (μ : SPMF (α × β)) (b : β) : μ.snd b = ∑' a, μ (a, b) := rfl

theorem mass_eq_fst_mass (μ : SPMF (α × β)) : mass μ = mass μ.fst := ENNReal.tsum_prod'

theorem mass_eq_snd_mass (μ : SPMF (α × β)) : mass μ = mass μ.snd :=
  ENNReal.tsum_prod'.trans (ENNReal.tsum_comm (α := α))

theorem fst_mass_eq_snd_mass (μ : SPMF (α × β)) : mass μ.fst = mass μ.snd := by
  rw [← mass_eq_fst_mass, ← mass_eq_snd_mass]

def coupling (μ₁ : SPMF α) (μ₂ : SPMF β) (μ : SPMF (α × β)) := μ₁ = μ.fst ∧ μ₂ = μ.snd

theorem coupling_def {μ₁ : SPMF α} {μ₂ : SPMF β} {μ : SPMF (α × β)} :
  coupling μ₁ μ₂ μ ↔ μ₁ = μ.fst ∧ μ₂ = μ.snd := Iff.rfl

theorem mass_eq_of_coupling_exists (μ₁ : SPMF α) (μ₂ : SPMF β) :
    (∃ μ : SPMF (α × β), coupling μ₁ μ₂ μ) → mass μ₁ = mass μ₂ := by
  rintro ⟨μ, rfl, rfl⟩
  exact μ.fst_mass_eq_snd_mass

section Flip

noncomputable def flip := bernoulli (1/2) (by norm_num)

theorem support_flip : massSupport flip = {false, true} := by
  refine' (massSupport_bernoulli _).trans _
  norm_num

@[simp]
theorem flip_apply (a : Bool) : flip a = 1/2 := (bernoulli_apply _ _).trans (by norm_num)

noncomputable def couple_flip_id : SPMF (Bool × Bool) :=
    ofFintype (fun (a, b) => if a = b then 1/2 else 0)
  (by norm_num [(ENNReal.inv_two_add_inv_two).le])

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

example : coupling flip flip couple_flip_id := by
  rw [coupling_def]
  constructor <;>
  ext b <;> cases b <;>
  simp only [flip_apply, one_div, fst_def, snd_def, couple_flip_id_apply, tsum_bool,
    ↓reduceIte, zero_add, add_zero]

example : coupling flip flip couple_flip_neg := by
  rw [coupling_def]
  constructor <;>
  ext b <;> cases b <;>
  simp only [flip_apply, one_div, fst_def, snd_def, couple_flip_neg_apply, tsum_bool,
    ↓reduceIte, zero_add, add_zero, Bool.not_false, Bool.not_true]

end Flip

end Coupling

/-

def lifting (R : Set (α × β)) (μ₁ : SPMF α) (μ₂ : SPMF β) (μ : SPMF (α × β)) : Prop :=
  coupling μ μ₁ μ₂ ∧ support μ ⊆ R

-/
end SPMF
