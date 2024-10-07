import Mathlib.Tactic.Tendsto.Multiseries.Basic
import Mathlib.Tactic.Tendsto.Multiseries.Basis

set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace TendstoTactic

namespace PreMS

def mulConst {basis : Basis} (ms : PreMS basis) (c : ℝ) : PreMS basis :=
  match basis with
  | [] => ms * c
  | _ :: _ =>
    CoList.map (fun (deg, coef) => (deg, mulConst coef c)) ms

def neg {basis : Basis} (ms : PreMS basis) : PreMS basis :=
  ms.mulConst (-1)

-------------------- theorems

open Filter Asymptotics

theorem const_isApproximation_const {c : ℝ} {basis : Basis} (h_wo : MS.wellOrderedBasis basis) :
    (const c basis).isApproximation (fun _ ↦ c) basis := by
  cases basis with
  | nil => simp [isApproximation, const]
  | cons basis_hd basis_tl =>
    simp [const]
    have ih : (const c basis_tl).isApproximation (fun _ ↦ c) basis_tl := by
      simp [MS.wellOrderedBasis] at h_wo
      apply const_isApproximation_const h_wo.right.left
    apply isApproximation.cons _ ih
    · intro deg h_deg
      apply Asymptotics.isLittleO_const_left.mpr
      right
      apply Tendsto.comp tendsto_norm_atTop_atTop
      apply Tendsto.comp (tendsto_rpow_atTop h_deg)
      apply MS.basis_tendsto_top h_wo
      simp
    · apply isApproximation.nil
      simp
      rfl

theorem const_wellOrdered {c : ℝ} {basis : Basis} :
    (const c basis).wellOrdered := by
  cases basis with
  | nil => constructor
  | cons basis_hd basis_tl =>
    simp [const]
    apply wellOrdered.cons
    · exact const_wellOrdered
    · simp [leadingExp, Ne.bot_lt] -- may be `Ne.bot_lt` should be simp lemma?
    · apply wellOrdered.nil


theorem zero_isApproximation_zero {basis : Basis} :
    (zero basis).isApproximation (fun _ ↦ 0) basis := by
  cases basis with
  | nil => simp [isApproximation, zero]
  | cons =>
    simp [zero]
    exact isApproximation.nil (by rfl)

theorem one_isApproximation_one {basis : Basis} (h_wo : MS.wellOrderedBasis basis) :
    (one basis).isApproximation (fun _ ↦ 1) basis :=
  const_isApproximation_const h_wo

@[simp]
theorem mulConst_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {c : ℝ} :
    mulConst (basis := basis_hd :: basis_tl) CoList.nil c = CoList.nil := by
  simp [mulConst]

@[simp]
theorem mulConst_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {c deg : ℝ}
    {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)} :
    mulConst (basis := basis_hd :: basis_tl) (CoList.cons (deg, coef) tl) c =
    CoList.cons (deg, coef.mulConst c) (tl.mulConst c) := by
  simp [mulConst]

@[simp]
theorem mulConst_leadingExp {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X : PreMS (basis_hd :: basis_tl)}
    {c : ℝ} :
    (mulConst X c).leadingExp = X.leadingExp := by
  apply X.casesOn
  · simp [mulConst]
  · intro (deg, coef) tl
    simp [mulConst, leadingExp]

@[simp]
theorem const_mulConst {basis : Basis} {x y : ℝ}: (const x basis).mulConst y = const (x * y) basis := by
  cases basis with
  | nil => simp [mulConst, const]
  | cons =>
    simp [mulConst, const]
    apply const_mulConst

theorem mulConst_wellOrdered {basis : Basis} {ms : PreMS basis} {c : ℝ}
    (h_wo : ms.wellOrdered) : (ms.mulConst c).wellOrdered := by
  cases basis with
  | nil => constructor
  | cons basis_hd basis_tl =>
    let motive : (PreMS (basis_hd :: basis_tl)) → Prop := fun ms' =>
      ∃ (X : PreMS (basis_hd :: basis_tl)), ms' = X.mulConst c ∧ X.wellOrdered
    apply wellOrdered.coind motive
    · intro ms ih
      simp [motive] at ih
      obtain ⟨X, h_ms_eq, hX_wo⟩ := ih
      subst h_ms_eq
      revert hX_wo
      apply X.casesOn
      · intro
        left
        simp [mulConst]
      · intro (deg, coef) tl hX_wo
        replace hX_wo := wellOrdered_cons hX_wo
        obtain ⟨hX_coef_wo, hX_tl_wo, hX_comp⟩ := hX_wo
        right
        use deg
        use coef.mulConst c
        use mulConst (basis := basis_hd :: basis_tl) tl c
        constructor
        · simp [mulConst]
        constructor
        · exact mulConst_wellOrdered hX_coef_wo
        constructor
        · simpa
        simp [motive]
        use tl
    · simp [motive]
      use ms

theorem mulConst_isApproximation {basis : Basis} {ms : PreMS basis} {c : ℝ} {F : ℝ → ℝ}
    (h_approx : ms.isApproximation F basis) :
    (ms.mulConst c).isApproximation (fun x ↦ F x * c) basis := by
  cases basis with
  | nil =>
    simp [isApproximation, mulConst] at *
    apply EventuallyEq.mul h_approx
    rfl
  | cons basis_hd basis_tl =>
    let motive : (ℝ → ℝ) → (PreMS (basis_hd :: basis_tl)) → Prop := fun f ms' =>
      ∃ (X : PreMS (basis_hd :: basis_tl)) (fX : ℝ → ℝ),
        ms' = X.mulConst c ∧ f =ᶠ[atTop] (fun x ↦ fX x * c) ∧
        X.isApproximation fX (basis_hd :: basis_tl)
    apply isApproximation.coind motive
    · intro f ms ih
      simp only [motive] at ih
      obtain ⟨X, fX, h_ms_eq, hf_eq, hX_approx⟩ := ih
      revert h_ms_eq hX_approx
      apply X.casesOn
      · intro h_ms_eq hX_approx
        left
        replace hX_approx := isApproximation_nil hX_approx
        simp [mulConst] at h_ms_eq
        constructor
        · exact h_ms_eq
        trans
        · exact hf_eq
        conv =>
          rhs
          ext x
          simp
          rw [← zero_mul c]
        apply EventuallyEq.mul hX_approx
        rfl
      · intro (X_deg, X_coef) X_tl h_ms_eq hX_approx
        replace hX_approx := isApproximation_cons hX_approx
        obtain ⟨XC, hX_coef, hX_comp, hX_tl⟩ := hX_approx
        right
        simp [mulConst] at h_ms_eq
        use ?_
        use ?_
        use ?_
        use fun x ↦ XC x * c
        constructor
        · exact h_ms_eq
        constructor
        · exact mulConst_isApproximation hX_coef
        constructor
        · intro deg h_deg
          apply Filter.EventuallyEq.trans_isLittleO hf_eq
          simp_rw [mul_comm]
          apply IsLittleO.const_mul_left (hX_comp deg h_deg)
        simp only [motive]
        use X_tl
        use fun x ↦ fX x - basis_hd x ^ X_deg * XC x
        constructor
        · rfl
        constructor
        · apply eventuallyEq_iff_sub.mpr
          eta_expand
          simp
          ring_nf!
          apply eventuallyEq_iff_sub.mp
          conv => rhs; ext; rw [mul_comm]
          exact hf_eq
        · exact hX_tl
    · simp only [motive]
      use ms
      use F


@[simp]
theorem neg_leadingExp {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X : PreMS (basis_hd :: basis_tl)} :
    X.neg.leadingExp = X.leadingExp := by
  simp [neg]

theorem neg_wellOrdered {basis : Basis} {ms : PreMS basis}
    (h_wo : ms.wellOrdered) : ms.neg.wellOrdered :=
  mulConst_wellOrdered h_wo

theorem neg_isApproximation {basis : Basis} {ms : PreMS basis} {F : ℝ → ℝ}
    (h_approx : ms.isApproximation F basis) : ms.neg.isApproximation (-F) basis := by
  rw [← mul_neg_one]
  eta_expand
  simp only [Pi.one_apply, Pi.neg_apply, Pi.mul_apply]
  apply mulConst_isApproximation h_approx

@[simp]
theorem neg_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    neg (basis := basis_hd :: basis_tl) CoList.nil = CoList.nil := by
  simp [neg]

@[simp]
theorem neg_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {deg : ℝ}
    {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)} :
    neg (basis := basis_hd :: basis_tl) (CoList.cons (deg, coef) tl) =
    CoList.cons (deg, coef.neg) tl.neg := by
  simp [neg]

end PreMS

end TendstoTactic
