/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Defs
public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Basis

/-!
# TODO
-/

set_option linter.flexible false
set_option linter.style.longLine false
set_option linter.style.multiGoal false

@[expose] public section

namespace ComputeAsymptotics

namespace PreMS

open Filter Stream'

-- TODO: move
lemma nil_tendsto_zero {basis_hd : ℝ → ℝ} {basis_tl : Basis} {f : ℝ → ℝ}
    (h : PreMS.Approximates (basis := basis_hd :: basis_tl) (mk .nil f)) :
    Tendsto f atTop (nhds 0) := by
  apply PreMS.Approximates_nil at h
  exact h.tendsto

-- TODO: move it
@[simp]
theorem real_real_rpow_zero (f : ℝ → ℝ) : f ^ (0 : ℝ) = 1 := by ext; simp

-- def SeqMS.enclose (basis_hd : ℝ → ℝ) {basis_tl : Basis} (ms : PreMS basis_tl) :
--     SeqMS basis_hd basis_tl :=
--   .cons 0 ms .nil

-- def enclose (basis_hd : ℝ → ℝ) {basis_tl : Basis} (ms : PreMS basis_tl) :
--     PreMS (basis_hd :: basis_tl) :=
--   mk (SeqMS.enclose basis_hd ms) ms.toFun

mutual

def SeqMS.const (basis_hd : ℝ → ℝ) (basis_tl : Basis) (c : ℝ) : SeqMS basis_hd basis_tl :=
  .cons 0 (const basis_tl c) .nil

/-- Multiseries representing constant. -/
def const (basis : Basis) (c : ℝ) : PreMS basis :=
  match basis with
  | [] => ofReal c
  | List.cons basis_hd basis_tl => mk (SeqMS.const basis_hd basis_tl c) (fun _ ↦ c)

end

/-- Neutral element for addition. It is `0 : ℝ` for empty basis and `[]` otherwise. -/
def zero {basis : Basis} : PreMS basis :=
  match basis with
  | [] => ofReal 0
  | List.cons _ _ => mk .nil (fun _ ↦ 0)

/-- This instance is needed to create instance for `AddCommMonoid (PreMS basis)`, which is
necessary for using `abel` tactic in our proofs. -/
instance {basis : Basis} : Zero (PreMS basis) where
  zero := zero

/-- This instance is needed to create instance for `AddCommMonoid (PreMS basis)`, which is
necessary for using `abel` tactic in our proofs. -/
instance {basis_hd : ℝ → ℝ} {basis_tl : Basis} : Zero (SeqMS basis_hd basis_tl) where
  zero := .nil

def SeqMS.one {basis_hd : ℝ → ℝ} {basis_tl : Basis} : SeqMS basis_hd basis_tl :=
  SeqMS.const _ _ 1

/-- Neutral element for multiplication. -/
def one {basis : Basis} : PreMS basis :=
  const basis 1

mutual

noncomputable def SeqMS.monomialRpow (basis_hd : ℝ → ℝ) (basis_tl : Basis) (n : ℕ) (r : ℝ) :
    SeqMS basis_hd basis_tl :=
  match n with
  | 0 => .cons r one .nil
  | m + 1 => .cons 0 (monomialRpow _ m r) .nil

/-- Multiseries representing `basis[n] ^ r`. -/
noncomputable def monomialRpow (basis : Basis) (n : ℕ) (r : ℝ) : PreMS basis :=
  match basis with
  | [] => default
  | List.cons basis_hd basis_tl => mk (SeqMS.monomialRpow _ _ n r) ((basis_hd :: basis_tl)[n]! ^ r)

end

noncomputable def SeqMS.monomial (basis_hd : ℝ → ℝ) (basis_tl : Basis) (n : ℕ) :
    SeqMS basis_hd basis_tl :=
  SeqMS.monomialRpow _ _ n 1

/-- Multiseries representing `basis[n]`. -/
noncomputable def monomial (basis : Basis) (n : ℕ) : PreMS basis :=
  monomialRpow _ n 1

theorem zero_def {basis_hd basis_tl} : (0 : PreMS (basis_hd :: basis_tl)) = mk .nil (fun _ ↦ 0) :=
  rfl

theorem SeqMS.zero_def {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    (0 : SeqMS basis_hd basis_tl) = .nil := rfl

#check SeqMS.const.eq_def

theorem SeqMS.const_def {basis_hd basis_tl} (c : ℝ) :
    SeqMS.const basis_hd basis_tl c = SeqMS.cons 0 (PreMS.const basis_tl c) .nil := by
  simp [SeqMS.const]

@[simp]
theorem const_toFun' {basis : Basis} {c : ℝ} : (const basis c).toFun = fun _ ↦ c := by
  match basis with
  | [] => simp [const, ofReal, toReal]
  | List.cons _ _ => simp [const]

@[simp]
theorem const_seq {basis_hd basis_tl} {c : ℝ} :
    (const (basis_hd :: basis_tl) c).seq = SeqMS.const basis_hd basis_tl c := by
  simp [const, SeqMS.const]

@[simp]
theorem zero_toFun {basis : Basis} : (@zero basis).toFun = 0 := by
  match basis with
  | [] => rfl
  | List.cons _ _ => rfl

@[simp]
theorem zero_seq {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    (0 : SeqMS basis_hd basis_tl) = .nil := rfl

@[simp]
theorem cons_ne_zero {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ} {coef : PreMS basis_tl}
    {tl : SeqMS basis_hd basis_tl} {f : ℝ → ℝ} :
    mk (basis_hd := basis_hd) (.cons exp coef tl) f ≠ 0 := by
  simp [zero_def]

@[simp]
theorem zero_ne_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ} {coef : PreMS basis_tl}
    {tl : SeqMS basis_hd basis_tl} {f : ℝ → ℝ} :
    0 ≠ mk (basis_hd := basis_hd) (.cons exp coef tl) f :=
  cons_ne_zero.symm

theorem SeqMS.one_def {basis_hd basis_tl} :
    @SeqMS.one basis_hd basis_tl = SeqMS.cons 0 PreMS.one .nil := by
  simp [SeqMS.one, SeqMS.const_def, PreMS.one]

@[simp]
theorem one_toFun {basis : Basis} : (@one basis).toFun = 1 := by
  simp [one]
  rfl

@[simp]
theorem one_seq {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    (@one (basis_hd :: basis_tl)).seq = SeqMS.one := by
  simp [one, SeqMS.one, const]

mutual

theorem SeqMS.const_WellOrdered {basis_hd : ℝ → ℝ} {basis_tl : Basis} {c : ℝ} :
    (SeqMS.const basis_hd basis_tl c).WellOrdered := by
  simp [SeqMS.const]
  apply WellOrdered.cons_nil
  exact const_WellOrdered

/-- Constants are well-ordered. -/
theorem const_WellOrdered {basis : Basis} {c : ℝ} :
    (const basis c).WellOrdered := by
  cases basis with
  | nil => constructor
  | cons basis_hd basis_tl =>
    simp [const]
    apply SeqMS.const_WellOrdered

end

/-- Zero is well-ordered. -/
theorem zero_WellOrdered {basis : Basis} : (0 : PreMS basis).WellOrdered := by
  cases basis with
  | nil => constructor
  | cons => apply WellOrdered.nil

theorem SeqMS.one_WellOrdered {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    (SeqMS.one : SeqMS basis_hd basis_tl).WellOrdered :=
  SeqMS.const_WellOrdered

/-- `one` is wellOrdered. -/
theorem one_WellOrdered {basis : Basis} : one.WellOrdered (basis := basis) :=
  const_WellOrdered

-- TODO : move it
/-- Constant multiseries approximates constant function. -/
theorem const_Approximates {c : ℝ} {basis : Basis} (h_basis : WellFormedBasis basis) :
    (const basis c).Approximates := by
  cases basis with
  | nil => simp
  | cons basis_hd basis_tl =>
    simp [const, SeqMS.const]
    have ih : (const basis_tl c).Approximates := by
      apply const_Approximates h_basis.tail
    apply Approximates.cons ih
    · apply const_majorated
      apply basis_tendsto_top h_basis
      simp
    · simp

-- TODO : move it
/-- `zero` approximates zero functions. -/
theorem zero_Approximates {basis : Basis} :
    (@zero basis).Approximates := by
  cases basis with
  | nil => simp [zero]
  | cons => exact Approximates.nil (by rfl)

-- theorem zero_Approximates_iff {basis : Basis} {f : ℝ → ℝ} :
--     (@zero basis).Approximates f ↔ (f =ᶠ[atTop] 0) where
--   mp h := by
--     cases basis with
--     | nil =>
--       simpa [zero] using h
--     | cons basis_hd basis_tl =>
--       simp only [zero] at h
--       exact Approximates_nil h
--   mpr h := Approximates_of_EventuallyEq h.symm zero_Approximates

/-- `one` approximates unit function. -/
theorem one_Approximates {basis : Basis} (h_basis : WellFormedBasis basis) :
    (@one basis).Approximates :=
  const_Approximates h_basis

@[simp]
theorem monomialRpow_toFun {basis : Basis} {n : Fin (List.length basis)} {r : ℝ} :
    (@monomialRpow basis n r).toFun = basis[n] ^ r := by
  cases basis with
  | nil => grind
  | cons basis_hd basis_tl => cases n using Fin.cases <;> simp [monomialRpow]

@[simp]
theorem monomialRpow_seq {basis_hd : ℝ → ℝ} {basis_tl : Basis} {n : ℕ} {r : ℝ} :
    (monomialRpow (basis_hd :: basis_tl) n r).seq = SeqMS.monomialRpow _ _ n r := by
  simp [monomialRpow]

mutual

theorem SeqMS.monomialRpow_WellOrdered {basis_hd : ℝ → ℝ} {basis_tl : Basis} {n : ℕ} {r : ℝ} :
    (@SeqMS.monomialRpow basis_hd basis_tl n r).WellOrdered := by
  cases n with
  | zero =>
    simp [SeqMS.monomialRpow]
    apply WellOrdered.cons_nil
    exact const_WellOrdered
  | succ m =>
    simp [SeqMS.monomialRpow]
    apply WellOrdered.cons_nil
    exact monomialRpow_WellOrdered

/-- `monomial` is well-ordered. -/
theorem monomialRpow_WellOrdered {basis : Basis} {n : ℕ} {r : ℝ} :
    (@monomialRpow basis n r).WellOrdered := by
  cases basis with
  | nil => constructor
  | cons basis_hd basis_tl =>
    simp
    apply SeqMS.monomialRpow_WellOrdered

end

/-- `monomialRpow` approximates monomial function. -/
theorem monomialRpow_Approximates {basis : Basis} {n : Fin (List.length basis)} {r : ℝ}
    (h_basis : WellFormedBasis basis) :
    (@monomialRpow basis n r).Approximates := by
  cases basis with
  | nil => simp
  | cons basis_hd basis_tl =>
    simp [monomialRpow]
    cases n using Fin.cases with
    | zero =>
      simp [SeqMS.monomialRpow]
      apply Approximates.cons
      · exact one_Approximates h_basis.tail
      · apply PreMS.majorated_self
        apply basis_tendsto_top h_basis
        simp
      · simp
    | succ m =>
      simp [SeqMS.monomialRpow]
      apply Approximates.cons
      · exact monomialRpow_Approximates h_basis.tail
      · apply basis_tail_pow_majorated_head h_basis
        simp
      · simp

@[simp]
theorem monomial_toFun {basis : Basis} {n : Fin (List.length basis)} :
    (@monomial basis n).toFun = basis[n] := by
  convert monomialRpow_toFun
  ext t
  simp

@[simp]
theorem monomial_seq {basis_hd : ℝ → ℝ} {basis_tl : Basis} {n : ℕ} :
    (monomial (basis_hd :: basis_tl) n).seq = SeqMS.monomial _ _ n :=
  monomialRpow_seq

theorem SeqMS.monomial_WellOrdered {basis_hd : ℝ → ℝ} {basis_tl : Basis} {n : ℕ} :
    (@SeqMS.monomial basis_hd basis_tl n).WellOrdered :=
  SeqMS.monomialRpow_WellOrdered

/-- `monomial` is well-ordered. -/
theorem monomial_WellOrdered {basis : Basis} {n : ℕ} : (@monomial basis n).WellOrdered :=
  monomialRpow_WellOrdered

/-- `monomial` approximates monomial function. -/
theorem monomial_Approximates {basis : Basis} {n : Fin (List.length basis)}
    (h_basis : WellFormedBasis basis) : (@monomial basis n).Approximates :=
  monomialRpow_Approximates h_basis

section BasisOperations

mutual

def SeqMS.updateBasis {basis_hd : ℝ → ℝ} {basis_tl : Basis} (ex : BasisExtension basis_tl)
    (ms : SeqMS basis_hd basis_tl) : SeqMS basis_hd ex.getBasis :=
  ms.map id (updateBasis ex ·)

/-- Given a basis extension `ex`, and a multiseries `ms`, immerses `ms` into the
basis `ex.getBasis`. -/
def updateBasis {basis : Basis} (ex : BasisExtension basis) (ms : PreMS basis) :
    PreMS ex.getBasis :=
  match ex with
  | .nil => ms
  | .keep basis_hd ex_tl => mk (ms.seq.updateBasis ex_tl) ms.toFun
  | .insert _ ex_tl => mk (.cons 0 (ms.updateBasis ex_tl) .nil) ms.toFun

end

-- TODO: remove. Unused
/-- Extends basis with `f` in the middle. -/
def extendBasisMiddle {left right : Basis} (f : ℝ → ℝ) (ms : PreMS (left ++ right)) :
    PreMS (left ++ f :: right) :=
  match left with
  | [] => mk (.cons 0 ms .nil) ms.toFun
  | List.cons _ _ => mk (ms.seq.map id (fun coef => extendBasisMiddle f coef)) ms.toFun

mutual

def SeqMS.extendBasisEnd {basis_hd : ℝ → ℝ} {basis_tl : Basis} (f : ℝ → ℝ)
    (ms : SeqMS basis_hd basis_tl) :
    SeqMS basis_hd (basis_tl ++ [f]) :=
  ms.map id (extendBasisEnd f ·)

/-- Extends basis with `f` at right end. -/
-- TODO: it's just extendMiddle with right = [].
def extendBasisEnd {basis : Basis} (f : ℝ → ℝ) (ms : PreMS basis) : PreMS (basis ++ [f]) :=
  match basis with
  | [] => const [f] ms
  | List.cons _ _ => mk (ms.seq.extendBasisEnd f) ms.toFun

end

-- TODO: move
@[simp]
theorem WithBot.map_id {α : Type*} (a : WithBot α) : WithBot.map id a = a := by
  cases a <;> rfl

@[simp]
lemma SeqMS.map_leadingExp {basis_hd basis_hd' basis_tl basis_tl'}
    {ms : SeqMS basis_hd basis_tl} {f : ℝ → ℝ} {g : PreMS basis_tl → PreMS basis_tl'} :
    (ms.map (basis_hd' := basis_hd') f g).leadingExp = ms.leadingExp.map f := by
  cases ms <;> simp

lemma SeqMS.map_id_WellOrdered {basis_hd basis_hd' basis_tl basis_tl'}
    {f : PreMS basis_tl → PreMS basis_tl'}
    {ms : SeqMS basis_hd basis_tl}
    (h_wo : ms.WellOrdered)
    (hf : ∀ coef, coef.WellOrdered → (f coef).WellOrdered) :
    (ms.map (basis_hd' := basis_hd') id f).WellOrdered := by
  let motive (ms : SeqMS basis_hd' basis_tl') : Prop :=
    ∃ (ms' : SeqMS basis_hd basis_tl), ms = ms'.map id f ∧ ms'.WellOrdered
  apply SeqMS.WellOrdered.coind motive
  · use ms
  intro exp coef tl ⟨ms, h_eq, h_wo⟩
  cases ms with
  | nil => simp at h_eq
  | cons exp' coef' tl' =>
  simp at h_eq
  obtain ⟨h_coef, h_comp, h_tl⟩ := WellOrdered_cons h_wo
  simp [h_eq, h_comp, motive]
  grind

lemma map_id_Approximates {basis_hd basis_tl basis_tl'}
    {f : PreMS basis_tl → PreMS basis_tl'}
    {ms : PreMS (basis_hd :: basis_tl)}
    (h_approx : ms.Approximates)
    (hf_approx : ∀ coef, coef.Approximates → (f coef).Approximates)
    (hf_toFun : ∀ coef, (f coef).toFun = coef.toFun) :
    (mk (ms.seq.map (basis_hd' := basis_hd) id f) ms.toFun).Approximates := by
  let motive (ms' : PreMS (basis_hd :: basis_tl')) : Prop :=
    ∃ (ms : PreMS (basis_hd :: basis_tl)),
      ms' = mk (ms.seq.map (basis_hd' := basis_hd) id f) ms.toFun ∧ ms.Approximates
  apply Approximates.coind motive
  · use ms
  rintro _ ⟨ms, rfl, h_approx⟩
  cases ms with
  | nil f => simpa using h_approx
  | cons exp coef tl g =>
  right
  obtain ⟨h_coef, h_maj, h_tl⟩ := Approximates_cons h_approx
  simp [hf_approx _ h_coef, h_maj, motive, hf_toFun]
  use mk tl (g - basis_hd ^ exp * coef.toFun)
  simp [h_tl]

@[simp]
theorem updateBasis_keep_seq {basis_hd : ℝ → ℝ} {basis_tl : Basis} (ex : BasisExtension basis_tl)
    {ms : PreMS (basis_hd :: basis_tl)} :
    (ms.updateBasis (.keep _ ex)).seq = ms.seq.updateBasis ex := by
  simp [PreMS.updateBasis]

@[simp]
theorem updateBasis_toFun {basis : Basis} {ex : BasisExtension basis} {ms : PreMS basis} :
    (ms.updateBasis ex).toFun = ms.toFun := by
  fun_cases updateBasis <;> simp [updateBasis]

theorem SeqMS.updateBasis_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ex : BasisExtension basis_tl} :
    (SeqMS.updateBasis (basis_hd := basis_hd) ex (.nil)) = .nil := by
  simp [SeqMS.updateBasis]

theorem SeqMS.updateBasis_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ex : BasisExtension basis_tl}
    {exp : ℝ} {coef : PreMS basis_tl} {tl : SeqMS basis_hd basis_tl} :
    (SeqMS.updateBasis ex (.cons exp coef tl)) =
    .cons exp (coef.updateBasis ex) (tl.updateBasis ex) := by
  simp [SeqMS.updateBasis]

mutual

theorem SeqMS.updateBasis_WellOrdered {basis_hd : ℝ → ℝ} {basis_tl : Basis} (ex : BasisExtension basis_tl)
    {ms : SeqMS basis_hd basis_tl}
    (h_wo : ms.WellOrdered) :
    (ms.updateBasis ex).WellOrdered := by
  simp [SeqMS.updateBasis]
  apply SeqMS.map_id_WellOrdered h_wo
  apply updateBasis_WellOrdered

theorem updateBasis_WellOrdered {basis : Basis} {ex : BasisExtension basis} {ms : PreMS basis}
    (h_wo : ms.WellOrdered) :
    (ms.updateBasis ex).WellOrdered := by
  cases ex with
  | nil => simpa [updateBasis]
  | insert f ex_tl =>
    simp only [updateBasis]
    apply WellOrdered.cons_nil
    exact updateBasis_WellOrdered h_wo
  | @keep basis_hd basis_tl ex_tl =>
    simp [updateBasis] at h_wo ⊢
    apply SeqMS.updateBasis_WellOrdered ex_tl h_wo

end

theorem updateBasis_Approximates {basis : Basis} {ex : BasisExtension basis} {ms : PreMS basis}
    (h_basis : WellFormedBasis ex.getBasis)
    (h_approx : ms.Approximates) :
    (ms.updateBasis ex).Approximates := by
  cases ex with
  | nil => simp
  | keep basis_hd ex_tl =>
    simp [updateBasis, SeqMS.updateBasis]
    apply map_id_Approximates h_approx
    · intro coef h_coef
      apply updateBasis_Approximates h_basis.tail h_coef
    · simp
  | insert g ex_tl =>
    simp [updateBasis]
    apply Approximates.cons
    · apply updateBasis_Approximates _ h_approx
      exact BasisExtension.insert_WellFormedBasis_tail h_basis
    · simp [BasisExtension.getBasis] at h_basis
      apply PreMS.Approximates_coef_majorated_head h_approx
      apply WellFormedBasis.of_sublist _ h_basis
      simp
      apply BasisExtension.getBasis_Sublist
    · apply Approximates.nil
      simp

@[simp]
theorem extendBasisMiddle_toFun {left right : Basis} {b : ℝ → ℝ} {ms : PreMS (left ++ right)} :
    (ms.extendBasisMiddle b).toFun = ms.toFun := by
  fun_cases extendBasisMiddle <;> rfl

theorem extendBasisMiddle_WellOrdered {left right : Basis} {b : ℝ → ℝ} {ms : PreMS (left ++ right)}
    (h_wo : ms.WellOrdered) : (ms.extendBasisMiddle b).WellOrdered := by
  cases left with
  | nil =>
    simp only [List.nil_append, extendBasisMiddle]
    apply WellOrdered.cons_nil
    assumption
  | cons left_hd left_tl =>
  simp [List.cons_append, extendBasisMiddle, List.append_eq]
  apply SeqMS.map_id_WellOrdered
  · simpa using h_wo
  · apply extendBasisMiddle_WellOrdered

theorem extendBasisMiddle_Approximates {left right : Basis} {b : ℝ → ℝ}
    {ms : PreMS (left ++ right)}
    (h_basis : WellFormedBasis (left ++ b :: right))
    (h_approx : ms.Approximates) :
    (ms.extendBasisMiddle b).Approximates := by
  cases left with
  | nil =>
    simp only [List.nil_append, extendBasisMiddle]
    apply Approximates.cons h_approx
    · exact PreMS.Approximates_coef_majorated_head h_approx h_basis
    · apply Approximates.nil
      simp
  | cons left_hd left_tl =>
  simp only [List.cons_append, extendBasisMiddle, List.append_eq]
  apply map_id_Approximates h_approx
  · intro coef h_coef
    apply extendBasisMiddle_Approximates h_basis.tail h_coef
  · simp

@[simp]
theorem extendBasisEnd_toFun {basis : Basis} {b : ℝ → ℝ} {ms : PreMS basis} :
    (ms.extendBasisEnd b).toFun = ms.toFun := by
  cases basis with
  | nil => simp [extendBasisEnd, toReal]
  | cons => simp [extendBasisEnd]

@[simp]
theorem extendBasisEnd_seq {basis_hd basis_tl} {b : ℝ → ℝ} {ms : PreMS (basis_hd :: basis_tl)} :
    (ms.extendBasisEnd b).seq = SeqMS.extendBasisEnd b ms.seq := by
  simp [extendBasisEnd]

theorem SeqMS.extendBasisEnd_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {f : ℝ → ℝ} :
    (SeqMS.extendBasisEnd (basis_hd := basis_hd) (basis_tl := basis_tl) f (.nil)) = .nil := by
  simp [SeqMS.extendBasisEnd]

theorem SeqMS.extendBasisEnd_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {f : ℝ → ℝ}
    {exp : ℝ} {coef : PreMS basis_tl} {tl : SeqMS basis_hd basis_tl} :
    (SeqMS.extendBasisEnd f (.cons exp coef tl)) = .cons exp (coef.extendBasisEnd f) (tl.extendBasisEnd f) := by
  simp [SeqMS.extendBasisEnd]

mutual

theorem SeqMS.extendBasisEnd_WellOrdered {basis_hd : ℝ → ℝ} {basis_tl : Basis} {f : ℝ → ℝ}
    {ms : SeqMS basis_hd basis_tl} (h_wo : ms.WellOrdered) :
    (ms.extendBasisEnd f).WellOrdered := by
  simp [SeqMS.extendBasisEnd]
  apply SeqMS.map_id_WellOrdered h_wo
  apply extendBasisEnd_WellOrdered

theorem extendBasisEnd_WellOrdered {basis : Basis} {b : ℝ → ℝ} {ms : PreMS basis}
    (h_wo : ms.WellOrdered) : (ms.extendBasisEnd b).WellOrdered := by
  cases basis with
  | nil => simpa only [extendBasisEnd] using const_WellOrdered
  | cons basis_hd basis_tl =>
  simp at *
  exact SeqMS.extendBasisEnd_WellOrdered h_wo

end

theorem extendBasisEnd_Approximates {basis : Basis} {b : ℝ → ℝ} {ms : PreMS basis}
    (h_basis : WellFormedBasis (basis ++ [b]))
    (h_approx : ms.Approximates) :
    (ms.extendBasisEnd b).Approximates := by
  cases basis with
  | nil =>
    simp only [List.nil_append, extendBasisEnd]
    apply const_Approximates h_basis
  | cons basis_hd basis_tl =>
  simp only [List.cons_append, extendBasisEnd, SeqMS.extendBasisEnd, List.append_eq]
  apply map_id_Approximates h_approx
  · intro coef h_coef
    apply extendBasisEnd_Approximates h_basis.tail h_coef
  · simp

end BasisOperations

end PreMS

end ComputeAsymptotics
