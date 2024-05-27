/-
Copyright (c) 2019 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import Mathlib.Algebra.ContinuedFractions.Basic
import Mathlib.Data.Rat.Cast.CharZero

#align_import algebra.continued_fractions.translations from "leanprover-community/mathlib"@"a7e36e48519ab281320c4d192da6a7b348ce40ad"

/-!
# Basic Translation Lemmas Between Functions Defined for Continued Fractions

## Summary

Some simple translation lemmas between the different definitions of functions defined in
`Algebra.ContinuedFractions.Basic`.
-/



open FGCF GCF List Filter Set

#noalign generalized_continued_fraction.terminated_at_iff_s_terminated_at

#noalign generalized_continued_fraction.terminated_at_iff_s_none

#noalign generalized_continued_fraction.part_num_none_iff_s_none

#noalign generalized_continued_fraction.terminated_at_iff_part_num_none

#noalign generalized_continued_fraction.part_denom_none_iff_s_none

#noalign generalized_continued_fraction.terminated_at_iff_part_denom_none

#noalign generalized_continued_fraction.part_num_eq_s_a

#noalign generalized_continued_fraction.part_denom_eq_s_b

#noalign generalized_continued_fraction.exists_s_a_of_part_num

#noalign generalized_continued_fraction.exists_s_b_of_part_denom

/-!
### Translations Between Computational Functions

Here we give some basic translations that hold by definition for the computational methods of a
continued fraction.
-/

namespace FGCF

variable {K : Type*} [DivisionRing K] [DecidableEq K]
  (f : FGCF K) (h : K) (l : List (K × K)) (p : K × K)

#noalign generalized_continued_fraction.nth_cont_eq_succ_nth_cont_aux

theorem num_eq_cont_fst : f.numerator = f.continuant.1 :=
  rfl
#align generalized_continued_fraction.num_eq_conts_a FGCF.num_eq_cont_fstₓ

theorem denom_eq_cont_snd : f.denominator = f.continuant.2 :=
  rfl
#align generalized_continued_fraction.denom_eq_conts_b FGCF.denom_eq_cont_sndₓ

#noalign generalized_continued_fraction.convergent_eq_num_div_denom

#noalign generalized_continued_fraction.convergent_eq_conts_a_div_conts_b

#noalign generalized_continued_fraction.exists_conts_a_of_num

#noalign generalized_continued_fraction.exists_conts_b_of_denom

#noalign generalized_continued_fraction.zeroth_continuant_aux_eq_one_zero

#noalign generalized_continued_fraction.first_continuant_aux_eq_h_one

@[simp]
theorem continuant_mk_nil : continuant ⟨h, []⟩ = (h, 1) :=
  rfl
#align generalized_continued_fraction.zeroth_continuant_eq_h_one FGCF.continuant_mk_nilₓ

@[simp]
theorem numerator_mk_nil : numerator ⟨h, []⟩ = h :=
  rfl
#align generalized_continued_fraction.zeroth_numerator_eq_h FGCF.numerator_mk_nilₓ

@[simp]
theorem denominator_mk_nil : denominator ⟨h, []⟩ = 1 :=
  rfl
#align generalized_continued_fraction.zeroth_denominator_eq_one FGCF.denominator_mk_nilₓ

@[simp]
theorem eval?_mk_nil : eval? ⟨h, []⟩ = some h := by
  simp [eval?]
#align generalized_continued_fraction.zeroth_convergent_eq_h FGCF.eval?_mk_nilₓ

#noalign generalized_continued_fraction.second_continuant_aux_eq

@[simp]
theorem continuant_mk_singleton : continuant ⟨h, [p]⟩ = (p.2 * h + p.1, p.2) := by
  simp [continuant]
#align generalized_continued_fraction.first_continuant_eq FGCF.continuant_mk_singletonₓ

@[simp]
theorem numerator_mk_singleton : numerator ⟨h, [p]⟩ = p.2 * h + p.1 := by
  rw [numerator, continuant_mk_singleton]
#align generalized_continued_fraction.first_numerator_eq FGCF.numerator_mk_singletonₓ

@[simp]
theorem denominator_mk_singleton : denominator ⟨h, [p]⟩ = p.2 := by
  rw [denominator, continuant_mk_singleton]
#align generalized_continued_fraction.first_denominator_eq FGCF.denominator_mk_singletonₓ

#noalign generalized_continued_fraction.zeroth_convergent'_aux_eq_zero

@[simp]
theorem evalF?_mk_nil : evalF? ⟨h, []⟩ = some h := by
  simp [evalF?]
#align generalized_continued_fraction.zeroth_convergent'_eq_h FGCF.evalF?_mk_nilₓ

#noalign generalized_continued_fraction.convergents'_aux_succ_none

#noalign generalized_continued_fraction.convergents'_aux_succ_some

end FGCF

namespace FCF

variable {K : Type*} [DivisionRing K] [CharZero K] [DecidableEq K]
  (f : FCF K) (h : ℤ) (l : List ℕ+) (n : ℕ+)

theorem num_eq_cont_fst : f.numerator = f.continuant.1 :=
  rfl

theorem denom_eq_cont_snd : f.denominator = f.continuant.2 :=
  rfl

@[simp]
theorem continuant_mk_nil : continuant (⟨h, []⟩ : FCF K) = (h, 1) :=
  rfl

@[simp]
theorem numerator_mk_nil : numerator (⟨h, []⟩ : FCF K) = h :=
  rfl

@[simp]
theorem denominator_mk_nil : denominator (⟨h, []⟩ : FCF K) = 1 :=
  rfl

@[simp]
theorem eval_mk_nil : eval (⟨h, []⟩ : FCF K) = h := by
  simp [eval, Rat.mkRat_one]

@[simp]
theorem continuant_mk_singleton : continuant (⟨h, [n]⟩ : FCF K) = (↑n * h + 1, n) := by
  simp [continuant, - PNat.coe_inj, ← PNat.coe_inj]

@[simp]
theorem numerator_mk_singleton : numerator (⟨h, [n]⟩ : FCF K) = ↑n * h + 1 := by
  rw [numerator, continuant_mk_singleton]

@[simp]
theorem denominator_mk_singleton : denominator (⟨h, [n]⟩ : FCF K) = n := by
  rw [denominator, continuant_mk_singleton]

@[simp]
theorem continuant_toFGCF : (↑f : FGCF K).continuant = (↑f.numerator, ↑f.denominator) := by
  suffices hf :
      f.l.foldl (fun (x : (K × K) × (K × K)) (y : ℕ+) ↦ FGCF.nextContinuants x (1, ↑y))
        ((1, 0), (↑f.h, 1)) =
          Prod.map (Prod.map (↑) (↑)) (Prod.map (↑) (↑))
            (f.l.foldl FCF.nextContinuants ((1, 0), (f.h, 1))) by
    simp [FGCF.continuant, FCF.numerator, FCF.denominator, FCF.continuant, List.foldl_map, hf,
      - FGCF.nextContinuants]
  have h : (((1, 0), (↑f.h, 1)) : (K × K) × (K × K)) =
      Prod.map (Prod.map (↑) (↑)) (Prod.map (↑) (↑)) (((1 : ℤ), (0 : ℕ)), (f.h, (1 : ℕ+))) := by
    simp
  rw [h]
  apply List.foldl_hom
  simp

@[simp]
theorem numerator_toFGCF : (↑f : FGCF K).numerator = ↑f.numerator := by
  simp [FGCF.numerator]

@[simp]
theorem denominator_toFGCF : (↑f : FGCF K).denominator = ↑f.denominator := by
  simp [FGCF.denominator]

@[simp]
theorem eval?_toFGCF : (↑f : FGCF K).eval? = some ↑f.eval := by
  simp [FGCF.eval?, FCF.eval]
  norm_cast

end FCF

namespace CF

variable {K : Type*} [DivisionRing K] [CharZero K] [DecidableEq K]

@[simp]
theorem convergents_toGCF (c : CF K) : GCF.convergents (↑c : GCF K) = ↑(CF.convergents c) := by
  apply PFun.ext
  intro v₁ v₂
  simp [GCF.convergents, CF.convergents]

theorem hasValue_iff_convergents_tendsto [TopologicalSpace K] {c : CF K} {v : K} :
    HasValue (↑c : GCF K) v ↔ Tendsto (convergents c) atTop (nhds v) := by
  rw [HasValue, convergents_toGCF, ← PFun.res_univ, ← tendsto_iff_ptendsto_univ]

end CF
