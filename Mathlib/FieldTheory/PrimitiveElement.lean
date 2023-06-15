/-
Copyright (c) 2020 Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Patrick Lutz

! This file was ported from Lean 3 source module field_theory.primitive_element
! leanprover-community/mathlib commit df76f43357840485b9d04ed5dee5ab115d420e87
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.FieldTheory.SplittingField.Construction
import Mathbin.FieldTheory.IsAlgClosed.Basic
import Mathbin.FieldTheory.Separable
import Mathbin.RingTheory.IntegralDomain

/-!
# Primitive Element Theorem

In this file we prove the primitive element theorem.

## Main results

- `exists_primitive_element`: a finite separable extension `E / F` has a primitive element, i.e.
  there is an `α : E` such that `F⟮α⟯ = (⊤ : subalgebra F E)`.

## Implementation notes

In declaration names, `primitive_element` abbreviates `adjoin_simple_eq_top`:
it stands for the statement `F⟮α⟯ = (⊤ : subalgebra F E)`. We did not add an extra
declaration `is_primitive_element F α := F⟮α⟯ = (⊤ : subalgebra F E)` because this
requires more unfolding without much obvious benefit.

## Tags

primitive element, separable field extension, separable extension, intermediate field, adjoin,
exists_adjoin_simple_eq_top

-/


noncomputable section

open scoped Classical Polynomial

open FiniteDimensional Polynomial IntermediateField

namespace Field

section PrimitiveElementFinite

variable (F : Type _) [Field F] (E : Type _) [Field E] [Algebra F E]

/-! ### Primitive element theorem for finite fields -/


/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/-- **Primitive element theorem** assuming E is finite. -/
theorem exists_primitive_element_of_finite_top [Finite E] : ∃ α : E, F⟮⟯ = ⊤ :=
  by
  obtain ⟨α, hα⟩ := IsCyclic.exists_generator (Units E)
  use α
  apply eq_top_iff.mpr
  rintro x -
  by_cases hx : x = 0
  · rw [hx]
    exact F⟮⟯.zero_mem
  · obtain ⟨n, hn⟩ := set.mem_range.mp (hα (Units.mk0 x hx))
    rw [show x = α ^ n by norm_cast; rw [hn, Units.val_mk0]]
    exact zpow_mem (mem_adjoin_simple_self F ↑α) n
#align field.exists_primitive_element_of_finite_top Field.exists_primitive_element_of_finite_top

/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/-- Primitive element theorem for finite dimensional extension of a finite field. -/
theorem exists_primitive_element_of_finite_bot [Finite F] [FiniteDimensional F E] :
    ∃ α : E, F⟮⟯ = ⊤ :=
  haveI : Finite E := finite_of_finite F E
  exists_primitive_element_of_finite_top F E
#align field.exists_primitive_element_of_finite_bot Field.exists_primitive_element_of_finite_bot

end PrimitiveElementFinite

/-! ### Primitive element theorem for infinite fields -/


section PrimitiveElementInf

variable {F : Type _} [Field F] [Infinite F] {E : Type _} [Field E] (ϕ : F →+* E) (α β : E)

theorem primitive_element_inf_aux_exists_c (f g : F[X]) :
    ∃ c : F, ∀ α' ∈ (f.map ϕ).roots, ∀ β' ∈ (g.map ϕ).roots, -(α' - α) / (β' - β) ≠ ϕ c :=
  by
  let sf := (f.map ϕ).roots
  let sg := (g.map ϕ).roots
  let s := (sf.bind fun α' => sg.map fun β' => -(α' - α) / (β' - β)).toFinset
  let s' := s.preimage ϕ fun x hx y hy h => ϕ.injective h
  obtain ⟨c, hc⟩ := Infinite.exists_not_mem_finset s'
  simp_rw [Finset.mem_preimage, Multiset.mem_toFinset, Multiset.mem_bind, Multiset.mem_map] at hc 
  push_neg at hc 
  exact ⟨c, hc⟩
#align field.primitive_element_inf_aux_exists_c Field.primitive_element_inf_aux_exists_c

variable (F) [Algebra F E]

/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
-- This is the heart of the proof of the primitive element theorem. It shows that if `F` is
-- infinite and `α` and `β` are separable over `F` then `F⟮α, β⟯` is generated by a single element.
theorem primitive_element_inf_aux [IsSeparable F E] : ∃ γ : E, F⟮⟯ = F⟮⟯ :=
  by
  have hα := IsSeparable.isIntegral F α
  have hβ := IsSeparable.isIntegral F β
  let f := minpoly F α
  let g := minpoly F β
  let ιFE := algebraMap F E
  let ιEE' := algebraMap E (splitting_field (g.map ιFE))
  obtain ⟨c, hc⟩ := primitive_element_inf_aux_exists_c (ιEE'.comp ιFE) (ιEE' α) (ιEE' β) f g
  let γ := α + c • β
  suffices β_in_Fγ : β ∈ F⟮⟯
  · use γ
    apply le_antisymm
    · rw [adjoin_le_iff]
      have α_in_Fγ : α ∈ F⟮⟯ := by
        rw [← add_sub_cancel α (c • β)]
        exact F⟮⟯.sub_mem (mem_adjoin_simple_self F γ) (F⟮⟯.toSubalgebra.smul_mem β_in_Fγ c)
      exact fun x hx => by cases hx <;> cases hx <;> cases hx <;> assumption
    · rw [adjoin_simple_le_iff]
      have α_in_Fαβ : α ∈ F⟮⟯ := subset_adjoin F {α, β} (Set.mem_insert α {β})
      have β_in_Fαβ : β ∈ F⟮⟯ := subset_adjoin F {α, β} (Set.mem_insert_of_mem α rfl)
      exact F⟮⟯.add_mem α_in_Fαβ (F⟮⟯.smul_mem β_in_Fαβ)
  let p :=
    EuclideanDomain.gcd ((f.map (algebraMap F F⟮⟯)).comp (C (adjoin_simple.gen F γ) - C ↑c * X))
      (g.map (algebraMap F F⟮⟯))
  let h := EuclideanDomain.gcd ((f.map ιFE).comp (C γ - C (ιFE c) * X)) (g.map ιFE)
  have map_g_ne_zero : g.map ιFE ≠ 0 := map_ne_zero (minpoly.ne_zero hβ)
  have h_ne_zero : h ≠ 0 :=
    mt euclidean_domain.gcd_eq_zero_iff.mp (not_and.mpr fun _ => map_g_ne_zero)
  suffices p_linear : p.map (algebraMap F⟮⟯ E) = C h.leading_coeff * (X - C β)
  · have finale : β = algebraMap F⟮⟯ E (-p.coeff 0 / p.coeff 1) :=
      by
      rw [map_div₀, RingHom.map_neg, ← coeff_map, ← coeff_map, p_linear]
      simp [mul_sub, coeff_C, mul_div_cancel_left β (mt leading_coeff_eq_zero.mp h_ne_zero)]
    rw [finale]
    exact Subtype.mem (-p.coeff 0 / p.coeff 1)
  have h_sep : h.separable := separable_gcd_right _ (IsSeparable.separable F β).map
  have h_root : h.eval β = 0 := by
    apply eval_gcd_eq_zero
    ·
      rw [eval_comp, eval_sub, eval_mul, eval_C, eval_C, eval_X, eval_map, ← aeval_def, ←
        Algebra.smul_def, add_sub_cancel, minpoly.aeval]
    · rw [eval_map, ← aeval_def, minpoly.aeval]
  have h_splits : splits ιEE' h :=
    splits_of_splits_gcd_right ιEE' map_g_ne_zero (splitting_field.splits _)
  have h_roots : ∀ x ∈ (h.map ιEE').roots, x = ιEE' β :=
    by
    intro x hx
    rw [mem_roots_map h_ne_zero] at hx 
    specialize
      hc (ιEE' γ - ιEE' (ιFE c) * x)
        (by
          have f_root := root_left_of_root_gcd hx
          rw [eval₂_comp, eval₂_sub, eval₂_mul, eval₂_C, eval₂_C, eval₂_X, eval₂_map] at f_root 
          exact (mem_roots_map (minpoly.ne_zero hα)).mpr f_root)
    specialize
      hc x
        (by
          rw [mem_roots_map (minpoly.ne_zero hβ), ← eval₂_map]
          exact root_right_of_root_gcd hx)
    by_contra a
    apply hc
    apply (div_eq_iff (sub_ne_zero.mpr a)).mpr
    simp only [Algebra.smul_def, RingHom.map_add, RingHom.map_mul, RingHom.comp_apply]
    ring
  rw [← eq_X_sub_C_of_separable_of_root_eq h_sep h_root h_splits h_roots]
  trans EuclideanDomain.gcd (_ : E[X]) (_ : E[X])
  · dsimp only [p]
    convert (gcd_map (algebraMap F⟮⟯ E)).symm
  · simpa [map_comp, Polynomial.map_map, ← IsScalarTower.algebraMap_eq, h]
#align field.primitive_element_inf_aux Field.primitive_element_inf_aux

end PrimitiveElementInf

variable (F E : Type _) [Field F] [Field E]

variable [Algebra F E] [FiniteDimensional F E]

section SeparableAssumption

variable [IsSeparable F E]

/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/-- Primitive element theorem: a finite separable field extension `E` of `F` has a
  primitive element, i.e. there is an `α ∈ E` such that `F⟮α⟯ = (⊤ : subalgebra F E)`.-/
theorem exists_primitive_element : ∃ α : E, F⟮⟯ = ⊤ :=
  by
  rcases isEmpty_or_nonempty (Fintype F) with (F_inf | ⟨⟨F_finite⟩⟩)
  · let P : IntermediateField F E → Prop := fun K => ∃ α : E, F⟮⟯ = K
    have base : P ⊥ := ⟨0, adjoin_zero⟩
    have ih : ∀ (K : IntermediateField F E) (x : E), P K → P (K⟮⟯.restrictScalars F) :=
      by
      intro K β hK
      cases' hK with α hK
      rw [← hK, adjoin_simple_adjoin_simple]
      haveI : Infinite F := is_empty_fintype.mp F_inf
      cases' primitive_element_inf_aux F α β with γ hγ
      exact ⟨γ, hγ.symm⟩
    exact induction_on_adjoin P base ih ⊤
  · exact exists_primitive_element_of_finite_bot F E
#align field.exists_primitive_element Field.exists_primitive_element

/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/-- Alternative phrasing of primitive element theorem:
a finite separable field extension has a basis `1, α, α^2, ..., α^n`.

See also `exists_primitive_element`. -/
noncomputable def powerBasisOfFiniteOfSeparable : PowerBasis F E :=
  let α := (exists_primitive_element F E).some
  let pb := adjoin.powerBasis (IsSeparable.isIntegral F α)
  have e : F⟮⟯ = ⊤ := (exists_primitive_element F E).choose_spec
  pb.map ((IntermediateField.equivOfEq e).trans IntermediateField.topEquiv)
#align field.power_basis_of_finite_of_separable Field.powerBasisOfFiniteOfSeparable

end SeparableAssumption

end Field

@[simp]
theorem AlgHom.card (F E K : Type _) [Field F] [Field E] [Field K] [IsAlgClosed K] [Algebra F E]
    [FiniteDimensional F E] [IsSeparable F E] [Algebra F K] :
    Fintype.card (E →ₐ[F] K) = finrank F E :=
  by
  convert
    (AlgHom.card_of_powerBasis (Field.powerBasisOfFiniteOfSeparable F E) (IsSeparable.separable _ _)
          (IsAlgClosed.splits_codomain _)).trans
      (PowerBasis.finrank _).symm
  infer_instance
#align alg_hom.card AlgHom.card

