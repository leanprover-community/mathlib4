/-
Copyright (c) 2020 Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Patrick Lutz
-/
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.IntegralDomain

#align_import field_theory.primitive_element from "leanprover-community/mathlib"@"df76f43357840485b9d04ed5dee5ab115d420e87"

/-!
# Primitive Element Theorem

In this file we prove the primitive element theorem.

## Main results

- `exists_primitive_element`: a finite separable extension `E / F` has a primitive element, i.e.
  there is an `α : E` such that `F⟮α⟯ = (⊤ : Subalgebra F E)`.

## Implementation notes

In declaration names, `primitive_element` abbreviates `adjoin_simple_eq_top`:
it stands for the statement `F⟮α⟯ = (⊤ : Subalgebra F E)`. We did not add an extra
declaration `IsPrimitiveElement F α := F⟮α⟯ = (⊤ : Subalgebra F E)` because this
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

variable (F : Type*) [Field F] (E : Type*) [Field E] [Algebra F E]

/-! ### Primitive element theorem for finite fields -/


/-- **Primitive element theorem** assuming E is finite. -/
theorem exists_primitive_element_of_finite_top [Finite E] : ∃ α : E, F⟮α⟯ = ⊤ := by
  obtain ⟨α, hα⟩ := @IsCyclic.exists_generator (Units E) _ _
  use α
  apply eq_top_iff.mpr
  rintro x -
  by_cases hx : x = 0
  · rw [hx]
    exact F⟮α.val⟯.zero_mem
  · obtain ⟨n, hn⟩ := Set.mem_range.mp (hα (Units.mk0 x hx))
    simp only at hn
    rw [show x = α ^ n by norm_cast; rw [hn, Units.val_mk0], Units.val_zpow_eq_zpow_val]
    exact zpow_mem (mem_adjoin_simple_self F (E := E) ↑α) n
#align field.exists_primitive_element_of_finite_top Field.exists_primitive_element_of_finite_top

/-- Primitive element theorem for finite dimensional extension of a finite field. -/
theorem exists_primitive_element_of_finite_bot [Finite F] [FiniteDimensional F E] :
    ∃ α : E, F⟮α⟯ = ⊤ :=
  haveI : Finite E := finite_of_finite F E
  exists_primitive_element_of_finite_top F E
#align field.exists_primitive_element_of_finite_bot Field.exists_primitive_element_of_finite_bot

end PrimitiveElementFinite

/-! ### Primitive element theorem for infinite fields -/


section PrimitiveElementInf

variable {F : Type*} [Field F] [Infinite F] {E : Type*} [Field E] (ϕ : F →+* E) (α β : E)

theorem primitive_element_inf_aux_exists_c (f g : F[X]) :
    ∃ c : F, ∀ α' ∈ (f.map ϕ).roots, ∀ β' ∈ (g.map ϕ).roots, -(α' - α) / (β' - β) ≠ ϕ c := by
  let sf := (f.map ϕ).roots
  let sg := (g.map ϕ).roots
  let s := (sf.bind fun α' => sg.map fun β' => -(α' - α) / (β' - β)).toFinset
  let s' := s.preimage ϕ fun x _ y _ h => ϕ.injective h
  obtain ⟨c, hc⟩ := Infinite.exists_not_mem_finset s'
  simp_rw [Finset.mem_preimage, Multiset.mem_toFinset, Multiset.mem_bind, Multiset.mem_map] at hc
  push_neg at hc
  exact ⟨c, hc⟩
#align field.primitive_element_inf_aux_exists_c Field.primitive_element_inf_aux_exists_c

variable (F)

variable [Algebra F E]

-- This is the heart of the proof of the primitive element theorem. It shows that if `F` is
-- infinite and `α` and `β` are separable over `F` then `F⟮α, β⟯` is generated by a single element.
theorem primitive_element_inf_aux [IsSeparable F E] : ∃ γ : E, F⟮α, β⟯ = F⟮γ⟯ := by
  have hα := IsSeparable.isIntegral F α
  have hβ := IsSeparable.isIntegral F β
  let f := minpoly F α
  let g := minpoly F β
  let ιFE := algebraMap F E
  let ιEE' := algebraMap E (SplittingField (g.map ιFE))
  obtain ⟨c, hc⟩ := primitive_element_inf_aux_exists_c (ιEE'.comp ιFE) (ιEE' α) (ιEE' β) f g
  let γ := α + c • β
  suffices β_in_Fγ : β ∈ F⟮γ⟯
  · use γ
    apply le_antisymm
    · rw [adjoin_le_iff]
      have α_in_Fγ : α ∈ F⟮γ⟯ := by
        rw [← add_sub_cancel α (c • β)]
        exact F⟮γ⟯.sub_mem (mem_adjoin_simple_self F γ) (F⟮γ⟯.toSubalgebra.smul_mem β_in_Fγ c)
      exact fun x hx => by
        -- Porting note: was `by cases hx <;> cases hx <;> cases hx <;> assumption`
        cases' hx with hx hx
        · rwa [← hx] at α_in_Fγ
        · cases hx; norm_cast
    · rw [adjoin_simple_le_iff]
      have α_in_Fαβ : α ∈ F⟮α, β⟯ := subset_adjoin F {α, β} (Set.mem_insert α {β})
      have β_in_Fαβ : β ∈ F⟮α, β⟯ := subset_adjoin F {α, β} (Set.mem_insert_of_mem α rfl)
      exact F⟮α, β⟯.add_mem α_in_Fαβ (F⟮α, β⟯.smul_mem β_in_Fαβ)
  let p := EuclideanDomain.gcd ((f.map (algebraMap F F⟮γ⟯)).comp
    (C (AdjoinSimple.gen F γ) - (C ↑c : F⟮γ⟯[X]) * X)) (g.map (algebraMap F F⟮γ⟯))
  let h := EuclideanDomain.gcd ((f.map ιFE).comp (C γ - C (ιFE c) * X)) (g.map ιFE)
  have map_g_ne_zero : g.map ιFE ≠ 0 := map_ne_zero (minpoly.ne_zero hβ)
  have h_ne_zero : h ≠ 0 :=
    mt EuclideanDomain.gcd_eq_zero_iff.mp (not_and.mpr fun _ => map_g_ne_zero)
  suffices p_linear : p.map (algebraMap F⟮γ⟯ E) = C h.leadingCoeff * (X - C β)
  · have finale : β = algebraMap F⟮γ⟯ E (-p.coeff 0 / p.coeff 1) := by
      rw [map_div₀, RingHom.map_neg, ← coeff_map, ← coeff_map, p_linear]
      -- Porting note: had to add `-map_add` to avoid going in the wrong direction.
      simp [mul_sub, coeff_C, mul_div_cancel_left β (mt leadingCoeff_eq_zero.mp h_ne_zero),
        -map_add]
      -- Porting note: an alternative solution is:
      -- simp_rw [Polynomial.coeff_C_mul, Polynomial.coeff_sub, mul_sub,
      --   Polynomial.coeff_X_zero, Polynomial.coeff_X_one, mul_zero, mul_one, zero_sub, neg_neg,
      --   Polynomial.coeff_C, eq_self_iff_true, Nat.one_ne_zero, if_true, if_false, mul_zero,
      --   sub_zero, mul_div_cancel_left β (mt leadingCoeff_eq_zero.mp h_ne_zero)]
    rw [finale]
    exact Subtype.mem (-p.coeff 0 / p.coeff 1)
  have h_sep : h.Separable := separable_gcd_right _ (IsSeparable.separable F β).map
  have h_root : h.eval β = 0 := by
    apply eval_gcd_eq_zero
    · rw [eval_comp, eval_sub, eval_mul, eval_C, eval_C, eval_X, eval_map, ← aeval_def, ←
        Algebra.smul_def, add_sub_cancel, minpoly.aeval]
    · rw [eval_map, ← aeval_def, minpoly.aeval]
  have h_splits : Splits ιEE' h :=
    splits_of_splits_gcd_right ιEE' map_g_ne_zero (SplittingField.splits _)
  have h_roots : ∀ x ∈ (h.map ιEE').roots, x = ιEE' β := by
    intro x hx
    rw [mem_roots_map h_ne_zero] at hx
    specialize hc (ιEE' γ - ιEE' (ιFE c) * x) (by
      have f_root := root_left_of_root_gcd hx
      rw [eval₂_comp, eval₂_sub, eval₂_mul, eval₂_C, eval₂_C, eval₂_X, eval₂_map] at f_root
      exact (mem_roots_map (minpoly.ne_zero hα)).mpr f_root)
    specialize hc x (by
      rw [mem_roots_map (minpoly.ne_zero hβ), ← eval₂_map]
      exact root_right_of_root_gcd hx)
    by_contra a
    apply hc
    apply (div_eq_iff (sub_ne_zero.mpr a)).mpr
    simp only [Algebra.smul_def, RingHom.map_add, RingHom.map_mul, RingHom.comp_apply]
    ring
  rw [← eq_X_sub_C_of_separable_of_root_eq h_sep h_root h_splits h_roots]
  trans EuclideanDomain.gcd (?_ : E[X]) (?_ : E[X])
  · dsimp only
    convert (gcd_map (algebraMap F⟮γ⟯ E)).symm
  · simp [map_comp, Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
    congr
#align field.primitive_element_inf_aux Field.primitive_element_inf_aux

end PrimitiveElementInf

variable (F E : Type*) [Field F] [Field E]

variable [Algebra F E] [FiniteDimensional F E]

section SeparableAssumption

variable [IsSeparable F E]

/-- Primitive element theorem: a finite separable field extension `E` of `F` has a
  primitive element, i.e. there is an `α ∈ E` such that `F⟮α⟯ = (⊤ : Subalgebra F E)`.-/
theorem exists_primitive_element : ∃ α : E, F⟮α⟯ = ⊤ := by
  rcases isEmpty_or_nonempty (Fintype F) with (F_inf | ⟨⟨F_finite⟩⟩)
  · let P : IntermediateField F E → Prop := fun K => ∃ α : E, F⟮α⟯ = K
    have base : P ⊥ := ⟨0, adjoin_zero⟩
    have ih : ∀ (K : IntermediateField F E) (x : E), P K → P (K⟮x⟯.restrictScalars F) := by
      intro K β hK
      cases' hK with α hK
      rw [← hK, adjoin_simple_adjoin_simple]
      haveI : Infinite F := isEmpty_fintype.mp F_inf
      cases' primitive_element_inf_aux F α β with γ hγ
      exact ⟨γ, hγ.symm⟩
    exact induction_on_adjoin P base ih ⊤
  · exact exists_primitive_element_of_finite_bot F E
#align field.exists_primitive_element Field.exists_primitive_element

/-- Alternative phrasing of primitive element theorem:
a finite separable field extension has a basis `1, α, α^2, ..., α^n`.

See also `exists_primitive_element`. -/
noncomputable def powerBasisOfFiniteOfSeparable : PowerBasis F E :=
  let α := (exists_primitive_element F E).choose
  let pb := adjoin.powerBasis (IsSeparable.isIntegral F α)
  have e : F⟮α⟯ = ⊤ := (exists_primitive_element F E).choose_spec
  pb.map ((IntermediateField.equivOfEq e).trans IntermediateField.topEquiv)
#align field.power_basis_of_finite_of_separable Field.powerBasisOfFiniteOfSeparable

end SeparableAssumption

end Field

@[simp]
theorem AlgHom.card (F E K : Type*) [Field F] [Field E] [Field K] [IsAlgClosed K] [Algebra F E]
    [FiniteDimensional F E] [IsSeparable F E] [Algebra F K] :
    Fintype.card (E →ₐ[F] K) = finrank F E := by
  convert (AlgHom.card_of_powerBasis (L := K) (Field.powerBasisOfFiniteOfSeparable F E)
    (IsSeparable.separable _ _) (IsAlgClosed.splits_codomain _)).trans (PowerBasis.finrank _).symm
#align alg_hom.card AlgHom.card
