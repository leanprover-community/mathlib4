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

- `exists_primitive_element_iff_finite_intermediateField`: a finite extension `E / F` has a
  primitive element if and only if there exist only finitely many intermediate fields between `E`
  and `F`.

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
  obtain ⟨α, hα⟩ := @IsCyclic.exists_generator Eˣ _ _
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

/-- This is the heart of the proof of the primitive element theorem. It shows that if `F` is
infinite and `α` and `β` are separable over `F` then `F⟮α, β⟯` is generated by a single element. -/
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
      rintro x (rfl | rfl) <;> assumption
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
  · simp only [map_comp, Polynomial.map_map, ← IsScalarTower.algebraMap_eq, Polynomial.map_sub,
      map_C, AdjoinSimple.algebraMap_gen, map_add, Polynomial.map_mul, map_X]
    congr
#align field.primitive_element_inf_aux Field.primitive_element_inf_aux

/-- If `F` is infinite and `E/F` has only finitely many intermediate fields, then for any
`α` and `β` in `E`, `F⟮α, β⟯` is generated by a single element. -/
theorem primitive_element_inf_aux_of_finite_intermediateField
    [Finite (IntermediateField F E)] : ∃ γ : E, F⟮α, β⟯ = F⟮γ⟯ := by
  let f : F → IntermediateField F E := fun x ↦ F⟮α + x • β⟯
  obtain ⟨x, y, hneq, heq⟩ := Finite.exists_ne_map_eq_of_infinite f
  use α + x • β
  apply le_antisymm
  · rw [adjoin_le_iff]
    have αxβ_in_K : α + x • β ∈ F⟮α + x • β⟯ := mem_adjoin_simple_self F _
    have αyβ_in_K : α + y • β ∈ F⟮α + y • β⟯ := mem_adjoin_simple_self F _
    simp only [← heq] at αyβ_in_K
    have β_in_K := sub_mem αxβ_in_K αyβ_in_K
    rw [show (α + x • β) - (α + y • β) = (x - y) • β by rw [sub_smul]; abel1] at β_in_K
    replace β_in_K := smul_mem _ β_in_K (x := (x - y)⁻¹)
    rw [smul_smul, inv_mul_eq_div, div_self (sub_ne_zero.2 hneq), one_smul] at β_in_K
    have α_in_K : α ∈ F⟮α + x • β⟯ := by
      convert ← sub_mem αxβ_in_K (smul_mem _ β_in_K)
      apply add_sub_cancel
    rintro x (rfl | rfl) <;> assumption
  · rw [adjoin_simple_le_iff]
    have α_in_Fαβ : α ∈ F⟮α, β⟯ := subset_adjoin F {α, β} (Set.mem_insert α {β})
    have β_in_Fαβ : β ∈ F⟮α, β⟯ := subset_adjoin F {α, β} (Set.mem_insert_of_mem α rfl)
    exact F⟮α, β⟯.add_mem α_in_Fαβ (F⟮α, β⟯.smul_mem β_in_Fαβ)

end PrimitiveElementInf

variable (F E : Type*) [Field F] [Field E]

variable [Algebra F E]

section SeparableAssumption

variable [FiniteDimensional F E] [IsSeparable F E]

/-- **Primitive element theorem**: a finite separable field extension `E` of `F` has a
  primitive element, i.e. there is an `α ∈ E` such that `F⟮α⟯ = (⊤ : Subalgebra F E)`. -/
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

section FiniteIntermediateField

-- TODO: move it to suitable file
theorem _root_.IntermediateField.mem_adjoin_iff {S : Set E} (x : E) :
    x ∈ adjoin F S ↔ (∃ r s : MvPolynomial S F,
      x = MvPolynomial.aeval Subtype.val r / MvPolynomial.aeval Subtype.val s) := by
  simp only [adjoin, mem_mk, Subring.mem_toSubsemiring, Subfield.mem_toSubring,
    Subfield.mem_closure_iff, ← Algebra.adjoin_eq_ring_closure, Subalgebra.mem_toSubring,
    Algebra.adjoin_eq_range, AlgHom.mem_range, exists_exists_eq_and]
  tauto

-- TODO: move it to suitable file
theorem _root_.IntermediateField.mem_adjoin_simple_iff {α : E} (x : E) :
    x ∈ F⟮α⟯ ↔ (∃ r s : Polynomial F, x = aeval α r / aeval α s) := by
  simp only [adjoin, mem_mk, Subring.mem_toSubsemiring, Subfield.mem_toSubring,
    Subfield.mem_closure_iff, ← Algebra.adjoin_eq_ring_closure, Subalgebra.mem_toSubring,
    Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range, exists_exists_eq_and]
  tauto

theorem isAlgebraic_of_adjoin_eq_adjoin {α : E} {m n : ℕ} (hm : 0 < m) (hmn : m < n)
    (heq : F⟮α ^ m⟯ = F⟮α ^ n⟯) : IsAlgebraic F α := by
  obtain ⟨r, s, h⟩ := (mem_adjoin_simple_iff F E _).1 (heq ▸ mem_adjoin_simple_self F (α ^ m))
  by_cases hzero : aeval (α ^ n) s = 0
  · simp only [hzero, div_zero, pow_eq_zero_iff hm] at h
    exact h.symm ▸ isAlgebraic_zero
  · rw [eq_div_iff hzero, ← sub_eq_zero] at h
    replace hzero : s ≠ 0 := fun h ↦ by simp only [h, map_zero, not_true] at hzero
    let f : F[X] := X ^ m * expand F n s - expand F n r
    use f
    constructor
    · have : f.coeff (n * s.natDegree + m) ≠ 0 := by
        have hn : 0 < n := by linarith only [hm, hmn]
        have hndvd : ¬ n ∣ n * s.natDegree + m := by
          rw [← Nat.dvd_add_iff_right (Nat.dvd_mul_right n s.natDegree)]
          exact Nat.not_dvd_of_pos_of_lt hm hmn
        simp only [coeff_sub, coeff_X_pow_mul, s.coeff_expand_mul' hn, coeff_natDegree,
          coeff_expand hn r, hndvd, ite_false, sub_zero]
        exact leadingCoeff_ne_zero.2 hzero
      intro h
      simp only [h, coeff_zero, ne_eq, not_true] at this
    · simp only [map_sub, map_mul, map_pow, aeval_X, expand_aeval, h]

theorem isAlgebraic_of_finite_intermediateField
    [Finite (IntermediateField F E)] : Algebra.IsAlgebraic F E := by
  intro α
  let f : ℕ → IntermediateField F E := fun n ↦ F⟮α ^ (n + 1)⟯
  obtain ⟨m, n, hneq, heq⟩ := Finite.exists_ne_map_eq_of_infinite f
  rcases Nat.lt_trichotomy m n with (hmn | hmn | hmn)
  · exact isAlgebraic_of_adjoin_eq_adjoin F E m.succ_pos (Nat.add_lt_add_right hmn 1) heq
  · contradiction
  · exact isAlgebraic_of_adjoin_eq_adjoin F E n.succ_pos (Nat.add_lt_add_right hmn 1) heq.symm

-- TODO: move it to suitable file
theorem _root_.IntermediateField.finiteDimensional_adjoin_of_finite_of_isAlgebraic
    (halg : Algebra.IsAlgebraic F E) (S : Set E) [Finite S] :
    FiniteDimensional F (adjoin F S) := by
  let t : S → IntermediateField F E := fun x ↦ F⟮x.1⟯
  have h : ∀ x : S, FiniteDimensional F (t x) := fun x ↦
    adjoin.finiteDimensional <| isAlgebraic_iff_isIntegral.1 (halg x.1)
  have hfin := finiteDimensional_iSup_of_finite (t := t)
  have := (gc (F := F) (E := E)).l_iSup (f := fun (x : S) ↦ {x.1})
  simp only [Set.iSup_eq_iUnion, Set.iUnion_singleton_eq_range, Subtype.range_coe_subtype,
    Set.setOf_mem_eq] at this
  rwa [← this] at hfin

theorem finiteDimensional_of_finite_intermediateField
    [Finite (IntermediateField F E)] : FiniteDimensional F E := by
  have halg := isAlgebraic_of_finite_intermediateField F E
  let IF := { K : IntermediateField F E // ∃ x, K = F⟮x⟯ }
  haveI : Finite IF := Subtype.finite
  haveI : ∀ K : IF, FiniteDimensional F K.1 := fun ⟨_, x, rfl⟩ ↦
    adjoin.finiteDimensional <| isAlgebraic_iff_isIntegral.1 (halg x)
  have hfin := finiteDimensional_iSup_of_finite (t := fun (K : IF) ↦ K.1)
  have htop : ⨆ (K : IF), K.1 = ⊤ := by
    apply le_antisymm le_top
    intro x _
    exact le_iSup (fun (K : IF) ↦ K.1) ⟨F⟮x⟯, x, rfl⟩ <| mem_adjoin_simple_self F x
  rw [htop] at hfin
  have := (topEquiv (F := F) (E := E)).toLinearEquiv
  exact FiniteDimensional.of_surjective this.toLinearMap this.surjective

theorem exists_primitive_element_of_finite_intermediateField
    [Finite (IntermediateField F E)] : ∃ α : E, F⟮α⟯ = ⊤ := by
  haveI := finiteDimensional_of_finite_intermediateField F E
  rcases finite_or_infinite F with (F_finite | F_inf)
  · exact exists_primitive_element_of_finite_bot F E
  · let P : IntermediateField F E → Prop := fun K ↦ ∃ α : E, F⟮α⟯ = K
    have base : P ⊥ := ⟨0, adjoin_zero⟩
    have ih : ∀ (K : IntermediateField F E) (x : E), P K → P (K⟮x⟯.restrictScalars F) := by
      rintro K β ⟨α, rfl⟩
      rw [adjoin_simple_adjoin_simple]
      cases' primitive_element_inf_aux_of_finite_intermediateField F α β with γ hγ
      exact ⟨γ, hγ.symm⟩
    exact induction_on_adjoin P base ih ⊤

-- TODO: move it to suitable file
lemma _root_.IntermediateField.adjoin_eq_top_of_adjoin_eq_top (A B C: Type*)
    [Field A] [Field B] [Field C] [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    {S : Set C} (hprim : adjoin A S = ⊤) : adjoin B S = ⊤ := by
  apply restrictScalars_injective (K := A) (L' := B) (L := C)
  rw [restrictScalars_top, ← top_le_iff, ← hprim, adjoin_le_iff,
    coe_restrictScalars, ← adjoin_le_iff]

-- TODO: move it to suitable file
lemma _root_.IntermediateField.eq_adjoin_minpoly_coeff_of_exists_primitive_element
    [FiniteDimensional F E] (α : E) (hprim : F⟮α⟯ = ⊤) (K : IntermediateField F E) :
    K = adjoin F ((minpoly K α).map (algebraMap K E)).frange := by
  set g := (minpoly K α).map (algebraMap K E)
  set K' : IntermediateField F E := adjoin F g.frange
  have hsub : K' ≤ K := by
    rw [adjoin_le_iff]
    intro x
    rw [Finset.mem_coe, mem_frange_iff]
    rintro ⟨n, _, rfl⟩
    rw [coeff_map]
    apply Subtype.mem
  have g_lifts : g ∈ lifts (algebraMap K' E) := by
    refine g.lifts_iff_coeff_lifts.mpr fun n ↦ ?_
    erw [Subtype.range_val]
    by_cases hn : n ∈ g.support
    · have h2 : ({coeff g n} : Set E) ⊆ g.frange := by
        rw [Set.singleton_subset_iff, Finset.mem_coe, mem_frange_iff]
        exact ⟨n, hn, rfl⟩
      exact adjoin.mono F _ _ h2 <| mem_adjoin_simple_self F (coeff g n)
    · rw [not_mem_support_iff.1 hn]
      exact zero_mem K'
  obtain ⟨p, hp⟩ := g.lifts_and_natDegree_eq_and_monic
    g_lifts ((minpoly.monic <| isIntegral_of_finite K α).map _)
  have dvd_p : minpoly K' α ∣ p
  · apply minpoly.dvd
    rw [aeval_def, eval₂_eq_eval_map, hp.1, ← eval₂_eq_eval_map, ← aeval_def]
    exact minpoly.aeval K α
  have finrank_eq : ∀ K : IntermediateField F E, finrank K E = natDegree (minpoly K α)
  · intro K
    have := adjoin.finrank (isIntegral_of_finite K α)
    erw [adjoin_eq_top_of_adjoin_eq_top F K E hprim, finrank_top K E] at this
    exact this
  refine (eq_of_le_of_finrank_le' hsub ?_).symm
  simp_rw [finrank_eq]
  convert natDegree_le_of_dvd dvd_p hp.2.2.ne_zero using 1
  rw [hp.2.1, natDegree_map]

theorem finiteDimensional_of_exists_primitive_element (halg : Algebra.IsAlgebraic F E)
    (h : ∃ α : E, F⟮α⟯ = ⊤) : FiniteDimensional F E := by
  obtain ⟨α, hprim⟩ := h
  have hfin := adjoin.finiteDimensional <| isAlgebraic_iff_isIntegral.1 (halg α)
  rw [hprim] at hfin
  have := (topEquiv (F := F) (E := E)).toLinearEquiv
  exact FiniteDimensional.of_surjective this.toLinearMap this.surjective

-- A finite simple extension has only finitely many intermediate fields
theorem finite_intermediateField_of_exists_primitive_element (halg : Algebra.IsAlgebraic F E)
    (h : ∃ α : E, F⟮α⟯ = ⊤) : Finite (IntermediateField F E) := by
  haveI := finiteDimensional_of_exists_primitive_element F E halg h
  obtain ⟨α, hprim⟩ := h
  -- Let `f` be the minimal polynomial of `α ∈ E` over `F`
  let f : F[X] := minpoly F α
  let G := { g : E[X] // g.Monic ∧ g ∣ f.map (algebraMap F E) }
  -- Then `f` has only finitely many monic factors
  have hfin : Finite G := @Finite.of_fintype _ <| fintypeSubtypeMonicDvd
    (f.map (algebraMap F E)) <| map_ne_zero (minpoly.ne_zero_of_finite F α)
  -- If `K` is an intermediate field of `E/F`, let `g` be the minimal polynomial of `α` over `K`
  -- which is a monic factor of `f`
  let g : IntermediateField F E → G := fun K ↦
    ⟨(minpoly K α).map (algebraMap K E), (minpoly.monic <| isIntegral_of_finite K α).map _, by
      convert Polynomial.map_dvd (algebraMap K E) (minpoly.dvd_map_of_isScalarTower F K α)
      rw [Polynomial.map_map]; rfl⟩
  -- The map `K ↦ g` is injective
  have hinj : Function.Injective g := fun K K' heq ↦ by
    rw [Subtype.mk.injEq] at heq
    apply_fun fun f : E[X] ↦ adjoin F (f.frange : Set E) at heq
    rwa [← eq_adjoin_minpoly_coeff_of_exists_primitive_element F E _ hprim K,
      ← eq_adjoin_minpoly_coeff_of_exists_primitive_element F E _ hprim K'] at heq
  -- Therefore there are only finitely many intermediate fields
  exact Finite.of_injective g hinj

/-- **Steinitz theorem**: an algebraic extension `E` of `F` has a
  primitive element (i.e. there is an `α ∈ E` such that `F⟮α⟯ = (⊤ : Subalgebra F E)`)
  if and only if there exist only finitely many intermediate fields between `E` and `F`. -/
theorem exists_primitive_element_iff_finite_intermediateField :
    (Algebra.IsAlgebraic F E ∧ ∃ α : E, F⟮α⟯ = ⊤) ↔ Finite (IntermediateField F E) :=
  ⟨fun ⟨halg, h⟩ ↦ finite_intermediateField_of_exists_primitive_element F E halg h,
    fun _ ↦ ⟨isAlgebraic_of_finite_intermediateField F E,
      exists_primitive_element_of_finite_intermediateField F E⟩⟩

end FiniteIntermediateField

end Field

@[simp]
theorem AlgHom.card (F E K : Type*) [Field F] [Field E] [Field K] [IsAlgClosed K] [Algebra F E]
    [FiniteDimensional F E] [IsSeparable F E] [Algebra F K] :
    Fintype.card (E →ₐ[F] K) = finrank F E := by
  convert (AlgHom.card_of_powerBasis (L := K) (Field.powerBasisOfFiniteOfSeparable F E)
    (IsSeparable.separable _ _) (IsAlgClosed.splits_codomain _)).trans (PowerBasis.finrank _).symm
#align alg_hom.card AlgHom.card
