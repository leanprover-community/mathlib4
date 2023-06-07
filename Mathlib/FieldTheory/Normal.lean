/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Thomas Browning, Patrick Lutz

! This file was ported from Lean 3 source module field_theory.normal
! leanprover-community/mathlib commit df76f43357840485b9d04ed5dee5ab115d420e87
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.FieldTheory.Adjoin
import Mathlib.FieldTheory.Tower
import Mathlib.GroupTheory.Solvable
import Mathlib.RingTheory.PowerBasis

/-!
# Normal field extensions

In this file we define normal field extensions and prove that for a finite extension, being normal
is the same as being a splitting field (`normal.of_is_splitting_field` and
`normal.exists_is_splitting_field`).

## Main Definitions

- `normal F K` where `K` is a field extension of `F`.
-/


noncomputable section

open scoped BigOperators

open scoped Classical Polynomial

open Polynomial IsScalarTower

variable (F K : Type _) [Field F] [Field K] [Algebra F K]

/-- Typeclass for normal field extension: `K` is a normal extension of `F` iff the minimal
polynomial of every element `x` in `K` splits in `K`, i.e. every conjugate of `x` is in `K`. -/
class Normal : Prop where
  is_algebraic' : Algebra.IsAlgebraic F K
  splits' (x : K) : Splits (algebraMap F K) (minpoly F x)
#align normal Normal

variable {F K}

theorem Normal.isAlgebraic (h : Normal F K) (x : K) : IsAlgebraic F x :=
  Normal.is_algebraic' x
#align normal.is_algebraic Normal.isAlgebraic

theorem Normal.isIntegral (h : Normal F K) (x : K) : IsIntegral F x :=
  isAlgebraic_iff_isIntegral.mp (h.IsAlgebraic x)
#align normal.is_integral Normal.isIntegral

theorem Normal.splits (h : Normal F K) (x : K) : Splits (algebraMap F K) (minpoly F x) :=
  Normal.splits' x
#align normal.splits Normal.splits

theorem normal_iff : Normal F K ↔ ∀ x : K, IsIntegral F x ∧ Splits (algebraMap F K) (minpoly F x) :=
  ⟨fun h x => ⟨h.IsIntegral x, h.Splits x⟩, fun h =>
    ⟨fun x => (h x).1.IsAlgebraic F, fun x => (h x).2⟩⟩
#align normal_iff normal_iff

theorem Normal.out : Normal F K → ∀ x : K, IsIntegral F x ∧ Splits (algebraMap F K) (minpoly F x) :=
  normal_iff.1
#align normal.out Normal.out

variable (F K)

instance normal_self : Normal F F :=
  ⟨fun x => isIntegral_algebraMap.IsAlgebraic F, fun x =>
    (minpoly.eq_X_sub_C' x).symm ▸ splits_X_sub_C _⟩
#align normal_self normal_self

variable {K}

variable (K)

theorem Normal.exists_isSplittingField [h : Normal F K] [FiniteDimensional F K] :
    ∃ p : F[X], IsSplittingField F K p := by
  let s := Basis.ofVectorSpace F K
  refine'
    ⟨∏ x, minpoly F (s x), splits_prod _ fun x hx => h.splits (s x),
      subalgebra.to_submodule.injective _⟩
  rw [Algebra.top_toSubmodule, eq_top_iff, ← s.span_eq, Submodule.span_le, Set.range_subset_iff]
  refine' fun x =>
    Algebra.subset_adjoin
      (multiset.mem_to_finset.mpr <|
        (mem_roots <|
              mt (Polynomial.map_eq_zero <| algebraMap F K).1 <|
                Finset.prod_ne_zero_iff.2 fun x hx => _).2
          _)
  · exact minpoly.ne_zero (h.is_integral (s x))
  rw [is_root.def, eval_map, ← aeval_def, AlgHom.map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ _) (minpoly.aeval _ _)
#align normal.exists_is_splitting_field Normal.exists_isSplittingField

section NormalTower

variable (E : Type _) [Field E] [Algebra F E] [Algebra K E] [IsScalarTower F K E]

theorem Normal.tower_top_of_normal [h : Normal F E] : Normal K E :=
  normal_iff.2 fun x => by
    cases' h.out x with hx hhx
    rw [algebra_map_eq F K E] at hhx 
    exact
      ⟨isIntegral_of_isScalarTower hx,
        Polynomial.splits_of_splits_of_dvd (algebraMap K E)
          (Polynomial.map_ne_zero (minpoly.ne_zero hx))
          ((Polynomial.splits_map_iff (algebraMap F K) (algebraMap K E)).mpr hhx)
          (minpoly.dvd_map_of_isScalarTower F K x)⟩
#align normal.tower_top_of_normal Normal.tower_top_of_normal

theorem AlgHom.normal_bijective [h : Normal F E] (ϕ : E →ₐ[F] K) : Function.Bijective ϕ :=
  ⟨ϕ.toRingHom.Injective, fun x => by
    letI : Algebra E K := ϕ.to_ring_hom.to_algebra
    obtain ⟨h1, h2⟩ := h.out (algebraMap K E x)
    cases'
      minpoly.mem_range_of_degree_eq_one E x
        (h2.def.resolve_left (minpoly.ne_zero h1)
          (minpoly.irreducible
            (isIntegral_of_isScalarTower
              ((isIntegral_algebraMap_iff (algebraMap K E).Injective).mp h1)))
          (minpoly.dvd E x
            ((algebraMap K E).Injective
              (by
                rw [RingHom.map_zero, aeval_map_algebra_map, ← aeval_algebra_map_apply]
                exact minpoly.aeval F (algebraMap K E x))))) with
      y hy
    exact ⟨y, hy⟩⟩
#align alg_hom.normal_bijective AlgHom.normal_bijective

variable {F} {E} {E' : Type _} [Field E'] [Algebra F E']

theorem Normal.of_algEquiv [h : Normal F E] (f : E ≃ₐ[F] E') : Normal F E' :=
  normal_iff.2 fun x => by
    cases' h.out (f.symm x) with hx hhx
    have H := map_isIntegral f.to_alg_hom hx
    rw [AlgEquiv.toAlgHom_eq_coe, AlgEquiv.coe_algHom, AlgEquiv.apply_symm_apply] at H 
    use H
    apply Polynomial.splits_of_splits_of_dvd (algebraMap F E') (minpoly.ne_zero hx)
    · rw [← AlgHom.comp_algebraMap f.to_alg_hom]
      exact Polynomial.splits_comp_of_splits (algebraMap F E) f.to_alg_hom.to_ring_hom hhx
    · apply minpoly.dvd _ _
      rw [← AddEquiv.map_eq_zero_iff f.symm.to_add_equiv]
      exact
        Eq.trans (Polynomial.aeval_algHom_apply f.symm.to_alg_hom x (minpoly F (f.symm x))).symm
          (minpoly.aeval _ _)
#align normal.of_alg_equiv Normal.of_algEquiv

theorem AlgEquiv.transfer_normal (f : E ≃ₐ[F] E') : Normal F E ↔ Normal F E' :=
  ⟨fun h => Normal.of_algEquiv f, fun h => Normal.of_algEquiv f.symm⟩
#align alg_equiv.transfer_normal AlgEquiv.transfer_normal

-- seems to be causing a diamond in the below proof
-- however, this may be a fluke and the proof below uses non-canonical `algebra` instances:
-- when I replaced all the instances inside the proof with the "canonical" instances we have,
-- I had the (unprovable) goal (of the form) `adjoin_root.mk f (C x) = adjoin_root.mk f X`
-- for some `x, f`. So maybe this is indeed the correct approach and rewriting this proof is
-- salient in the future, or at least taking a closer look at the algebra instances it uses.
attribute [-instance] AdjoinRoot.hasSmul

theorem Normal.of_isSplittingField (p : F[X]) [hFEp : IsSplittingField F E p] : Normal F E := by
  rcases eq_or_ne p 0 with (rfl | hp)
  · have := hFEp.adjoin_roots
    simp only [Polynomial.map_zero, roots_zero, Multiset.toFinset_zero, Finset.coe_empty,
      Algebra.adjoin_empty] at this 
    exact
      Normal.of_algEquiv
        (AlgEquiv.ofBijective (Algebra.ofId F E) (Algebra.bijective_algebraMap_iff.2 this.symm))
  refine' normal_iff.2 fun x => _
  have hFE : FiniteDimensional F E := is_splitting_field.finite_dimensional E p
  have Hx : IsIntegral F x := isIntegral_of_noetherian (IsNoetherian.iff_fg.2 hFE) x
  refine' ⟨Hx, Or.inr _⟩
  rintro q q_irred ⟨r, hr⟩
  let D := AdjoinRoot q
  haveI := Fact.mk q_irred
  let pbED := AdjoinRoot.powerBasis q_irred.ne_zero
  haveI : FiniteDimensional E D := PowerBasis.finiteDimensional pbED
  have finrankED : FiniteDimensional.finrank E D = q.nat_degree := by
    rw [PowerBasis.finrank pbED, AdjoinRoot.powerBasis_dim]
  haveI : FiniteDimensional F D := FiniteDimensional.trans F E D
  rsuffices ⟨ϕ⟩ : Nonempty (D →ₐ[F] E)
  · rw [← WithBot.coe_one, degree_eq_iff_nat_degree_eq q_irred.ne_zero, ← finrankED]
    have nat_lemma : ∀ a b c : ℕ, a * b = c → c ≤ a → 0 < c → b = 1 := by intro a b c h1 h2 h3;
      nlinarith
    exact
      nat_lemma _ _ _ (FiniteDimensional.finrank_mul_finrank F E D)
        (LinearMap.finrank_le_finrank_of_injective
          (show Function.Injective ϕ.to_linear_map from ϕ.to_ring_hom.injective))
        FiniteDimensional.finrank_pos
  let C := AdjoinRoot (minpoly F x)
  haveI Hx_irred := Fact.mk (minpoly.irreducible Hx)
  letI : Algebra C D :=
    RingHom.toAlgebra
      (AdjoinRoot.lift (algebraMap F D) (AdjoinRoot.root q)
        (by
          rw [algebra_map_eq F E D, ← eval₂_map, hr, AdjoinRoot.algebraMap_eq, eval₂_mul,
            AdjoinRoot.eval₂_root, MulZeroClass.zero_mul]))
  letI : Algebra C E := RingHom.toAlgebra (AdjoinRoot.lift (algebraMap F E) x (minpoly.aeval F x))
  haveI : IsScalarTower F C D := of_algebra_map_eq fun x => (AdjoinRoot.lift_of _).symm
  haveI : IsScalarTower F C E := of_algebra_map_eq fun x => (AdjoinRoot.lift_of _).symm
  suffices Nonempty (D →ₐ[C] E) by exact Nonempty.map (AlgHom.restrictScalars F) this
  let S : Set D := ((p.map (algebraMap F E)).roots.map (algebraMap E D)).toFinset
  suffices ⊤ ≤ IntermediateField.adjoin C S by
    refine' IntermediateField.algHom_mk_adjoin_splits' (top_le_iff.mp this) fun y hy => _
    rcases multiset.mem_map.mp (multiset.mem_to_finset.mp hy) with ⟨z, hz1, hz2⟩
    have Hz : IsIntegral F z := isIntegral_of_noetherian (IsNoetherian.iff_fg.2 hFE) z
    use
      show IsIntegral C y from
        isIntegral_of_noetherian (IsNoetherian.iff_fg.2 (FiniteDimensional.right F C D)) y
    apply splits_of_splits_of_dvd (algebraMap C E) (map_ne_zero (minpoly.ne_zero Hz))
    · rw [splits_map_iff, ← algebra_map_eq F C E]
      exact
        splits_of_splits_of_dvd _ hp hFEp.splits
          (minpoly.dvd F z (Eq.trans (eval₂_eq_eval_map _) ((mem_roots (map_ne_zero hp)).mp hz1)))
    · apply minpoly.dvd
      rw [← hz2, aeval_def, eval₂_map, ← algebra_map_eq F C D, algebra_map_eq F E D, ← hom_eval₂, ←
        aeval_def, minpoly.aeval F z, RingHom.map_zero]
  rw [← IntermediateField.toSubalgebra_le_toSubalgebra, IntermediateField.top_toSubalgebra]
  apply ge_trans (IntermediateField.algebra_adjoin_le_adjoin C S)
  suffices
    (Algebra.adjoin C S).restrictScalars F =
      (Algebra.adjoin E {AdjoinRoot.root q}).restrictScalars F by
    rw [AdjoinRoot.adjoinRoot_eq_top, Subalgebra.restrictScalars_top, ←
      @Subalgebra.restrictScalars_top F C] at this 
    exact top_le_iff.mpr (Subalgebra.restrictScalars_injective F this)
  dsimp only [S]
  rw [← Finset.image_toFinset, Finset.coe_image]
  apply
    Eq.trans
      (Algebra.adjoin_res_eq_adjoin_res F E C D hFEp.adjoin_roots AdjoinRoot.adjoinRoot_eq_top)
  rw [Set.image_singleton, RingHom.algebraMap_toAlgebra, AdjoinRoot.lift_root]
#align normal.of_is_splitting_field Normal.of_isSplittingField

end NormalTower

namespace IntermediateField

/-- A compositum of normal extensions is normal -/
instance normal_iSup {ι : Type _} (t : ι → IntermediateField F K) [h : ∀ i, Normal F (t i)] :
    Normal F (⨆ i, t i : IntermediateField F K) := by
  refine' ⟨is_algebraic_supr fun i => (h i).1, fun x => _⟩
  obtain ⟨s, hx⟩ := exists_finset_of_mem_supr'' (fun i => (h i).1) x.2
  let E : IntermediateField F K := ⨆ i ∈ s, adjoin F ((minpoly F (i.2 : _)).rootSet K)
  have hF : Normal F E := by
    apply Normal.of_isSplittingField (∏ i in s, minpoly F i.2)
    refine' is_splitting_field_supr _ fun i hi => adjoin_root_set_is_splitting_field _
    · exact finset.prod_ne_zero_iff.mpr fun i hi => minpoly.ne_zero ((h i.1).IsIntegral i.2)
    · exact Polynomial.splits_comp_of_splits _ (algebraMap (t i.1) K) ((h i.1).Splits i.2)
  have hE : E ≤ ⨆ i, t i := by
    refine' iSup_le fun i => iSup_le fun hi => le_iSup_of_le i.1 _
    rw [adjoin_le_iff, ← image_root_set ((h i.1).Splits i.2) (t i.1).val]
    exact fun _ ⟨a, _, h⟩ => h ▸ a.2
  have := hF.splits ⟨x, hx⟩
  rw [minpoly_eq, Subtype.coe_mk, ← minpoly_eq] at this 
  exact Polynomial.splits_comp_of_splits _ (inclusion hE).toRingHom this
#align intermediate_field.normal_supr IntermediateField.normal_iSup

variable {F K} {L : Type _} [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L]

@[simp]
theorem restrictScalars_normal {E : IntermediateField K L} :
    Normal F (E.restrictScalars F) ↔ Normal F E :=
  Iff.rfl
#align intermediate_field.restrict_scalars_normal IntermediateField.restrictScalars_normal

end IntermediateField

variable {F} {K} {K₁ K₂ K₃ : Type _} [Field K₁] [Field K₂] [Field K₃] [Algebra F K₁] [Algebra F K₂]
  [Algebra F K₃] (ϕ : K₁ →ₐ[F] K₂) (χ : K₁ ≃ₐ[F] K₂) (ψ : K₂ →ₐ[F] K₃) (ω : K₂ ≃ₐ[F] K₃)

section Restrict

variable (E : Type _) [Field E] [Algebra F E] [Algebra E K₁] [Algebra E K₂] [Algebra E K₃]
  [IsScalarTower F E K₁] [IsScalarTower F E K₂] [IsScalarTower F E K₃]

/-- Restrict algebra homomorphism to image of normal subfield -/
def AlgHom.restrictNormalAux [h : Normal F E] :
    (toAlgHom F E K₁).range →ₐ[F] (toAlgHom F E K₂).range where
  toFun x :=
    ⟨ϕ x, by
      suffices (to_alg_hom F E K₁).range.map ϕ ≤ _ by exact this ⟨x, Subtype.mem x, rfl⟩
      rintro x ⟨y, ⟨z, hy⟩, hx⟩
      rw [← hx, ← hy]
      apply minpoly.mem_range_of_degree_eq_one E
      refine'
        Or.resolve_left (h.splits z).def (minpoly.ne_zero (h.is_integral z)) (minpoly.irreducible _)
          (minpoly.dvd E _ (by simp [aeval_alg_hom_apply]))
      simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
      suffices IsIntegral F _ by exact isIntegral_of_isScalarTower this
      exact map_isIntegral ϕ (map_isIntegral (to_alg_hom F E K₁) (h.is_integral z))⟩
  map_zero' := Subtype.ext ϕ.map_zero
  map_one' := Subtype.ext ϕ.map_one
  map_add' x y := Subtype.ext (ϕ.map_add x y)
  map_mul' x y := Subtype.ext (ϕ.map_mul x y)
  commutes' x := Subtype.ext (ϕ.commutes x)
#align alg_hom.restrict_normal_aux AlgHom.restrictNormalAux

/-- Restrict algebra homomorphism to normal subfield -/
def AlgHom.restrictNormal [Normal F E] : E →ₐ[F] E :=
  ((AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F E K₂)).symm.toAlgHom.comp
        (ϕ.restrictNormalAux E)).comp
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F E K₁)).toAlgHom
#align alg_hom.restrict_normal AlgHom.restrictNormal

/-- Restrict algebra homomorphism to normal subfield (`alg_equiv` version) -/
def AlgHom.restrictNormal' [Normal F E] : E ≃ₐ[F] E :=
  AlgEquiv.ofBijective (AlgHom.restrictNormal ϕ E) (AlgHom.normal_bijective F E E _)
#align alg_hom.restrict_normal' AlgHom.restrictNormal'

@[simp]
theorem AlgHom.restrictNormal_commutes [Normal F E] (x : E) :
    algebraMap E K₂ (ϕ.restrictNormal E x) = ϕ (algebraMap E K₁ x) :=
  Subtype.ext_iff.mp
    (AlgEquiv.apply_symm_apply (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F E K₂))
      (ϕ.restrictNormalAux E ⟨IsScalarTower.toAlgHom F E K₁ x, x, rfl⟩))
#align alg_hom.restrict_normal_commutes AlgHom.restrictNormal_commutes

theorem AlgHom.restrictNormal_comp [Normal F E] :
    (ψ.restrictNormal E).comp (ϕ.restrictNormal E) = (ψ.comp ϕ).restrictNormal E :=
  AlgHom.ext fun _ =>
    (algebraMap E K₃).Injective (by simp only [AlgHom.comp_apply, AlgHom.restrictNormal_commutes])
#align alg_hom.restrict_normal_comp AlgHom.restrictNormal_comp

theorem AlgHom.fieldRange_of_normal {E : IntermediateField F K} [Normal F E] (f : E →ₐ[F] K) :
    f.fieldRange = E := by
  haveI : IsScalarTower F E E := by infer_instance
  let g := f.restrict_normal' E
  rw [← show E.val.comp ↑g = f from fun_like.ext_iff.mpr (f.restrict_normal_commutes E), ←
    AlgHom.map_fieldRange, g.field_range_eq_top, ← E.val.field_range_eq_map, E.field_range_val]
#align alg_hom.field_range_of_normal AlgHom.fieldRange_of_normal

/-- Restrict algebra isomorphism to a normal subfield -/
def AlgEquiv.restrictNormal [h : Normal F E] : E ≃ₐ[F] E :=
  AlgHom.restrictNormal' χ.toAlgHom E
#align alg_equiv.restrict_normal AlgEquiv.restrictNormal

@[simp]
theorem AlgEquiv.restrictNormal_commutes [Normal F E] (x : E) :
    algebraMap E K₂ (χ.restrictNormal E x) = χ (algebraMap E K₁ x) :=
  χ.toAlgHom.restrictNormal_commutes E x
#align alg_equiv.restrict_normal_commutes AlgEquiv.restrictNormal_commutes

theorem AlgEquiv.restrictNormal_trans [Normal F E] :
    (χ.trans ω).restrictNormal E = (χ.restrictNormal E).trans (ω.restrictNormal E) :=
  AlgEquiv.ext fun _ =>
    (algebraMap E K₃).Injective
      (by simp only [AlgEquiv.trans_apply, AlgEquiv.restrictNormal_commutes])
#align alg_equiv.restrict_normal_trans AlgEquiv.restrictNormal_trans

/-- Restriction to an normal subfield as a group homomorphism -/
def AlgEquiv.restrictNormalHom [Normal F E] : (K₁ ≃ₐ[F] K₁) →* E ≃ₐ[F] E :=
  MonoidHom.mk' (fun χ => χ.restrictNormal E) fun ω χ => χ.restrictNormal_trans ω E
#align alg_equiv.restrict_normal_hom AlgEquiv.restrictNormalHom

variable (F K₁ E)

/-- If `K₁/E/F` is a tower of fields with `E/F` normal then `normal.alg_hom_equiv_aut` is an
 equivalence. -/
@[simps]
def Normal.algHomEquivAut [Normal F E] : (E →ₐ[F] K₁) ≃ E ≃ₐ[F] E where
  toFun σ := AlgHom.restrictNormal' σ E
  invFun σ := (IsScalarTower.toAlgHom F E K₁).comp σ.toAlgHom
  left_inv σ := by
    ext
    simp [AlgHom.restrictNormal']
  right_inv σ := by
    ext
    simp only [AlgHom.restrictNormal', AlgEquiv.toAlgHom_eq_coe, AlgEquiv.coe_ofBijective]
    apply NoZeroSMulDivisors.algebraMap_injective E K₁
    rw [AlgHom.restrictNormal_commutes]
    simp
#align normal.alg_hom_equiv_aut Normal.algHomEquivAut

end Restrict

section lift

variable {F} {K₁ K₂} (E : Type _) [Field E] [Algebra F E] [Algebra K₁ E] [Algebra K₂ E]
  [IsScalarTower F K₁ E] [IsScalarTower F K₂ E]

/-- If `E/Kᵢ/F` are towers of fields with `E/F` normal then we can lift
  an algebra homomorphism `ϕ : K₁ →ₐ[F] K₂` to `ϕ.lift_normal E : E →ₐ[F] E`. -/
noncomputable def AlgHom.liftNormal [h : Normal F E] : E →ₐ[F] E :=
  @AlgHom.restrictScalars F K₁ E E _ _ _ _ _ _
      ((IsScalarTower.toAlgHom F K₂ E).comp ϕ).toRingHom.toAlgebra _ _ _ _ <|
    Nonempty.some <|
      @IntermediateField.algHom_mk_adjoin_splits' _ _ _ _ _ _ _
        ((IsScalarTower.toAlgHom F K₂ E).comp ϕ).toRingHom.toAlgebra _
        (IntermediateField.adjoin_univ _ _) fun x hx =>
        ⟨isIntegral_of_isScalarTower (h.out x).1,
          splits_of_splits_of_dvd _ (map_ne_zero (minpoly.ne_zero (h.out x).1))
            (by rw [splits_map_iff, ← IsScalarTower.algebraMap_eq]; exact (h.out x).2)
            (minpoly.dvd_map_of_isScalarTower F K₁ x)⟩
#align alg_hom.lift_normal AlgHom.liftNormal

@[simp]
theorem AlgHom.liftNormal_commutes [Normal F E] (x : K₁) :
    ϕ.liftNormal E (algebraMap K₁ E x) = algebraMap K₂ E (ϕ x) := by
  apply @AlgHom.commutes K₁ E E _ _ _ _
#align alg_hom.lift_normal_commutes AlgHom.liftNormal_commutes

@[simp]
theorem AlgHom.restrict_liftNormal (ϕ : K₁ →ₐ[F] K₁) [Normal F K₁] [Normal F E] :
    (ϕ.liftNormal E).restrictNormal K₁ = ϕ :=
  AlgHom.ext fun x =>
    (algebraMap K₁ E).Injective
      (Eq.trans (AlgHom.restrictNormal_commutes _ K₁ x) (ϕ.liftNormal_commutes E x))
#align alg_hom.restrict_lift_normal AlgHom.restrict_liftNormal

/-- If `E/Kᵢ/F` are towers of fields with `E/F` normal then we can lift
  an algebra isomorphism `ϕ : K₁ ≃ₐ[F] K₂` to `ϕ.lift_normal E : E ≃ₐ[F] E`. -/
noncomputable def AlgEquiv.liftNormal [Normal F E] : E ≃ₐ[F] E :=
  AlgEquiv.ofBijective (χ.toAlgHom.liftNormal E) (AlgHom.normal_bijective F E E _)
#align alg_equiv.lift_normal AlgEquiv.liftNormal

@[simp]
theorem AlgEquiv.liftNormal_commutes [Normal F E] (x : K₁) :
    χ.liftNormal E (algebraMap K₁ E x) = algebraMap K₂ E (χ x) :=
  χ.toAlgHom.liftNormal_commutes E x
#align alg_equiv.lift_normal_commutes AlgEquiv.liftNormal_commutes

@[simp]
theorem AlgEquiv.restrict_liftNormal (χ : K₁ ≃ₐ[F] K₁) [Normal F K₁] [Normal F E] :
    (χ.liftNormal E).restrictNormal K₁ = χ :=
  AlgEquiv.ext fun x =>
    (algebraMap K₁ E).Injective
      (Eq.trans (AlgEquiv.restrictNormal_commutes _ K₁ x) (χ.liftNormal_commutes E x))
#align alg_equiv.restrict_lift_normal AlgEquiv.restrict_liftNormal

theorem AlgEquiv.restrictNormalHom_surjective [Normal F K₁] [Normal F E] :
    Function.Surjective (AlgEquiv.restrictNormalHom K₁ : (E ≃ₐ[F] E) → K₁ ≃ₐ[F] K₁) := fun χ =>
  ⟨χ.liftNormal E, χ.restrict_liftNormal E⟩
#align alg_equiv.restrict_normal_hom_surjective AlgEquiv.restrictNormalHom_surjective

variable (F) (K₁) (E)

theorem isSolvable_of_isScalarTower [Normal F K₁] [h1 : IsSolvable (K₁ ≃ₐ[F] K₁)]
    [h2 : IsSolvable (E ≃ₐ[K₁] E)] : IsSolvable (E ≃ₐ[F] E) := by
  let f : (E ≃ₐ[K₁] E) →* E ≃ₐ[F] E :=
    { toFun := fun ϕ =>
        AlgEquiv.ofAlgHom (ϕ.to_alg_hom.restrict_scalars F) (ϕ.symm.to_alg_hom.restrict_scalars F)
          (AlgHom.ext fun x => ϕ.apply_symm_apply x) (AlgHom.ext fun x => ϕ.symm_apply_apply x)
      map_one' := AlgEquiv.ext fun _ => rfl
      map_mul' := fun _ _ => AlgEquiv.ext fun _ => rfl }
  refine'
    solvable_of_ker_le_range f (AlgEquiv.restrictNormalHom K₁) fun ϕ hϕ =>
      ⟨{ ϕ with commutes' := fun x => _ }, AlgEquiv.ext fun _ => rfl⟩
  exact Eq.trans (ϕ.restrict_normal_commutes K₁ x).symm (congr_arg _ (alg_equiv.ext_iff.mp hϕ x))
#align is_solvable_of_is_scalar_tower isSolvable_of_isScalarTower

end lift

section normalClosure

open IntermediateField

variable (F K) (L : Type _) [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L]

/-- The normal closure of `K` in `L`. -/
noncomputable def normalClosure : IntermediateField K L :=
  { (⨆ f : K →ₐ[F] L, f.fieldRange).toSubfield with
    algebraMap_mem' := fun r =>
      le_iSup (fun f : K →ₐ[F] L => f.fieldRange) (IsScalarTower.toAlgHom F K L) ⟨r, rfl⟩ }
#align normal_closure normalClosure

namespace normalClosure

theorem restrictScalars_eq_iSup_adjoin [h : Normal F L] :
    (normalClosure F K L).restrictScalars F = ⨆ x : K, adjoin F ((minpoly F x).rootSet L) := by
  refine' le_antisymm (iSup_le _) (iSup_le fun x => adjoin_le_iff.mpr fun y hy => _)
  · rintro f _ ⟨x, rfl⟩
    refine'
      le_iSup (fun x => adjoin F ((minpoly F x).rootSet L)) x
        (subset_adjoin F ((minpoly F x).rootSet L) _)
    rw [mem_root_set_of_ne, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    exact
      minpoly.ne_zero
        ((isIntegral_algebraMap_iff (algebraMap K L).Injective).mp
          (h.is_integral (algebraMap K L x)))
  · rw [Polynomial.rootSet, Finset.mem_coe, Multiset.mem_toFinset] at hy 
    let g :=
      (alg_hom_adjoin_integral_equiv F
            ((isIntegral_algebraMap_iff (algebraMap K L).Injective).mp
              (h.is_integral (algebraMap K L x)))).symm
        ⟨y, hy⟩
    refine'
      le_iSup (fun f : K →ₐ[F] L => f.fieldRange)
        ((g.lift_normal L).comp (IsScalarTower.toAlgHom F K L))
        ⟨x, (g.lift_normal_commutes L (adjoin_simple.gen F x)).trans _⟩
    rw [Algebra.id.map_eq_id, RingHom.id_apply]
    apply PowerBasis.lift_gen
#align normal_closure.restrict_scalars_eq_supr_adjoin normalClosure.restrictScalars_eq_iSup_adjoin

instance normal [h : Normal F L] : Normal F (normalClosure F K L) := by
  let ϕ := algebraMap K L
  rw [← IntermediateField.restrictScalars_normal, restrict_scalars_eq_supr_adjoin]
  apply IntermediateField.normal_iSup F L _
  intro x
  apply Normal.of_isSplittingField (minpoly F x)
  exact
    adjoin_root_set_is_splitting_field
      ((minpoly.eq_of_algebraMap_eq ϕ.injective
            ((isIntegral_algebraMap_iff ϕ.injective).mp (h.is_integral (ϕ x))) rfl).symm ▸
        h.splits _)
#align normal_closure.normal normalClosure.normal

instance is_finiteDimensional [FiniteDimensional F K] : FiniteDimensional F (normalClosure F K L) :=
  by
  haveI : ∀ f : K →ₐ[F] L, FiniteDimensional F f.fieldRange := fun f =>
    f.to_linear_map.finite_dimensional_range
  apply IntermediateField.finiteDimensional_iSup_of_finite
#align normal_closure.is_finite_dimensional normalClosure.is_finiteDimensional

instance isScalarTower : IsScalarTower F (normalClosure F K L) L :=
  IsScalarTower.subalgebra' F L L _
#align normal_closure.is_scalar_tower normalClosure.isScalarTower

end normalClosure

end normalClosure

