/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Thomas Browning, Patrick Lutz
-/
import Mathlib.FieldTheory.Extension
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.GroupTheory.Solvable

#align_import field_theory.normal from "leanprover-community/mathlib"@"9fb8964792b4237dac6200193a0d533f1b3f7423"

/-!
# Normal field extensions

In this file we define normal field extensions and prove that for a finite extension, being normal
is the same as being a splitting field (`Normal.of_isSplittingField` and
`Normal.exists_isSplittingField`).

## Main Definitions

- `Normal F K` where `K` is a field extension of `F`.
-/


noncomputable section

open scoped Classical Polynomial

open Polynomial IsScalarTower

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

/-- Typeclass for normal field extension: `K` is a normal extension of `F` iff the minimal
polynomial of every element `x` in `K` splits in `K`, i.e. every conjugate of `x` is in `K`. -/
class Normal extends Algebra.IsAlgebraic F K : Prop where
  splits' (x : K) : Splits (algebraMap F K) (minpoly F x)
#align normal Normal

variable {F K}

theorem Normal.isIntegral (_ : Normal F K) (x : K) : IsIntegral F x :=
  Algebra.IsIntegral.isIntegral x
#align normal.is_integral Normal.isIntegral

theorem Normal.splits (_ : Normal F K) (x : K) : Splits (algebraMap F K) (minpoly F x) :=
  Normal.splits' x
#align normal.splits Normal.splits

theorem normal_iff : Normal F K ↔ ∀ x : K, IsIntegral F x ∧ Splits (algebraMap F K) (minpoly F x) :=
  ⟨fun h x => ⟨h.isIntegral x, h.splits x⟩, fun h =>
    { isAlgebraic := fun x => (h x).1.isAlgebraic
      splits' := fun x => (h x).2 }⟩
#align normal_iff normal_iff

theorem Normal.out : Normal F K → ∀ x : K, IsIntegral F x ∧ Splits (algebraMap F K) (minpoly F x) :=
  normal_iff.1
#align normal.out Normal.out

variable (F K)

instance normal_self : Normal F F where
  isAlgebraic := fun _ => isIntegral_algebraMap.isAlgebraic
  splits' := fun x => (minpoly.eq_X_sub_C' x).symm ▸ splits_X_sub_C _
#align normal_self normal_self

theorem Normal.exists_isSplittingField [h : Normal F K] [FiniteDimensional F K] :
    ∃ p : F[X], IsSplittingField F K p := by
  let s := Basis.ofVectorSpace F K
  refine
    ⟨∏ x, minpoly F (s x), splits_prod _ fun x _ => h.splits (s x),
      Subalgebra.toSubmodule.injective ?_⟩
  rw [Algebra.top_toSubmodule, eq_top_iff, ← s.span_eq, Submodule.span_le, Set.range_subset_iff]
  refine fun x =>
    Algebra.subset_adjoin
      (Multiset.mem_toFinset.mpr <|
        (mem_roots <|
              mt (Polynomial.map_eq_zero <| algebraMap F K).1 <|
                Finset.prod_ne_zero_iff.2 fun x _ => ?_).2 ?_)
  · exact minpoly.ne_zero (h.isIntegral (s x))
  rw [IsRoot.def, eval_map, ← aeval_def, AlgHom.map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ _) (minpoly.aeval _ _)
#align normal.exists_is_splitting_field Normal.exists_isSplittingField

section NormalTower

variable (E : Type*) [Field E] [Algebra F E] [Algebra K E] [IsScalarTower F K E]

theorem Normal.tower_top_of_normal [h : Normal F E] : Normal K E :=
  normal_iff.2 fun x => by
    cases' h.out x with hx hhx
    rw [algebraMap_eq F K E] at hhx
    exact
      ⟨hx.tower_top,
        Polynomial.splits_of_splits_of_dvd (algebraMap K E)
          (Polynomial.map_ne_zero (minpoly.ne_zero hx))
          ((Polynomial.splits_map_iff (algebraMap F K) (algebraMap K E)).mpr hhx)
          (minpoly.dvd_map_of_isScalarTower F K x)⟩
#align normal.tower_top_of_normal Normal.tower_top_of_normal

theorem AlgHom.normal_bijective [h : Normal F E] (ϕ : E →ₐ[F] K) : Function.Bijective ϕ :=
  h.toIsAlgebraic.bijective_of_isScalarTower' ϕ
#align alg_hom.normal_bijective AlgHom.normal_bijective

-- Porting note: `[Field F] [Field E] [Algebra F E]` added by hand.
variable {F E} {E' : Type*} [Field F] [Field E] [Algebra F E] [Field E'] [Algebra F E']

theorem Normal.of_algEquiv [h : Normal F E] (f : E ≃ₐ[F] E') : Normal F E' := by
  rw [normal_iff] at h ⊢
  intro x; specialize h (f.symm x)
  rw [← f.apply_symm_apply x, minpoly.algEquiv_eq, ← f.toAlgHom.comp_algebraMap]
  exact ⟨h.1.map f, splits_comp_of_splits _ _ h.2⟩
#align normal.of_alg_equiv Normal.of_algEquiv

theorem AlgEquiv.transfer_normal (f : E ≃ₐ[F] E') : Normal F E ↔ Normal F E' :=
  ⟨fun _ ↦ Normal.of_algEquiv f, fun _ ↦ Normal.of_algEquiv f.symm⟩
#align alg_equiv.transfer_normal AlgEquiv.transfer_normal

open IntermediateField

theorem Normal.of_isSplittingField (p : F[X]) [hFEp : IsSplittingField F E p] : Normal F E := by
  rcases eq_or_ne p 0 with (rfl | hp)
  · have := hFEp.adjoin_rootSet
    rw [rootSet_zero, Algebra.adjoin_empty] at this
    exact Normal.of_algEquiv
      (AlgEquiv.ofBijective (Algebra.ofId F E) (Algebra.bijective_algebraMap_iff.2 this.symm))
  refine normal_iff.mpr fun x ↦ ?_
  haveI : FiniteDimensional F E := IsSplittingField.finiteDimensional E p
  have hx := IsIntegral.of_finite F x
  let L := (p * minpoly F x).SplittingField
  have hL := splits_of_splits_mul' _ ?_ (SplittingField.splits (p * minpoly F x))
  · let j : E →ₐ[F] L := IsSplittingField.lift E p hL.1
    refine ⟨hx, splits_of_comp _ (j : E →+* L) (j.comp_algebraMap ▸ hL.2) fun a ha ↦ ?_⟩
    rw [j.comp_algebraMap] at ha
    letI : Algebra F⟮x⟯ L := ((algHomAdjoinIntegralEquiv F hx).symm ⟨a, ha⟩).toRingHom.toAlgebra
    let j' : E →ₐ[F⟮x⟯] L := IsSplittingField.lift E (p.map (algebraMap F F⟮x⟯)) ?_
    · change a ∈ j.range
      rw [← IsSplittingField.adjoin_rootSet_eq_range E p j,
            IsSplittingField.adjoin_rootSet_eq_range E p (j'.restrictScalars F)]
      exact ⟨x, (j'.commutes _).trans (algHomAdjoinIntegralEquiv_symm_apply_gen F hx _)⟩
    · rw [splits_map_iff, ← IsScalarTower.algebraMap_eq]; exact hL.1
  · rw [Polynomial.map_ne_zero_iff (algebraMap F L).injective, mul_ne_zero_iff]
    exact ⟨hp, minpoly.ne_zero hx⟩
#align normal.of_is_splitting_field Normal.of_isSplittingField

instance Polynomial.SplittingField.instNormal (p : F[X]) : Normal F p.SplittingField :=
  Normal.of_isSplittingField p
#align polynomial.splitting_field.normal Polynomial.SplittingField.instNormal

end NormalTower

namespace IntermediateField

/-- A compositum of normal extensions is normal -/
instance normal_iSup {ι : Type*} (t : ι → IntermediateField F K) [h : ∀ i, Normal F (t i)] :
    Normal F (⨆ i, t i : IntermediateField F K) := by
  refine { toIsAlgebraic := isAlgebraic_iSup fun i => (h i).1, splits' := fun x => ?_ }
  obtain ⟨s, hx⟩ := exists_finset_of_mem_supr'' (fun i => (h i).1) x.2
  let E : IntermediateField F K := ⨆ i ∈ s, adjoin F ((minpoly F (i.2 : _)).rootSet K)
  have hF : Normal F E := by
    haveI : IsSplittingField F E (∏ i ∈ s, minpoly F i.snd) := by
      refine isSplittingField_iSup ?_ fun i _ => adjoin_rootSet_isSplittingField ?_
      · exact Finset.prod_ne_zero_iff.mpr fun i _ => minpoly.ne_zero ((h i.1).isIntegral i.2)
      · exact Polynomial.splits_comp_of_splits _ (algebraMap (t i.1) K) ((h i.1).splits i.2)
    apply Normal.of_isSplittingField (∏ i ∈ s, minpoly F i.2)
  have hE : E ≤ ⨆ i, t i := by
    refine iSup_le fun i => iSup_le fun _ => le_iSup_of_le i.1 ?_
    rw [adjoin_le_iff, ← image_rootSet ((h i.1).splits i.2) (t i.1).val]
    exact fun _ ⟨a, _, h⟩ => h ▸ a.2
  have := hF.splits ⟨x, hx⟩
  rw [minpoly_eq, Subtype.coe_mk, ← minpoly_eq] at this
  exact Polynomial.splits_comp_of_splits _ (inclusion hE).toRingHom this
#align intermediate_field.normal_supr IntermediateField.normal_iSup

/-- If a set of algebraic elements in a field extension `K/F` have minimal polynomials that
  split in another extension `L/F`, then all minimal polynomials in the intermediate field
  generated by the set also split in `L/F`. -/
theorem splits_of_mem_adjoin {L} [Field L] [Algebra F L] {S : Set K}
    (splits : ∀ x ∈ S, IsIntegral F x ∧ (minpoly F x).Splits (algebraMap F L)) {x : K}
    (hx : x ∈ adjoin F S) : (minpoly F x).Splits (algebraMap F L) := by
  let E : IntermediateField F L := ⨆ x : S, adjoin F ((minpoly F x.val).rootSet L)
  have normal : Normal F E := normal_iSup (h := fun x ↦
    Normal.of_isSplittingField (hFEp := adjoin_rootSet_isSplittingField (splits x x.2).2))
  have : ∀ x ∈ S, (minpoly F x).Splits (algebraMap F E) := fun x hx ↦ splits_of_splits
    (splits x hx).2 fun y hy ↦ (le_iSup _ ⟨x, hx⟩ : _ ≤ E) (subset_adjoin F _ <| by exact hy)
  obtain ⟨φ⟩ := nonempty_algHom_adjoin_of_splits fun x hx ↦ ⟨(splits x hx).1, this x hx⟩
  convert splits_comp_of_splits _ E.val.toRingHom (normal.splits <| φ ⟨x, hx⟩)
  rw [minpoly.algHom_eq _ φ.injective, ← minpoly.algHom_eq _ (adjoin F S).val.injective, val_mk]

instance normal_sup
    (E E' : IntermediateField F K) [Normal F E] [Normal F E'] :
    Normal F (E ⊔ E' : IntermediateField F K) :=
  iSup_bool_eq (f := Bool.rec E' E) ▸ normal_iSup (h := by rintro (_|_) <;> infer_instance)

-- Porting note `[Field F] [Field K] [Algebra F K]` added by hand.
variable {F K} {L : Type*} [Field F] [Field K] [Field L] [Algebra F L] [Algebra K L]
  [Algebra F K] [IsScalarTower F K L]

@[simp]
theorem restrictScalars_normal {E : IntermediateField K L} :
    Normal F (E.restrictScalars F) ↔ Normal F E :=
  Iff.rfl
#align intermediate_field.restrict_scalars_normal IntermediateField.restrictScalars_normal

end IntermediateField

-- Porting note `[Field F]` added by hand.
variable {F} {K} {K₁ K₂ K₃ : Type*} [Field F] [Field K₁] [Field K₂] [Field K₃] [Algebra F K₁]
  [Algebra F K₂] [Algebra F K₃] (ϕ : K₁ →ₐ[F] K₂) (χ : K₁ ≃ₐ[F] K₂) (ψ : K₂ →ₐ[F] K₃)
  (ω : K₂ ≃ₐ[F] K₃)

section Restrict

variable (E : Type*) [Field E] [Algebra F E] [Algebra E K₁] [Algebra E K₂] [Algebra E K₃]
  [IsScalarTower F E K₁] [IsScalarTower F E K₂] [IsScalarTower F E K₃]

/-- Restrict algebra homomorphism to image of normal subfield -/
def AlgHom.restrictNormalAux [h : Normal F E] :
    (toAlgHom F E K₁).range →ₐ[F] (toAlgHom F E K₂).range where
  toFun x :=
    ⟨ϕ x, by
      suffices (toAlgHom F E K₁).range.map ϕ ≤ _ by exact this ⟨x, Subtype.mem x, rfl⟩
      rintro x ⟨y, ⟨z, hy⟩, hx⟩
      rw [← hx, ← hy]
      apply minpoly.mem_range_of_degree_eq_one E
      refine
        Or.resolve_left (h.splits z).def (minpoly.ne_zero (h.isIntegral z)) (minpoly.irreducible ?_)
          (minpoly.dvd E _ (by simp [aeval_algHom_apply]))
      simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
      suffices IsIntegral F _ by exact this.tower_top
      exact ((h.isIntegral z).map <| toAlgHom F E K₁).map ϕ⟩
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

/-- Restrict algebra homomorphism to normal subfield (`AlgEquiv` version) -/
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
    (algebraMap E K₃).injective (by simp only [AlgHom.comp_apply, AlgHom.restrictNormal_commutes])
#align alg_hom.restrict_normal_comp AlgHom.restrictNormal_comp

-- Porting note `[Algebra F K]` added by hand.
theorem AlgHom.fieldRange_of_normal [Algebra F K] {E : IntermediateField F K} [Normal F E]
    (f : E →ₐ[F] K) : f.fieldRange = E := by
-- Porting note: this was `IsScalarTower F E E := by infer_instance`.
  letI : Algebra E E := Algebra.id E
  let g := f.restrictNormal' E
  rw [← show E.val.comp ↑g = f from DFunLike.ext_iff.mpr (f.restrictNormal_commutes E),
    ← AlgHom.map_fieldRange, AlgEquiv.fieldRange_eq_top g, ← AlgHom.fieldRange_eq_map,
    IntermediateField.fieldRange_val]
#align alg_hom.field_range_of_normal AlgHom.fieldRange_of_normal

/-- Restrict algebra isomorphism to a normal subfield -/
def AlgEquiv.restrictNormal [Normal F E] : E ≃ₐ[F] E :=
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
    (algebraMap E K₃).injective
      (by simp only [AlgEquiv.trans_apply, AlgEquiv.restrictNormal_commutes])
#align alg_equiv.restrict_normal_trans AlgEquiv.restrictNormal_trans

/-- Restriction to a normal subfield as a group homomorphism -/
def AlgEquiv.restrictNormalHom [Normal F E] : (K₁ ≃ₐ[F] K₁) →* E ≃ₐ[F] E :=
  MonoidHom.mk' (fun χ => χ.restrictNormal E) fun ω χ => χ.restrictNormal_trans ω E
#align alg_equiv.restrict_normal_hom AlgEquiv.restrictNormalHom

variable (F K₁)

/-- If `K₁/E/F` is a tower of fields with `E/F` normal then `AlgHom.restrictNormal'` is an
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

variable (E : Type*) [Field E] [Algebra F E] [Algebra K₁ E] [Algebra K₂ E] [IsScalarTower F K₁ E]
  [IsScalarTower F K₂ E]

/-- If `E/Kᵢ/F` are towers of fields with `E/F` normal then we can lift
  an algebra homomorphism `ϕ : K₁ →ₐ[F] K₂` to `ϕ.liftNormal E : E →ₐ[F] E`. -/
noncomputable def AlgHom.liftNormal [h : Normal F E] : E →ₐ[F] E :=
  @AlgHom.restrictScalars F K₁ E E _ _ _ _ _ _
      ((IsScalarTower.toAlgHom F K₂ E).comp ϕ).toRingHom.toAlgebra _ _ _ _ <|
    Nonempty.some <|
      @IntermediateField.nonempty_algHom_of_adjoin_splits _ _ _ _ _ _ _
        ((IsScalarTower.toAlgHom F K₂ E).comp ϕ).toRingHom.toAlgebra _
        (fun x _ ↦ ⟨(h.out x).1.tower_top,
          splits_of_splits_of_dvd _ (map_ne_zero (minpoly.ne_zero (h.out x).1))
            -- Porting note: had to override typeclass inference below using `(_)`
            (by rw [splits_map_iff, ← @IsScalarTower.algebraMap_eq _ _ _ _ _ _ (_) (_) (_)];
                exact (h.out x).2)
            (minpoly.dvd_map_of_isScalarTower F K₁ x)⟩)
        (IntermediateField.adjoin_univ _ _)
#align alg_hom.lift_normal AlgHom.liftNormal

@[simp]
theorem AlgHom.liftNormal_commutes [Normal F E] (x : K₁) :
    ϕ.liftNormal E (algebraMap K₁ E x) = algebraMap K₂ E (ϕ x) :=
  -- Porting note: This seems to have been some sort of typeclass override trickery using `by apply`
  -- Now we explicitly specify which typeclass to override, using `(_)` instead of `_`
  @AlgHom.commutes K₁ E E _ _ _ _ (_) _ _
#align alg_hom.lift_normal_commutes AlgHom.liftNormal_commutes

@[simp]
theorem AlgHom.restrict_liftNormal (ϕ : K₁ →ₐ[F] K₁) [Normal F K₁] [Normal F E] :
    (ϕ.liftNormal E).restrictNormal K₁ = ϕ :=
  AlgHom.ext fun x =>
    (algebraMap K₁ E).injective
      (Eq.trans (AlgHom.restrictNormal_commutes _ K₁ x) (ϕ.liftNormal_commutes E x))
#align alg_hom.restrict_lift_normal AlgHom.restrict_liftNormal

/-- If `E/Kᵢ/F` are towers of fields with `E/F` normal then we can lift
  an algebra isomorphism `ϕ : K₁ ≃ₐ[F] K₂` to `ϕ.liftNormal E : E ≃ₐ[F] E`. -/
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
    (algebraMap K₁ E).injective
      (Eq.trans (AlgEquiv.restrictNormal_commutes _ K₁ x) (χ.liftNormal_commutes E x))
#align alg_equiv.restrict_lift_normal AlgEquiv.restrict_liftNormal

theorem AlgEquiv.restrictNormalHom_surjective [Normal F K₁] [Normal F E] :
    Function.Surjective (AlgEquiv.restrictNormalHom K₁ : (E ≃ₐ[F] E) → K₁ ≃ₐ[F] K₁) := fun χ =>
  ⟨χ.liftNormal E, χ.restrict_liftNormal E⟩
#align alg_equiv.restrict_normal_hom_surjective AlgEquiv.restrictNormalHom_surjective

open IntermediateField in
theorem Normal.minpoly_eq_iff_mem_orbit [h : Normal F E] {x y : E} :
    minpoly F x = minpoly F y ↔ x ∈ MulAction.orbit (E ≃ₐ[F] E) y := by
  refine ⟨fun he ↦ ?_, fun ⟨f, he⟩ ↦ he ▸ minpoly.algEquiv_eq f y⟩
  obtain ⟨φ, hφ⟩ := exists_algHom_of_splits_of_aeval (normal_iff.mp h) (he ▸ minpoly.aeval F x)
  exact ⟨AlgEquiv.ofBijective φ (φ.normal_bijective F E E), hφ⟩

variable (F K₁)

theorem isSolvable_of_isScalarTower [Normal F K₁] [h1 : IsSolvable (K₁ ≃ₐ[F] K₁)]
    [h2 : IsSolvable (E ≃ₐ[K₁] E)] : IsSolvable (E ≃ₐ[F] E) := by
  let f : (E ≃ₐ[K₁] E) →* E ≃ₐ[F] E :=
    { toFun := fun ϕ =>
        AlgEquiv.ofAlgHom (ϕ.toAlgHom.restrictScalars F) (ϕ.symm.toAlgHom.restrictScalars F)
          (AlgHom.ext fun x => ϕ.apply_symm_apply x) (AlgHom.ext fun x => ϕ.symm_apply_apply x)
      map_one' := AlgEquiv.ext fun _ => rfl
      map_mul' := fun _ _ => AlgEquiv.ext fun _ => rfl }
  refine
    solvable_of_ker_le_range f (AlgEquiv.restrictNormalHom K₁) fun ϕ hϕ =>
      ⟨{ ϕ with commutes' := fun x => ?_ }, AlgEquiv.ext fun _ => rfl⟩
  exact Eq.trans (ϕ.restrictNormal_commutes K₁ x).symm (congr_arg _ (AlgEquiv.ext_iff.mp hϕ x))
#align is_solvable_of_is_scalar_tower isSolvable_of_isScalarTower

end lift

namespace minpoly

variable {K L : Type _} [Field K] [Field L] [Algebra K L]

open AlgEquiv IntermediateField

/-- If `x : L` is a root of `minpoly K y`, then we can find `(σ : L ≃ₐ[K] L)` with `σ x = y`.
  That is, `x` and `y` are Galois conjugates. -/
theorem exists_algEquiv_of_root [Normal K L] {x y : L} (hy : IsAlgebraic K y)
    (h_ev : (Polynomial.aeval x) (minpoly K y) = 0) : ∃ σ : L ≃ₐ[K] L, σ x = y := by
  have hx : IsAlgebraic K x := ⟨minpoly K y, ne_zero hy.isIntegral, h_ev⟩
  set f : K⟮x⟯ ≃ₐ[K] K⟮y⟯ := algEquiv hx (eq_of_root hy h_ev)
  have hxy : (liftNormal f L) ((algebraMap (↥K⟮x⟯) L) (AdjoinSimple.gen K x)) = y := by
    rw [liftNormal_commutes f L, algEquiv_apply, AdjoinSimple.algebraMap_gen K y]
  exact ⟨(liftNormal f L), hxy⟩

/-- If `x : L` is a root of `minpoly K y`, then we can find `(σ : L ≃ₐ[K] L)` with `σ y = x`.
  That is, `x` and `y` are Galois conjugates. -/
theorem exists_algEquiv_of_root' [Normal K L]{x y : L} (hy : IsAlgebraic K y)
    (h_ev : (Polynomial.aeval x) (minpoly K y) = 0) : ∃ σ : L ≃ₐ[K] L, σ y = x := by
  obtain ⟨σ, hσ⟩ := exists_algEquiv_of_root hy h_ev
  use σ.symm
  rw [← hσ, symm_apply_apply]

end minpoly
