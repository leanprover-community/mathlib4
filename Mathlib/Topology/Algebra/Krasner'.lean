import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.Topology.Defs.Induced
import Mathlib.FieldTheory.Adjoin
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.RingTheory.Henselian
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Connected.Separation
import Mathlib.FieldTheory.Normal
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.Topology.Algebra.UniformField

import Mathlib.Topology.Algebra.KrasnerDependency

/-!
## TODO
1. uniform space eq -- no need
2. proof ‖z‖ = ‖z'‖ -- finished
3. add dictionary --
4. fill the version of valuations

5. Furthur change theorem like `Normal.minpoly_eq_iff_mem_orbit` using `IsConjRoot`

How to split into PRs? blocked by spectral Norm, Function extends, Valued,
application blocked by C_p
delete KrasnerNorm?

OutParam vR

If K is perfectoid field, K is algebraically closed iff K♭ is (not needed)
completion of alg closure is completed is needed

-/

open Polynomial minpoly IntermediateField

section conj

variable {R : Type*} {A : Type*} [CommRing R] [Ring A] [Algebra R A]

variable (K : Type*) {L : Type*} {ΓK ΓL : outParam Type*}
    [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓL]
    [Field K] [Field L] [Algebra K L] [vK : Valued K ΓK] [vL : Valued L ΓL]

variable (R) in
def IsConjRoot (x x' : A) : Prop := (minpoly R x) = (minpoly R x')
-- Galois action

namespace IsConjRoot

theorem refl {x : A} : IsConjRoot R x x := rfl

theorem symm {x x' : A} (h : IsConjRoot R x x') : IsConjRoot R x' x := Eq.symm h

theorem trans {x x' x'': A} (h₁ : IsConjRoot R x x') (h₂ : IsConjRoot R x' x'') :
    IsConjRoot R x x'' := Eq.trans h₁ h₂

theorem of_minpoly_eq {x x' : A} (h : minpoly R x = minpoly R x') : IsConjRoot R x x' := h

theorem algEquiv_apply (x : A) (s : A ≃ₐ[R] A) : IsConjRoot R x (s x) :=
  Eq.symm (minpoly.algEquiv_eq s x)

theorem algEquiv_apply₂ (x : A) (s₁ s₂ : A ≃ₐ[R] A) : IsConjRoot R (s₁ x) (s₂ x) :=
  of_minpoly_eq <| (minpoly.algEquiv_eq s₂ x) ▸ (minpoly.algEquiv_eq s₁ x)

variable {K} in
theorem exist_algEquiv [Normal K L] {x x': L} (h : IsConjRoot K x x') :
    ∃ σ : L ≃ₐ[K] L, x' = σ x := by
  obtain ⟨σ, hσ⟩ :=
    exists_algHom_of_splits_of_aeval (normal_iff.mp inferInstance) (h ▸ minpoly.aeval K x')
  exact ⟨AlgEquiv.ofBijective σ (σ.normal_bijective _ _ _), hσ.symm⟩

variable {K} in
theorem not_mem_iff_exist_ne {x : L} (h : IsSeparable K x)
    (sp : (minpoly K x).Splits (algebraMap K L)) :
    x ∉ (⊥ : Subalgebra K L) ↔ ∃ x' : L, x ≠ x' ∧ IsConjRoot K x x' := sorry
-- `should decide what is the definition when both x, x' are trancendental over R`

variable (R) in
theorem of_isScalarTower {S : Type*} [CommRing S] [Algebra R S] [Algebra S A]
    [IsScalarTower R S A] {x x' : A} (h : IsConjRoot S x x') : IsConjRoot R x x' := sorry
-- minpoly.aeval_of_isScalarTower

-- isIntegral_algHom_iff
theorem algHom_iff {B} [Ring B] [Algebra R B] {x x' : A} (f : A →ₐ[R] B)
    (hf : Function.Injective f) :
  IsConjRoot R (f x) (f x') ↔ IsConjRoot R x x' := sorry

theorem add_algebraMap {x x' : A} (r : R) (h : IsConjRoot R x x') :
    IsConjRoot R (x + algebraMap R A r) (x' + algebraMap R A r) := sorry
-- minpoly.add_algebraMap
-- `should decide what is the definition when both x, x' are trancendental over R`

/-
theorem eq_of_degree_minpoly_eq_one {x x' : A} (h : IsConjRoot R x x')
    (g : degree (minpoly R x) = 1) : x = x' := by
  sorry

theorem eq_of_natDegree_minpoly_eq_one {x x' : A} (h : IsConjRoot R x x')
    (g : natDegree (minpoly R x) = 1) : x = x' := sorry

theorem eq_of_isConjRoot_algebraMap {r : R} {x : A} (h : IsConjRoot R x (algebraMap R A r)) :
    x = algebraMap R A r := sorry

theorem neg {x x' : A} (r : R) (h : IsConjRoot R x x') :  IsConjRoot R (-x) (-x') := sorry


theorem sub_algebraMap {x x' : A} (r : R) (h : IsConjRoot R x x') :
    IsConjRoot R (x - algebraMap R A r) (x' - algebraMap R A r) := sorry

theorem smul {x x' : A} (r : R) (h : IsConjRoot R x x') :  IsConjRoot R (r • x) (r • x') := sorry

variable {K} in
theorem isIntegral {x x' : L} (hx : IsIntegral K x) (h : IsConjRoot K x x') :
    IsIntegral K x' := by sorry

theorem iff_eq_zero {x : A} : IsConjRoot R 0 x ↔ x = 0 := sorry

theorem ne_zero {x x' : A} (hx : x ≠ 0) (h : IsConjRoot R x x') : x' ≠ 0 := sorry
-/
end IsConjRoot

end conj

section ContinuousSMul

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
    [TopologicalSpace L] [TopologicalRing L] (M : IntermediateField K L)

-- shortcut to avoid time out
instance : ContinuousSMul M L := Submonoid.continuousSMul

instance ContinuousSMul.instBotIntermediateField :
    ContinuousSMul (⊥ : IntermediateField K L) M :=
  Inducing.continuousSMul (X := L) (N := (⊥ : IntermediateField K L)) (Y := M)
    (M := (⊥ : IntermediateField K L)) inducing_subtype_val continuous_id rfl

end ContinuousSMul

section NormedField

instance instNormedSubfield {L : Type*} [NL : NormedField L] {M : Subfield L} : NormedField M := {
  M.toField with
  dist_eq := fun _ _ ↦ NL.dist_eq _ _
  norm_mul' := fun _ _ ↦ NL.norm_mul' _ _
}

instance instNormedIntermediateField {K L : Type*} [Field K] [NormedField L] [Algebra K L]
    {M : IntermediateField K L} : NormedField M :=
  inferInstanceAs (NormedField M.toSubfield)

end NormedField

section FunctionExtends

variable {R : Type*} [CommRing R]

theorem functionExtends_of_functionExtends_of_functionExtends {A} [CommRing A] [Algebra R A]
    {B : Type*} [Ring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B] {fR : R → ℝ}
    {fA : A → ℝ} {fB : B → ℝ} (h1 : FunctionExtends fR fA) (h2 : FunctionExtends fA fB) :
    FunctionExtends fR fB := by
  intro x
  calc
    fB ((algebraMap R B) x) = fA (algebraMap R A x) :=
      h2 _ ▸ IsScalarTower.algebraMap_apply R A B x ▸ rfl
    _ = fR x := h1 x

end FunctionExtends

section IntegralClosure

#check Subalgebra.isField_of_algebraic

-- not in mathlib, maximal algebraic extension
instance IntermediateField.algebraicClosure (K L : Type*) [Field K] [Field L] [Algebra K L]
    : IntermediateField K L where
  toSubalgebra := _root_.integralClosure K L
  inv_mem' x hx := Subalgebra.inv_mem_of_algebraic (x := ⟨x, hx⟩)
    (isAlgebraic_iff_isIntegral.mpr hx)

instance isIntegralClosureIntermediateFieldAlgebraicClosure (K L : Type*) [Field K] [Field L]
    [Algebra K L] : IsIntegralClosure (IntermediateField.algebraicClosure K L) K L :=
  inferInstanceAs (IsIntegralClosure (_root_.integralClosure K L) K L)

theorem Algebra.IsAlgebraic.of_isIntegralClosure (A R B : Type*)
    [Field R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B] [IsIntegralClosure A R B] : Algebra.IsAlgebraic R A :=
  Algebra.isAlgebraic_iff_isIntegral.mpr (IsIntegralClosure.isIntegral_algebra R B)

instance instIntermediateFieldAlgebraicClosureIsAlgebraic (K L : Type*) [Field K] [Field L]
    [Algebra K L] : Algebra.IsAlgebraic K (IntermediateField.algebraicClosure K L) :=
  Algebra.isAlgebraic_iff_isIntegral.mpr (IsIntegralClosure.isIntegral_algebra K L)

end IntegralClosure

section split

variable {A} [Field A]
theorem minpoly.add_algebraMap' {B : Type*} [CommRing B] [Algebra A B] {x : B}
    (a : A) : minpoly A (x + algebraMap A B a) = (minpoly A x).comp (X - C a) := by
  by_cases hx : IsIntegral A x
  · refine (minpoly.unique _ _ ((minpoly.monic hx).comp_X_sub_C _) ?_ fun q qmo hq => ?_).symm
    · simp [aeval_comp]
    · have : (Polynomial.aeval x) (q.comp (X + C a)) = 0 := by simpa [aeval_comp] using hq
      have H := minpoly.min A x (qmo.comp_X_add_C _) this
      rw [degree_eq_natDegree qmo.ne_zero,
        degree_eq_natDegree ((minpoly.monic hx).comp_X_sub_C _).ne_zero, natDegree_comp,
        natDegree_X_sub_C, mul_one]
      rwa [degree_eq_natDegree (minpoly.ne_zero hx),
        degree_eq_natDegree (qmo.comp_X_add_C _).ne_zero, natDegree_comp,
        natDegree_X_add_C, mul_one] at H
  · rw [minpoly.eq_zero hx, minpoly.eq_zero, zero_comp]
    refine fun h ↦ hx ?_
    simpa only [add_sub_cancel_right] using IsIntegral.sub h (isIntegral_algebraMap (x := a))

theorem Polynomial.dvd_comp_X_sub_C_iff {B : Type*} [CommRing B] {p q : Polynomial B} {a : B} :
    p ∣ q.comp (X - C a) ↔ p.comp (X + C a) ∣ q := by
  convert (map_dvd_iff <| algEquivAevalXAddC a).symm using 2
  rw [C_eq_algebraMap, algEquivAevalXAddC_apply, ← comp_eq_aeval]
  simp [comp_assoc]

theorem Polynomial.irreducible_comp

theorem Polynomial.splits_of_comp_X_sub_C {B : Type*} [Field B] [Algebra A B] (a : A) {p : Polynomial A}
    (h : p.Splits (algebraMap A B)) : (p.comp (X - C a)).Splits (algebraMap A B) := by
  cases h with
  | inl h0 =>
    left
    simp only [map_eq_zero] at h0 ⊢
    exact h0.symm ▸ zero_comp
  | inr h =>
    right
    intro g irr dvd
    rw [Polynomial.map_comp] at dvd
    simp at dvd
    rw [Polynomial.dvd_comp_X_sub_C_iff] at dvd


variable {R k : Type*} {K : Type*} [Field R] [Field k] [Field K] [Algebra R K] [Algebra k K]

theorem minpoly_split_add_algebraMap {x : K} (r : R)
    (g : (minpoly R x).Splits (algebraMap R K)) :
    (minpoly R (x + algebraMap R K r)).Splits (algebraMap R K) := by
  cases g with
  | inl g0 =>
    left
    simp only [Polynomial.map_eq_zero (algebraMap R K)] at g0 ⊢

  | inr => sorry


theorem minpoly_split_sub_algebraMap {x : K} (r : R)
    (g : (minpoly R x).Splits (algebraMap R K)) :
    (minpoly R (x - algebraMap R K r)).Splits (algebraMap R K) := by
  simpa only [sub_eq_add_neg, map_neg] using minpoly_split_add_algebraMap (-r) g

theorem minpoly_split_algebraClosure {x : K} (h : IsIntegral k x)
    (g : (minpoly k x).Splits (algebraMap k K)) :
    (minpoly k x).Splits (algebraMap k (IntermediateField.algebraicClosure k K)) := sorry

end split

open Algebra
open IntermediateField

variable (K : Type*) {L : Type*} {ΓK ΓL : outParam Type*}
    [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓL]
    [Field K] [Field L] [Algebra K L] [vK : Valued K ΓK] [vL : Valued L ΓL]
-- should add x split in L
variable (L) in
class IsKrasner : Prop where
  krasner' : ∀ {x y : L}, IsSeparable K x → (minpoly K x).Splits (algebraMap K L) →
    IsIntegral K y → (∀ x' : L, IsConjRoot K x x' → x ≠ x' → vL.v (x - y) < vL.v (x - x')) →
      x ∈ K⟮y⟯
-- `As an application of IsKrasner, prove that C_p is algebraically closed,`
-- ` accelerating integrating into mathlib`
class IsKrasnerNorm (K L : Type*) [Field K] [NormedField L] [Algebra K L] : Prop where
  krasner_norm' : ∀ {x y : L}, IsSeparable K x → (minpoly K x).Splits (algebraMap K L) →
    IsIntegral K y → (∀ x' : L, IsConjRoot K x x' →  x ≠ x' → ‖x - y‖ < ‖x - x'‖) →
      x ∈ K⟮y⟯

section
variable [IsKrasner K L]

theorem IsKrasner.krasner {x y : L} (hx : IsSeparable K x)
    (sp : (minpoly K x).Splits (algebraMap K L)) (hy : IsIntegral K y)
    (h : (∀ x' : L, IsConjRoot K x x' → x ≠ x' → vL.v (x - y) < vL.v (x - x'))) : x ∈ K⟮y⟯ :=
  IsKrasner.krasner' hx sp hy h

end

theorem IsKrasnerNorm.krasner_norm {K L : Type*} [Field K] [NormedField L] [Algebra K L]
    [IsKrasnerNorm K L] {x y : L} (hx : (minpoly K x).Separable)
    (sp : (minpoly K x).Splits (algebraMap K L)) (hy : IsIntegral K y)
    (h : (∀ x' : L, IsConjRoot K x x' → x ≠ x' → ‖x - y‖ < ‖x - x'‖)) : x ∈ K⟮y⟯ :=
  IsKrasnerNorm.krasner_norm' hx sp hy h

namespace IsKrasnerNorm

variable {K L : Type*} [NK : NontriviallyNormedField K] (is_na : IsNonarchimedean (norm : K → ℝ))
    [NL : NormedField L] [Algebra K L] (extd : FunctionExtends (norm : K → ℝ) (norm : L → ℝ))


variable (M : IntermediateField K L)

#synth Algebra K M
#synth NormedField M
#synth Algebra M L
#synth Algebra (⊥ : IntermediateField K L) M
-- #synth IsScalarTower K (⊥ : IntermediateField K L) M

#check spectralNorm_aut_isom
#check spectralNorm_unique_field_norm_ext

include extd is_na
theorem of_completeSpace_aux [Algebra.IsAlgebraic K L] [CompleteSpace K] : IsKrasnerNorm K L := by
  constructor
  intro x y xsep sp hyK hxy
  let z := x - y
  let M := K⟮y⟯
  let FDM := IntermediateField.adjoin.finiteDimensional hyK
  let BotEquiv : NormedAddGroupHom K (⊥ : IntermediateField K L) := -- put this outside
    {
      (IntermediateField.botEquiv K L).symm with
      bound' := by
        use 1
        intro x
        erw [extd x]
        simp only [one_mul, le_refl]
    }
  have : ContinuousSMul K M := by
    -- decompose as `ContinuousSMul K L`
    -- and `ContinuousSMul K L implies ContinuousSMul K M`
    apply Inducing.continuousSMul (N := K) (M := (⊥ : IntermediateField K L)) (X := M) (Y := M)
      (f := (IntermediateField.botEquiv K L).symm) inducing_id
    · exact BotEquiv.continuous
    · intros c x
      rw [Algebra.smul_def, @Algebra.smul_def (⊥ : IntermediateField K L) M _ _ _]
      rfl
  letI : CompleteSpace M := FiniteDimensional.complete K M
  have hy : y ∈ K⟮y⟯ := IntermediateField.subset_adjoin K {y} rfl
  have zsep : IsSeparable M z := by
    apply Field.isSeparable_sub (IsSeparable.tower_top M xsep)
    simp only [IsSeparable]
    exact
      minpoly.eq_X_sub_C_of_algebraMap_inj (⟨y, hy⟩ : M)
          (NoZeroSMulDivisors.algebraMap_injective (↥M) L) ▸
        Polynomial.separable_X_sub_C (x := (⟨y, hy⟩ : M))
  suffices z ∈ K⟮y⟯ by simpa [z] using add_mem this hy
  by_contra hnin
  have : z ∈ K⟮y⟯ ↔ z ∈ (⊥ : Subalgebra M L) := by simp [Algebra.mem_bot]
  rw [this.not] at hnin
  -- need + algebra map split and split tower.
  obtain ⟨z', hne, h1⟩ := (IsConjRoot.not_mem_iff_exist_ne zsep
      (IsIntegral.minpoly_splits_tower_top (R := K) sorry sorry)).mp hnin -- wrong
  -- this is where the separablity is used.
  simp only [ne_eq, Subtype.mk.injEq] at hne
  have eq_spnM : (norm : M → ℝ) = spectralNorm K M :=
    funext <| spectralNorm_unique_field_norm_ext
      (f := instNormedIntermediateField.toMulRingNorm) extd is_na
  have eq_spnL : (norm : L → ℝ) = spectralNorm K L :=
    funext <| spectralNorm_unique_field_norm_ext (f := NL.toMulRingNorm) extd is_na
  have is_naM : IsNonarchimedean (norm : M → ℝ) := eq_spnM ▸ spectralNorm_isNonarchimedean K M is_na
  have is_naL : IsNonarchimedean (norm : L → ℝ) := eq_spnL ▸ spectralNorm_isNonarchimedean K L is_na
  letI : NontriviallyNormedField M := {
    instNormedIntermediateField with
    non_trivial := by
      obtain ⟨k, hk⟩ :=  @NontriviallyNormedField.non_trivial K _
      use algebraMap K M k
      change 1 < ‖(algebraMap K L) k‖
      simp [extd k, hk]-- a lemma for extends nontrivial implies nontrivial
  }
  have eq_spnML: (norm : L → ℝ) = spectralNorm M L := by
    apply Eq.trans eq_spnL
    apply (_root_.funext <| spectralNorm_unique_field_norm_ext (K := K)
      (f := (spectralMulAlgNorm is_naM).toMulRingNorm) _ is_na).symm
    apply functionExtends_of_functionExtends_of_functionExtends (fA := (norm : M → ℝ))
    · intro m
      exact extd m
    · exact spectralNorm_extends M L -- a lemma for extends extends
  have norm_eq: ‖z‖ = ‖z'‖ := by -- a lemma
    simp only [eq_spnML, spectralNorm]
    congr 1
    -- spectralNorm K L = spectralnorm M L
  -- IsConjRoot.val_eq M hM (Polynomial.Separable.isIntegral zsep) h1
  -- need rank one -- exist_algEquiv
  have : ‖z - z'‖ < ‖z - z'‖ := by
    calc
      _ ≤ max ‖z‖ ‖z'‖ := by
        simpa only [norm_neg, sub_eq_add_neg] using (is_naL z (- z'))
      _ ≤ ‖x - y‖ := by
        simp only [← norm_eq, max_self, le_refl]
      _ < ‖x - (z' + y)‖ := by
        apply hxy (z' + y)
        · apply IsConjRoot.of_isScalarTower (S := M) K
          simpa only [IntermediateField.algebraMap_apply, sub_add_cancel, z] using
            IsConjRoot.add_algebraMap ⟨y, hy⟩ h1
        · simpa [z, sub_eq_iff_eq_add] using hne
      _ = ‖z - z'‖ := by congr 1; ring
  simp only [lt_self_iff_false] at this

variable (K L) (M : IntermediateField K L)
#synth Algebra M L

-- add a requirement that the uniquess is need and
-- TODO: we know this is true and after it is in mathlib we can remove this condition.
theorem of_completeSpace [CompleteSpace K] : IsKrasnerNorm K L := by
  constructor
  intro x y xsep sp hyK hxy
  let L' := IntermediateField.algebraicClosure K L
  let xL : L' := ⟨x, IsSeparable.isIntegral xsep⟩
  let yL : L' := ⟨y, hyK⟩
  suffices xL ∈ K⟮yL⟯ by
    rwa [← IntermediateField.lift_adjoin_simple K L' yL, IntermediateField.mem_lift xL]
  have hL' : IsKrasnerNorm K L' := IsKrasnerNorm.of_completeSpace_aux is_na extd
  apply hL'.krasner_norm
  · exact IsSeparable.of_algHom (L'.val) xsep
  · exact Polynomial.splits_of_algHom (minpoly.algHom_eq (A := K) (B := L') (B' := L) (L'.val) sorry xL ▸ sp) _  -- If split, then split in the algebraic closure.
  · exact (isIntegral_algHom_iff _ L'.val.toRingHom.injective).mp hyK
  · exact fun x' hx' hne => hxy x' ((IsConjRoot.algHom_iff _ L'.val.toRingHom.injective).mpr hx')
      (Subtype.coe_ne_coe.mpr hne)
end IsKrasnerNorm

section Valued

variable {Γ Γ' : Type*} [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Γ']
    {vK : Valued K Γ} {vK' : Valued K Γ'}

variable {K} (vK) in
theorem Valued.surj : Function.Surjective vK.v := sorry -- wrong, but will be
  -- replaced once the definition of Valued changed.

variable {K} in
/-- Equivalent valuations induces the same topology -/
theorem Valued.toUniformSpace_eq_of_isEquiv (h : vK.v.IsEquiv vK'.v) :
    vK.toUniformSpace = vK'.toUniformSpace := by
  apply UniformAddGroup.ext vK.toUniformAddGroup vK'.toUniformAddGroup
  ext U
  rw [vK.is_topological_valuation, vK'.is_topological_valuation]
  constructor <;>
  intro ⟨γ, hγ⟩
  · obtain ⟨x, hx⟩ := Valued.surj vK γ.1
    use Units.mk0 (vK'.v x) (h.ne_zero.mp <| hx ▸ γ.ne_zero)
    convert hγ
    simp only [Units.val_mk0, ← hx]
    exact (Valuation.isEquiv_iff_val_lt_val.mp h).symm
  · obtain ⟨x, hx⟩ := Valued.surj vK' γ.1
    use Units.mk0 (vK.v x) (h.symm.ne_zero.mp <| hx ▸ γ.ne_zero)
    convert hγ
    simp only [Units.val_mk0, ← hx]
    exact (Valuation.isEquiv_iff_val_lt_val.mp h)
-- `prove a copy of this using that the valuation is surjective`

variable {A B : Type*} [CommRing A] [Ring B] {Γ : Type*}
  [LinearOrderedCommGroupWithZero Γ]
  [Algebra A B]

def Valued.comap (vB : Valued B Γ) : Valued A Γ := {
  vB.toUniformSpace.comap (algebraMap A B), vB.toUniformAddGroup.comap (algebraMap A B) with
  v := vB.v.comap (algebraMap A B)
  is_topological_valuation := by
    intro U
    have teq := UniformSpace.toTopologicalSpace_comap (u := vB.toUniformSpace) (f := algebraMap A B)
    rw [(@induced_iff_nhds_eq _ _ _ (vB.toUniformSpace.comap (algebraMap A B)).toTopologicalSpace
        (algebraMap A B)).mp teq 0]
    simp only [map_zero, Filter.mem_comap, Valuation.comap_apply]
    constructor
    · rintro ⟨V, hV⟩
      obtain ⟨γ, hγ⟩ := (vB.is_topological_valuation V).mp hV.1
      exact ⟨γ, subset_trans (fun _ h ↦ hγ h) hV.2⟩
    · rintro ⟨γ, hγ⟩
      exact ⟨{x | vB.v x < γ}, ⟨(vB.is_topological_valuation _).mpr ⟨γ, subset_refl _⟩, hγ⟩⟩
}

end Valued

namespace IsKrasner

-- TODO: it is possible to remove the condition `vL.v.RankOne`, since
-- any algebraic extension of rank one valued field K is rank one valued.
-- Just extract the maximal algebraic extension of K in L
-- `show the existence of IsIntegralClosure, i.e. construct a maximal algebraic extension of K in L`
-- it should be an instance after h is a type class
theorem of_completeSpace [rk1L : vL.v.RankOne] {ΓK : outParam Type*}
    [LinearOrderedCommGroupWithZero ΓK] [vK : Valued K ΓK] [rk1K : vK.v.RankOne] [CompleteSpace K]
    (h : vK.v.IsEquiv <| vL.v.comap (algebraMap K L)): IsKrasner K L := by
  constructor
  intro x y xsep sp hyK hxy
  letI := vL.toNormedField
  letI vK' : Valued K ΓL := {
    vK.toUniformSpace with
    v := (vL.v.comap (algebraMap K L))
    is_topological_valuation := by
      have useq : vL.comap.toUniformSpace = vK.toUniformSpace :=
        (Valued.toUniformSpace_eq_of_isEquiv h).symm
      simp only [Valuation.comap_apply]
      exact useq ▸ vL.comap.is_topological_valuation
  }
  letI : vK'.v.RankOne := {
    hom := rk1L.hom
    strictMono' := rk1L.strictMono'
    nontrivial' := by
      obtain ⟨x, ⟨hx0, hx1⟩⟩ := rk1K.nontrivial'
      use x
      exact ⟨h.ne_zero.mp hx0 , ((Valuation.isEquiv_iff_val_eq_one _ _).mp h).not.mp hx1⟩
  }
  letI := vK'.toNontriviallyNormedField
  refine (IsKrasnerNorm.of_completeSpace (K := K) (L := L) ?_ (fun _ ↦ rfl)).krasner_norm
    xsep sp hyK ?_
  · exact Valued.toNormedField.isNonarchimedean
  · intros x' hx' hne
    exact Valued.toNormedField.norm_lt_iff.mpr (hxy x' hx' hne)

end IsKrasner

/- `theorem the completion of an algebraic closure of a complete rank one valued field`
`is again complete`
`Or a normed field`
-/


def valuedIsAlgebraic (k K : Type*) {Γk : Type*} [Field k] [LinearOrderedCommGroupWithZero Γk]
    [vk : Valued k Γk] [CompleteSpace k] [rk1k : vk.v.RankOne] [Field K] [Algebra k K]
    [Algebra.IsAlgebraic k K] :
    Valued K NNReal := sorry

variable (k K : Type*) {Γk : Type*} [Field k] [LinearOrderedCommGroupWithZero Γk] [vk : Valued k Γk]
    [CompleteSpace k] [rk1k : vk.v.RankOne] [Field K] [Algebra k K] [IsAlgClosure k K]

instance :
    letI := valuedIsAlgebraic k K
    TopologicalDivisionRing K := sorry

instance :
    @TopologicalDivisionRing K _ (valuedIsAlgebraic k K).toTopologicalSpace:= sorry

instance :
    letI := valuedIsAlgebraic k K
    CompletableTopField K := sorry

instance :
    letI := valuedIsAlgebraic k K
    UniformAddGroup K := sorry

instance :
    letI := valuedIsAlgebraic k K
    IsAlgClosed (UniformSpace.Completion K) := sorry




-- inline Function extd.
