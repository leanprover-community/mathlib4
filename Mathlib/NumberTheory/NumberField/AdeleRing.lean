/-
Copyright (c) 2024 Salvatore Mercuri, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, María Inés de Frutos-Fernández
-/
module

public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.ProductFormula
public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.RingTheory.Ideal.Int

/-!
# The adele ring of a number field

This file contains the formalisation of the adele ring of a number field as the
direct product of the infinite adele ring and the finite adele ring.

## Main definitions

- `NumberField.AdeleRing K` is the adele ring of a number field `K`.
- `NumberField.AdeleRing.principalSubgroup K` is the subgroup of principal adeles `(x)ᵥ`.

## References
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]

## Tags
adele ring, number field
-/

@[expose] public section

noncomputable section

namespace NumberField

open InfinitePlace AbsoluteValue.Completion InfinitePlace.Completion IsDedekindDomain

/-! ## The adele ring  -/

/-- `AdeleRing (𝓞 K) K` is the adele ring of a number field `K`.

More generally `AdeleRing R K` can be used if `K` is the field of fractions
of the Dedekind domain `R`. This enables use of rings like `AdeleRing ℤ ℚ`, which
in practice are easier to work with than `AdeleRing (𝓞 ℚ) ℚ`.

Note that this definition does not give the correct answer in the function field case.
-/
def AdeleRing (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] := InfiniteAdeleRing K × FiniteAdeleRing R K

namespace AdeleRing

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

instance : CommRing (AdeleRing R K) := Prod.instCommRing

instance : Inhabited (AdeleRing R K) := ⟨0⟩

instance : TopologicalSpace (AdeleRing R K) := instTopologicalSpaceProd

instance : IsTopologicalRing (AdeleRing R K) := instIsTopologicalRingProd

instance : Algebra K (AdeleRing R K) := Prod.algebra _ _ _

@[simp]
theorem algebraMap_fst_apply (x : K) (v : InfinitePlace K) :
    (algebraMap K (AdeleRing R K) x).1 v = x := rfl

theorem algebraMap_fst_def (x : K) :
    (algebraMap K (AdeleRing R K) x).1 = algebraMap K (InfiniteAdeleRing K) x := rfl

@[simp]
theorem algebraMap_snd_apply (x : K) (v : HeightOneSpectrum R) :
    (algebraMap K (AdeleRing R K) x).2 v = x := rfl

theorem algebraMap_snd_def (x : K) :
    (algebraMap K (AdeleRing R K) x).2 = algebraMap K (FiniteAdeleRing R K) x := rfl

theorem algebraMap_injective [NumberField K] : Function.Injective (algebraMap K (AdeleRing R K)) :=
  fun _ _ hxy => (algebraMap K _).injective (Prod.ext_iff.1 hxy).1

/-- The subgroup of principal adeles `(x)ᵥ` where `x ∈ K`. -/
abbrev principalSubgroup : AddSubgroup (AdeleRing R K) := (algebraMap K _).range.toAddSubgroup

end AdeleRing

section norm

variable {K : Type*} [Field K] [NumberField K]

namespace FiniteAdeleRing

open RingOfIntegers.HeightOneSpectrum

theorem mulSupport_finite (x : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    (Function.mulSupport fun v ↦ ‖x.1 v‖).Finite := by
  simpa [Function.mulSupport, Valued.toNormedField.norm_eq_one_iff] using
    FiniteAdeleRing.unitsEquiv_finite_valued_eq_one x

theorem hasProd_zero_of_not_isUnit {x : FiniteAdeleRing (𝓞 K) K} (hx : ¬IsUnit x) :
    HasProd (fun v ↦ ‖x.1 v‖) 0 := by
  by_cases hx₀ : ∃ v, x v = 0
  · have : ∃ v, ‖x v‖ = 0 := by simp [hx₀]
    exact hasProd_zero_of_exists_eq_zero this
  replace hx := FiniteAdeleRing.infinite_valued_ne_one_of_not_isUnit (by simpa using hx₀) hx
  let S := {v : HeightOneSpectrum (𝓞 K) | 1 < Valued.v (x v)}
  let S₁ := {v : HeightOneSpectrum (𝓞 K) | Valued.v (x v) = 1}
  let hSf : S.Finite := by simpa [HeightOneSpectrum.mem_adicCompletionIntegers] using x.2
  have : Fintype S := Set.Finite.fintype hSf
  have hS : HasProd (fun v : S ↦ ‖x v‖) (∏ v : S, ‖x v‖) := hasProd_fintype _
  have hS₁ : HasProd (fun v : S₁ ↦ ‖x v‖) 1 := by
    have : (fun v : S₁ ↦ ‖x v‖) = 1 := by
      ext v
      rw [Pi.one_apply, Valued.toNormedField.norm_eq_one_iff]
      exact v.2
    rw [this]
    exact hasProd_one
  let S' := S ∪ S₁
  have hSu : HasProd (fun (v : S') ↦ ‖x v‖) (∏ v : S, ‖x v‖) := by
    have : Disjoint S S₁ := by grind
    have := HasProd.mul_disjoint (f := fun v ↦ ‖x v‖) this (a := ∏ v : S, ‖x v‖) (b := 1)
      hS hS₁
    simpa using this
  let T := S'ᶜ
  have hT' : T.Infinite := by
    push_neg at hx₀
    have : {v | Valued.v (x v) ≠ 1} = S ∪ T := by ext v; grind
    rw [this, Set.infinite_union] at hx
    rcases hx with (hSi | hTi)
    · absurd hSi
      exact hSf
    · exact hTi
  have hT : HasProd (fun v : T ↦ ‖x v‖) 0 := by
    have : Filter.Tendsto (fun s : Finset T ↦ (∏ v ∈ s, ‖x v‖)⁻¹) Filter.atTop Filter.atTop := by
      have h : ∀ v ∈ T, 2 ≤ ‖x v‖⁻¹ := by
        intro v hv
        rw [← norm_inv]
        apply FinitePlace.two_le_norm_of_one_lt_norm
        rw [Valued.toNormedField.one_lt_norm_iff, map_inv₀, one_lt_inv_iff₀]
        constructor
        · contrapose! hx₀
          use v
          simp_all
        · grind
      have h_le : ∀ S : Finset T, 2 ^ S.card ≤ (∏ v ∈ S, ‖x v‖)⁻¹ := by
        intro S
        have : ∀ v ∈ S, 2 ≤ ‖x v‖⁻¹  := by
          intro v hv
          exact h v v.2
        have := Finset.prod_le_prod (by grind) this
        rw [Finset.prod_const] at this
        apply this.trans
        simp
      apply Filter.tendsto_atTop_mono h_le
      have := tendsto_pow_atTop_atTop_of_one_lt (r := (2 : ℝ)) (by norm_num)
      apply this.comp
      apply Filter.tendsto_atTop_atTop_of_monotone
      · exact Finset.card_mono
      · intro N
        obtain ⟨t, ht, ht'⟩ := hT'.exists_subset_card_eq N
        use t.subtype _
        rw [Finset.card_subtype, ← ht']
        apply le_of_eq
        symm
        rw [Finset.card_filter_eq_iff.2 ht]
    apply (tendsto_inv_atTop_zero.comp this).congr (by simp)
  simpa using hT.compl_mul hSu (f := fun v ↦ ‖x.1 v‖)

theorem tprod_norm_of_isUnit {x : FiniteAdeleRing (𝓞 K) K} (hx : IsUnit x) :
    ∏' v, ‖x.1 v‖ = ∏ᶠ v, ‖x.1 v‖ := by
  rw [tprod_eq_finprod]
  exact mulSupport_finite hx.unit

theorem tprod_norm_of_unit (x : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    ∏' v, ‖x.1 v‖ = ∏ᶠ v, ‖x.1 v‖ :=
  tprod_norm_of_isUnit x.isUnit

theorem tprod_eq_zero_of_not_isUnit {x : FiniteAdeleRing (𝓞 K) K} (hx : ¬ IsUnit x) :
    ∏' v, ‖x.1 v‖ = 0 := by
  rw [HasProd.tprod_eq]
  exact hasProd_zero_of_not_isUnit hx

instance : Norm (FiniteAdeleRing (𝓞 K) K) where norm x := ∏' v, ‖x.1 v‖

theorem norm_def (x : FiniteAdeleRing (𝓞 K) K) : ‖x‖ = ∏' v, ‖x.1 v‖ := rfl

theorem norm_def_unit (x : (FiniteAdeleRing (𝓞 K) K)ˣ) : ‖x.1‖ = ∏ᶠ v, ‖x.1 v‖ :=
  tprod_norm_of_unit x

theorem norm_eq_zero_of_not_isUnit {x : FiniteAdeleRing (𝓞 K) K} (hx : ¬IsUnit x) : ‖x‖ = 0 :=
  tprod_eq_zero_of_not_isUnit hx

theorem coe_norm_apply (x : Kˣ) :
    ‖(x : (FiniteAdeleRing (𝓞 K) K)ˣ).1‖ = ∏ᶠ v, FinitePlace.mk v x.1 := norm_def_unit _

theorem coe_norm_apply_eq_finprod_finitePlace (x : Kˣ) :
    ‖(x : (FiniteAdeleRing (𝓞 K) K)ˣ).1‖ = ∏ᶠ v : FinitePlace K, v x := by
  rw [coe_norm_apply, ← finprod_comp FinitePlace.equivHeightOneSpectrum.invFun
    FinitePlace.equivHeightOneSpectrum.symm.bijective]
  exact finprod_congr fun _ ↦ rfl

theorem coe_norm_eq_inv_abs_norm (x : Kˣ) :
    ‖(x : (FiniteAdeleRing (𝓞 K) K)ˣ).1‖ = |Algebra.norm ℚ x.1|⁻¹ := by
  rw [← FinitePlace.prod_eq_inv_abs_norm x.ne_zero, coe_norm_apply_eq_finprod_finitePlace]

end FiniteAdeleRing

namespace AdeleRing

set_option backward.isDefEq.respectTransparency false in
theorem isUnit_iff {x : AdeleRing (𝓞 K) K} :
    IsUnit x ↔ (∀ v, x.1 v ≠ 0) ∧ (∀ v, x.2 v ≠ 0) ∧
      ∀ᶠ v in Filter.cofinite, Valued.v (x.2 v) = 1 := by
  rw [Prod.isUnit_iff, Pi.isUnit_iff, FiniteAdeleRing.isUnit_iff]
  simp_rw [isUnit_iff_ne_zero]

instance : Norm (AdeleRing (𝓞 K) K) where norm x := ‖x.1‖ * ‖x.2‖

theorem norm_def (x : AdeleRing (𝓞 K) K) : ‖x‖ = ‖x.1‖ * ‖x.2‖ := rfl

theorem norm_def_unit (x : (AdeleRing (𝓞 K) K)ˣ) :
    ‖x.1‖ = ‖x.1.1‖ * ‖(MulEquiv.prodUnits x).2.1‖ := rfl

theorem norm_apply_unit (x : (AdeleRing (𝓞 K) K)ˣ) :
    ‖x.1‖ = (∏ v, ‖x.1.1 v‖ ^ v.mult) * ∏ᶠ v, ‖(MulEquiv.prodUnits x).2.1 v‖ := by
  rw [norm_def_unit, FiniteAdeleRing.norm_def_unit]
  rfl

theorem norm_eq_zero_of_not_isUnit {x : AdeleRing (𝓞 K) K} (hx : ¬IsUnit x) : ‖x‖ = 0 := by
  rcases not_and_or.1 <| Prod.isUnit_iff.not.1 hx with hi | hf
  · simp [norm_def, InfiniteAdeleRing.norm_eq_zero_of_not_isUnit hi]
  · simp [norm_def, FiniteAdeleRing.norm_eq_zero_of_not_isUnit hf]

variable (K) in
def unitEmbedding : Kˣ →* (AdeleRing (𝓞 K) K)ˣ := Units.map (algebraMap K (AdeleRing (𝓞 K) K))

@[simp] theorem unitEmbedding_apply (k : Kˣ) :
    unitEmbedding K k = algebraMap K (AdeleRing (𝓞 K) K) k := rfl

theorem unitEmbedding_prodUnits_apply (k : Kˣ) :
    (MulEquiv.prodUnits (unitEmbedding K k)).2 = k := rfl

instance : Coe Kˣ (AdeleRing (𝓞 K) K)ˣ where
  coe x := unitEmbedding K x

theorem coe_norm_eq_one {x : Kˣ} :
    ‖(x : (AdeleRing (𝓞 K) K)ˣ).1‖ = 1 := by
  rw [norm_def_unit, unitEmbedding_apply, algebraMap_fst_def, unitEmbedding_prodUnits_apply,
    InfiniteAdeleRing.coe_norm_eq_abs_norm, FiniteAdeleRing.coe_norm_eq_inv_abs_norm]
  simp

end AdeleRing

end norm

end NumberField
