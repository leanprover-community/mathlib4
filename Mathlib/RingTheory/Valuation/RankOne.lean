/-
Copyright (c) 2024 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
module

public import Mathlib.Algebra.Order.Group.Units
public import Mathlib.Algebra.Order.GroupWithZero.WithZero
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Real.Embedding
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.Valued.WithVal

/-!
# Rank one valuations

We define rank one valuations.

## Main Definitions
* `RankOne` : A valuation has rank one if it is nontrivial and its image (defined as
`MonoidWithZeroHom.valueGroup₀ v`) is contained in `ℝ≥0`. Note that this class includes the data
of an inclusion morphism `MonoidWithZeroHom.valueGroup₀ v → ℝ≥0`.
* `RankOne.restrict_RankOne` is the `RankOne` instance for the restriction of a valuation to its
image, as defined in

## Tags

valuation, rank one
-/

@[expose] public section

@[expose] public section

noncomputable section

open Function Multiplicative MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀

open scoped NNReal

variable {R Γ₀ : Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ₀]

namespace Valuation

/-- A valuation has rank one if it is nontrivial and its image (defined as
`MonoidWithZeroHom.valueGroup₀ v`) is contained in `ℝ≥0`. Note that this class includes the data
of an inclusion morphism `MonoidWithZeroHom.valueGroup₀ v → ℝ≥0`. -/
class RankOne (v : Valuation R Γ₀) extends Valuation.IsNontrivial v where
  /-- The inclusion morphism from `Γ₀` to `ℝ≥0`. -/
  hom (v) : ValueGroup₀ v →*₀ ℝ≥0
  strictMono' : StrictMono hom

open WithZero

lemma nonempty_rankOne_iff_mulArchimedean {v : Valuation R Γ₀} [v.IsNontrivial] :
    Nonempty v.RankOne ↔ MulArchimedean (ValueGroup₀ v) := by
  constructor
  · rintro ⟨⟨f, hf⟩⟩
    exact MulArchimedean.comap f.toMonoidHom hf
  · intro _
    obtain ⟨f, hf⟩ :=
      Archimedean.exists_orderAddMonoidHom_real_injective (Additive  (ValueGroup₀ v)ˣ)
    let e := AddMonoidHom.toMultiplicativeRight (α :=  (ValueGroup₀ v)ˣ) (β := ℝ) f
    have he : StrictMono e := by
      simp only [AddMonoidHom.coe_toMultiplicativeRight, AddMonoidHom.coe_coe, e]
      -- toAdd_strictMono is already in an applied form, do defeq abuse instead
      exact StrictMono.comp strictMono_id (f.monotone'.strictMono_of_injective hf)
    let rf : Multiplicative ℝ →* ℝ≥0ˣ := {
      toFun x := Units.mk0 ⟨(2 : ℝ) ^ (log (M := ℝ) x), by positivity⟩ <| by
        rw [ne_eq, Subtype.ext_iff]
        positivity
      map_one' := by simp
      map_mul' _ _ := by
        rw [Units.ext_iff, Subtype.ext_iff]
        simp [log_mul, Real.rpow_add]
      }
    have H : StrictMono (map' (rf.comp e)) := by
      refine map'_strictMono ?_
      intro a b h
      simpa [← Units.val_lt_val, ← NNReal.coe_lt_coe, rf] using he h
    exact ⟨{
      hom := withZeroUnitsEquiv.toMonoidWithZeroHom.comp <| (map' (rf.comp e)).comp
        withZeroUnitsEquiv.symm.toMonoidWithZeroHom
      strictMono' := withZeroUnitsEquiv_strictMono.comp <| H.comp
        withZeroUnitsEquiv_symm_strictMono
    }⟩

namespace RankOne

variable (v : Valuation R Γ₀) [RankOne v]

lemma strictMono : StrictMono (hom v) := strictMono'

lemma nontrivial : ∃ r : R, v r ≠ 0 ∧ v r ≠ 1 := IsNontrivial.exists_val_nontrivial

/-- If `v` is a rank one valuation and `x : Γ₀` has image `0` under `RankOne.hom v`, then
  `x = 0`. -/
theorem zero_of_hom_zero {x : ValueGroup₀ v} (hx : hom v x = 0) : x = 0 := by
  refine (eq_of_le_of_not_lt (zero_le' (a := x)) fun h_lt ↦ ?_).symm
  have hs := strictMono v h_lt
  rw [map_zero, hx] at hs
  exact hs.false

/-- If `v` is a rank one valuation, then `x : Γ₀` has image `0` under `RankOne.hom v` if and
  only if `x = 0`. -/
theorem hom_eq_zero_iff {x : ValueGroup₀ v} : hom v x = 0 ↔ x = 0 :=
  ⟨fun h ↦ zero_of_hom_zero v h, fun h ↦ by rw [h, map_zero]⟩

/-- A nontrivial unit of `Γ₀`, given that there exists a rank one `v : Valuation R Γ₀`. -/
def unit : Γ₀ˣ :=
  Units.mk0 (v (nontrivial v).choose) ((nontrivial v).choose_spec).1

/-- A proof that `RankOne.unit v ≠ 1`. -/
theorem unit_ne_one : unit v ≠ 1 := by
  rw [Ne, ← Units.val_inj, Units.val_one]
  exact ((nontrivial v).choose_spec).2

instance [RankOne v] : IsNontrivial v where
  exists_val_nontrivial := RankOne.nontrivial v

section Restrict

instance restrict_Nontrivial [v.IsNontrivial] : (v.restrict).IsNontrivial where
  exists_val_nontrivial := by
    obtain ⟨x, ⟨hx0, hx1⟩⟩ := IsNontrivial.exists_val_nontrivial (v := v)
    use x
    constructor
    · simp [hx0]
    · rw [restrict_def]
      intro H
      rw [restrict₀_eq_one_iff] at H
      tauto

variable (K : Type*) [Field K] (v : Valuation K Γ₀) [RankOne v]

instance restrict_RankOne [RankOne v] : RankOne (v.restrict) where
  hom := (RankOne.hom v).comp embedding
  strictMono' := (strictMono v).comp embedding_strictMono

end Restrict

end RankOne

-- Not the correct map. Where is this used?
/- instance instRankOneCompletion {K : Type*} [Field K] {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) [h : v.RankOne] :
    (Valued.v : Valuation v.Completion Γ).RankOne where
  hom := sorry --Valuation.RankOne.hom v
  strictMono' := sorry --Valuation.RankOne.strictMono v
  exists_val_nontrivial := by
    rcases h.exists_val_nontrivial with ⟨x, hx1, hx2⟩
    use (WithVal.equiv v).symm x
    simp_all -/

end Valuation

section ValuativeRel

open ValuativeRel

variable {R : Type*} [CommRing R] [ValuativeRel R]

/-- A valuative relation has a rank one valuation when it is both nontrivial
and the rank is at most one. -/
def Valuation.RankOne.ofRankLeOneStruct [ValuativeRel.IsNontrivial R] (e : RankLeOneStruct R) :
    Valuation.RankOne (valuation R) where
  hom := e.emb.comp embedding
  strictMono' := e.strictMono.comp embedding_strictMono

instance [IsNontrivial R] [IsRankLeOne R] :
    Valuation.RankOne (valuation R) :=
  Valuation.RankOne.ofRankLeOneStruct IsRankLeOne.nonempty.some

/-- Convert between the rank one statement on valuative relation's induced valuation. -/
def Valuation.RankOne.rankLeOneStruct (e : Valuation.RankOne (valuation R)) :
    RankLeOneStruct R where
  emb := e.hom.comp
      (ValuativeRel.ValueGroupWithZero.embed (v := valuation R))
  strictMono := by
    apply e.strictMono.comp
    exact ValueGroupWithZero.embed_strictMono (valuation R)

lemma ValuativeRel.isRankLeOne_of_rankOne [h : (valuation R).RankOne] :
    IsRankLeOne R :=
  ⟨⟨h.rankLeOneStruct⟩⟩

lemma ValuativeRel.isNontrivial_of_rankOne [h : (valuation R).RankOne] :
    ValuativeRel.IsNontrivial R :=
  (isNontrivial_iff_isNontrivial _).mpr h.toIsNontrivial

open WithZero

lemma ValuativeRel.isRankLeOne_iff_mulArchimedean :
    IsRankLeOne R ↔ MulArchimedean (ValueGroupWithZero R) := by
  constructor
  · rintro ⟨⟨f, hf⟩⟩
    exact .comap f.toMonoidHom hf
  · intro h
    by_cases H : IsNontrivial R
    · rw [isNontrivial_iff_isNontrivial (valuation R)] at H
      have h' : MulArchimedean (ValueGroup₀ (valuation R)) :=
        MulArchimedean.comap embedding.toMonoidHom embedding_strictMono
      rw [← (valuation R).nonempty_rankOne_iff_mulArchimedean] at h'
      obtain ⟨f⟩ := h'
      exact isRankLeOne_of_rankOne
    · refine ⟨⟨{ emb := 1, strictMono := ?_ }⟩⟩
      intro a b
      contrapose! H
      obtain ⟨H, H'⟩ := H
      rcases eq_or_ne a 0 with rfl | ha
      · simp_all
      rcases eq_or_ne a 1 with rfl | ha'
      · exact ⟨⟨b, (H.trans' zero_lt_one).ne', H.ne'⟩⟩
      · exact ⟨⟨a, ha, ha'⟩⟩

lemma ValuativeRel.IsRankLeOne.of_compatible_mulArchimedean [MulArchimedean Γ₀]
    (v : Valuation R Γ₀) [v.Compatible] :
    ValuativeRel.IsRankLeOne R := by
  rw [isRankLeOne_iff_mulArchimedean]
  exact MulArchimedean.comap (embedding.toMonoidHom.comp (ValueGroupWithZero.embed v).toMonoidHom)
    (embedding_strictMono.comp (ValueGroupWithZero.embed_strictMono v))

end ValuativeRel
