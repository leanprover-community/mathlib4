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
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity

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

noncomputable section

open Function Multiplicative MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀

open scoped NNReal

variable {R Γ₀ : Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ₀]

namespace Valuation

/-- A valuation has rank at most one if its image (defined as `MonoidWithZeroHom.valueGroup₀ v`)
is contained in `ℝ≥0`. Note that this class includes the data
of an inclusion morphism `MonoidWithZeroHom.valueGroup₀ v → ℝ≥0`. -/
class RankLeOne (v : Valuation R Γ₀) where
  /-- The inclusion morphism from `Γ₀` to `ℝ≥0`. -/
  hom' (v) : ValueGroup₀ v →*₀ ℝ≥0
  strictMono' : StrictMono hom'

/-- A valuation has rank one if it is nontrivial and its image is contained in `ℝ≥0`.
  Note that this class includes the data of an inclusion morphism `Γ₀ → ℝ≥0`. -/
class RankOne (v : Valuation R Γ₀) extends RankLeOne v, Valuation.IsNontrivial v

open WithZero

set_option backward.isDefEq.respectTransparency false in
lemma nonempty_rankOne_iff_mulArchimedean {v : Valuation R Γ₀} [v.IsNontrivial] :
    Nonempty v.RankOne ↔ MulArchimedean (ValueGroup₀ v) := by
  constructor
  · intro h
    obtain hv := Nonempty.some h
    exact MulArchimedean.comap hv.hom'.toMonoidHom hv.strictMono'
  · intro _
    obtain ⟨f, hf⟩ :=
      Archimedean.exists_orderAddMonoidHom_real_injective (Additive (ValueGroup₀ v)ˣ)
    let e := AddMonoidHom.toMultiplicativeRight (α := (ValueGroup₀ v)ˣ) (β := ℝ) f
    have he : StrictMono e := by
      simp only [AddMonoidHom.coe_toMultiplicativeRight, AddMonoidHom.coe_coe, e]
      -- toAdd_strictMono is already in an applied form, do defeq abuse instead
      exact StrictMono.comp strictMono_id (f.monotone'.strictMono_of_injective hf)
    let rf : Multiplicative ℝ →* ℝ≥0ˣ := {
      toFun x := Units.mk0 (.mk ((2 : ℝ) ^ (log (M := ℝ) x)) (by positivity)) <| by
        rw [ne_eq, Subtype.ext_iff]
        simp only [NNReal.val_eq_coe, NNReal.coe_mk, NNReal.coe_zero]
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
      hom' := withZeroUnitsEquiv.toMonoidWithZeroHom.comp <| (map' (rf.comp e)).comp
        withZeroUnitsEquiv.symm.toMonoidWithZeroHom
      strictMono' := withZeroUnitsEquiv_strictMono.comp <| H.comp
        withZeroUnitsEquiv_symm_strictMono
    }⟩

namespace RankOne

variable (v : Valuation R Γ₀) [hv : RankOne v]

/-- The inclusion morphism from `Γ₀` to `ℝ≥0`. -/
abbrev hom := RankLeOne.hom' v

lemma strictMono : StrictMono (hom v) := hv.strictMono'

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

instance : IsNontrivial v where
  exists_val_nontrivial := RankOne.nontrivial v

section Restrict

instance isNontrivial_restrict [v.IsNontrivial] : (v.restrict).IsNontrivial where
  exists_val_nontrivial := by
    obtain ⟨x, ⟨hx0, hx1⟩⟩ := IsNontrivial.exists_val_nontrivial (v := v)
    exact ⟨x, by simp [hx0], by grind [restrict_eq_one_iff]⟩

variable (K : Type*) [Field K] (v : Valuation K Γ₀) [RankOne v]

instance restrict_RankOne : RankOne (v.restrict) where
  hom' := (RankOne.hom v).comp embedding
  strictMono' := (strictMono v).comp embedding_strictMono

@[simp]
lemma restrict_RankOne_hom_eq :
  RankOne.hom v.restrict = (RankOne.hom v).comp embedding := rfl

set_option backward.defeqAttrib.useBackward true in
variable {K} in
set_option backward.isDefEq.respectTransparency false in
theorem exists_val_lt {γ : ℝ≥0} (hγ : γ ≠ 0) : ∃ x ≠ 0, RankOne.hom v (v.restrict x) < γ := by
  have hγ_pos : 0 < γ := pos_iff_ne_zero.mpr hγ
  obtain ⟨x, h⟩ := NNReal.exists_lt_of_strictMono (RankOne.strictMono v.restrict) hγ_pos
  obtain ⟨k, hk⟩ := ValueGroup₀.restrict₀_surjective _ x.val
  refine ⟨k, ?_, ?_⟩
  · simp only [restrict₀_apply, restrict_def, map_eq_zero, dite_eq_left_iff, coe_ne_zero,
      imp_false, not_not] at hk
    by_contra h0
    rw [dif_pos (by rw [dif_pos ((zero_iff v).mpr h0)]), eq_comm] at hk
    simp at hk
  · convert h
    simp only [restrict_RankOne_hom_eq, coe_comp, Function.comp_apply, ← hk]
    congr 1
    exact (embedding_restrict₀ k).symm

end Restrict

end RankOne

namespace RankLeOne

variable {K : Type*} [DivisionRing K] (v : Valuation K Γ₀) [RankLeOne v]

/-- If a valuation has rank at most one and is non trivial,
then it has rank one -/
@[implicit_reducible]
def rankOne_of_exists (H : ∃ x ≠ 0, v x ≠ 1) : RankOne v where
  exists_val_nontrivial := by
    by_contra! H'
    obtain ⟨x, hx, hx'⟩ := H
    exact hx' (H' x ((ne_zero_iff v).mpr hx))

/-- If a valuation has rank at most one and is non trivial,
then it has rank one -/
@[implicit_reducible]
def rankOne_of_nontrivial (H : Nontrivial (ValueGroup₀ v)ˣ) : RankOne v where
  exists_val_nontrivial := by
    by_contra! H'
    rw [nontrivial_iff_exists_ne 1] at H
    obtain ⟨x, hx⟩ := H
    obtain ⟨k, hk⟩ := ValueGroup₀.restrict₀_surjective _ x.val
    have h0 : v k ≠ 0 := by
      rw [ne_eq, ← restrict₀_eq_zero_iff, hk]
      simp
    have h1 : v k ≠ 1 := by
      rw [ne_eq, ← restrict₀_eq_one_iff, hk]
      simp [hx]
    exact h1 (H' k h0)

theorem exists_val_lt {K : Type*} [Field K] (v : Valuation K Γ₀) [RankLeOne v] :
    Subsingleton ((ValueGroup₀ v)ˣ) ∨
      ∀ {γ : ℝ≥0} (_ : γ ≠ 0), ∃ (x : K), x ≠ 0 ∧ (RankLeOne.hom' v) (v.restrict x) < γ := by
  simp only [ne_eq, or_iff_not_imp_left, not_subsingleton_iff_nontrivial]
  exact fun H ↦ (rankOne_of_nontrivial v H).exists_val_lt

end RankLeOne

end Valuation

section ValuativeRel

open ValuativeRel

variable {R : Type*} [CommRing R] [ValuativeRel R]

/-- A valuative relation has a rank one valuation when it is both nontrivial
and the rank is at most one. -/
@[implicit_reducible]
def Valuation.RankOne.ofRankLeOneStruct [ValuativeRel.IsNontrivial R] (e : RankLeOneStruct R) :
    Valuation.RankOne (valuation R) where
  hom' := e.emb.comp embedding
  strictMono' := e.strictMono.comp embedding_strictMono

instance [IsNontrivial R] [IsRankLeOne R] :
    Valuation.RankOne (valuation R) :=
  Valuation.RankOne.ofRankLeOneStruct IsRankLeOne.nonempty.some

/-- Convert between the rank one statement on valuative relation's induced valuation. -/
def Valuation.RankOne.rankLeOneStruct (e : Valuation.RankOne (valuation R)) :
    RankLeOneStruct R where
  emb := e.hom.comp (ValuativeRel.ValueGroupWithZero.embed (v := valuation R))
  strictMono := e.strictMono.comp (ValueGroupWithZero.embed_strictMono (valuation R))

lemma ValuativeRel.isRankLeOne_of_rankOne [h : (valuation R).RankOne] :
    IsRankLeOne R := ⟨⟨h.rankLeOneStruct⟩⟩

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
