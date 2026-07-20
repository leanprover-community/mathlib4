/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.Data.Sigma.Lex
public import Mathlib.SetTheory.ZFC.Constructible.MinimalStage
public import Mathlib.SetTheory.ZFC.Constructible.DefWellOrder

/-!
# External birth-layer orders for constructible stages

This file decomposes each constructible stage into the disjoint layers of
sets born at earlier ordinals.  A well-order on each layer can then be combined
lexicographically and transported back to the stage carrier.

All orders in this file are external Lean relations.  No claim is made here
that their graphs are internally represented `ZFSet`s or belong to `L`.
-/

@[expose] public section

open Set

universe u v

namespace Constructible

/-! ## Birth layers -/

/-- Constructible sets whose canonical birth stage is exactly `alpha`. -/
def BornAt (alpha : Ordinal.{u}) :=
  {x : ZFSet.{u} //
    ∃ hx : x ∈ L, birthStage x hx = alpha}

/-- The new part of `L_(alpha + 1)` over `L_alpha`. -/
abbrev StageDifference (alpha : Ordinal.{u}) :=
  {x : ZFSet.{u} //
    x ∈ LStageZF (Order.succ alpha) ∧ x ∉ LStageZF alpha}

namespace BornAt

theorem mem_L {alpha : Ordinal.{u}} (x : BornAt alpha) : x.1 ∈ L :=
  Classical.choose x.2

@[simp]
theorem birthStage_eq {alpha : Ordinal.{u}} (x : BornAt alpha) :
    birthStage x.1 x.mem_L = alpha :=
  Classical.choose_spec x.2

theorem mem_LStageZF_succ {alpha : Ordinal.{u}} (x : BornAt alpha) :
    x.1 ∈ LStageZF (Order.succ alpha) := by
  rw [LStageZF_succ]
  have hx := mem_DefZF_birthStage x.1 x.mem_L
  simpa only [x.birthStage_eq] using hx

theorem not_mem_LStageZF {alpha : Ordinal.{u}} (x : BornAt alpha) :
    x.1 ∉ LStageZF alpha := by
  have hx := not_mem_LStageZF_birthStage x.1 x.mem_L
  simpa only [x.birthStage_eq] using hx

/-- A birth-layer element, regarded as a member of the corresponding
Gödel-definability step. -/
def toDefCarrier {alpha : Ordinal.{u}} (x : BornAt alpha) :
    Godel.DefCarrier (LStageZF alpha) := by
  refine ⟨x.1, ?_⟩
  rw [← Godel.DefZF_eq_godelDef (LStageZF_isTransitive alpha)]
  have hx := mem_DefZF_birthStage x.1 x.mem_L
  simpa only [x.birthStage_eq] using hx

theorem toDefCarrier_injective {alpha : Ordinal.{u}} :
    Function.Injective (@toDefCarrier alpha) := by
  intro x y hxy
  apply Subtype.ext
  exact congrArg (fun z : Godel.DefCarrier (LStageZF alpha) => z.1) hxy

end BornAt

/-- Being born at `alpha` is equivalent to entering the hierarchy precisely
between `L_alpha` and `L_(alpha + 1)`. -/
theorem bornAt_iff_mem_succ_not_mem (alpha : Ordinal.{u}) (x : ZFSet.{u}) :
    (∃ hx : x ∈ L, birthStage x hx = alpha) ↔
      x ∈ LStageZF (Order.succ alpha) ∧ x ∉ LStageZF alpha := by
  constructor
  · rintro ⟨hxL, hbirth⟩
    have hmem := mem_DefZF_birthStage x hxL
    have hnot := not_mem_LStageZF_birthStage x hxL
    constructor
    · rw [LStageZF_succ]
      simpa only [hbirth] using hmem
    · simpa only [hbirth] using hnot
  · rintro ⟨hxSucc, hxNot⟩
    let hxL : x ∈ L :=
      LStageZF_subset_constructibleUniverse (Order.succ alpha) hxSucc
    refine ⟨hxL, ?_⟩
    apply le_antisymm
    · exact Order.lt_succ_iff.mp (birthStage_lt_of_mem_LStageZF hxSucc)
    · apply le_of_not_gt
      intro hbirth
      apply hxNot
      have hxBirth :
          x ∈ LStageZF (Order.succ (birthStage x hxL)) := by
        rw [LStageZF_succ]
        exact mem_DefZF_birthStage x hxL
      exact LStageZF_mono (Order.succ_le_of_lt hbirth) hxBirth

/-- `BornAt alpha` is exactly the subtype difference
`L_(alpha + 1) \ L_alpha`. -/
noncomputable def bornAtEquivStageDifference (alpha : Ordinal.{u}) :
    BornAt alpha ≃ StageDifference alpha where
  toFun x :=
    ⟨x.1, x.mem_LStageZF_succ, x.not_mem_LStageZF⟩
  invFun x :=
    ⟨x.1, (bornAt_iff_mem_succ_not_mem alpha x.1).mpr x.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-! ## The local least-term order -/

/-- Restrict the least-term order on `godelDef (LStageZF alpha)` to the sets
born at `alpha`. -/
noncomputable def bornAtRel (alpha : Ordinal.{u})
    (r : Option (ZFCarrier (LStageZF alpha)) →
      Option (ZFCarrier (LStageZF alpha)) → Prop)
    [IsWellOrder (Option (ZFCarrier (LStageZF alpha))) r] :
    BornAt alpha → BornAt alpha → Prop :=
  InvImage (Godel.defCarrierRel (LStageZF alpha) r) BornAt.toDefCarrier

theorem bornAtRel_isWellOrder (alpha : Ordinal.{u})
    (r : Option (ZFCarrier (LStageZF alpha)) →
      Option (ZFCarrier (LStageZF alpha)) → Prop)
    [IsWellOrder (Option (ZFCarrier (LStageZF alpha))) r] :
    IsWellOrder (BornAt alpha) (bornAtRel alpha r) := by
  letI : IsWellOrder (Godel.DefCarrier (LStageZF alpha))
      (Godel.defCarrierRel (LStageZF alpha) r) :=
    Godel.defCarrierRel_isWellOrder (LStageZF alpha) r
  refine
    { wf := InvImage.wf BornAt.toDefCarrier
        (IsWellFounded.wf :
          WellFounded (Godel.defCarrierRel (LStageZF alpha) r))
      trichotomous :=
        (InvImage.trichotomous (r :=
          Godel.defCarrierRel (LStageZF alpha) r)
          BornAt.toDefCarrier_injective).trichotomous }

/-! ## Decomposing a stage by birth ordinal -/

/-- The ordinary subtype carrier of the internally represented stage. -/
abbrev LStageCarrier (alpha : Ordinal.{u}) :=
  ZFCarrier (LStageZF alpha)

/-- The dependent sum of all birth layers indexed below `alpha`. -/
abbrev BirthLayers (alpha : Ordinal.{u}) :=
  Σ' beta : Set.Iio alpha, BornAt beta.1

/-- Send a member of `L_alpha` to its canonical birth layer. -/
noncomputable def toBirthLayers (alpha : Ordinal.{u}) :
    LStageCarrier alpha → BirthLayers alpha :=
  fun x =>
    let hxL : x.1 ∈ L :=
      LStageZF_subset_constructibleUniverse alpha x.2
    ⟨⟨birthStage x.1 hxL, birthStage_lt_of_mem_LStageZF x.2⟩,
      ⟨x.1, ⟨hxL, rfl⟩⟩⟩

/-- Forget the birth index and include the layer into `L_alpha`. -/
def fromBirthLayers (alpha : Ordinal.{u}) :
    BirthLayers alpha → LStageCarrier alpha
  | ⟨beta, x⟩ =>
      ⟨x.1, LStageZF_mono (Order.succ_le_of_lt beta.2)
        x.mem_LStageZF_succ⟩

@[simp]
theorem fromBirthLayers_toBirthLayers (alpha : Ordinal.{u})
    (x : LStageCarrier alpha) :
    fromBirthLayers alpha (toBirthLayers alpha x) = x := by
  apply Subtype.ext
  rfl

private theorem bornAt_heq_of_eq {beta gamma : Ordinal.{u}}
    (hbg : beta = gamma) (x : BornAt beta) (y : BornAt gamma)
    (hxy : x.1 = y.1) : HEq x y := by
  subst gamma
  exact heq_of_eq (Subtype.ext hxy)

@[simp]
theorem toBirthLayers_fromBirthLayers (alpha : Ordinal.{u})
    (x : BirthLayers alpha) :
    toBirthLayers alpha (fromBirthLayers alpha x) = x := by
  rcases x with ⟨beta, x⟩
  have hbirth :
      birthStage x.1
          (LStageZF_subset_constructibleUniverse alpha
            (fromBirthLayers alpha ⟨beta, x⟩).2) = beta.1 := by
    calc
      birthStage x.1
          (LStageZF_subset_constructibleUniverse alpha
            (fromBirthLayers alpha ⟨beta, x⟩).2) =
          birthStage x.1 x.mem_L :=
        birthStage_proof_irrel _ _ _
      _ = beta.1 := x.birthStage_eq
  have hindex :
      (toBirthLayers alpha (fromBirthLayers alpha ⟨beta, x⟩)).1 = beta :=
    Subtype.ext hbirth
  apply PSigma.ext hindex
  exact bornAt_heq_of_eq hbirth _ _ rfl

/-- Every element of `L_alpha` is uniquely a set born at one `beta < alpha`. -/
noncomputable def lStageCarrierEquivBirthLayers (alpha : Ordinal.{u}) :
    LStageCarrier alpha ≃ BirthLayers alpha where
  toFun := toBirthLayers alpha
  invFun := fromBirthLayers alpha
  left_inv := fromBirthLayers_toBirthLayers alpha
  right_inv := toBirthLayers_fromBirthLayers alpha

/-! ## Lexicographically combining external layer orders -/

/-- Lexicographic order: first compare birth ordinals, then compare inside a
fixed birth layer. -/
def birthLayersRel (alpha : Ordinal.{u})
    (s : ∀ beta : Set.Iio alpha,
      BornAt beta.1 → BornAt beta.1 → Prop) :
    BirthLayers alpha → BirthLayers alpha → Prop :=
  PSigma.Lex (fun beta gamma : Set.Iio alpha => beta.1 < gamma.1) s

private theorem psigmaLex_isWellOrder
    {ι : Type u} {family : ι → Type v}
    (r : ι → ι → Prop) (s : ∀ i, family i → family i → Prop)
    [IsWellOrder ι r] [∀ i, IsWellOrder (family i) (s i)] :
    IsWellOrder (PSigma family) (PSigma.Lex r s) := by
  refine
    { wf := WellFounded.intro fun
        | ⟨i, x⟩ =>
            PSigma.lexAccessible
              ((IsWellFounded.wf : WellFounded r).apply i)
              (fun j =>
                (IsWellFounded.wf : WellFounded (s j))) x
      trichotomous := ?_ }
  apply (Std.trichotomous_of_rel_or_eq_or_rel_swap ?_).trichotomous
  rintro ⟨i, x⟩ ⟨j, y⟩
  rcases trichotomous_of r i j with hij | hij | hji
  · exact Or.inl (PSigma.Lex.left x y hij)
  · subst j
    rcases trichotomous_of (s i) x y with hxy | hxy | hyx
    · exact Or.inl (PSigma.Lex.right i hxy)
    · subst y
      exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (PSigma.Lex.right i hyx))
  · exact Or.inr (Or.inr (PSigma.Lex.left y x hji))

/-- A well-order on every birth layer combines to a well-order on their
dependent sum. -/
theorem birthLayersRel_isWellOrder (alpha : Ordinal.{u})
    (s : ∀ beta : Set.Iio alpha,
      BornAt beta.1 → BornAt beta.1 → Prop)
    (hs : ∀ beta, IsWellOrder (BornAt beta.1) (s beta)) :
    IsWellOrder (BirthLayers alpha) (birthLayersRel alpha s) := by
  letI : IsWellOrder (Set.Iio alpha)
      (fun beta gamma : Set.Iio alpha => beta.1 < gamma.1) := by
    refine
      { wf := InvImage.wf Subtype.val
          (IsWellFounded.wf :
            WellFounded ((· < ·) : Ordinal.{u} → Ordinal.{u} → Prop))
        trichotomous :=
          (InvImage.trichotomous
            (r := ((· < ·) : Ordinal.{u} → Ordinal.{u} → Prop))
            Subtype.val_injective).trichotomous }
  letI : ∀ beta, IsWellOrder (BornAt beta.1) (s beta) := hs
  exact psigmaLex_isWellOrder
    (fun beta gamma : Set.Iio alpha => beta.1 < gamma.1) s

/-- Pull a family of birth-layer orders back to the ordinary carrier of
`LStageZF alpha`. -/
noncomputable def lStageBirthRel (alpha : Ordinal.{u})
    (s : ∀ beta : Set.Iio alpha,
      BornAt beta.1 → BornAt beta.1 → Prop) :
    LStageCarrier alpha → LStageCarrier alpha → Prop :=
  InvImage (birthLayersRel alpha s)
    (lStageCarrierEquivBirthLayers alpha)

/-- Any family of external well-orders on the birth layers induces an
external well-order on `LStageZF alpha`. -/
theorem lStageBirthRel_isWellOrder (alpha : Ordinal.{u})
    (s : ∀ beta : Set.Iio alpha,
      BornAt beta.1 → BornAt beta.1 → Prop)
    (hs : ∀ beta, IsWellOrder (BornAt beta.1) (s beta)) :
    IsWellOrder (LStageCarrier alpha) (lStageBirthRel alpha s) := by
  letI : IsWellOrder (BirthLayers alpha) (birthLayersRel alpha s) :=
    birthLayersRel_isWellOrder alpha s hs
  refine
    { wf := InvImage.wf (lStageCarrierEquivBirthLayers alpha)
        (IsWellFounded.wf : WellFounded (birthLayersRel alpha s))
      trichotomous :=
        (InvImage.trichotomous (r := birthLayersRel alpha s)
          (lStageCarrierEquivBirthLayers alpha).injective).trichotomous }

end Constructible
