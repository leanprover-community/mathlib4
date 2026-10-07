/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Presentable.SharplyLT.Basic

/-!
# Lemmas about sharply smaller regular cardinals

We obtain two lemmas `Cardinal.SharplyLT.of_pow_lt` and `Cardinal.SharplyLT.of_le` which
allow to show that certain regular cardinals are sharply smaller
than others. We also obtain `Cardinal.SharplyLT.exists_of_small` (and
variants `exists_of_pair` and `exists_of_triple`) which shows that for
any small family of regular cardinals, there exists a regular cardinal
that is sharply greater than all the cardinals in the family.

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace CategoryTheory.CardinalDirectedPoset.SetCardinalLT

variable (κ : Cardinal.{u}) (X : Type u)

/-- The surjectivity of this map (see lemma `fromSigma_surjective`) says that
if `X` is a type, then any subset of `X` that is of cardinality `< κ` can be obtained
as the range of a map `κ'.ord.ToType → X` for some `κ' < κ`. -/
def fromSigma (x : Σ (κ' : Set.Iio κ), κ'.val.ord.ToType → X) : SetCardinalLT κ X :=
  ⟨Set.range x.2,
    HasCardinalLT.of_surjective
      (by simpa only [hasCardinalLT_iff_cardinal_mk_lt,
        Cardinal.mk_toType, Cardinal.card_ord] using! x.1.prop) _
      Set.rangeFactorization_surjective⟩

/-- If `X` is a type, then any subset of `X` that is of cardinality `< κ` can
be obtained as the range of a map `κ'.ord.ToType → X` for some `κ' < κ`. -/
lemma fromSigma_surjective : Function.Surjective (fromSigma κ X) := by
  rintro ⟨A, hA⟩
  rw [hasCardinalLT_iff_cardinal_mk_lt] at hA
  let e : (Cardinal.mk A).ord.ToType ≃ A :=
    Nonempty.some (by simp [← Cardinal.lift_mk_eq'])
  refine ⟨⟨⟨_, hA⟩, Subtype.val ∘ e⟩, ?_⟩
  rw [Subtype.mk_eq_mk]
  simp [fromSigma]

end CategoryTheory.CardinalDirectedPoset.SetCardinalLT

namespace Cardinal.SharplyLT

open CardinalDirectedPoset

lemma of_pow_lt {κ₁ κ₂ : Cardinal.{u}} [Fact κ₁.IsRegular] [Fact κ₂.IsRegular]
    (h₀ : κ₁ < κ₂) (h : ∀ (α β : Cardinal.{u}), α < κ₁ → β < κ₂ → β ^ α < κ₂) :
    SharplyLT κ₁ κ₂ :=
  .of_exists_cofinal h₀ (fun X hX ↦ by
    refine ⟨.univ, ?_, by simp⟩
    rw [hasCardinalLT_iff_of_equiv (Equiv.Set.univ _)]
    refine HasCardinalLT.of_surjective ?_ _ (SetCardinalLT.fromSigma_surjective _ _)
    refine hasCardinalLT_sigma _ _ ?_ (fun ⟨α, hα⟩ ↦ ?_)
    · refine lt_of_le_of_lt (le_trans ?_ (Cardinal.mk_iio_le_lift κ₁)) (by simpa)
      rw [lift_id'.{u, u + 1}]
    · simpa [hasCardinalLT_iff_cardinal_mk_lt] using
        h _ _ hα (by rwa [hasCardinalLT_iff_cardinal_mk_lt] at hX))

lemma succ_two_pow_of_le {κ₁ κ₂ : Cardinal.{u}} [Fact κ₁.IsRegular]
    (h₀ : κ₁ ≤ κ₂) (hκ₂ : Cardinal.aleph0 ≤ κ₂) :
    letI : Fact (Cardinal.IsRegular (Order.succ (2 ^ κ₂))) :=
      ⟨isRegular_succ (hκ₂.trans (cantor _).le)⟩
    SharplyLT κ₁ (Order.succ (2 ^ κ₂)) := by
  let : Fact (Cardinal.IsRegular (Order.succ (2 ^ κ₂))) :=
    ⟨isRegular_succ (hκ₂.trans (cantor _).le)⟩
  refine of_pow_lt ?_ (fun α β hα hβ ↦ ?_)
  · simp only [Order.lt_succ_iff]
    exact h₀.trans (cantor _).le
  · simp only [Order.lt_succ_iff] at hβ ⊢
    refine (power_le_power_right hβ).trans ?_
    rw [← power_mul]
    refine power_le_power_left (by simp) ?_
    conv_rhs => rw [← mul_eq_self hκ₂]
    exact mul_le_mul_right (hα.le.trans h₀) _

lemma exists_of_small {ι : Type*} [Small.{u} ι] (κ : ι → Cardinal.{u})
    [∀ i, Fact (κ i).IsRegular] :
    ∃ (κ' : Cardinal.{u}) (_ : Fact κ'.IsRegular),
      ∀ i, SharplyLT (κ i) κ' := by
  obtain ⟨κ₀, hκ₀, h⟩ :
      ∃ (κ₀ : Cardinal.{u}), Cardinal.aleph0 ≤ κ₀ ∧ ∀ (i : ι), κ i ≤ κ₀ := by
    obtain ⟨κ', h⟩ := Cardinal.exists_le_of_small κ
    exact ⟨max κ' .aleph0, by simp, fun i ↦ (h i).trans (by simp)⟩
  exact ⟨Order.succ (2 ^ κ₀), ⟨isRegular_succ (hκ₀.trans (cantor _).le)⟩,
    fun i ↦ succ_two_pow_of_le (h i) hκ₀⟩

lemma exists_single (κ : Cardinal.{u}) [Fact κ.IsRegular] :
    ∃ (κ' : Cardinal.{u}) (_ : Fact κ'.IsRegular),
      SharplyLT κ κ' := by
  obtain ⟨κ', f, h⟩ := exists_of_small (fun (_ : Unit) ↦ κ)
  exact ⟨κ', f, h ()⟩

lemma exists_of_pair (κ₁ κ₂ : Cardinal.{u})
    [Fact κ₁.IsRegular] [Fact κ₂.IsRegular] :
    ∃ (κ' : Cardinal.{u}) (_ : Fact κ'.IsRegular),
      SharplyLT κ₁ κ' ∧ SharplyLT κ₂ κ' := by
  let f (i : Fin 2) : Cardinal.{u} := match i with
    | 0 => κ₁
    | 1 => κ₂
  have (i : _) : Fact (f i).IsRegular := match i with
    | 0 => by assumption
    | 1 => by assumption
  obtain ⟨κ', _, h₂⟩ := exists_of_small f
  exact ⟨κ', inferInstance, h₂ 0, h₂ 1⟩

lemma exists_of_triple (κ₁ κ₂ κ₃ : Cardinal.{u})
    [Fact κ₁.IsRegular] [Fact κ₂.IsRegular] [Fact κ₃.IsRegular] :
    ∃ (κ' : Cardinal.{u}) (_ : Fact κ'.IsRegular),
      SharplyLT κ₁ κ' ∧ SharplyLT κ₂ κ' ∧ SharplyLT κ₃ κ':= by
  obtain ⟨κ₁₂, _, h₁, h₂⟩ := exists_of_pair κ₁ κ₂
  obtain ⟨κ, _, h₁₂, h₃⟩ := exists_of_pair κ₁₂ κ₃
  exact ⟨κ, inferInstance, h₁.trans h₁₂, h₂.trans h₁₂, h₃⟩


local instance (κ : Cardinal.{u}) [Fact κ.IsRegular] : Fact (Cardinal.IsRegular (Order.succ κ)) :=
  .mk <| Cardinal.isRegular_succ (inferInstance : Fact (Cardinal.IsRegular κ)).out.aleph0_le

-- TODO: clean up this proof. Currently it is ewww
lemma succ (κ : Cardinal.{u}) [Fact κ.IsRegular] : Cardinal.SharplyLT κ (Order.succ κ) := by
  refine Cardinal.SharplyLT.tfae (Order.lt_succ _) |>.out 1 4 |>.mpr ?_
  intro X hX
  have : Cardinal.aleph0 ≤ κ := Cardinal.IsRegular.aleph0_le Fact.out
  rw [hasCardinalLT_iff_cardinal_mk_lt, Order.lt_succ_iff] at hX
  obtain ⟨Φ⟩ : Nonempty (X ↪ κ.ord.ToType) := by simpa [← Cardinal.le_def]
  let Ψ (x : κ.ord.ToType) : CardinalDirectedPoset.SetCardinalLT κ X :=
    ⟨Φ ⁻¹' (Set.Iic x), by
      simp only [hasCardinalLT_iff_cardinal_mk_lt]
      grw [Cardinal.mk_preimage_of_injective]
      · have := Cardinal.mk_Iio_lt x (by simp)
        rw [← Set.Iio_union_right]
        grw [Cardinal.mk_union_le]
        simp only [Cardinal.mk_toType, Cardinal.card_ord, Cardinal.mk_fintype, Fintype.card_unique,
          Nat.cast_one] at this ⊢
        exact Cardinal.add_one_lt_of_lt (by assumption) this
      · exact Φ.injective⟩
  use Set.range Ψ
  constructor
  · rw [hasCardinalLT_iff_cardinal_mk_lt]
    grw [Cardinal.mk_range_le]
    simp
  · intro x
    let G0 : X → Set.Iio κ.ord := Ordinal.ToType.toOrd ∘ Φ
    let V : Set _ := G0 '' x
    let W : Set Ordinal := (↑) '' V
    have bdda : BddAbove W := by
      use κ.ord
      simp only [upperBounds, Set.mem_ofPred_eq]
      grind
    let W' := sSup W
    have : ∀ T ∈ W, T < κ.ord := by
      intro T hT
      have := x.prop
      simp [hasCardinalLT_iff_cardinal_mk_lt] at this
      grind
    have : W' < κ.ord := by
      apply Ordinal.sSup_lt_of_lt_cof _ this
      have := x.prop
      simp [hasCardinalLT_iff_cardinal_mk_lt] at this
      simp only [Cardinal.lift_ord, gt_iff_lt, W, V]
      grw [Cardinal.mk_image_le]
      have := Cardinal.mk_image_le_lift (f := G0) (s := x.val)
      rw [← Cardinal.lift_ord, ← Ordinal.lift_cof, Cardinal.IsRegular.cof_ord (Fact.out),
        ← Cardinal.lift_lt.{u + 1}]
      grw [this]
      simpa
    let j1 := Ψ <| Ordinal.ToType.mk ⟨W', this⟩
    refine ⟨j1, Set.mem_range_self _, ?_⟩
    dsimp [j1, W', Ψ, W, V]
    intro x0 hx0
    simp only [Set.mem_preimage, Set.mem_Iic, ← (Ordinal.ToType.mk (o := κ.ord)).symm.le_iff_le,
      OrderIso.symm_apply_apply]
    rw [← Subtype.coe_le_coe]
    have : Set.Nonempty W := by
      have : x.val.Nonempty := ⟨x0, hx0⟩
      simpa [W, V]
    have := ConditionallyCompleteLattice.isLUB_csSup W this bdda|>.1.out
    apply this
    simp only [Set.mem_image, exists_exists_and_eq_and, W, V, G0]
    exact ⟨x0, hx0, rfl⟩

end Cardinal.SharplyLT
