/-
Copyright (c) 2022 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Junyan Xu, Jack McKoen
-/
module

public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.Localization.AsSubring
public import Mathlib.Algebra.Algebra.Subalgebra.Tower
public import Mathlib.Algebra.Ring.Subring.Pointwise
public import Mathlib.Algebra.Ring.Action.Field
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!

# Valuation subrings of a field

## Projects

The order structure on `ValuationSubring K`.

-/

@[expose] public section


universe u

noncomputable section

variable (K : Type u) [Field K]

/-- A valuation subring of a field `K` is a subring `A` such that for every `x : K`,
either `x ∈ A` or `x⁻¹ ∈ A`.

This is equivalent to being maximal in the domination order
of local subrings (the stacks project definition). See `LocalSubring.isMax_iff`.
-/
structure ValuationSubring extends Subring K where
  mem_or_inv_mem' : ∀ x : K, x ∈ carrier ∨ x⁻¹ ∈ carrier

namespace ValuationSubring

variable {K}
variable (A : ValuationSubring K)

instance : SetLike (ValuationSubring K) K where
  coe A := A.toSubring
  coe_injective' := by
    intro ⟨_, _⟩ ⟨_, _⟩ h
    replace h := SetLike.coe_injective' h
    congr

instance : PartialOrder (ValuationSubring K) := .ofSetLike (ValuationSubring K) K

theorem mem_carrier (x : K) : x ∈ A.carrier ↔ x ∈ A := Iff.refl _

@[simp]
theorem mem_toSubring (x : K) : x ∈ A.toSubring ↔ x ∈ A := Iff.refl _

@[ext]
theorem ext (A B : ValuationSubring K) (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B := SetLike.ext h

theorem zero_mem : (0 : K) ∈ A := A.toSubring.zero_mem

theorem one_mem : (1 : K) ∈ A := A.toSubring.one_mem

theorem add_mem (x y : K) : x ∈ A → y ∈ A → x + y ∈ A := A.toSubring.add_mem

theorem mul_mem (x y : K) : x ∈ A → y ∈ A → x * y ∈ A := A.toSubring.mul_mem

theorem neg_mem (x : K) : x ∈ A → -x ∈ A := A.toSubring.neg_mem

theorem mem_or_inv_mem (x : K) : x ∈ A ∨ x⁻¹ ∈ A := A.mem_or_inv_mem' _

instance : SubringClass (ValuationSubring K) K where
  zero_mem := zero_mem
  add_mem {_} a b := add_mem _ a b
  one_mem := one_mem
  mul_mem {_} a b := mul_mem _ a b
  neg_mem {_} x := neg_mem _ x

theorem toSubring_injective : Function.Injective (toSubring : ValuationSubring K → Subring K) :=
  fun x y h => by cases x; cases y; congr

instance : CommRing A := inferInstanceAs <| CommRing A.toSubring

instance : IsDomain A := inferInstanceAs <| IsDomain A.toSubring

instance : Top (ValuationSubring K) :=
  Top.mk <| { (⊤ : Subring K) with mem_or_inv_mem' := fun _ => Or.inl trivial }

@[simp]
theorem toSubring_top : (⊤ : ValuationSubring K).toSubring = ⊤ := rfl

@[simp]
theorem mem_top (x : K) : x ∈ (⊤ : ValuationSubring K) :=
  trivial

theorem le_top : A ≤ ⊤ := fun _a _ha => mem_top _

/-- If `K` is a field, then so is `K` viewed as a valuation subring
of itself. (That is, `⊤ : ValuationSubring K`.) -/
instance : Field (⊤ : ValuationSubring K) := inferInstanceAs (Field (⊤ : Subfield K))

@[simp, norm_cast]
theorem top_coe_div (x y : (⊤ : ValuationSubring K)) :
    ((x / y : (⊤ : ValuationSubring K)) : K) = (x : K) / (y : K) :=
  rfl

@[simp, norm_cast]
theorem top_coe_inv (x : (⊤ : ValuationSubring K)) :
    ((x⁻¹ : (⊤ : ValuationSubring K)) : K) = (x : K)⁻¹ :=
  rfl

instance : OrderTop (ValuationSubring K) where
  le_top := le_top

instance : Inhabited (ValuationSubring K) :=
  ⟨⊤⟩

instance : ValuationRing A where
  cond' a b := by
    by_cases h : (b : K) = 0
    · use 0
      left
      ext
      simp [h]
    by_cases h : (a : K) = 0
    · use 0; right
      ext
      simp [h]
    rcases A.mem_or_inv_mem (a / b) with hh | hh
    · use ⟨a / b, hh⟩
      right
      ext
      simp [field]
    · rw [show (a / b : K)⁻¹ = b / a by simp] at hh
      use ⟨b / a, hh⟩
      left
      ext
      simp [field]

instance : Algebra A K := inferInstance

instance isLocalRing : IsLocalRing A := inferInstance

@[simp]
theorem algebraMap_apply (a : A) : algebraMap A K a = a := rfl

instance : IsFractionRing A K where
  map_units := fun ⟨y, hy⟩ =>
    (Units.mk0 (y : K) fun c => nonZeroDivisors.ne_zero hy <| Subtype.ext c).isUnit
  surj z := by
    by_cases h : z = 0; · use (0, 1); simp [h]
    rcases A.mem_or_inv_mem z with hh | hh
    · use (⟨z, hh⟩, 1); simp
    · refine ⟨⟨1, ⟨⟨_, hh⟩, ?_⟩⟩, mul_inv_cancel₀ h⟩
      exact mem_nonZeroDivisors_iff_ne_zero.2 fun c => h (inv_eq_zero.mp (congr_arg Subtype.val c))
  exists_of_eq {a b} h := ⟨1, by ext; simpa using h⟩

/-- The value group of the valuation associated to `A`. Note: it is actually a group with zero. -/
def ValueGroup :=
  ValuationRing.ValueGroup A K
deriving LinearOrderedCommGroupWithZero

/-- Any valuation subring of `K` induces a natural valuation on `K`. -/
def valuation : Valuation K A.ValueGroup :=
  ValuationRing.valuation A K

instance inhabitedValueGroup : Inhabited A.ValueGroup := ⟨A.valuation 0⟩

theorem valuation_le_one (a : A) : A.valuation a ≤ 1 :=
  (ValuationRing.mem_integer_iff A K _).2 ⟨a, rfl⟩

theorem mem_of_valuation_le_one (x : K) (h : A.valuation x ≤ 1) : x ∈ A :=
  let ⟨a, ha⟩ := (ValuationRing.mem_integer_iff A K x).1 h
  ha ▸ a.2

@[simp]
theorem valuation_le_one_iff (x : K) : A.valuation x ≤ 1 ↔ x ∈ A :=
  ⟨mem_of_valuation_le_one _ _, fun ha => A.valuation_le_one ⟨x, ha⟩⟩

theorem valuation_eq_iff (x y : K) : A.valuation x = A.valuation y ↔ ∃ a : Aˣ, (a : K) * y = x :=
  Quotient.eq''

theorem valuation_le_iff (x y : K) : A.valuation x ≤ A.valuation y ↔ ∃ a : A, (a : K) * y = x :=
  Iff.rfl

theorem valuation_surjective : Function.Surjective A.valuation := Quot.mk_surjective

@[simp]
theorem valuation_unit (a : Aˣ) : A.valuation a = 1 := by
  rw [← A.valuation.map_one, valuation_eq_iff]; use a; simp

theorem valuation_eq_one_iff (a : A) : IsUnit a ↔ A.valuation a = 1 where
  mp h := A.valuation_unit h.unit
  mpr h := by
    have ha : (a : K) ≠ 0 := by
      intro c
      rw [c, A.valuation.map_zero] at h
      exact zero_ne_one h
    have ha' : (a : K)⁻¹ ∈ A := by rw [← valuation_le_one_iff, map_inv₀, h, inv_one]
    refine .of_mul_eq_one ⟨a⁻¹, ha'⟩ ?_
    ext
    simp [field]

theorem eq_top_iff : A = ⊤ ↔ ¬ A.valuation.IsNontrivial := by
  simp [Valuation.IsNontrivial_iff_exists_one_lt, SetLike.ext_iff]

theorem valuation_lt_one_or_eq_one (a : A) : A.valuation a < 1 ∨ A.valuation a = 1 :=
  lt_or_eq_of_le (A.valuation_le_one a)

theorem valuation_lt_one_iff (a : A) : a ∈ IsLocalRing.maximalIdeal A ↔ A.valuation a < 1 := by
  rw [IsLocalRing.mem_maximalIdeal]
  dsimp [nonunits]; rw [valuation_eq_one_iff]
  exact (A.valuation_le_one a).lt_iff_ne.symm

/-- A subring `R` of `K` such that for all `x : K` either `x ∈ R` or `x⁻¹ ∈ R` is
  a valuation subring of `K`. -/
def ofSubring (R : Subring K) (hR : ∀ x : K, x ∈ R ∨ x⁻¹ ∈ R) : ValuationSubring K :=
  { R with mem_or_inv_mem' := hR }

@[simp]
theorem mem_ofSubring (R : Subring K) (hR : ∀ x : K, x ∈ R ∨ x⁻¹ ∈ R) (x : K) :
    x ∈ ofSubring R hR ↔ x ∈ R :=
  Iff.refl _

/-- An overring of a valuation ring is a valuation ring. -/
def ofLE (R : ValuationSubring K) (S : Subring K) (h : R.toSubring ≤ S) : ValuationSubring K :=
  { S with mem_or_inv_mem' := fun x => (R.mem_or_inv_mem x).imp (@h x) (@h _) }

section Order

instance : SemilatticeSup (ValuationSubring K) :=
  { (inferInstance : PartialOrder (ValuationSubring K)) with
    sup := fun R S => ofLE R (R.toSubring ⊔ S.toSubring) <| le_sup_left
    le_sup_left := fun R S _ hx => (le_sup_left : R.toSubring ≤ R.toSubring ⊔ S.toSubring) hx
    le_sup_right := fun R S _ hx => (le_sup_right : S.toSubring ≤ R.toSubring ⊔ S.toSubring) hx
    sup_le := fun R S T hR hT _ hx => (sup_le hR hT : R.toSubring ⊔ S.toSubring ≤ T.toSubring) hx }

/-- The ring homomorphism induced by the partial order. -/
def inclusion (R S : ValuationSubring K) (h : R ≤ S) : R →+* S :=
  Subring.inclusion h

/-- The canonical ring homomorphism from a valuation ring to its field of fractions. -/
def subtype (R : ValuationSubring K) : R →+* K :=
  Subring.subtype R.toSubring

@[simp]
lemma subtype_apply {R : ValuationSubring K} (x : R) :
    R.subtype x = x := rfl

lemma subtype_injective (R : ValuationSubring K) :
    Function.Injective R.subtype :=
  R.toSubring.subtype_injective

@[simp]
theorem coe_subtype (R : ValuationSubring K) : ⇑(subtype R) = Subtype.val :=
  rfl

/-- The canonical map on value groups induced by a coarsening of valuation rings. -/
def mapOfLE (R S : ValuationSubring K) (h : R ≤ S) : R.ValueGroup →*₀ S.ValueGroup where
  toFun := Quotient.map' id fun _ _ ⟨u, hu⟩ => ⟨Units.map (R.inclusion S h).toMonoidHom u, hu⟩
  map_zero' := rfl
  map_one' := rfl
  map_mul' := by rintro ⟨⟩ ⟨⟩; rfl

@[mono]
theorem monotone_mapOfLE (R S : ValuationSubring K) (h : R ≤ S) : Monotone (R.mapOfLE S h) := by
  rintro ⟨⟩ ⟨⟩ ⟨a, ha⟩; exact ⟨R.inclusion S h a, ha⟩

@[simp]
theorem mapOfLE_comp_valuation (R S : ValuationSubring K) (h : R ≤ S) :
    R.mapOfLE S h ∘ R.valuation = S.valuation := by ext; rfl

@[simp]
theorem mapOfLE_valuation_apply (R S : ValuationSubring K) (h : R ≤ S) (x : K) :
    R.mapOfLE S h (R.valuation x) = S.valuation x := rfl

/-- The ideal corresponding to a coarsening of a valuation ring. -/
def idealOfLE (R S : ValuationSubring K) (h : R ≤ S) : Ideal R :=
  (IsLocalRing.maximalIdeal S).comap (R.inclusion S h)

@[simp]
theorem idealOfLE_self : A.idealOfLE A (refl _) = IsLocalRing.maximalIdeal A := rfl

@[simp]
theorem idealOfLE_top : A.idealOfLE ⊤ (fun _ _ => trivial) = ⊥ := by
  rw [Submodule.eq_bot_iff, ValuationSubring.idealOfLE]
  intro x hx
  simp only [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_comap, Submodule.mem_bot, Subtype.ext_iff,
    ZeroMemClass.coe_zero] at hx ⊢
  rw [← hx]
  rfl

instance prime_idealOfLE (R S : ValuationSubring K) (h : R ≤ S) : (idealOfLE R S h).IsPrime :=
  (IsLocalRing.maximalIdeal S).comap_isPrime _

/-- The coarsening of a valuation ring associated to a prime ideal. -/
def ofPrime (A : ValuationSubring K) (P : Ideal A) [P.IsPrime] : ValuationSubring K :=
  ofLE A (Localization.subalgebra.ofField K _ P.primeCompl_le_nonZeroDivisors).toSubring
    fun a ha => Subalgebra.mem_toSubring.mpr <|
      Subalgebra.algebraMap_mem
        (Localization.subalgebra.ofField K _ P.primeCompl_le_nonZeroDivisors) (⟨a, ha⟩ : A)

instance ofPrimeAlgebra (A : ValuationSubring K) (P : Ideal A) [P.IsPrime] :
    Algebra A (A.ofPrime P) :=
  Subalgebra.algebra (Localization.subalgebra.ofField K _ P.primeCompl_le_nonZeroDivisors)

instance ofPrime_scalar_tower (A : ValuationSubring K) (P : Ideal A) [P.IsPrime] :
    letI : SMul A (A.ofPrime P) := SMulZeroClass.toSMul
    IsScalarTower A (A.ofPrime P) K :=
  IsScalarTower.subalgebra' A K K
    (Localization.subalgebra.ofField K _ P.primeCompl_le_nonZeroDivisors)

instance ofPrime_localization (A : ValuationSubring K) (P : Ideal A) [P.IsPrime] :
    IsLocalization.AtPrime (A.ofPrime P) P := by
  apply
    Localization.subalgebra.isLocalization_ofField K P.primeCompl
      P.primeCompl_le_nonZeroDivisors

theorem le_ofPrime (A : ValuationSubring K) (P : Ideal A) [P.IsPrime] : A ≤ ofPrime A P :=
  fun a ha => Subalgebra.mem_toSubring.mpr <| Subalgebra.algebraMap_mem _ (⟨a, ha⟩ : A)

theorem ofPrime_valuation_eq_one_iff_mem_primeCompl (A : ValuationSubring K) (P : Ideal A)
    [P.IsPrime] (x : A) : (ofPrime A P).valuation x = 1 ↔ x ∈ P.primeCompl := by
  rw [← IsLocalization.AtPrime.isUnit_to_map_iff (A.ofPrime P) P x, valuation_eq_one_iff]; rfl

@[simp]
theorem idealOfLE_ofPrime (A : ValuationSubring K) (P : Ideal A) [P.IsPrime] :
    idealOfLE A (ofPrime A P) (le_ofPrime A P) = P := by
  refine Ideal.ext (fun x => ?_)
  apply IsLocalization.AtPrime.to_map_mem_maximal_iff
  exact isLocalRing (ofPrime A P)

@[simp]
theorem ofPrime_idealOfLE (R S : ValuationSubring K) (h : R ≤ S) :
    ofPrime R (idealOfLE R S h) = S := by
  ext x; constructor
  · rintro ⟨a, r, hr, rfl⟩; apply mul_mem; · exact h a.2
    · rw [← valuation_le_one_iff, map_inv₀, ← inv_one, inv_le_inv₀]
      · exact not_lt.1 ((not_iff_not.2 <| valuation_lt_one_iff S _).1 hr)
      · simpa [Valuation.pos_iff] using fun hr₀ ↦ hr₀ ▸ hr <| Ideal.zero_mem (R.idealOfLE S h)
      · exact zero_lt_one
  · intro hx; by_cases hr : x ∈ R; · exact R.le_ofPrime _ hr
    have : x ≠ 0 := fun h => hr (by rw [h]; exact R.zero_mem)
    replace hr := (R.mem_or_inv_mem x).resolve_left hr
    refine ⟨1, ⟨x⁻¹, hr⟩, ?_, ?_⟩
    · simp only [Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_compl_iff,
        SetLike.mem_coe, idealOfLE, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        not_not]
      change IsUnit (⟨x⁻¹, h hr⟩ : S)
      refine .of_mul_eq_one (⟨x, hx⟩ : S) ?_
      ext
      simp [field]
    · simp

@[simp]
theorem ofPrime_bot : A.ofPrime (⊥ : Ideal A) = ⊤ := by
  simp [← idealOfLE_top, ValuationSubring.ofPrime_idealOfLE]

@[simp]
theorem ofPrime_top : A.ofPrime (IsLocalRing.maximalIdeal A) = A := by simp [← idealOfLE_self]

theorem ofPrime_le_of_le (P Q : Ideal A) [P.IsPrime] [Q.IsPrime] (h : P ≤ Q) :
    ofPrime A Q ≤ ofPrime A P := fun _x ⟨a, s, hs, he⟩ => ⟨a, s, fun c => hs (h c), he⟩

theorem idealOfLE_le_of_le (R S : ValuationSubring K) (hR : A ≤ R) (hS : A ≤ S) (h : R ≤ S) :
    idealOfLE A S hS ≤ idealOfLE A R hR := fun x hx =>
  (valuation_lt_one_iff R _).2
    (by
      by_contra! c; replace c := monotone_mapOfLE R S h c
      rw [(mapOfLE _ _ _).map_one, mapOfLE_valuation_apply] at c
      apply not_le_of_gt ((valuation_lt_one_iff S _).1 hx) c)

/-- The equivalence between coarsenings of a valuation ring and its prime ideals. -/
@[simps apply]
def primeSpectrumEquiv : PrimeSpectrum A ≃ {S // A ≤ S} where
  toFun P := ⟨ofPrime A P.asIdeal, le_ofPrime _ _⟩
  invFun S := ⟨idealOfLE _ S S.2, inferInstance⟩
  left_inv P := by ext1; simp
  right_inv S := by ext1; simp

/-- An ordered variant of `primeSpectrumEquiv`. -/
@[simps!]
def primeSpectrumOrderEquiv : (PrimeSpectrum A)ᵒᵈ ≃o {S // A ≤ S} :=
  { OrderDual.ofDual.trans (primeSpectrumEquiv A) with
    map_rel_iff' {a b} :=
      ⟨a.rec <| fun a => b.rec <| fun b => fun h => by
        simp only [OrderDual.toDual_le_toDual]
        dsimp at h
        have := idealOfLE_le_of_le A _ _ ?_ ?_ h
        · rwa [idealOfLE_ofPrime, idealOfLE_ofPrime] at this
        all_goals exact le_ofPrime A (PrimeSpectrum.asIdeal _),
      fun h => by apply ofPrime_le_of_le; exact h⟩ }

instance le_total_ideal : @Std.Total {S // A ≤ S} (· ≤ ·) := by
  classical
  let _ : @Std.Total (PrimeSpectrum A) (· ≤ ·) := ⟨fun ⟨x, _⟩ ⟨y, _⟩ => LE.total.total x y⟩
  exact (primeSpectrumOrderEquiv A).symm.toRelEmbedding.total

open scoped Classical in
instance linearOrderOverring : LinearOrder {S // A ≤ S} where
  le_total := (le_total_ideal A).1
  max_def a b := congr_fun₂ sup_eq_maxDefault a b
  toDecidableLE := _

end Order

end ValuationSubring

namespace Valuation

variable {K}
variable {Γ Γ₁ Γ₂ : Type*} [LinearOrderedCommGroupWithZero Γ]
  [LinearOrderedCommGroupWithZero Γ₁] [LinearOrderedCommGroupWithZero Γ₂] (v : Valuation K Γ)
  (v₁ : Valuation K Γ₁) (v₂ : Valuation K Γ₂)

/-- The valuation subring associated to a valuation. -/
def valuationSubring : ValuationSubring K :=
  { v.integer with
    mem_or_inv_mem' := by
      intro x
      rcases val_le_one_or_val_inv_le_one v x with h | h
      exacts [Or.inl h, Or.inr h] }

@[simp]
theorem mem_valuationSubring_iff (x : K) : x ∈ v.valuationSubring ↔ v x ≤ 1 := Iff.refl _

theorem isEquiv_iff_valuationSubring :
    v₁.IsEquiv v₂ ↔ v₁.valuationSubring = v₂.valuationSubring := by
  constructor
  · intro h; ext x; specialize h x 1; simpa using h
  · intro h; apply isEquiv_of_val_le_one
    intro x
    have : x ∈ v₁.valuationSubring ↔ x ∈ v₂.valuationSubring := by rw [h]
    simpa using this

theorem isEquiv_valuation_valuationSubring : v.IsEquiv v.valuationSubring.valuation := by
  rw [isEquiv_iff_val_le_one]
  intro x
  rw [ValuationSubring.valuation_le_one_iff, mem_valuationSubring_iff]

@[simp]
theorem isNontrivial_valuation_valuationSubring_iff :
    v.valuationSubring.valuation.IsNontrivial ↔ v.IsNontrivial :=
  (isEquiv_valuation_valuationSubring v).isNontrivial_iff.symm

lemma valuationSubring.integers : v.Integers v.valuationSubring :=
  Valuation.integer.integers _

@[simp]
theorem valuationSubring_eq_top_iff : v.valuationSubring = ⊤ ↔ ¬ v.IsNontrivial := by
  simp [ValuationSubring.eq_top_iff]

end Valuation

namespace ValuationSubring

variable {K}
variable (A : ValuationSubring K)

@[simp]
theorem valuationSubring_valuation : A.valuation.valuationSubring = A := by
  ext; rw [← A.valuation_le_one_iff]; rfl

theorem integer_valuation : A.valuation.integer = A.toSubring :=
  congr(($A.valuationSubring_valuation).toSubring)

section UnitGroup

/-- The unit group of a valuation subring, as a subgroup of `Kˣ`. -/
def unitGroup : Subgroup Kˣ :=
  (A.valuation.toMonoidWithZeroHom.toMonoidHom.comp (Units.coeHom K)).ker

@[simp]
theorem mem_unitGroup_iff (x : Kˣ) : x ∈ A.unitGroup ↔ A.valuation x = 1 := Iff.rfl

/-- For a valuation subring `A`, `A.unitGroup` agrees with the units of `A`. -/
def unitGroupMulEquiv : A.unitGroup ≃* Aˣ where
  toFun x :=
    { val := ⟨(x : Kˣ), mem_of_valuation_le_one A _ x.prop.le⟩
      inv := ⟨((x⁻¹ : A.unitGroup) : Kˣ), mem_of_valuation_le_one _ _ x⁻¹.prop.le⟩
      val_inv := Subtype.ext (by simp)
      inv_val := Subtype.ext (by simp) }
  invFun x := ⟨Units.map A.subtype.toMonoidHom x, A.valuation_unit x⟩
  map_mul' a b := by ext; rfl

@[simp]
theorem coe_unitGroupMulEquiv_apply (a : A.unitGroup) :
    ((A.unitGroupMulEquiv a : A) : K) = ((a : Kˣ) : K) := rfl

@[simp]
theorem coe_unitGroupMulEquiv_symm_apply (a : Aˣ) : ((A.unitGroupMulEquiv.symm a : Kˣ) : K) = a :=
  rfl

theorem unitGroup_le_unitGroup {A B : ValuationSubring K} : A.unitGroup ≤ B.unitGroup ↔ A ≤ B := by
  constructor
  · intro h x hx
    rw [← A.valuation_le_one_iff x, le_iff_lt_or_eq] at hx
    by_cases h_1 : x = 0; · simp only [h_1, zero_mem]
    by_cases h_2 : 1 + x = 0
    · simp only [← add_eq_zero_iff_neg_eq.1 h_2, neg_mem _ _ (one_mem _)]
    rcases hx with hx | hx
    · have := h (show Units.mk0 _ h_2 ∈ A.unitGroup from A.valuation.map_one_add_of_lt hx)
      simpa using
        B.add_mem _ _ (show 1 + x ∈ B from SetLike.coe_mem (B.unitGroupMulEquiv ⟨_, this⟩ : B))
          (B.neg_mem _ B.one_mem)
    · have := h (show Units.mk0 x h_1 ∈ A.unitGroup from hx)
      exact SetLike.coe_mem (B.unitGroupMulEquiv ⟨_, this⟩ : B)
  · rintro h x (hx : A.valuation x = 1)
    apply_fun A.mapOfLE B h at hx
    simpa using hx

theorem unitGroup_injective : Function.Injective (unitGroup : ValuationSubring K → Subgroup _) :=
  fun A B h => by simpa only [le_antisymm_iff, unitGroup_le_unitGroup] using h

theorem eq_iff_unitGroup {A B : ValuationSubring K} : A = B ↔ A.unitGroup = B.unitGroup :=
  unitGroup_injective.eq_iff.symm

/-- The map on valuation subrings to their unit groups is an order embedding. -/
def unitGroupOrderEmbedding : ValuationSubring K ↪o Subgroup Kˣ where
  toFun A := A.unitGroup
  inj' := unitGroup_injective
  map_rel_iff' {_A _B} := unitGroup_le_unitGroup

theorem unitGroup_strictMono : StrictMono (unitGroup : ValuationSubring K → Subgroup _) :=
  unitGroupOrderEmbedding.strictMono

end UnitGroup

section nonunits

/-- The nonunits of a valuation subring of `K`, as a nonunital subring of `K` -/
def nonunits : NonUnitalSubring K where
  carrier := {x | A.valuation x < 1}
  mul_mem' ha hb := (mul_lt_mul'' (Set.mem_setOf.mp ha) (Set.mem_setOf.mp hb)
    zero_le' zero_le').trans_eq <| mul_one _
  add_mem' ha hb := (A.valuation.map_add ..).trans_lt (max_lt ha hb)
  zero_mem' := by simp
  neg_mem' h := (A.valuation.map_neg _).trans_lt h

theorem mem_nonunits_iff {x : K} : x ∈ A.nonunits ↔ A.valuation x < 1 :=
  Iff.rfl

theorem mem_nonunits_iff_or {x : K} : x ∈ A.nonunits ↔ x = 0 ∨ x⁻¹ ∉ A := by
  rw [← valuation_le_one_iff, ← or_congr_right' fun h ↦ (A.valuation.one_le_val_iff h).not,
    ← lt_iff_not_ge, ← mem_nonunits_iff, or_iff_right_of_imp]
  rintro rfl
  exact A.nonunits.zero_mem

theorem inv_mem_nonunits_iff {x : K} : x⁻¹ ∈ A.nonunits ↔ x = 0 ∨ x ∉ A := by
  rw [mem_nonunits_iff_or, inv_inv, inv_eq_zero]

theorem nonunits_le_nonunits {A B : ValuationSubring K} : B.nonunits ≤ A.nonunits ↔ A ≤ B := by
  constructor
  · intro h x hx
    by_cases h_1 : x = 0; · simp only [h_1, zero_mem]
    rw [← valuation_le_one_iff, ← not_lt, Valuation.one_lt_val_iff _ h_1] at hx ⊢
    by_contra h_2; exact hx (h h_2)
  · intro h x hx
    by_contra h_1; exact not_lt.2 (monotone_mapOfLE _ _ h (not_lt.1 h_1)) hx

theorem nonunits_injective :
    Function.Injective (nonunits : ValuationSubring K → NonUnitalSubring _) :=
  fun A B h => by simpa only [le_antisymm_iff, nonunits_le_nonunits] using h.symm

theorem nonunits_inj {A B : ValuationSubring K} : A.nonunits = B.nonunits ↔ A = B :=
  nonunits_injective.eq_iff

/-- The map on valuation subrings to their nonunits is a dual order embedding. -/
def nonunitsOrderEmbedding : ValuationSubring K ↪o (NonUnitalSubring K)ᵒᵈ where
  toFun A := A.nonunits
  inj' := nonunits_injective
  map_rel_iff' {_A _B} := nonunits_le_nonunits

variable {A}

/-- The elements of `A.nonunits` are those of the maximal ideal of `A` after coercion to `K`.

See also `mem_nonunits_iff_exists_mem_maximalIdeal`, which gets rid of the coercion to `K`,
at the expense of a more complicated right-hand side.
-/
theorem coe_mem_nonunits_iff {a : A} : (a : K) ∈ A.nonunits ↔ a ∈ IsLocalRing.maximalIdeal A :=
  (valuation_lt_one_iff _ _).symm

theorem nonunits_le : A.nonunits ≤ A.toNonUnitalSubring := fun _a ha =>
  (A.valuation_le_one_iff _).mp (A.mem_nonunits_iff.mp ha).le

theorem nonunits_subset : (A.nonunits : Set K) ⊆ A :=
  nonunits_le

/-- The elements of `A.nonunits` are those of the maximal ideal of `A`.

See also `coe_mem_nonunits_iff`, which has a simpler right-hand side but requires the element
to be in `A` already.
-/
theorem mem_nonunits_iff_exists_mem_maximalIdeal {a : K} :
    a ∈ A.nonunits ↔ ∃ ha, (⟨a, ha⟩ : A) ∈ IsLocalRing.maximalIdeal A :=
  ⟨fun h => ⟨nonunits_subset h, coe_mem_nonunits_iff.mp h⟩, fun ⟨_, h⟩ =>
    coe_mem_nonunits_iff.mpr h⟩

/-- `A.nonunits` agrees with the maximal ideal of `A`, after taking its image in `K`. -/
theorem image_maximalIdeal : ((↑) : A → K) '' IsLocalRing.maximalIdeal A = A.nonunits := by
  ext a
  simp only [Set.mem_image, SetLike.mem_coe, mem_nonunits_iff_exists_mem_maximalIdeal]
  rw [Subtype.exists]
  simp_rw [exists_and_right, exists_eq_right]

end nonunits

section PrincipalUnitGroup

/-- The principal unit group of a valuation subring, as a subgroup of `Kˣ`. -/
def principalUnitGroup : Subgroup Kˣ where
  carrier := {x | A.valuation (x - 1) < 1}
  mul_mem' := by
    intro a b ha hb
    rw [Set.mem_setOf] at ha hb ⊢
    refine lt_of_le_of_lt ?_ (max_lt hb ha)
    rw [← one_mul (A.valuation (b - 1)), ← A.valuation.map_one_add_of_lt ha, add_sub_cancel,
      ← Valuation.map_mul, mul_sub_one, ← sub_add_sub_cancel]
    exact A.valuation.map_add _ _
  one_mem' := by simp
  inv_mem' := by
    dsimp
    intro a ha
    conv =>
      lhs
      rw [← mul_one (A.valuation _), ← A.valuation.map_one_add_of_lt ha]
    rwa [add_sub_cancel, ← Valuation.map_mul, sub_mul, Units.inv_mul, ← neg_sub, one_mul,
      Valuation.map_neg]

theorem principal_units_le_units : A.principalUnitGroup ≤ A.unitGroup := fun a h => by
  simpa only [add_sub_cancel] using A.valuation.map_one_add_of_lt h

theorem mem_principalUnitGroup_iff (x : Kˣ) :
    x ∈ A.principalUnitGroup ↔ A.valuation ((x : K) - 1) < 1 :=
  Iff.rfl

theorem principalUnitGroup_le_principalUnitGroup {A B : ValuationSubring K} :
    B.principalUnitGroup ≤ A.principalUnitGroup ↔ A ≤ B := by
  constructor
  · intro h x hx
    by_cases h_1 : x = 0; · simp only [h_1, zero_mem]
    by_cases h_2 : x⁻¹ + 1 = 0
    · rw [add_eq_zero_iff_eq_neg, inv_eq_iff_eq_inv, inv_neg, inv_one] at h_2
      simpa only [h_2] using B.neg_mem _ B.one_mem
    · rw [← valuation_le_one_iff, ← not_lt, Valuation.one_lt_val_iff _ h_1,
        ← add_sub_cancel_right x⁻¹, ← Units.val_mk0 h_2, ← mem_principalUnitGroup_iff] at hx ⊢
      simpa only [hx] using @h (Units.mk0 (x⁻¹ + 1) h_2)
  · intro h x hx
    by_contra h_1; exact not_lt.2 (monotone_mapOfLE _ _ h (not_lt.1 h_1)) hx

theorem principalUnitGroup_injective :
    Function.Injective (principalUnitGroup : ValuationSubring K → Subgroup _) := fun A B h => by
  simpa [le_antisymm_iff, principalUnitGroup_le_principalUnitGroup] using h.symm

theorem eq_iff_principalUnitGroup {A B : ValuationSubring K} :
    A = B ↔ A.principalUnitGroup = B.principalUnitGroup :=
  principalUnitGroup_injective.eq_iff.symm

/-- The map on valuation subrings to their principal unit groups is an order embedding. -/
def principalUnitGroupOrderEmbedding : ValuationSubring K ↪o (Subgroup Kˣ)ᵒᵈ where
  toFun A := A.principalUnitGroup
  inj' := principalUnitGroup_injective
  map_rel_iff' {_A _B} := principalUnitGroup_le_principalUnitGroup

set_option backward.isDefEq.respectTransparency false in
theorem coe_mem_principalUnitGroup_iff {x : A.unitGroup} :
    (x : Kˣ) ∈ A.principalUnitGroup ↔
      A.unitGroupMulEquiv x ∈ (Units.map (IsLocalRing.residue A).toMonoidHom).ker := by
  rw [MonoidHom.mem_ker, Units.ext_iff]
  let π := Ideal.Quotient.mk (IsLocalRing.maximalIdeal A); convert_to _ ↔ π _ = 1
  rw [← π.map_one, ← sub_eq_zero, ← π.map_sub, Ideal.Quotient.eq_zero_iff_mem, valuation_lt_one_iff]
  simp [mem_principalUnitGroup_iff]

/-- The principal unit group agrees with the kernel of the canonical map from
the units of `A` to the units of the residue field of `A`. -/
def principalUnitGroupEquiv :
    A.principalUnitGroup ≃* (Units.map (IsLocalRing.residue A).toMonoidHom).ker where
  toFun x :=
    ⟨A.unitGroupMulEquiv ⟨_, A.principal_units_le_units x.2⟩,
      A.coe_mem_principalUnitGroup_iff.1 x.2⟩
  invFun x :=
    ⟨A.unitGroupMulEquiv.symm x, by
      rw [A.coe_mem_principalUnitGroup_iff]; simp⟩
  left_inv x := by simp
  right_inv x := by simp
  map_mul' _ _ := rfl

theorem principalUnitGroupEquiv_apply (a : A.principalUnitGroup) :
    (((principalUnitGroupEquiv A a : Aˣ) : A) : K) = (a : Kˣ) :=
  rfl

theorem principalUnitGroup_symm_apply (a : (Units.map (IsLocalRing.residue A).toMonoidHom).ker) :
    ((A.principalUnitGroupEquiv.symm a : Kˣ) : K) = ((a : Aˣ) : A) :=
  rfl

/-- The canonical map from the unit group of `A` to the units of the residue field of `A`. -/
def unitGroupToResidueFieldUnits : A.unitGroup →* (IsLocalRing.ResidueField A)ˣ :=
  MonoidHom.comp (Units.map <| (Ideal.Quotient.mk _).toMonoidHom) A.unitGroupMulEquiv.toMonoidHom

@[simp]
theorem coe_unitGroupToResidueFieldUnits_apply (x : A.unitGroup) :
    (A.unitGroupToResidueFieldUnits x : IsLocalRing.ResidueField A) =
      Ideal.Quotient.mk _ (A.unitGroupMulEquiv x : A) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem ker_unitGroupToResidueFieldUnits :
    A.unitGroupToResidueFieldUnits.ker = A.principalUnitGroup.comap A.unitGroup.subtype := by
  ext
  simp_rw [Subgroup.mem_comap, Subgroup.coe_subtype, coe_mem_principalUnitGroup_iff,
    unitGroupToResidueFieldUnits, IsLocalRing.residue, RingHom.toMonoidHom_eq_coe,
    MulEquiv.toMonoidHom_eq_coe, MonoidHom.mem_ker, MonoidHom.coe_comp, MonoidHom.coe_coe,
    Function.comp_apply]

theorem surjective_unitGroupToResidueFieldUnits :
    Function.Surjective A.unitGroupToResidueFieldUnits :=
  IsLocalRing.surjective_units_map_of_local_ringHom _ Ideal.Quotient.mk_surjective
    (inferInstanceAs (IsLocalHom (IsLocalRing.residue A))) |>.comp (MulEquiv.surjective _)

/-- The quotient of the unit group of `A` by the principal unit group of `A` agrees with
the units of the residue field of `A`. -/
def unitsModPrincipalUnitsEquivResidueFieldUnits :
    A.unitGroup ⧸ A.principalUnitGroup.comap A.unitGroup.subtype ≃* (IsLocalRing.ResidueField A)ˣ :=
  QuotientGroup.liftEquiv _ A.surjective_unitGroupToResidueFieldUnits
    A.ker_unitGroupToResidueFieldUnits.symm

set_option backward.isDefEq.respectTransparency false in
theorem unitsModPrincipalUnitsEquivResidueFieldUnits_comp_quotientGroup_mk :
    (A.unitsModPrincipalUnitsEquivResidueFieldUnits : _ ⧸ Subgroup.comap _ _ →* _).comp
        (QuotientGroup.mk' (A.principalUnitGroup.subgroupOf A.unitGroup)) =
      A.unitGroupToResidueFieldUnits := rfl

theorem unitsModPrincipalUnitsEquivResidueFieldUnits_comp_quotientGroup_mk_apply
    (x : A.unitGroup) :
    A.unitsModPrincipalUnitsEquivResidueFieldUnits.toMonoidHom (QuotientGroup.mk x) =
      A.unitGroupToResidueFieldUnits x := rfl

end PrincipalUnitGroup

/-! ### Pointwise actions

This transfers the action from `Subring.pointwiseMulAction`, noting that it only applies when
the action is by a group. Notably this provides an instances when `G` is `K ≃+* K`.

These instances are in the `Pointwise` locale.

The lemmas in this section are copied from the file `Mathlib/Algebra/Ring/Subring/Pointwise.lean`;
try to keep these in sync.
-/


section PointwiseActions

open scoped Pointwise

variable {G : Type*} [Group G] [MulSemiringAction G K]

/-- The action on a valuation subring corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale. -/
@[instance_reducible]
def pointwiseHasSMul : SMul G (ValuationSubring K) where
  smul g S := -- TODO: if we add `ValuationSubring.map` at a later date, we should use it here
    { g • S.toSubring with
      mem_or_inv_mem' := fun x =>
        (mem_or_inv_mem S (g⁻¹ • x)).imp Subring.mem_pointwise_smul_iff_inv_smul_mem.mpr fun h =>
          Subring.mem_pointwise_smul_iff_inv_smul_mem.mpr <| by rwa [smul_inv''] }

scoped[Pointwise] attribute [instance] ValuationSubring.pointwiseHasSMul

open scoped Pointwise

@[simp]
theorem coe_pointwise_smul (g : G) (S : ValuationSubring K) : ↑(g • S) = g • (S : Set K) := rfl

@[simp]
theorem pointwise_smul_toSubring (g : G) (S : ValuationSubring K) :
    (g • S).toSubring = g • S.toSubring := rfl

/-- The action on a valuation subring corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale.

This is a stronger version of `ValuationSubring.pointwiseSMul`. -/
@[instance_reducible]
def pointwiseMulAction : MulAction G (ValuationSubring K) :=
  toSubring_injective.mulAction toSubring pointwise_smul_toSubring

scoped[Pointwise] attribute [instance] ValuationSubring.pointwiseMulAction

open scoped Pointwise

theorem smul_mem_pointwise_smul (g : G) (x : K) (S : ValuationSubring K) : x ∈ S → g • x ∈ g • S :=
  (Set.smul_mem_smul_set : _ → _ ∈ g • (S : Set K))

instance : CovariantClass G (ValuationSubring K) HSMul.hSMul LE.le :=
  ⟨fun _ _ _ => Set.image_mono⟩

theorem mem_smul_pointwise_iff_exists (g : G) (x : K) (S : ValuationSubring K) :
    x ∈ g • S ↔ ∃ s : K, s ∈ S ∧ g • s = x :=
  (Set.mem_smul_set : x ∈ g • (S : Set K) ↔ _)

instance pointwise_central_scalar [MulSemiringAction Gᵐᵒᵖ K] [IsCentralScalar G K] :
    IsCentralScalar G (ValuationSubring K) :=
  ⟨fun g S => toSubring_injective <| op_smul_eq_smul g S.toSubring⟩

@[simp]
theorem smul_mem_pointwise_smul_iff {g : G} {S : ValuationSubring K} {x : K} :
    g • x ∈ g • S ↔ x ∈ S := Set.smul_mem_smul_set_iff

theorem mem_pointwise_smul_iff_inv_smul_mem {g : G} {S : ValuationSubring K} {x : K} :
    x ∈ g • S ↔ g⁻¹ • x ∈ S := Set.mem_smul_set_iff_inv_smul_mem

theorem mem_inv_pointwise_smul_iff {g : G} {S : ValuationSubring K} {x : K} :
    x ∈ g⁻¹ • S ↔ g • x ∈ S := Set.mem_inv_smul_set_iff

@[simp]
theorem pointwise_smul_le_pointwise_smul_iff {g : G} {S T : ValuationSubring K} :
    g • S ≤ g • T ↔ S ≤ T := Set.smul_set_subset_smul_set_iff

theorem pointwise_smul_subset_iff {g : G} {S T : ValuationSubring K} : g • S ≤ T ↔ S ≤ g⁻¹ • T :=
  Set.smul_set_subset_iff_subset_inv_smul_set

theorem subset_pointwise_smul_iff {g : G} {S T : ValuationSubring K} : S ≤ g • T ↔ g⁻¹ • S ≤ T :=
  Set.subset_smul_set_iff

end PointwiseActions

section

variable {L J : Type*} [Field L] [Field J]

/-- The pullback of a valuation subring `A` along a ring homomorphism `K →+* L`. -/
def comap (A : ValuationSubring L) (f : K →+* L) : ValuationSubring K :=
  { A.toSubring.comap f with mem_or_inv_mem' := fun k => by simp [ValuationSubring.mem_or_inv_mem] }

@[simp]
theorem coe_comap (A : ValuationSubring L) (f : K →+* L) : (A.comap f : Set K) = f ⁻¹' A := rfl

@[simp]
theorem mem_comap {A : ValuationSubring L} {f : K →+* L} {x : K} : x ∈ A.comap f ↔ f x ∈ A :=
  Iff.rfl

theorem comap_comap (A : ValuationSubring J) (g : L →+* J) (f : K →+* L) :
    (A.comap g).comap f = A.comap (g.comp f) := rfl

end

end ValuationSubring

namespace Valuation

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (x : Kˣ)

theorem mem_unitGroup_iff : x ∈ v.valuationSubring.unitGroup ↔ v x = 1 :=
  IsEquiv.eq_one_iff_eq_one (Valuation.isEquiv_valuation_valuationSubring _).symm

theorem mem_maximalIdeal_iff {a : v.valuationSubring} :
    a ∈ IsLocalRing.maximalIdeal (v.valuationSubring) ↔ v a < 1 :=
  Integer.not_isUnit_iff_valuation_lt_one

end Valuation
