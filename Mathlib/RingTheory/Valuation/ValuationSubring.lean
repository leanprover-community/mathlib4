/-
Copyright (c) 2022 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Junyan Xu, Jack McKoen
-/
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.Algebra.Ring.Subring.Pointwise
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic

#align_import ring_theory.valuation.valuation_subring from "leanprover-community/mathlib"@"2196ab363eb097c008d4497125e0dde23fb36db2"

/-!

# Valuation subrings of a field

## Projects

The order structure on `ValuationSubring K`.

-/


universe u

open scoped Classical

noncomputable section

variable (K : Type u) [Field K]

/-- A valuation subring of a field `K` is a subring `A` such that for every `x : K`,
either `x ∈ A` or `x⁻¹ ∈ A`. -/
structure ValuationSubring extends Subring K where
  mem_or_inv_mem' : ∀ x : K, x ∈ carrier ∨ x⁻¹ ∈ carrier
#align valuation_subring ValuationSubring

namespace ValuationSubring

variable {K}
variable (A : ValuationSubring K)

instance : SetLike (ValuationSubring K) K where
  coe A := A.toSubring
  coe_injective' := by
    intro ⟨_, _⟩ ⟨_, _⟩ h
    replace h := SetLike.coe_injective' h
    congr

@[simp, nolint simpNF] -- Porting note (#10959): simp cannot prove that
theorem mem_carrier (x : K) : x ∈ A.carrier ↔ x ∈ A := Iff.refl _
#align valuation_subring.mem_carrier ValuationSubring.mem_carrier

@[simp]
theorem mem_toSubring (x : K) : x ∈ A.toSubring ↔ x ∈ A := Iff.refl _
#align valuation_subring.mem_to_subring ValuationSubring.mem_toSubring

@[ext]
theorem ext (A B : ValuationSubring K) (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B := SetLike.ext h
#align valuation_subring.ext ValuationSubring.ext

theorem zero_mem : (0 : K) ∈ A := A.toSubring.zero_mem
#align valuation_subring.zero_mem ValuationSubring.zero_mem

theorem one_mem : (1 : K) ∈ A := A.toSubring.one_mem
#align valuation_subring.one_mem ValuationSubring.one_mem

theorem add_mem (x y : K) : x ∈ A → y ∈ A → x + y ∈ A := A.toSubring.add_mem
#align valuation_subring.add_mem ValuationSubring.add_mem

theorem mul_mem (x y : K) : x ∈ A → y ∈ A → x * y ∈ A := A.toSubring.mul_mem
#align valuation_subring.mul_mem ValuationSubring.mul_mem

theorem neg_mem (x : K) : x ∈ A → -x ∈ A := A.toSubring.neg_mem
#align valuation_subring.neg_mem ValuationSubring.neg_mem

theorem mem_or_inv_mem (x : K) : x ∈ A ∨ x⁻¹ ∈ A := A.mem_or_inv_mem' _
#align valuation_subring.mem_or_inv_mem ValuationSubring.mem_or_inv_mem

instance : SubringClass (ValuationSubring K) K where
  zero_mem := zero_mem
  add_mem {_} a b := add_mem _ a b
  one_mem := one_mem
  mul_mem {_} a b := mul_mem _ a b
  neg_mem {_} x := neg_mem _ x

theorem toSubring_injective : Function.Injective (toSubring : ValuationSubring K → Subring K) :=
  fun x y h => by cases x; cases y; congr
#align valuation_subring.to_subring_injective ValuationSubring.toSubring_injective

instance : CommRing A :=
  show CommRing A.toSubring by infer_instance

instance : IsDomain A :=
  show IsDomain A.toSubring by infer_instance

instance : Top (ValuationSubring K) :=
  Top.mk <| { (⊤ : Subring K) with mem_or_inv_mem' := fun _ => Or.inl trivial }

theorem mem_top (x : K) : x ∈ (⊤ : ValuationSubring K) :=
  trivial
#align valuation_subring.mem_top ValuationSubring.mem_top

theorem le_top : A ≤ ⊤ := fun _a _ha => mem_top _
#align valuation_subring.le_top ValuationSubring.le_top

instance : OrderTop (ValuationSubring K) where
  top := ⊤
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
    cases' A.mem_or_inv_mem (a / b) with hh hh
    · use ⟨a / b, hh⟩
      right
      ext
      field_simp
    · rw [show (a / b : K)⁻¹ = b / a by field_simp] at hh
      use ⟨b / a, hh⟩;
      left
      ext
      field_simp

instance : Algebra A K :=
  show Algebra A.toSubring K by infer_instance

-- Porting note: Somehow it cannot find this instance and I'm too lazy to debug. wrong prio?
instance localRing : LocalRing A := ValuationRing.localRing A

@[simp]
theorem algebraMap_apply (a : A) : algebraMap A K a = a := rfl
#align valuation_subring.algebra_map_apply ValuationSubring.algebraMap_apply

instance : IsFractionRing A K where
  map_units' := fun ⟨y, hy⟩ =>
    (Units.mk0 (y : K) fun c => nonZeroDivisors.ne_zero hy <| Subtype.ext c).isUnit
  surj' z := by
    by_cases h : z = 0; · use (0, 1); simp [h]
    cases' A.mem_or_inv_mem z with hh hh
    · use (⟨z, hh⟩, 1); simp
    · refine ⟨⟨1, ⟨⟨_, hh⟩, ?_⟩⟩, mul_inv_cancel h⟩
      exact mem_nonZeroDivisors_iff_ne_zero.2 fun c => h (inv_eq_zero.mp (congr_arg Subtype.val c))
  exists_of_eq {a b} h := ⟨1, by ext; simpa using h⟩

/-- The value group of the valuation associated to `A`. Note: it is actually a group with zero. -/
def ValueGroup :=
  ValuationRing.ValueGroup A K
-- deriving LinearOrderedCommGroupWithZero
#align valuation_subring.value_group ValuationSubring.ValueGroup

-- Porting note: see https://github.com/leanprover-community/mathlib4/issues/5020
instance : LinearOrderedCommGroupWithZero (ValueGroup A) := by
  unfold ValueGroup
  infer_instance

/-- Any valuation subring of `K` induces a natural valuation on `K`. -/
def valuation : Valuation K A.ValueGroup :=
  ValuationRing.valuation A K
#align valuation_subring.valuation ValuationSubring.valuation

instance inhabitedValueGroup : Inhabited A.ValueGroup := ⟨A.valuation 0⟩
#align valuation_subring.inhabited_value_group ValuationSubring.inhabitedValueGroup

theorem valuation_le_one (a : A) : A.valuation a ≤ 1 :=
  (ValuationRing.mem_integer_iff A K _).2 ⟨a, rfl⟩
#align valuation_subring.valuation_le_one ValuationSubring.valuation_le_one

theorem mem_of_valuation_le_one (x : K) (h : A.valuation x ≤ 1) : x ∈ A :=
  let ⟨a, ha⟩ := (ValuationRing.mem_integer_iff A K x).1 h
  ha ▸ a.2
#align valuation_subring.mem_of_valuation_le_one ValuationSubring.mem_of_valuation_le_one

theorem valuation_le_one_iff (x : K) : A.valuation x ≤ 1 ↔ x ∈ A :=
  ⟨mem_of_valuation_le_one _ _, fun ha => A.valuation_le_one ⟨x, ha⟩⟩
#align valuation_subring.valuation_le_one_iff ValuationSubring.valuation_le_one_iff

theorem valuation_eq_iff (x y : K) : A.valuation x = A.valuation y ↔ ∃ a : Aˣ, (a : K) * y = x :=
  Quotient.eq''
#align valuation_subring.valuation_eq_iff ValuationSubring.valuation_eq_iff

theorem valuation_le_iff (x y : K) : A.valuation x ≤ A.valuation y ↔ ∃ a : A, (a : K) * y = x :=
  Iff.rfl
#align valuation_subring.valuation_le_iff ValuationSubring.valuation_le_iff

theorem valuation_surjective : Function.Surjective A.valuation := surjective_quot_mk _
#align valuation_subring.valuation_surjective ValuationSubring.valuation_surjective

theorem valuation_unit (a : Aˣ) : A.valuation a = 1 := by
  rw [← A.valuation.map_one, valuation_eq_iff]; use a; simp
#align valuation_subring.valuation_unit ValuationSubring.valuation_unit

theorem valuation_eq_one_iff (a : A) : IsUnit a ↔ A.valuation a = 1 :=
  ⟨fun h => A.valuation_unit h.unit, fun h => by
    have ha : (a : K) ≠ 0 := by
      intro c
      rw [c, A.valuation.map_zero] at h
      exact zero_ne_one h
    have ha' : (a : K)⁻¹ ∈ A := by rw [← valuation_le_one_iff, map_inv₀, h, inv_one]
    apply isUnit_of_mul_eq_one a ⟨a⁻¹, ha'⟩; ext; field_simp⟩
#align valuation_subring.valuation_eq_one_iff ValuationSubring.valuation_eq_one_iff

theorem valuation_lt_one_or_eq_one (a : A) : A.valuation a < 1 ∨ A.valuation a = 1 :=
  lt_or_eq_of_le (A.valuation_le_one a)
#align valuation_subring.valuation_lt_one_or_eq_one ValuationSubring.valuation_lt_one_or_eq_one

theorem valuation_lt_one_iff (a : A) : a ∈ LocalRing.maximalIdeal A ↔ A.valuation a < 1 := by
  rw [LocalRing.mem_maximalIdeal]
  dsimp [nonunits]; rw [valuation_eq_one_iff]
  exact (A.valuation_le_one a).lt_iff_ne.symm
#align valuation_subring.valuation_lt_one_iff ValuationSubring.valuation_lt_one_iff

/-- A subring `R` of `K` such that for all `x : K` either `x ∈ R` or `x⁻¹ ∈ R` is
  a valuation subring of `K`. -/
def ofSubring (R : Subring K) (hR : ∀ x : K, x ∈ R ∨ x⁻¹ ∈ R) : ValuationSubring K :=
  { R with mem_or_inv_mem' := hR }
#align valuation_subring.of_subring ValuationSubring.ofSubring

@[simp]
theorem mem_ofSubring (R : Subring K) (hR : ∀ x : K, x ∈ R ∨ x⁻¹ ∈ R) (x : K) :
    x ∈ ofSubring R hR ↔ x ∈ R :=
  Iff.refl _
#align valuation_subring.mem_of_subring ValuationSubring.mem_ofSubring

/-- An overring of a valuation ring is a valuation ring. -/
def ofLE (R : ValuationSubring K) (S : Subring K) (h : R.toSubring ≤ S) : ValuationSubring K :=
  { S with mem_or_inv_mem' := fun x => (R.mem_or_inv_mem x).imp (@h x) (@h _) }
#align valuation_subring.of_le ValuationSubring.ofLE

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
#align valuation_subring.inclusion ValuationSubring.inclusion

/-- The canonical ring homomorphism from a valuation ring to its field of fractions. -/
def subtype (R : ValuationSubring K) : R →+* K :=
  Subring.subtype R.toSubring
#align valuation_subring.subtype ValuationSubring.subtype

/-- The canonical map on value groups induced by a coarsening of valuation rings. -/
def mapOfLE (R S : ValuationSubring K) (h : R ≤ S) : R.ValueGroup →*₀ S.ValueGroup where
  toFun := Quotient.map' id fun x y ⟨u, hu⟩ => ⟨Units.map (R.inclusion S h).toMonoidHom u, hu⟩
  map_zero' := rfl
  map_one' := rfl
  map_mul' := by rintro ⟨⟩ ⟨⟩; rfl
#align valuation_subring.map_of_le ValuationSubring.mapOfLE

@[mono]
theorem monotone_mapOfLE (R S : ValuationSubring K) (h : R ≤ S) : Monotone (R.mapOfLE S h) := by
  rintro ⟨⟩ ⟨⟩ ⟨a, ha⟩; exact ⟨R.inclusion S h a, ha⟩
#align valuation_subring.monotone_map_of_le ValuationSubring.monotone_mapOfLE

@[simp]
theorem mapOfLE_comp_valuation (R S : ValuationSubring K) (h : R ≤ S) :
    R.mapOfLE S h ∘ R.valuation = S.valuation := by ext; rfl
#align valuation_subring.map_of_le_comp_valuation ValuationSubring.mapOfLE_comp_valuation

@[simp]
theorem mapOfLE_valuation_apply (R S : ValuationSubring K) (h : R ≤ S) (x : K) :
    R.mapOfLE S h (R.valuation x) = S.valuation x := rfl
#align valuation_subring.map_of_le_valuation_apply ValuationSubring.mapOfLE_valuation_apply

/-- The ideal corresponding to a coarsening of a valuation ring. -/
def idealOfLE (R S : ValuationSubring K) (h : R ≤ S) : Ideal R :=
  (LocalRing.maximalIdeal S).comap (R.inclusion S h)
#align valuation_subring.ideal_of_le ValuationSubring.idealOfLE

instance prime_idealOfLE (R S : ValuationSubring K) (h : R ≤ S) : (idealOfLE R S h).IsPrime :=
  (LocalRing.maximalIdeal S).comap_isPrime _
#align valuation_subring.prime_ideal_of_le ValuationSubring.prime_idealOfLE

/-- The coarsening of a valuation ring associated to a prime ideal. -/
def ofPrime (A : ValuationSubring K) (P : Ideal A) [P.IsPrime] : ValuationSubring K :=
  ofLE A (Localization.subalgebra.ofField K _ P.primeCompl_le_nonZeroDivisors).toSubring
    -- Porting note: added `Subalgebra.mem_toSubring.mpr`
    fun a ha => Subalgebra.mem_toSubring.mpr <|
      Subalgebra.algebraMap_mem
        (Localization.subalgebra.ofField K _ P.primeCompl_le_nonZeroDivisors) (⟨a, ha⟩ : A)
#align valuation_subring.of_prime ValuationSubring.ofPrime

instance ofPrimeAlgebra (A : ValuationSubring K) (P : Ideal A) [P.IsPrime] :
    Algebra A (A.ofPrime P) :=
  -- Porting note: filled in the argument
  Subalgebra.algebra (Localization.subalgebra.ofField K _ P.primeCompl_le_nonZeroDivisors)
#align valuation_subring.of_prime_algebra ValuationSubring.ofPrimeAlgebra

instance ofPrime_scalar_tower (A : ValuationSubring K) (P : Ideal A) [P.IsPrime] :
    -- porting note (#10754): added instance
    letI : SMul A (A.ofPrime P) := SMulZeroClass.toSMul
    IsScalarTower A (A.ofPrime P) K :=
  IsScalarTower.subalgebra' A K K
    -- Porting note: filled in the argument
    (Localization.subalgebra.ofField K _ P.primeCompl_le_nonZeroDivisors)
#align valuation_subring.of_prime_scalar_tower ValuationSubring.ofPrime_scalar_tower

instance ofPrime_localization (A : ValuationSubring K) (P : Ideal A) [P.IsPrime] :
    IsLocalization.AtPrime (A.ofPrime P) P := by
  apply
    Localization.subalgebra.isLocalization_ofField K P.primeCompl
      P.primeCompl_le_nonZeroDivisors
#align valuation_subring.of_prime_localization ValuationSubring.ofPrime_localization

theorem le_ofPrime (A : ValuationSubring K) (P : Ideal A) [P.IsPrime] : A ≤ ofPrime A P :=
  -- Porting note: added `Subalgebra.mem_toSubring.mpr`
  fun a ha => Subalgebra.mem_toSubring.mpr <| Subalgebra.algebraMap_mem _ (⟨a, ha⟩ : A)
#align valuation_subring.le_of_prime ValuationSubring.le_ofPrime

theorem ofPrime_valuation_eq_one_iff_mem_primeCompl (A : ValuationSubring K) (P : Ideal A)
    [P.IsPrime] (x : A) : (ofPrime A P).valuation x = 1 ↔ x ∈ P.primeCompl := by
  rw [← IsLocalization.AtPrime.isUnit_to_map_iff (A.ofPrime P) P x, valuation_eq_one_iff]; rfl
#align valuation_subring.of_prime_valuation_eq_one_iff_mem_prime_compl ValuationSubring.ofPrime_valuation_eq_one_iff_mem_primeCompl

@[simp]
theorem idealOfLE_ofPrime (A : ValuationSubring K) (P : Ideal A) [P.IsPrime] :
    idealOfLE A (ofPrime A P) (le_ofPrime A P) = P := by
  refine Ideal.ext (fun x => ?_)
  apply IsLocalization.AtPrime.to_map_mem_maximal_iff
  exact localRing (ofPrime A P)
#align valuation_subring.ideal_of_le_of_prime ValuationSubring.idealOfLE_ofPrime

@[simp]
theorem ofPrime_idealOfLE (R S : ValuationSubring K) (h : R ≤ S) :
    ofPrime R (idealOfLE R S h) = S := by
  ext x; constructor
  · rintro ⟨a, r, hr, rfl⟩; apply mul_mem; · exact h a.2
    · rw [← valuation_le_one_iff, map_inv₀, ← inv_one, inv_le_inv₀]
      · exact not_lt.1 ((not_iff_not.2 <| valuation_lt_one_iff S _).1 hr)
      · intro hh; erw [Valuation.zero_iff, Subring.coe_eq_zero_iff] at hh
        apply hr; rw [hh]; apply Ideal.zero_mem (R.idealOfLE S h)
      · exact one_ne_zero
  · intro hx; by_cases hr : x ∈ R; · exact R.le_ofPrime _ hr
    have : x ≠ 0 := fun h => hr (by rw [h]; exact R.zero_mem)
    replace hr := (R.mem_or_inv_mem x).resolve_left hr
    -- Porting note: added `⟨⟩` brackets and reordered goals
    use 1, ⟨x⁻¹, hr⟩; constructor
    · field_simp
    · change (⟨x⁻¹, h hr⟩ : S) ∉ nonunits S
      rw [mem_nonunits_iff, Classical.not_not]
      apply isUnit_of_mul_eq_one _ (⟨x, hx⟩ : S)
      ext; field_simp
#align valuation_subring.of_prime_ideal_of_le ValuationSubring.ofPrime_idealOfLE

theorem ofPrime_le_of_le (P Q : Ideal A) [P.IsPrime] [Q.IsPrime] (h : P ≤ Q) :
    ofPrime A Q ≤ ofPrime A P := fun _x ⟨a, s, hs, he⟩ => ⟨a, s, fun c => hs (h c), he⟩
#align valuation_subring.of_prime_le_of_le ValuationSubring.ofPrime_le_of_le

theorem idealOfLE_le_of_le (R S : ValuationSubring K) (hR : A ≤ R) (hS : A ≤ S) (h : R ≤ S) :
    idealOfLE A S hS ≤ idealOfLE A R hR := fun x hx =>
  (valuation_lt_one_iff R _).2
    (by
      by_contra c; push_neg at c; replace c := monotone_mapOfLE R S h c
      rw [(mapOfLE _ _ _).map_one, mapOfLE_valuation_apply] at c
      apply not_le_of_lt ((valuation_lt_one_iff S _).1 hx) c)
#align valuation_subring.ideal_of_le_le_of_le ValuationSubring.idealOfLE_le_of_le

/-- The equivalence between coarsenings of a valuation ring and its prime ideals. -/
@[simps]
def primeSpectrumEquiv : PrimeSpectrum A ≃ {S // A ≤ S} where
  toFun P := ⟨ofPrime A P.asIdeal, le_ofPrime _ _⟩
  invFun S := ⟨idealOfLE _ S S.2, inferInstance⟩
  left_inv P := by ext1; simp
  right_inv S := by ext1; simp
#align valuation_subring.prime_spectrum_equiv ValuationSubring.primeSpectrumEquiv

/-- An ordered variant of `primeSpectrumEquiv`. -/
@[simps!]
def primeSpectrumOrderEquiv : (PrimeSpectrum A)ᵒᵈ ≃o {S // A ≤ S} :=
  { primeSpectrumEquiv A with
    map_rel_iff' :=
      ⟨fun h => by
        dsimp at h
        have := idealOfLE_le_of_le A _ _ ?_ ?_ h
        iterate 2 erw [idealOfLE_ofPrime] at this
        · exact this
        all_goals exact le_ofPrime A (PrimeSpectrum.asIdeal _),
      fun h => by apply ofPrime_le_of_le; exact h⟩ }
#align valuation_subring.prime_spectrum_order_equiv ValuationSubring.primeSpectrumOrderEquiv

instance linearOrderOverring : LinearOrder {S // A ≤ S} :=
  { (inferInstance : PartialOrder _) with
    le_total :=
      let i : IsTotal (PrimeSpectrum A) (· ≤ ·) := ⟨fun ⟨x, _⟩ ⟨y, _⟩ => LE.isTotal.total x y⟩
      (primeSpectrumOrderEquiv A).symm.toRelEmbedding.isTotal.total
    decidableLE := inferInstance }
#align valuation_subring.linear_order_overring ValuationSubring.linearOrderOverring

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
      rcases le_or_lt (v x) 1 with h | h
      · left; exact h
      · right; change v x⁻¹ ≤ 1
        rw [map_inv₀ v, ← inv_one, inv_le_inv₀]
        · exact le_of_lt h
        · intro c; simp [c] at h
        · exact one_ne_zero }
#align valuation.valuation_subring Valuation.valuationSubring

@[simp]
theorem mem_valuationSubring_iff (x : K) : x ∈ v.valuationSubring ↔ v x ≤ 1 := Iff.refl _
#align valuation.mem_valuation_subring_iff Valuation.mem_valuationSubring_iff

theorem isEquiv_iff_valuationSubring :
    v₁.IsEquiv v₂ ↔ v₁.valuationSubring = v₂.valuationSubring := by
  constructor
  · intro h; ext x; specialize h x 1; simpa using h
  · intro h; apply isEquiv_of_val_le_one
    intro x
    have : x ∈ v₁.valuationSubring ↔ x ∈ v₂.valuationSubring := by rw [h]
    simpa using this
#align valuation.is_equiv_iff_valuation_subring Valuation.isEquiv_iff_valuationSubring

theorem isEquiv_valuation_valuationSubring : v.IsEquiv v.valuationSubring.valuation := by
  rw [isEquiv_iff_val_le_one]
  intro x
  rw [ValuationSubring.valuation_le_one_iff]
  rfl
#align valuation.is_equiv_valuation_valuation_subring Valuation.isEquiv_valuation_valuationSubring

end Valuation

namespace ValuationSubring

variable {K}
variable (A : ValuationSubring K)

@[simp]
theorem valuationSubring_valuation : A.valuation.valuationSubring = A := by
  ext; rw [← A.valuation_le_one_iff]; rfl
#align valuation_subring.valuation_subring_valuation ValuationSubring.valuationSubring_valuation

section UnitGroup

/-- The unit group of a valuation subring, as a subgroup of `Kˣ`. -/
def unitGroup : Subgroup Kˣ :=
  (A.valuation.toMonoidWithZeroHom.toMonoidHom.comp (Units.coeHom K)).ker
#align valuation_subring.unit_group ValuationSubring.unitGroup

@[simp]
theorem mem_unitGroup_iff (x : Kˣ) : x ∈ A.unitGroup ↔ A.valuation x = 1 := Iff.rfl
#align valuation_subring.mem_unit_group_iff ValuationSubring.mem_unitGroup_iff

/-- For a valuation subring `A`, `A.unitGroup` agrees with the units of `A`. -/
def unitGroupMulEquiv : A.unitGroup ≃* Aˣ where
  toFun x :=
    { val := ⟨(x : Kˣ), mem_of_valuation_le_one A _ x.prop.le⟩
      inv := ⟨((x⁻¹ : A.unitGroup) : Kˣ), mem_of_valuation_le_one _ _ x⁻¹.prop.le⟩
      -- Porting note: was `Units.mul_inv x`
      val_inv := Subtype.ext (by simp)
      -- Porting note: was `Units.inv_mul x`
      inv_val := Subtype.ext (by simp) }
  invFun x := ⟨Units.map A.subtype.toMonoidHom x, A.valuation_unit x⟩
  left_inv a := by ext; rfl
  right_inv a := by ext; rfl
  map_mul' a b := by ext; rfl
#align valuation_subring.unit_group_mul_equiv ValuationSubring.unitGroupMulEquiv

@[simp]
theorem coe_unitGroupMulEquiv_apply (a : A.unitGroup) :
    ((A.unitGroupMulEquiv a : A) : K) = ((a : Kˣ) : K) := rfl
#align valuation_subring.coe_unit_group_mul_equiv_apply ValuationSubring.coe_unitGroupMulEquiv_apply

@[simp]
theorem coe_unitGroupMulEquiv_symm_apply (a : Aˣ) : ((A.unitGroupMulEquiv.symm a : Kˣ) : K) = a :=
  rfl
#align valuation_subring.coe_unit_group_mul_equiv_symm_apply ValuationSubring.coe_unitGroupMulEquiv_symm_apply

theorem unitGroup_le_unitGroup {A B : ValuationSubring K} : A.unitGroup ≤ B.unitGroup ↔ A ≤ B := by
  constructor
  · intro h x hx
    rw [← A.valuation_le_one_iff x, le_iff_lt_or_eq] at hx
    by_cases h_1 : x = 0; · simp only [h_1, zero_mem]
    by_cases h_2 : 1 + x = 0
    · simp only [← add_eq_zero_iff_neg_eq.1 h_2, neg_mem _ _ (one_mem _)]
    cases' hx with hx hx
    · have := h (show Units.mk0 _ h_2 ∈ A.unitGroup from A.valuation.map_one_add_of_lt hx)
      simpa using
        B.add_mem _ _ (show 1 + x ∈ B from SetLike.coe_mem (B.unitGroupMulEquiv ⟨_, this⟩ : B))
          (B.neg_mem _ B.one_mem)
    · have := h (show Units.mk0 x h_1 ∈ A.unitGroup from hx)
      exact SetLike.coe_mem (B.unitGroupMulEquiv ⟨_, this⟩ : B)
  · rintro h x (hx : A.valuation x = 1)
    apply_fun A.mapOfLE B h at hx
    simpa using hx
#align valuation_subring.unit_group_le_unit_group ValuationSubring.unitGroup_le_unitGroup

theorem unitGroup_injective : Function.Injective (unitGroup : ValuationSubring K → Subgroup _) :=
  fun A B h => by simpa only [le_antisymm_iff, unitGroup_le_unitGroup] using h
#align valuation_subring.unit_group_injective ValuationSubring.unitGroup_injective

theorem eq_iff_unitGroup {A B : ValuationSubring K} : A = B ↔ A.unitGroup = B.unitGroup :=
  unitGroup_injective.eq_iff.symm
#align valuation_subring.eq_iff_unit_group ValuationSubring.eq_iff_unitGroup

/-- The map on valuation subrings to their unit groups is an order embedding. -/
def unitGroupOrderEmbedding : ValuationSubring K ↪o Subgroup Kˣ where
  toFun A := A.unitGroup
  inj' := unitGroup_injective
  map_rel_iff' {_A _B} := unitGroup_le_unitGroup
#align valuation_subring.unit_group_order_embedding ValuationSubring.unitGroupOrderEmbedding

theorem unitGroup_strictMono : StrictMono (unitGroup : ValuationSubring K → Subgroup _) :=
  unitGroupOrderEmbedding.strictMono
#align valuation_subring.unit_group_strict_mono ValuationSubring.unitGroup_strictMono

end UnitGroup

section nonunits

/-- The nonunits of a valuation subring of `K`, as a subsemigroup of `K`-/
def nonunits : Subsemigroup K where
  carrier := {x | A.valuation x < 1}
  -- Porting note: added `Set.mem_setOf.mp`
  mul_mem' ha hb := (mul_lt_mul₀ (Set.mem_setOf.mp ha) (Set.mem_setOf.mp hb)).trans_eq <| mul_one _
#align valuation_subring.nonunits ValuationSubring.nonunits

theorem mem_nonunits_iff {x : K} : x ∈ A.nonunits ↔ A.valuation x < 1 :=
  Iff.rfl
#align valuation_subring.mem_nonunits_iff ValuationSubring.mem_nonunits_iff

theorem nonunits_le_nonunits {A B : ValuationSubring K} : B.nonunits ≤ A.nonunits ↔ A ≤ B := by
  constructor
  · intro h x hx
    by_cases h_1 : x = 0; · simp only [h_1, zero_mem]
    rw [← valuation_le_one_iff, ← not_lt, Valuation.one_lt_val_iff _ h_1] at hx ⊢
    by_contra h_2; exact hx (h h_2)
  · intro h x hx
    by_contra h_1; exact not_lt.2 (monotone_mapOfLE _ _ h (not_lt.1 h_1)) hx
#align valuation_subring.nonunits_le_nonunits ValuationSubring.nonunits_le_nonunits

theorem nonunits_injective : Function.Injective (nonunits : ValuationSubring K → Subsemigroup _) :=
  fun A B h => by simpa only [le_antisymm_iff, nonunits_le_nonunits] using h.symm
#align valuation_subring.nonunits_injective ValuationSubring.nonunits_injective

theorem nonunits_inj {A B : ValuationSubring K} : A.nonunits = B.nonunits ↔ A = B :=
  nonunits_injective.eq_iff
#align valuation_subring.nonunits_inj ValuationSubring.nonunits_inj

/-- The map on valuation subrings to their nonunits is a dual order embedding. -/
def nonunitsOrderEmbedding : ValuationSubring K ↪o (Subsemigroup K)ᵒᵈ where
  toFun A := A.nonunits
  inj' := nonunits_injective
  map_rel_iff' {_A _B} := nonunits_le_nonunits
#align valuation_subring.nonunits_order_embedding ValuationSubring.nonunitsOrderEmbedding

variable {A}

/-- The elements of `A.nonunits` are those of the maximal ideal of `A` after coercion to `K`.

See also `mem_nonunits_iff_exists_mem_maximalIdeal`, which gets rid of the coercion to `K`,
at the expense of a more complicated right hand side.
 -/
theorem coe_mem_nonunits_iff {a : A} : (a : K) ∈ A.nonunits ↔ a ∈ LocalRing.maximalIdeal A :=
  (valuation_lt_one_iff _ _).symm
#align valuation_subring.coe_mem_nonunits_iff ValuationSubring.coe_mem_nonunits_iff

theorem nonunits_le : A.nonunits ≤ A.toSubring.toSubmonoid.toSubsemigroup := fun _a ha =>
  (A.valuation_le_one_iff _).mp (A.mem_nonunits_iff.mp ha).le
#align valuation_subring.nonunits_le ValuationSubring.nonunits_le

theorem nonunits_subset : (A.nonunits : Set K) ⊆ A :=
  nonunits_le
#align valuation_subring.nonunits_subset ValuationSubring.nonunits_subset

/-- The elements of `A.nonunits` are those of the maximal ideal of `A`.

See also `coe_mem_nonunits_iff`, which has a simpler right hand side but requires the element
to be in `A` already.
 -/
theorem mem_nonunits_iff_exists_mem_maximalIdeal {a : K} :
    a ∈ A.nonunits ↔ ∃ ha, (⟨a, ha⟩ : A) ∈ LocalRing.maximalIdeal A :=
  ⟨fun h => ⟨nonunits_subset h, coe_mem_nonunits_iff.mp h⟩, fun ⟨_, h⟩ =>
    coe_mem_nonunits_iff.mpr h⟩
#align valuation_subring.mem_nonunits_iff_exists_mem_maximal_ideal ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal

/-- `A.nonunits` agrees with the maximal ideal of `A`, after taking its image in `K`. -/
theorem image_maximalIdeal : ((↑) : A → K) '' LocalRing.maximalIdeal A = A.nonunits := by
  ext a
  simp only [Set.mem_image, SetLike.mem_coe, mem_nonunits_iff_exists_mem_maximalIdeal]
  erw [Subtype.exists]
  simp_rw [exists_and_right, exists_eq_right]
  -- Porting note: added
  simp
#align valuation_subring.image_maximal_ideal ValuationSubring.image_maximalIdeal

end nonunits

section PrincipalUnitGroup

/-- The principal unit group of a valuation subring, as a subgroup of `Kˣ`. -/
def principalUnitGroup : Subgroup Kˣ where
  carrier := {x | A.valuation (x - 1) < 1}
  mul_mem' := by
    intro a b ha hb
    -- Porting note: added
    rw [Set.mem_setOf] at ha hb
    refine lt_of_le_of_lt ?_ (max_lt hb ha)
    -- Porting note: `sub_add_sub_cancel` needed some help
    rw [← one_mul (A.valuation (b - 1)), ← A.valuation.map_one_add_of_lt ha, add_sub_cancel,
      ← Valuation.map_mul, mul_sub_one, ← sub_add_sub_cancel (↑(a * b) : K) _ 1]
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
#align valuation_subring.principal_unit_group ValuationSubring.principalUnitGroup

theorem principal_units_le_units : A.principalUnitGroup ≤ A.unitGroup := fun a h => by
  simpa only [add_sub_cancel] using A.valuation.map_one_add_of_lt h
#align valuation_subring.principal_units_le_units ValuationSubring.principal_units_le_units

theorem mem_principalUnitGroup_iff (x : Kˣ) :
    x ∈ A.principalUnitGroup ↔ A.valuation ((x : K) - 1) < 1 :=
  Iff.rfl
#align valuation_subring.mem_principal_unit_group_iff ValuationSubring.mem_principalUnitGroup_iff

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
#align valuation_subring.principal_unit_group_le_principal_unit_group ValuationSubring.principalUnitGroup_le_principalUnitGroup

theorem principalUnitGroup_injective :
    Function.Injective (principalUnitGroup : ValuationSubring K → Subgroup _) := fun A B h => by
  simpa [le_antisymm_iff, principalUnitGroup_le_principalUnitGroup] using h.symm
#align valuation_subring.principal_unit_group_injective ValuationSubring.principalUnitGroup_injective

theorem eq_iff_principalUnitGroup {A B : ValuationSubring K} :
    A = B ↔ A.principalUnitGroup = B.principalUnitGroup :=
  principalUnitGroup_injective.eq_iff.symm
#align valuation_subring.eq_iff_principal_unit_group ValuationSubring.eq_iff_principalUnitGroup

/-- The map on valuation subrings to their principal unit groups is an order embedding. -/
def principalUnitGroupOrderEmbedding : ValuationSubring K ↪o (Subgroup Kˣ)ᵒᵈ where
  toFun A := A.principalUnitGroup
  inj' := principalUnitGroup_injective
  map_rel_iff' {_A _B} := principalUnitGroup_le_principalUnitGroup
#align valuation_subring.principal_unit_group_order_embedding ValuationSubring.principalUnitGroupOrderEmbedding

theorem coe_mem_principalUnitGroup_iff {x : A.unitGroup} :
    (x : Kˣ) ∈ A.principalUnitGroup ↔
      A.unitGroupMulEquiv x ∈ (Units.map (LocalRing.residue A).toMonoidHom).ker := by
  rw [MonoidHom.mem_ker, Units.ext_iff]
  let π := Ideal.Quotient.mk (LocalRing.maximalIdeal A); convert_to _ ↔ π _ = 1
  rw [← π.map_one, ← sub_eq_zero, ← π.map_sub, Ideal.Quotient.eq_zero_iff_mem, valuation_lt_one_iff]
  simp [mem_principalUnitGroup_iff]
#align valuation_subring.coe_mem_principal_unit_group_iff ValuationSubring.coe_mem_principalUnitGroup_iff

/-- The principal unit group agrees with the kernel of the canonical map from
the units of `A` to the units of the residue field of `A`. -/
def principalUnitGroupEquiv :
    A.principalUnitGroup ≃* (Units.map (LocalRing.residue A).toMonoidHom).ker where
  toFun x :=
    ⟨A.unitGroupMulEquiv ⟨_, A.principal_units_le_units x.2⟩,
      A.coe_mem_principalUnitGroup_iff.1 x.2⟩
  invFun x :=
    ⟨A.unitGroupMulEquiv.symm x, by
      rw [A.coe_mem_principalUnitGroup_iff]; simpa using SetLike.coe_mem x⟩
  left_inv x := by simp
  right_inv x := by simp
  map_mul' x y := rfl
#align valuation_subring.principal_unit_group_equiv ValuationSubring.principalUnitGroupEquiv

theorem principalUnitGroupEquiv_apply (a : A.principalUnitGroup) :
    (((principalUnitGroupEquiv A a : Aˣ) : A) : K) = (a : Kˣ) :=
  rfl
#align valuation_subring.principal_unit_group_equiv_apply ValuationSubring.principalUnitGroupEquiv_apply

theorem principalUnitGroup_symm_apply (a : (Units.map (LocalRing.residue A).toMonoidHom).ker) :
    ((A.principalUnitGroupEquiv.symm a : Kˣ) : K) = ((a : Aˣ) : A) :=
  rfl
#align valuation_subring.principal_unit_group_symm_apply ValuationSubring.principalUnitGroup_symm_apply

/-- The canonical map from the unit group of `A` to the units of the residue field of `A`. -/
def unitGroupToResidueFieldUnits : A.unitGroup →* (LocalRing.ResidueField A)ˣ :=
  MonoidHom.comp (Units.map <| (Ideal.Quotient.mk _).toMonoidHom) A.unitGroupMulEquiv.toMonoidHom
#align valuation_subring.unit_group_to_residue_field_units ValuationSubring.unitGroupToResidueFieldUnits

set_option backward.isDefEq.lazyWhnfCore false in -- See https://github.com/leanprover-community/mathlib4/issues/12534
@[simp]
theorem coe_unitGroupToResidueFieldUnits_apply (x : A.unitGroup) :
    (A.unitGroupToResidueFieldUnits x : LocalRing.ResidueField A) =
      Ideal.Quotient.mk _ (A.unitGroupMulEquiv x : A) :=
  rfl
#align valuation_subring.coe_unit_group_to_residue_field_units_apply ValuationSubring.coe_unitGroupToResidueFieldUnits_apply

theorem ker_unitGroupToResidueFieldUnits :
    A.unitGroupToResidueFieldUnits.ker = A.principalUnitGroup.comap A.unitGroup.subtype := by
  ext
  -- Porting note: simp fails but rw works
  -- See https://github.com/leanprover-community/mathlib4/issues/5026
  -- simp [Subgroup.mem_comap, Subgroup.coeSubtype, coe_mem_principalUnitGroup_iff]
  rw [Subgroup.mem_comap, Subgroup.coeSubtype, coe_mem_principalUnitGroup_iff]
  rfl
  -- simp [Subgroup.mem_comap, Subgroup.coeSubtype, coe_mem_principalUnitGroup_iff]
#align valuation_subring.ker_unit_group_to_residue_field_units ValuationSubring.ker_unitGroupToResidueFieldUnits

theorem surjective_unitGroupToResidueFieldUnits :
    Function.Surjective A.unitGroupToResidueFieldUnits :=
  (LocalRing.surjective_units_map_of_local_ringHom _ Ideal.Quotient.mk_surjective
        LocalRing.isLocalRingHom_residue).comp
    (MulEquiv.surjective _)
#align valuation_subring.surjective_unit_group_to_residue_field_units ValuationSubring.surjective_unitGroupToResidueFieldUnits

/-- The quotient of the unit group of `A` by the principal unit group of `A` agrees with
the units of the residue field of `A`. -/
def unitsModPrincipalUnitsEquivResidueFieldUnits :
    A.unitGroup ⧸ A.principalUnitGroup.comap A.unitGroup.subtype ≃* (LocalRing.ResidueField A)ˣ :=
  (QuotientGroup.quotientMulEquivOfEq A.ker_unitGroupToResidueFieldUnits.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ A.surjective_unitGroupToResidueFieldUnits)
#align valuation_subring.units_mod_principal_units_equiv_residue_field_units ValuationSubring.unitsModPrincipalUnitsEquivResidueFieldUnits

/-- Porting note: Lean needs to be reminded of this instance -/
local instance : MulOneClass ({ x // x ∈ unitGroup A } ⧸
  Subgroup.comap (Subgroup.subtype (unitGroup A)) (principalUnitGroup A)) := inferInstance

-- @[simp] -- Porting note: not in simpNF
theorem unitsModPrincipalUnitsEquivResidueFieldUnits_comp_quotientGroup_mk :
    A.unitsModPrincipalUnitsEquivResidueFieldUnits.toMonoidHom.comp (QuotientGroup.mk' _) =
      A.unitGroupToResidueFieldUnits := rfl
#align valuation_subring.units_mod_principal_units_equiv_residue_field_units_comp_quotient_group_mk ValuationSubring.unitsModPrincipalUnitsEquivResidueFieldUnits_comp_quotientGroup_mk

theorem unitsModPrincipalUnitsEquivResidueFieldUnits_comp_quotientGroup_mk_apply
    (x : A.unitGroup) :
    A.unitsModPrincipalUnitsEquivResidueFieldUnits.toMonoidHom (QuotientGroup.mk x) =
      A.unitGroupToResidueFieldUnits x := rfl
#align valuation_subring.units_mod_principal_units_equiv_residue_field_units_comp_quotient_group_mk_apply ValuationSubring.unitsModPrincipalUnitsEquivResidueFieldUnits_comp_quotientGroup_mk_apply

end PrincipalUnitGroup

/-! ### Pointwise actions

This transfers the action from `Subring.pointwiseMulAction`, noting that it only applies when
the action is by a group. Notably this provides an instances when `G` is `K ≃+* K`.

These instances are in the `Pointwise` locale.

The lemmas in this section are copied from `RingTheory/Subring/Pointwise.lean`; try to keep these
in sync.
-/


section PointwiseActions

open scoped Pointwise

variable {G : Type*} [Group G] [MulSemiringAction G K]

/-- The action on a valuation subring corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale. -/
def pointwiseHasSMul : SMul G (ValuationSubring K) where
  smul g S :=-- TODO: if we add `ValuationSubring.map` at a later date, we should use it here
    { g • S.toSubring with
      mem_or_inv_mem' := fun x =>
        (mem_or_inv_mem S (g⁻¹ • x)).imp Subring.mem_pointwise_smul_iff_inv_smul_mem.mpr fun h =>
          Subring.mem_pointwise_smul_iff_inv_smul_mem.mpr <| by rwa [smul_inv''] }
#align valuation_subring.pointwise_has_smul ValuationSubring.pointwiseHasSMul

scoped[Pointwise] attribute [instance] ValuationSubring.pointwiseHasSMul

open scoped Pointwise

@[simp]
theorem coe_pointwise_smul (g : G) (S : ValuationSubring K) : ↑(g • S) = g • (S : Set K) := rfl
#align valuation_subring.coe_pointwise_smul ValuationSubring.coe_pointwise_smul

@[simp]
theorem pointwise_smul_toSubring (g : G) (S : ValuationSubring K) :
    (g • S).toSubring = g • S.toSubring := rfl
#align valuation_subring.pointwise_smul_to_subring ValuationSubring.pointwise_smul_toSubring

/-- The action on a valuation subring corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale.

This is a stronger version of `ValuationSubring.pointwiseSMul`. -/
def pointwiseMulAction : MulAction G (ValuationSubring K) :=
  toSubring_injective.mulAction toSubring pointwise_smul_toSubring
#align valuation_subring.pointwise_mul_action ValuationSubring.pointwiseMulAction

scoped[Pointwise] attribute [instance] ValuationSubring.pointwiseMulAction

open scoped Pointwise

theorem smul_mem_pointwise_smul (g : G) (x : K) (S : ValuationSubring K) : x ∈ S → g • x ∈ g • S :=
  (Set.smul_mem_smul_set : _ → _ ∈ g • (S : Set K))
#align valuation_subring.smul_mem_pointwise_smul ValuationSubring.smul_mem_pointwise_smul

instance : CovariantClass G (ValuationSubring K) HSMul.hSMul LE.le :=
  ⟨fun _ _ _ => Set.image_subset _⟩

theorem mem_smul_pointwise_iff_exists (g : G) (x : K) (S : ValuationSubring K) :
    x ∈ g • S ↔ ∃ s : K, s ∈ S ∧ g • s = x :=
  (Set.mem_smul_set : x ∈ g • (S : Set K) ↔ _)
#align valuation_subring.mem_smul_pointwise_iff_exists ValuationSubring.mem_smul_pointwise_iff_exists

instance pointwise_central_scalar [MulSemiringAction Gᵐᵒᵖ K] [IsCentralScalar G K] :
    IsCentralScalar G (ValuationSubring K) :=
  ⟨fun g S => toSubring_injective <| op_smul_eq_smul g S.toSubring⟩
#align valuation_subring.pointwise_central_scalar ValuationSubring.pointwise_central_scalar

@[simp]
theorem smul_mem_pointwise_smul_iff {g : G} {S : ValuationSubring K} {x : K} :
    g • x ∈ g • S ↔ x ∈ S := Set.smul_mem_smul_set_iff
#align valuation_subring.smul_mem_pointwise_smul_iff ValuationSubring.smul_mem_pointwise_smul_iff

theorem mem_pointwise_smul_iff_inv_smul_mem {g : G} {S : ValuationSubring K} {x : K} :
    x ∈ g • S ↔ g⁻¹ • x ∈ S := Set.mem_smul_set_iff_inv_smul_mem
#align valuation_subring.mem_pointwise_smul_iff_inv_smul_mem ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem

theorem mem_inv_pointwise_smul_iff {g : G} {S : ValuationSubring K} {x : K} :
    x ∈ g⁻¹ • S ↔ g • x ∈ S := Set.mem_inv_smul_set_iff
#align valuation_subring.mem_inv_pointwise_smul_iff ValuationSubring.mem_inv_pointwise_smul_iff

@[simp]
theorem pointwise_smul_le_pointwise_smul_iff {g : G} {S T : ValuationSubring K} :
    g • S ≤ g • T ↔ S ≤ T := Set.set_smul_subset_set_smul_iff
#align valuation_subring.pointwise_smul_le_pointwise_smul_iff ValuationSubring.pointwise_smul_le_pointwise_smul_iff

theorem pointwise_smul_subset_iff {g : G} {S T : ValuationSubring K} : g • S ≤ T ↔ S ≤ g⁻¹ • T :=
  Set.set_smul_subset_iff
#align valuation_subring.pointwise_smul_subset_iff ValuationSubring.pointwise_smul_subset_iff

theorem subset_pointwise_smul_iff {g : G} {S T : ValuationSubring K} : S ≤ g • T ↔ g⁻¹ • S ≤ T :=
  Set.subset_set_smul_iff
#align valuation_subring.subset_pointwise_smul_iff ValuationSubring.subset_pointwise_smul_iff

end PointwiseActions

section

variable {L J : Type*} [Field L] [Field J]

/-- The pullback of a valuation subring `A` along a ring homomorphism `K →+* L`. -/
def comap (A : ValuationSubring L) (f : K →+* L) : ValuationSubring K :=
  { A.toSubring.comap f with mem_or_inv_mem' := fun k => by simp [ValuationSubring.mem_or_inv_mem] }
#align valuation_subring.comap ValuationSubring.comap

@[simp]
theorem coe_comap (A : ValuationSubring L) (f : K →+* L) : (A.comap f : Set K) = f ⁻¹' A := rfl
#align valuation_subring.coe_comap ValuationSubring.coe_comap

@[simp]
theorem mem_comap {A : ValuationSubring L} {f : K →+* L} {x : K} : x ∈ A.comap f ↔ f x ∈ A :=
  Iff.rfl
#align valuation_subring.mem_comap ValuationSubring.mem_comap

theorem comap_comap (A : ValuationSubring J) (g : L →+* J) (f : K →+* L) :
    (A.comap g).comap f = A.comap (g.comp f) := rfl
#align valuation_subring.comap_comap ValuationSubring.comap_comap

end

end ValuationSubring

namespace Valuation

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (x : Kˣ)

-- @[simp] -- Porting note: not in simpNF
theorem mem_unitGroup_iff : x ∈ v.valuationSubring.unitGroup ↔ v x = 1 :=
  (Valuation.isEquiv_iff_val_eq_one _ _).mp (Valuation.isEquiv_valuation_valuationSubring _).symm
#align valuation.mem_unit_group_iff Valuation.mem_unitGroup_iff

end Valuation
