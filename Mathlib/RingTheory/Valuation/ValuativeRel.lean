/-
Copyright (c) 2025 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu, Adam Topaz
-/
import Mathlib.GroupTheory.Congruence.GroupWithZero
import Mathlib.RingTheory.Localization.AtPrime
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Topology.Defs.Filter

/-!

# Valuative Relations

In this file we introduce a class called `ValuativeRel R` for a ring `R`.
This bundles a relation `rel : R → R → Prop` on `R` which mimics a
preorder on `R` arising from a valuation.
We introduce the notation `x ≤ᵥ y` for this relation.

Recall that the equivalence class of a valuation is *completely* characterized by
such a preorder. Thus, we can think of `ValuativeRel R` as a way of
saying that `R` is endowed with an equivalence class of valuations.

## Main Definitions

- `ValuativeRel R` endows a commutative ring `R` with a relation arising from a valuation.
  This is equivalent to fixing an equivalence class of valuations on `R`.
  Use the notation `x ≤ᵥ y` for this relation.
- `ValuativeRel.valuation R` is the "canonical" valuation associated to `ValuativeRel R`,
  taking values in `ValuativeRel.ValueGroupWithZero R`.
- Given a valution `v` on `R` and an instance `[ValuativeRel R]`, writing `[v.Compatible]`
  ensures that the relation `x ≤ᵥ y` is equivalent to `v x ≤ v y`. Note that
  it is possible to have `[v.Compatible]` and `[w.Compatible]` for two different valuations on `R`.
- If we have both `[ValuativeRel R]` and `[TopologicalSpace R]`, then writing
  `[ValuativeTopology R]` ensures that the topology on `R` agrees with the one induced by the
  valuation.
- Given `[ValuativeRel A]`, `[ValuativeRel B]` and `[Algebra A B]`, the class
  `[ValuativeExtension A B]` ensures that the algebra map `A → B` is compatible with the valuations
  on `A` and `B`. For example, this can be used to talk about extensions of valued fields.


## Remark

The last two axioms in `ValuativeRel`, namely `rel_mul_cancel` and `not_rel_one_zero`, are
used to ensure that we have a well-behaved valuation taking values in a *value group* (with zero).
In principle, it should be possible to drop these two axioms and obtain a value monoid,
however, such a value monoid would not necessarily embed into an ordered abelian group with zero.
Similarly, without these axioms, the support of the valuation need not be a prime ideal.
We have thus opted to include these two axioms and obtain a `ValueGroupWithZero` associated to
a `ValuativeRel` in order to best align with the literature about valuations on commutative rings.

Future work could refactor `ValuativeRel` by dropping the `rel_mul_cancel` and `not_rel_one_zero`
axioms, opting to make these mixins instead.

## Projects

The `ValuativeRel` class should eventually replace the existing `Valued` typeclass.
Once such a refactor happens, `ValuativeRel` could be renamed to `Valued`.

-/

noncomputable section

-- TODO: move me
lemma _root_.Valuation.IsEquiv.isNontrivial {R : Type*} [CommRing R] {Γ₁ Γ₂ : Type*}
    [LinearOrderedCommGroupWithZero Γ₁] [LinearOrderedCommGroupWithZero Γ₂]
    {v₁ : Valuation R Γ₁} {v₂ : Valuation R Γ₂} [hv₁ : v₁.IsNontrivial] (h : v₁.IsEquiv v₂) :
    v₂.IsNontrivial where
  exists_val_nontrivial := by
    rcases hv₁.exists_val_nontrivial with ⟨x, hx⟩
    use x
    rwa [h.ne_zero, Ne, Ne, h.eq_one_iff_eq_one] at hx

-- TODO: move me
lemma _root_.Valuation.IsEquiv.isNontrivial_iff {R : Type*} [CommRing R] {Γ₁ Γ₂ : Type*}
    [LinearOrderedCommGroupWithZero Γ₁] [LinearOrderedCommGroupWithZero Γ₂]
    {v₁ : Valuation R Γ₁} {v₂ : Valuation R Γ₂} (h : v₁.IsEquiv v₂) :
    v₁.IsNontrivial ↔ v₂.IsNontrivial :=
  ⟨fun _ ↦ h.isNontrivial, fun _ ↦ h.symm.isNontrivial⟩

/-- The class `[ValuativeRel R]` class introduces an operator `x ≤ᵥ y : Prop` for `x y : R`
which is the natural relation arising from (the equivalence class of) a valuation on `R`.
More precisely, if v is a valuation on R then the associated relation is `x ≤ᵥ y ↔ v x ≤ v y`.
Use this class to talk about the case where `R` is equipped with an equivalence class
of valuations. -/
class ValuativeRel (R : Type*) [CommRing R] where
  /-- The relation operator arising from `ValuativeRel`. -/
  rel : R → R → Prop
  rel_total (x y) : rel x y ∨ rel y x
  rel_trans {z y x} : rel x y → rel y z → rel x z
  rel_add {x y z} : rel x z → rel y z → rel (x + y) z
  rel_mul_right {x y} (z) : rel x y → rel (x * z) (y * z)
  rel_mul_cancel {x y z} : ¬ rel z 0 → rel (x * z) (y * z) → rel x y
  not_rel_one_zero : ¬ rel 1 0

@[inherit_doc] infix:50 " ≤ᵥ " => ValuativeRel.rel

macro_rules | `($a ≤ᵥ $b) => `(binrel% ValuativeRel.rel $a $b)

/-- If `B` is an `A` algebra and both `A` and `B` have valuative relations,
we say that `B|A` is a valuative extension if the valuative relation on `A` is
induced by the one on `B`. -/
class ValuativeExtension
    (A B : Type*)
    [CommRing A] [CommRing B]
    [ValuativeRel A] [ValuativeRel B]
    [Algebra A B] where
  rel_iff_rel (a b : A) : algebraMap A B a ≤ᵥ algebraMap A B b ↔ a ≤ᵥ b

namespace Valuation

variable {R Γ : Type*} [CommRing R] [LinearOrderedCommMonoidWithZero Γ]
  (v : Valuation R Γ)

/-- We say that a valuation `v` is `Compatible` if the relation `x ≤ᵥ y`
is equivalent to `v x ≤ x y`. -/
class Compatible [ValuativeRel R] where
  rel_iff_le (x y : R) : x ≤ᵥ y ↔ v x ≤ v y

end Valuation

/-- A preorder on a ring is said to be "valuative" if it agrees with the
valuative relation. -/
class ValuativePreorder (R : Type*) [CommRing R] [ValuativeRel R] [Preorder R] where
  rel_iff_le (x y : R) : x ≤ᵥ y ↔ x ≤ y

namespace ValuativeRel

variable {R : Type*} [CommRing R] [ValuativeRel R]

@[simp]
lemma rel_refl (x : R) : x ≤ᵥ x := by
  cases rel_total x x <;> assumption

lemma rel_rfl {x : R} : x ≤ᵥ x :=
  rel_refl x

protected alias rel.refl := rel_refl

protected alias rel.rfl := rel_rfl

instance (priority := low) : Nontrivial R where
  exists_pair_ne := ⟨0, 1, fun h ↦ (h ▸ ValuativeRel.not_rel_one_zero) rel_rfl⟩

@[simp]
theorem zero_rel (x : R) : 0 ≤ᵥ x := by
  simpa using rel_mul_right x ((rel_total 0 1).resolve_right not_rel_one_zero)

lemma rel_mul_left {x y : R} (z) : x ≤ᵥ y → (z * x) ≤ᵥ (z * y) := by
  rw [mul_comm z x, mul_comm z y]
  apply rel_mul_right

instance : Trans (rel (R := R)) (rel (R := R)) (rel (R := R)) where
  trans h1 h2 := rel_trans h1 h2

protected alias rel.trans := rel_trans

lemma rel_trans' {x y z : R} (h1 : y ≤ᵥ z) (h2 : x ≤ᵥ y) : x ≤ᵥ z :=
  h2.trans h1

protected alias rel.trans' := rel_trans'

lemma rel_mul {x x' y y' : R} (h1 : x ≤ᵥ y) (h2 : x' ≤ᵥ y') : (x * x') ≤ᵥ y * y' := by
  calc x * x' ≤ᵥ x * y' := rel_mul_left _ h2
    _ ≤ᵥ y * y' := rel_mul_right _ h1

lemma rel_mul_cancel_iff {x y z : R} (hz : ¬ z ≤ᵥ 0) : x * z ≤ᵥ y * z ↔ x ≤ᵥ y :=
  ⟨rel_mul_cancel hz, rel_mul_right z⟩

theorem rel_add_cases (x y : R) : x + y ≤ᵥ x ∨ x + y ≤ᵥ y :=
  (rel_total y x).imp (fun h => rel_add .rfl h) (fun h => rel_add h .rfl)

variable (R) in
/-- The support of the valuation on `R`. -/
def supp : Ideal R where
  carrier := { x | x ≤ᵥ 0 }
  add_mem' := rel_add
  zero_mem' := rel_rfl
  smul_mem' x _ h := by simpa using rel_mul_left _ h

@[simp]
lemma supp_def (x : R) : x ∈ supp R ↔ x ≤ᵥ 0 := Iff.refl _

lemma supp_eq_of_compatible {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    {v : Valuation R Γ} [hv : v.Compatible] : supp R = v.supp := by
  ext x
  rw [supp_def, v.mem_supp_iff, hv.rel_iff_le, map_zero, le_zero_iff]

instance : Ideal.IsPrime (ValuativeRel.supp R) where
  ne_top' := Ideal.ne_top_iff_one _ |>.mpr not_rel_one_zero
  mem_or_mem' hxy := or_iff_not_imp_left.mpr fun hx ↦ rel_mul_cancel hx <|
    by rwa [zero_mul, mul_comm]

instance (priority := low) {k : Type*} [Field k] [ValuativeRel k] : Ideal.IsMaximal (supp k) where
  out := isCoatom_iff_eq_bot.mpr <| (eq_bot_or_eq_top _).resolve_right <|
    Ideal.IsPrime.ne_top inferInstance

variable (R) in
/-- The submonoid of elements `x : R` whose valuation is positive. -/
abbrev posSubmonoid : Submonoid R := (supp R).primeCompl

@[simp]
lemma posSubmonoid_def (x : R) : x ∈ posSubmonoid R ↔ ¬ x ≤ᵥ 0 := Iff.refl _

@[simp]
lemma right_cancel_posSubmonoid (x y : R) (u : posSubmonoid R) :
    x * u ≤ᵥ y * u ↔ x ≤ᵥ y := ⟨rel_mul_cancel u.prop, rel_mul_right _⟩

@[simp]
lemma left_cancel_posSubmonoid (x y : R) (u : posSubmonoid R) :
    u * x ≤ᵥ u * y ↔ x ≤ᵥ y := by
  simp only [← right_cancel_posSubmonoid x y u, mul_comm]

/-- Construct a valuative relation on a ring using a valuation. -/
def ofValuation
    {S Γ : Type*} [CommRing S]
    [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation S Γ) : ValuativeRel S where
  rel x y := v x ≤ v y
  rel_total x y := le_total (v x) (v y)
  rel_trans := le_trans
  rel_add hab hbc := (map_add_le_max v _ _).trans (sup_le hab hbc)
  rel_mul_right _ h := by simp only [map_mul, mul_le_mul_right' h]
  rel_mul_cancel h0 h := by
    rw [map_zero, le_zero_iff] at h0
    simp only [map_mul] at h
    exact le_of_mul_le_mul_right h (lt_of_le_of_ne' zero_le' h0)
  not_rel_one_zero := by simp

lemma _root_.Valuation.Compatible.ofValuation
    {S Γ : Type*} [CommRing S]
    [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation S Γ) :
    letI := ValuativeRel.ofValuation v  -- letI so that instance is inlined directly in declaration
    Valuation.Compatible v :=
  letI := ValuativeRel.ofValuation v
  ⟨fun _ _ ↦ Iff.rfl⟩

lemma isEquiv {Γ₁ Γ₂ : Type*}
    [LinearOrderedCommMonoidWithZero Γ₁]
    [LinearOrderedCommMonoidWithZero Γ₂]
    (v₁ : Valuation R Γ₁)
    (v₂ : Valuation R Γ₂)
    [v₁.Compatible] [v₂.Compatible] :
    v₁.IsEquiv v₂ := by
  intro x y
  simp_rw [← Valuation.Compatible.rel_iff_le]

variable (R) in
/-- An alias for endowing a ring with a preorder defined as the valuative relation. -/
def WithPreorder := R

/-- The ring instance on `WithPreorder R` arising from the ring structure on `R`. -/
instance : CommRing (WithPreorder R) := inferInstanceAs (CommRing R)

/-- The preorder on `WithPreorder R` arising from the valuative relation on `R`. -/
instance : Preorder (WithPreorder R) where
  le (x y : R) := x ≤ᵥ y
  le_refl _ := rel_refl _
  le_trans _ _ _ := rel_trans

/-- The valutaive relation on `WithPreorder R` arising from the valuative relation on `R`.
This is defined as the preorder itself. -/
instance : ValuativeRel (WithPreorder R) where
  rel := (· ≤ ·)
  rel_total := rel_total (R := R)
  rel_trans := rel_trans (R := R)
  rel_add := rel_add (R := R)
  rel_mul_right := rel_mul_right (R := R)
  rel_mul_cancel := rel_mul_cancel (R := R)
  not_rel_one_zero := not_rel_one_zero (R := R)

instance : ValuativePreorder (WithPreorder R) where
  rel_iff_le _ _ := Iff.rfl

section Equiv

def equiv (x y : R) : Prop := x ≤ᵥ y ∧ y ≤ᵥ x

@[inherit_doc ValuativeRel.equiv]
notation:50 a:50 " ∼ᵥ " b:51 => binrel% ValuativeRel.equiv a b

@[simp]
lemma equiv_refl (x : R) : x ∼ᵥ x :=
  ⟨rel_refl _, rel_refl _⟩

lemma equiv_rfl {x : R} : x ∼ᵥ x :=
  equiv_refl x

lemma equiv_trans {x y z : R} (hxy : x ∼ᵥ y) (hyz : y ∼ᵥ z) : x ∼ᵥ z :=
  ⟨rel_trans hxy.1 hyz.1, rel_trans hyz.2 hxy.2⟩

lemma equiv_symm {x y : R} (hxy : x ∼ᵥ y) : y ∼ᵥ x :=
  ⟨hxy.2, hxy.1⟩

lemma equiv_mul {x x' y y' : R} (hx : x ∼ᵥ x') (hy : y ∼ᵥ y') : x * y ∼ᵥ x' * y' :=
  ⟨rel_mul hx.1 hy.1, rel_mul hx.2 hy.2⟩

lemma equiv_zero {x : R} : x ∼ᵥ 0 ↔ x ≤ᵥ 0 := ⟨fun H ↦ H.1, fun H ↦ ⟨H, zero_rel _⟩⟩

lemma not_equiv_one_zero : ¬ ((1 : R) ∼ᵥ 0) := fun H ↦ not_rel_one_zero H.1

lemma _root_.ValuativeExtension.equiv_iff_equiv {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [ValuativeRel A] [ValuativeRel B] [ValuativeExtension A B] {a b : A} :
    algebraMap A B a ∼ᵥ algebraMap A B b ↔ a ∼ᵥ b := by
  rw [equiv, equiv, ValuativeExtension.rel_iff_rel, ValuativeExtension.rel_iff_rel]

variable (R) in
def equivCon : Con R where
  r x y := x ∼ᵥ y
  iseqv :=
  { refl := equiv_refl
    symm := equiv_symm
    trans := equiv_trans }
  mul' := equiv_mul

@[simp]
lemma equivCon_apply {x y : R} : equivCon R x y ↔ x ∼ᵥ y := .rfl

variable (R) in
def ValueQuotient : Type _ := (equivCon R).Quotient

namespace ValueQuotient

def mk : R → ValueQuotient R := Quotient.mk''

@[simp]
protected lemma eq {x y : R} : mk x = mk y ↔ x ∼ᵥ y := Quotient.eq

instance : CommMonoidWithZero (ValueQuotient R) :=
  inferInstanceAs <| CommMonoidWithZero (equivCon R).Quotient

-- TODO: Should be general instance
instance : LinearOrder (ValueQuotient R) where
  le := Quotient.lift₂ (· ≤ᵥ ·) fun a₁ b₁ a₂ b₂ ha hb ↦ iff_iff_eq.mp
    ⟨fun H ↦ rel_trans ha.2 (rel_trans H hb.1), fun H ↦ rel_trans ha.1 (rel_trans H hb.2)⟩
  le_refl := Quotient.ind fun x ↦ rel_refl x
  le_trans := Quotient.ind fun x ↦ Quotient.ind₂ fun y z ↦ rel_trans
  le_antisymm := Quotient.ind₂ fun x y hx hy ↦ Quotient.eq.mpr ⟨hx, hy⟩
  le_total := Quotient.ind₂ rel_total
  toDecidableLE := open Classical in inferInstance

instance : LinearOrderedCommMonoidWithZero (ValueQuotient R) where
  mul_le_mul_left := Quotient.ind₂ fun _ _ hxy ↦ Quotient.ind fun _ ↦ rel_mul_left _ hxy
  bot := 0
  bot_le := Quotient.ind zero_rel
  zero_le_one := zero_rel _

instance : Nontrivial (ValueQuotient R) where
  exists_pair_ne := ⟨1, 0, by
    rw [Ne, ← Con.coe_one, ← Con.coe_zero, Con.eq, equivCon_apply]
    exact not_equiv_one_zero ⟩

lemma mk_add_le {x y : R} {r : ValueQuotient R} :
    mk x ≤ r → mk y ≤ r → mk (x + y) ≤ r :=
  Quotient.inductionOn r fun _ ↦ rel_add

end ValueQuotient

variable (R) in
def preValuation : Valuation R (ValueQuotient R) where
  toFun := ValueQuotient.mk
  map_zero' := rfl
  map_add_le_max' _ _ :=
    ValueQuotient.mk_add_le (le_max_left _ _) (le_max_right _ _)
  __ := (equivCon R).mk'

instance : (preValuation R).Compatible where
  rel_iff_le _ _ := Iff.rfl

section LocalRing

variable [IsLocalRing R] [hmax : Ideal.IsMaximal (supp R)]

lemma isUnit_iff_supp {x : R} : IsUnit x ↔ x ∉ supp R := by
  rw [IsLocalRing.isMaximal_iff _ |>.mp hmax, IsLocalRing.notMem_maximalIdeal]

namespace ValueQuotient

protected lemma isUnit_iff_ne_zero {v : ValueQuotient R} : IsUnit v ↔ v ≠ 0 := by
  refine ⟨fun H ↦ H.ne_zero, Quotient.inductionOn v fun x (hx : mk x ≠ mk 0) ↦ ?_⟩
  rw [Ne, ValueQuotient.eq, equiv_zero] at hx
  exact (isUnit_iff_supp.mpr hx).map (preValuation R)

instance : CommGroupWithZero (ValueQuotient R) where
  inv x := open scoped Classical in
    if h : IsUnit x then h.unit.inv else 0
  inv_zero := by simp
  mul_inv_cancel a ha := by
    simp [ValueQuotient.isUnit_iff_ne_zero.mpr ha]

instance : LinearOrderedCommGroupWithZero (ValueQuotient R) where

end ValueQuotient

end LocalRing

end Equiv

section Localization

variable {S : Submonoid R} (hS : S ≤ (posSubmonoid R))

-- Note: to extend this to any `R`-algebra `B` satisfying `IsLocalization B S`, we
-- need a version of `Localization.liftOn₂` to lift the relation.
@[reducible] noncomputable def localization : ValuativeRel (Localization S) where
  rel x y := Localization.liftOn₂ x y (fun a s b t ↦ t * a ≤ᵥ s * b) <| by
    simp_rw [Localization.r_iff_exists, eq_iff_iff]
    rintro a₁ a₂ s₁ s₂ b₁ b₂ t₁ t₂ ⟨u, hu⟩ ⟨v, hv⟩
    conv_lhs => rw [← rel_mul_cancel_iff (hS (u * v * s₂ * t₂).2)]
    conv_rhs => rw [← rel_mul_cancel_iff (hS (u * v * s₁ * t₁).2)]
    calc  t₁ * a₁ * (u * v * s₂ * t₂) ≤ᵥ s₁ * b₁ * (u * v * s₂ * t₂)
      _ ↔ (u * (s₂ * a₁)) * v * t₁ * t₂ ≤ᵥ (v * (t₂ * b₁)) * u * s₁ * s₂ := by ring_nf
      _ ↔ (u * (s₁ * a₂)) * v * t₁ * t₂ ≤ᵥ (v * (t₁ * b₂)) * u * s₁ * s₂ := by rw [hu, hv]
      _ ↔ t₂ * a₂ * (u * v * s₁ * t₁) ≤ᵥ s₂ * b₂ * (u * v * s₁ * t₁) := by ring_nf
  rel_total x y := Localization.induction_on₂ x y fun ⟨a, s⟩ ⟨b, t⟩ ↦ by
    simpa only [Localization.liftOn₂_mk] using rel_total _ _
  rel_trans {x y z} := Localization.induction_on₃ x y z fun ⟨a, s⟩ ⟨b, t⟩ ⟨c, u⟩ ↦ by
    simp_rw [Localization.liftOn₂_mk]
    refine fun h1 h2 ↦ rel_mul_cancel (hS t.2) ?_
    calc  s * c * t
      _ = s * (t * c) := by ring
      _ ≤ᵥ s * (u * b) := rel_mul_left (s : R) h1
      _ = u * (s * b) := by ring
      _ ≤ᵥ u * (t * a) := rel_mul_left (u : R) h2
      _ = u * a * t := by ring
  rel_add {x y z} := Localization.induction_on₃ x y z fun ⟨a, s⟩ ⟨b, t⟩ ⟨c, u⟩ ↦ by
    simp_rw [Localization.add_mk, Localization.liftOn₂_mk]
    intro h1 h2
    calc  u * (s * b + t * a)
      _ = s * (u * b) + t * (u * a) := by ring
      _ ≤ᵥ s * t * c := by
        refine rel_add ?_ ?_
        · convert rel_mul_left (s : R) h2 using 1; ring
        · convert rel_mul_left (t : R) h1 using 1; ring
  rel_mul_right {x y z} := Localization.induction_on₃ x y z fun ⟨a, s⟩ ⟨b, t⟩ ⟨c, u⟩ ↦ by
    simp_rw [Localization.mk_mul, Localization.liftOn₂_mk]
    intro h
    calc  t * u * (a * c)
      _ = (u * c) * (t * a) := by ring
      _ ≤ᵥ (u * c) * (s * b) := rel_mul_left (u * c) h
      _ = s * u * (b * c) := by ring
  rel_mul_cancel {x y z} := Localization.induction_on₃ x y z fun ⟨a, s⟩ ⟨b, t⟩ ⟨c, u⟩ ↦ by
    simp_rw [← Localization.mk_zero 1, Localization.mk_mul, Localization.liftOn₂_mk,
      Submonoid.coe_one, one_mul, mul_zero]
    refine fun hc h ↦ rel_mul_cancel (hS u.2) <| rel_mul_cancel hc ?_
    calc  t * a * u * c
      _ = (t * u) * (a * c) := by ring
      _ ≤ᵥ (s * u) * (b * c) := h
      _ = s * b * u * c := by ring
  not_rel_one_zero := by
    rw [← Localization.mk_zero 1, ← Localization.mk_one, Localization.liftOn₂_mk,
      mul_one, mul_zero]
    exact not_rel_one_zero

lemma rel_localization {a : R} {s : S} {b : R} {t : S} :
    letI : ValuativeRel (Localization S) := .localization hS
    Localization.mk a s ≤ᵥ Localization.mk b t ↔ t * a ≤ᵥ s * b :=
  Iff.rfl

lemma equiv_localization {a : R} {s : S} {b : R} {t : S} :
    letI : ValuativeRel (Localization S) := .localization hS
    Localization.mk a s ∼ᵥ Localization.mk b t ↔ t * a ∼ᵥ s * b :=
  Iff.rfl

lemma rel_iff_localization {x y : R} :
    letI : ValuativeRel (Localization S) := .localization hS
    x ≤ᵥ y ↔ algebraMap R (Localization S) x ≤ᵥ algebraMap R (Localization S) y := by
  simp [← Localization.mk_one_eq_algebraMap, rel_localization]

lemma supp_localization :
    letI : ValuativeRel (Localization S) := .localization hS
    supp (Localization S) = Ideal.map (algebraMap R (Localization S)) (supp R) := by
  let _ : ValuativeRel (Localization S) := .localization hS
  refine le_antisymm ?_ ?_
  · intro x
    refine Localization.induction_on x fun ⟨a, s⟩ has ↦ ?_
    simp_rw [supp_def, ← Localization.mk_zero 1, rel_localization hS, mul_zero,
      Submonoid.coe_one, one_mul] at has
    convert Ideal.mul_mem_right (Localization.mk 1 s) _ <|
      (supp R).mem_map_of_mem (algebraMap R (Localization S)) has
    simp [← Localization.mk_one_eq_algebraMap, Localization.mk_mul]
  · refine Ideal.map_le_iff_le_comap.mpr fun x ↦ ?_
    simpa using (rel_iff_localization (x := x) (y := 0) hS).mp

instance : ValuativeRel (Localization (posSubmonoid R)) := localization le_rfl

instance : Ideal.IsMaximal (supp (Localization (posSubmonoid R))) := by
  rw [supp_localization le_rfl, Localization.AtPrime.map_eq_maximalIdeal]
  infer_instance

instance : ValuativeExtension R (Localization (posSubmonoid R)) :=
  ⟨fun _ _ ↦ rel_iff_localization le_rfl |>.symm⟩

end Localization

section ValueGroupWithZero

variable (R) in
def ValueGroupWithZero : Type _ := ValueQuotient (Localization (posSubmonoid R))

instance : LinearOrderedCommGroupWithZero (ValueGroupWithZero R) :=
  ValueQuotient.instLinearOrderedCommGroupWithZero

/-- Construct an element of the value group-with-zero from an element `r : R` and
  `y : posSubmonoid R`. This should be thought of as `v r / v y`. -/
protected
def ValueGroupWithZero.mk (x : R) (y : posSubmonoid R) : ValueGroupWithZero R :=
  Quotient.mk _ <| Localization.mk x y

protected
theorem ValueGroupWithZero.sound {x y : R} {t s : posSubmonoid R}
    (h : s * x ∼ᵥ t * y) :
    ValueGroupWithZero.mk x t = ValueGroupWithZero.mk y s :=
  Quotient.sound h

protected
theorem ValueGroupWithZero.exact {x y : R} {t s : posSubmonoid R}
    (h : ValueGroupWithZero.mk x t = ValueGroupWithZero.mk y s) :
    s * x ∼ᵥ t * y :=
  Quotient.exact h

protected
theorem ValueGroupWithZero.ind {motive : ValueGroupWithZero R → Prop} (mk : ∀ x y, motive (.mk x y))
    (t : ValueGroupWithZero R) : motive t :=
  Quotient.ind (Localization.ind fun (x, y) ↦ mk x y) t

/-- Lifts a function `R → posSubmonoid R → α` to the value group-with-zero of `R`. -/
protected
def ValueGroupWithZero.lift {α : Sort*} (f : R → posSubmonoid R → α)
    (hf : ∀ (x y : R) (t s : posSubmonoid R), t * x ∼ᵥ s * y → f x s = f y t)
    (t : ValueGroupWithZero R) : α :=
  have {x y : R} {s t : posSubmonoid R} (h : Localization.r _ (x, s) (y, t)) :
      f x s = f y t :=
    have : Localization.mk x s = Localization.mk y t := Localization.mk_eq_mk_iff.mpr h
    hf x y t s (equiv_localization le_rfl |>.mp <| this ▸ equiv_rfl)
  Quotient.liftOn t (fun a ↦ Localization.liftOn a f this)
    fun a b ↦ Localization.induction_on₂ a b fun _ _ ↦ hf _ _ _ _

@[simp] protected
theorem ValueGroupWithZero.lift_mk {α : Sort*} (f : R → posSubmonoid R → α)
    (hf : ∀ (x y : R) (t s : posSubmonoid R), t * x ∼ᵥ s * y → f x s = f y t)
    (x : R) (y : posSubmonoid R) : ValueGroupWithZero.lift f hf (.mk x y) = f x y := rfl

/-- Lifts a function `R → posSubmonoid R → R → posSubmonoid R → α` to
  the value group-with-zero of `R`. -/
protected
def ValueGroupWithZero.lift₂ {α : Sort*} (f : R → posSubmonoid R → R → posSubmonoid R → α)
    (hf : ∀ (x y z w : R) (t s u v : posSubmonoid R),
      t * x ∼ᵥ s * y → u * z ∼ᵥ v * w → f x s z v = f y t w u)
    (t₁ : ValueGroupWithZero R) (t₂ : ValueGroupWithZero R) : α :=
  ValueGroupWithZero.lift
    (fun x s ↦ ValueGroupWithZero.lift (f x s) (fun _ _ _ _ ↦ hf _ _ _ _ _ _ _ _ equiv_rfl) t₂)
    (fun _ _ _ _ H ↦ by
      induction t₂ using ValueGroupWithZero.ind with | mk x y
      exact hf _ _ _ _ _ _ _ _ H equiv_rfl) t₁

@[simp] protected
lemma ValueGroupWithZero.lift₂_mk {α : Sort*} (f : R → posSubmonoid R → R → posSubmonoid R → α)
    (hf : ∀ (x y z w : R) (t s u v : posSubmonoid R),
      t * x ∼ᵥ s * y → u * z ∼ᵥ v * w → f x s z v = f y t w u)
    (x y : R) (z w : posSubmonoid R) :
    ValueGroupWithZero.lift₂ f hf (.mk x z) (.mk y w) = f x z y w := rfl

theorem ValueGroupWithZero.mk_eq_mk {x y : R} {t s : posSubmonoid R} :
    ValueGroupWithZero.mk x t = ValueGroupWithZero.mk y s ↔ s * x ∼ᵥ t * y :=
  Quotient.eq

@[simp]
theorem ValueGroupWithZero.mk_zero (x : posSubmonoid R) : ValueGroupWithZero.mk 0 x = 0 :=
  congr(Quotient.mk _ $(Localization.mk_zero _))

@[simp]
theorem ValueGroupWithZero.mk_eq_zero (x : R) (y : posSubmonoid R) :
    ValueGroupWithZero.mk x y = 0 ↔ x ≤ᵥ 0 := by
  rw [← mk_zero 1, mk_eq_mk, Submonoid.coe_one, one_mul, mul_zero, equiv_zero]

@[simp]
theorem ValueGroupWithZero.mk_self (x : posSubmonoid R) : ValueGroupWithZero.mk (x : R) x = 1 :=
  congr(Quotient.mk _ $(Localization.mk_self _))

@[simp]
theorem ValueGroupWithZero.mk_one_one : ValueGroupWithZero.mk (1 : R) 1 = 1 :=
  ValueGroupWithZero.mk_self 1

@[simp]
theorem ValueGroupWithZero.mk_eq_one (x : R) (y : posSubmonoid R) :
    ValueGroupWithZero.mk x y = 1 ↔ x ∼ᵥ y := by
  simp [← mk_one_one, mk_eq_mk]

theorem ValueGroupWithZero.lift_zero {α : Sort*} (f : R → posSubmonoid R → α)
    (hf : ∀ (x y : R) (t s : posSubmonoid R), t * x ∼ᵥ s * y → f x s = f y t) :
    ValueGroupWithZero.lift f hf 0 = f 0 1 := by
  rw [← mk_zero 1, ValueGroupWithZero.lift_mk]

@[simp]
theorem ValueGroupWithZero.lift_one {α : Sort*} (f : R → posSubmonoid R → α)
    (hf : ∀ (x y : R) (t s : posSubmonoid R), t * x ∼ᵥ s * y → f x s = f y t) :
    ValueGroupWithZero.lift f hf 1 = f 1 1 := by
  rw [← mk_one_one, ValueGroupWithZero.lift_mk]

@[simp]
theorem ValueGroupWithZero.mk_mul_mk (a b : R) (c d : posSubmonoid R) :
    ValueGroupWithZero.mk a c * ValueGroupWithZero.mk b d = ValueGroupWithZero.mk (a * b) (c * d) :=
  congr(Quotient.mk _ $(Localization.mk_mul _ _ _ _))

theorem ValueGroupWithZero.lift_mul {α : Type*} [Mul α] (f : R → posSubmonoid R → α)
    (hf : ∀ (x y : R) (t s : posSubmonoid R), t * x ∼ᵥ s * y → f x s = f y t)
    (hdist : ∀ (a b r s), f (a * b) (r * s) = f a r * f b s)
    (a b : ValueGroupWithZero R) :
    ValueGroupWithZero.lift f hf (a * b) =
      ValueGroupWithZero.lift f hf a * ValueGroupWithZero.lift f hf b := by
  induction a using ValueGroupWithZero.ind
  induction b using ValueGroupWithZero.ind
  simpa using hdist _ _ _ _

@[simp]
theorem ValueGroupWithZero.mk_le_mk (x y : R) (t s : posSubmonoid R) :
    ValueGroupWithZero.mk x t ≤ ValueGroupWithZero.mk y s ↔ s * x ≤ᵥ t * y :=
  Iff.rfl

@[simp]
theorem ValueGroupWithZero.mk_lt_mk (x y : R) (t s : posSubmonoid R) :
    ValueGroupWithZero.mk x t < ValueGroupWithZero.mk y s ↔
      s * x ≤ᵥ t * y ∧ ¬ t * y ≤ᵥ s * x :=
  Iff.rfl

theorem ValueGroupWithZero.bot_eq_zero : (⊥ : ValueGroupWithZero R) = 0 := rfl

@[simp]
theorem ValueGroupWithZero.inv_mk (x : R) (y : posSubmonoid R) (hx : ¬x ≤ᵥ 0) :
    (ValueGroupWithZero.mk x y)⁻¹ = ValueGroupWithZero.mk (y : R) ⟨x, hx⟩ :=
  inv_eq_of_mul_eq_one_left <| by simp [mul_comm x]

variable (R) in
def valuation : Valuation R (ValueGroupWithZero R) :=
  preValuation (Localization (posSubmonoid R)) |>.comap (algebraMap R _)

lemma valuation_eq_mk {x : R} : valuation R x = ValueGroupWithZero.mk x 1 := rfl

instance : (valuation R).Compatible where
  rel_iff_le _ _ := by simp [valuation_eq_mk]

@[simp]
lemma ValueGroupWithZero.lift_valuation {α : Sort*} (f : R → posSubmonoid R → α)
    (hf : ∀ (x y : R) (t s : posSubmonoid R), t * x ∼ᵥ s * y → f x s = f y t)
    (x : R) :
    ValueGroupWithZero.lift f hf (valuation R x) = f x 1 :=
  rfl

lemma ValueGroupWithZero.mk_eq_valuation_div {x : R} {y : posSubmonoid R} :
    ValueGroupWithZero.mk x y = valuation R x / valuation R y := by
  have : valuation R y ≠ 0 := by
    rw [Ne, valuation_eq_mk, ValueGroupWithZero.mk_eq_zero]
    exact y.2
  rw [eq_div_iff this, valuation_eq_mk, valuation_eq_mk, ValueGroupWithZero.mk_mul_mk,
    ValueGroupWithZero.mk_eq_mk, Submonoid.coe_one, one_mul, mul_one, mul_comm x]
  exact equiv_rfl

lemma valuation_eq_preValuation {x : R} : valuation R x = preValuation _ (algebraMap R _ x) := rfl

lemma valuation_surjective (γ : ValueGroupWithZero R) :
    ∃ (a : R) (b : posSubmonoid R), valuation _ a / valuation _ (b : R) = γ := by
  induction γ using ValueGroupWithZero.ind with | mk x y
  use x, y
  rw [ValueGroupWithZero.mk_eq_valuation_div]

end ValueGroupWithZero

open NNReal in variable (R) in
/-- An auxiliary structure used to define `IsRankOne`. -/
structure RankLeOneStruct where
  /-- The embedding of the value group-with-zero into the nonnegative reals. -/
  emb : ValueGroupWithZero R →*₀ ℝ≥0
  strictMono : StrictMono emb

variable (R) in
/-- We say that a ring with a valuative relation is of rank one if
there exists a strictly monotone embedding of the "canonical" value group-with-zero into
the nonnegative reals, and the image of this embedding contains some element different
from `0` and `1`. -/
class IsRankLeOne where
  nonempty : Nonempty (RankLeOneStruct R)

variable (R) in
/-- We say that a valuative relation on a ring is *nontrivial* if the
  value group-with-zero is nontrivial, meaning that it has an element
  which is different from 0 and 1. -/
class IsNontrivial where
  condition : ∃ γ : ValueGroupWithZero R, γ ≠ 0 ∧ γ ≠ 1

lemma isNontrivial_iff_nontrivial_units :
    IsNontrivial R ↔ Nontrivial (ValueGroupWithZero R)ˣ := by
  constructor
  · rintro ⟨γ, hγ, hγ'⟩
    refine ⟨Units.mk0 _ hγ, 1, ?_⟩
    simp [← Units.val_eq_one, hγ']
  · rintro ⟨r, s, h⟩
    rcases eq_or_ne r 1 with rfl | hr
    · exact ⟨s.val, by simp, by simpa using h.symm⟩
    · exact ⟨r.val, by simp, by simpa using hr⟩

lemma isNontrivial_iff_isNontrivial {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    {v : Valuation R Γ} [hv : v.Compatible] :
    IsNontrivial R ↔ v.IsNontrivial := by
  rw [ValuativeRel.isEquiv v (valuation R) |>.isNontrivial_iff]
  constructor
  · rintro ⟨r, hr, hr'⟩
    induction r using ValueGroupWithZero.ind with | mk r s
    rw [ValueGroupWithZero.mk_eq_valuation_div] at hr hr'
    by_cases hs : valuation R s = 1
    · rw [hs, div_one] at hr hr'
      exact ⟨r, hr, hr'⟩
    · refine ⟨s, fun H ↦ ?_, hs⟩
      rw [H, div_zero] at hr
      contradiction
  · rintro ⟨r, hr, hr'⟩
    exact ⟨valuation R r, hr, hr'⟩

variable (R) in
/-- A ring with a valuative relation is discrete if its value group-with-zero
has a maximal element `< 1`. -/
class IsDiscrete where
  has_maximal_element :
    ∃ γ : ValueGroupWithZero R, γ < 1 ∧ (∀ δ : ValueGroupWithZero R, δ < 1 → δ ≤ γ)

end ValuativeRel

open Topology ValuativeRel in
/-- We say that a topology on `R` is valuative if the neighborhoods of `0` in `R`
are determined by the relation `· ≤ᵥ ·`. -/
class ValuativeTopology (R : Type*) [CommRing R] [ValuativeRel R] [TopologicalSpace R] where
  mem_nhds_iff : ∀ s : Set R, s ∈ 𝓝 (0 : R) ↔
    ∃ γ : (ValueGroupWithZero R)ˣ, { x | valuation _ x < γ } ⊆ s

namespace ValuativeExtension

open ValuativeRel

variable {A B : Type*} [CommRing A] [CommRing B]
  [ValuativeRel A] [ValuativeRel B] [Algebra A B]
  [ValuativeExtension A B]

variable (A B) in
/-- The morphism of `posSubmonoid`s associated to an algebra map.
This is used in constructing `ValuativeExtension.mapValueGroupWithZero`. -/
@[simps]
def mapPosSubmonoid : posSubmonoid A →* posSubmonoid B where
  toFun := fun ⟨a,ha⟩ => ⟨algebraMap _ _ a,
    by simpa only [posSubmonoid_def, ← (algebraMap A B).map_zero, rel_iff_rel] using ha⟩
  map_one' := by simp
  map_mul' := by simp

variable (A B) in
/-- The map on value groups-with-zero associated to the structure morphism of an algebra. -/
def mapValueGroupWithZero : ValueGroupWithZero A →*₀ ValueGroupWithZero B where
  toFun := ValueGroupWithZero.lift
    (fun a u => ValueGroupWithZero.mk (algebraMap _ _ a) (mapPosSubmonoid _ _ u)) <| by
      intro x y s t h
      apply ValueGroupWithZero.sound
      simpa only [mapPosSubmonoid_apply_coe, ← (algebraMap A B).map_mul, equiv_iff_equiv]
  map_zero' := by
    simp [ValueGroupWithZero.lift_zero]
  map_one' := by
    simp [ValueGroupWithZero.lift_one]
  map_mul' x y := by
    apply x.ind; apply y.ind
    intro x s y t
    simp

@[simp]
lemma mapValueGroupWithZero_valuation (a : A) :
    mapValueGroupWithZero A B (valuation _ a) = valuation _ (algebraMap _ _ a) := by
  apply ValueGroupWithZero.sound
  simp

end ValuativeExtension
