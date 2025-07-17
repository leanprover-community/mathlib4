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

@[inherit_doc ValuativeRel.rel]
notation:50 (name := valuativeRel) a:50 " ≤ᵥ " b:51 => binrel% ValuativeRel.rel a b

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
def supp : Ideal R where
  carrier := { x | x ≤ᵥ 0 }
  add_mem' := rel_add
  zero_mem' := rel_rfl
  smul_mem' c _ h := by simpa using rel_mul_left c h

@[simp]
lemma mem_supp {x : R} : x ∈ supp R ↔ x ≤ᵥ 0 := Iff.rfl

instance : Ideal.IsPrime (ValuativeRel.supp R) where
  ne_top' := Ideal.ne_top_iff_one _ |>.mpr not_rel_one_zero
  mem_or_mem' hxy := or_iff_not_imp_left.mpr fun hx ↦ rel_mul_cancel hx <|
    by rwa [zero_mul, mul_comm]

instance (priority := low) {k : Type*} [Field k] [ValuativeRel k] : Ideal.IsMaximal (supp k) where
  out := isCoatom_iff_eq_bot.mpr <| (eq_bot_or_eq_top _).resolve_right <|
    Ideal.IsPrime.ne_top inferInstance

variable (R) in
/-- The submonoid of elements `x : R` whose valuation is positive. -/
def posSubmonoid : Submonoid R where
  carrier := { x | ¬ x ≤ᵥ 0}
  __ := (supp R).primeCompl

section Localization

variable {S : Submonoid R} (hS : S ≤ (supp R).primeCompl)

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

lemma localization_def {a : R} {s : S} {b : R} {t : S} :
    letI : ValuativeRel (Localization S) := .localization hS
    Localization.mk a s ≤ᵥ Localization.mk b t ↔ t * a ≤ᵥ s * b :=
  Iff.rfl

lemma rel_iff_localization {x y : R} :
    letI : ValuativeRel (Localization S) := .localization hS
    x ≤ᵥ y ↔ algebraMap R (Localization S) x ≤ᵥ algebraMap R (Localization S) y := by
  simp [← Localization.mk_one_eq_algebraMap, localization_def]

lemma supp_localization :
    letI : ValuativeRel (Localization S) := .localization hS
    supp (Localization S) = Ideal.map (algebraMap R (Localization S)) (supp R) := by
  let _ : ValuativeRel (Localization S) := .localization hS
  refine le_antisymm ?_ ?_
  · intro x
    refine Localization.induction_on x fun ⟨a, s⟩ has ↦ ?_
    simp_rw [mem_supp, ← Localization.mk_zero 1, localization_def hS, mul_zero,
      Submonoid.coe_one, one_mul] at has
    convert Ideal.mul_mem_right (Localization.mk 1 s) _ <|
      (supp R).mem_map_of_mem (algebraMap R (Localization S)) has
    simp [← Localization.mk_one_eq_algebraMap, Localization.mk_mul]
  · refine Ideal.map_le_iff_le_comap.mpr fun x ↦ ?_
    simpa using (rel_iff_localization (x := x) (y := 0) hS).mp

instance : ValuativeRel (Localization (supp R).primeCompl) := localization le_rfl

instance : Ideal.IsMaximal (supp (Localization (supp R).primeCompl)) := by
  rw [supp_localization le_rfl, Localization.AtPrime.map_eq_maximalIdeal]
  infer_instance

end Localization

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

section Valuation

variable (R) in
def ValueGroupWithZero : Type _ := ValueQuotient (Localization (supp R).primeCompl)

instance : LinearOrderedCommGroupWithZero (ValueGroupWithZero R) :=
  ValueQuotient.instLinearOrderedCommGroupWithZero

variable (R) in
def valuation : Valuation R (ValueGroupWithZero R) :=
  preValuation (Localization (supp R).primeCompl) |>.comap (algebraMap R _)

instance : (valuation R).Compatible where
  rel_iff_le _ _ := by
    rw [rel_iff_localization le_rfl]
    rfl

end Valuation

@[simp]
lemma ValueGroupWithZero.lift_valuation {α : Sort*} (f : R → posSubmonoid R → α)
    (hf : ∀ (x y : R) (t s : posSubmonoid R), x * t ≤ᵥ y * s → y * s ≤ᵥ x * t → f x s = f y t)
    (x : R) :
    ValueGroupWithZero.lift f hf (valuation R x) = f x 1 :=
  rfl

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

variable (R) in
/-- The support of the valuation on `R`. -/
def supp : Ideal R where
  carrier := { x | x ≤ᵥ 0 }
  add_mem' ha hb := rel_add ha hb
  zero_mem' := rel_refl _
  smul_mem' x _ h := by simpa using rel_mul_left _ h

@[simp]
lemma supp_def (x : R) : x ∈ supp R ↔ x ≤ᵥ 0 := Iff.refl _

lemma supp_eq_valuation_supp : supp R = (valuation R).supp := by
  ext x
  constructor
  · intro h
    simp only [supp_def, Valuation.mem_supp_iff] at h ⊢
    apply ValueGroupWithZero.sound
    · simpa
    · simp
  · intro h
    have := ValueGroupWithZero.exact h
    simpa using this.left

instance : (supp R).IsPrime := by
  rw [supp_eq_valuation_supp]
  infer_instance

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

lemma isNontrivial_iff_isNontrivial :
    IsNontrivial R ↔ (valuation R).IsNontrivial := by
  constructor
  · rintro ⟨r, hr, hr'⟩
    induction r using ValueGroupWithZero.ind with | mk r s
    by_cases hs : valuation R s = 1
    · refine ⟨r, ?_, ?_⟩
      · simpa [valuation] using hr
      · simp only [ne_eq, ValueGroupWithZero.mk_eq_one, not_and, valuation, Valuation.coe_mk,
          MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, OneMemClass.coe_one] at hr' hs ⊢
        contrapose! hr'
        exact hr'.imp hs.right.trans' hs.left.trans
    · refine ⟨s, ?_, hs⟩
      simp [valuation, ← posSubmonoid_def]
  · rintro ⟨r, hr, hr'⟩
    exact ⟨valuation R r, hr, hr'⟩

variable (R) in
/-- A ring with a valuative relation is discrete if its value group-with-zero
has a maximal element `< 1`. -/
class IsDiscrete where
  has_maximal_element :
    ∃ γ : ValueGroupWithZero R, γ < 1 ∧ (∀ δ : ValueGroupWithZero R, δ < 1 → δ ≤ γ)

lemma valuation_surjective (γ : ValueGroupWithZero R) :
    ∃ (a : R) (b : posSubmonoid R), valuation _ a / valuation _ (b : R) = γ := by
  induction γ using ValueGroupWithZero.ind with | mk a b
  use a, b
  simp [valuation, div_eq_mul_inv, ValueGroupWithZero.inv_mk (b : R) 1 b.prop]

end ValuativeRel

open Topology ValuativeRel in
/-- We say that a topology on `R` is valuative if the neighborhoods of `0` in `R`
are determined by the relation `· ≤ᵥ ·`. -/
class ValuativeTopology (R : Type*) [CommRing R] [ValuativeRel R] [TopologicalSpace R] where
  mem_nhds_iff : ∀ s : Set R, s ∈ 𝓝 (0 : R) ↔
    ∃ γ : (ValueGroupWithZero R)ˣ, { x | valuation _ x < γ } ⊆ s

namespace ValuativeRel

variable
  {R Γ : Type*} [CommRing R] [ValuativeRel R] [TopologicalSpace R]
  [LinearOrderedCommGroupWithZero Γ]
  (v : Valuation R Γ) [v.Compatible]

end ValuativeRel

/-- If `B` is an `A` algebra and both `A` and `B` have valuative relations,
we say that `B|A` is a valuative extension if the valuative relation on `A` is
induced by the one on `B`. -/
class ValuativeExtension
    (A B : Type*)
    [CommRing A] [CommRing B]
    [ValuativeRel A] [ValuativeRel B]
    [Algebra A B] where
  rel_iff_rel (a b : A) : algebraMap A B a ≤ᵥ algebraMap A B b ↔ a ≤ᵥ b

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
      intro x y s t h1 h2
      apply ValueGroupWithZero.sound <;>
        simpa only [mapPosSubmonoid_apply_coe, ← (algebraMap A B).map_mul, rel_iff_rel]
  map_zero' := by
    apply ValueGroupWithZero.sound <;> simp
  map_one' := by
    apply ValueGroupWithZero.sound <;> simp
  map_mul' x y := by
    apply x.ind; apply y.ind
    intro x s y t
    simp

@[simp]
lemma mapValueGroupWithZero_valuation (a : A) :
    mapValueGroupWithZero A B (valuation _ a) = valuation _ (algebraMap _ _ a) := by
  apply ValueGroupWithZero.sound <;> simp

end ValuativeExtension
