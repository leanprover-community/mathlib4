/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Divisibility.Prod
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Order.GroupWithZero.Associated
public import Mathlib.Algebra.Order.Monoid.Associated
public import Mathlib.Algebra.Ring.Divisibility.Basic
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.WithBot

/-!
# Order isomorphisms between associates

We construct order isomorphisms between the associates of some basic monoids:

* `MulEquiv.associatesOrderIso`: a multiplicative equivalence `M ≃* N` induces an order isomorphism
  `Associates M ≃o Associates N`.
* `Associates.prodOrderIso`: `Associates (M × N) ≃o Associates M × Associates N`.
* `Associates.unitsOrderIso`: the associates of a group form a subsingleton.
* `Associates.multiplicativeOrderIso`: `Associates (Multiplicative A) ≃o A` for a canonically
  ordered additive monoid `A`.
* `Associates.withZeroOrderIso`: `Associates (WithZero M) ≃o WithTop (Associates M)`.
-/

@[expose] public section

namespace Associates

attribute [local instance] Associated.setoid

section CommMonoid
variable {M N : Type*} [CommMonoid M] [CommMonoid N]

lemma associated_prod_iff {a b : M × N} :
    Associated a b ↔ Associated a.1 b.1 ∧ Associated a.2 b.2 := by
  refine ⟨fun h ↦ ⟨h.map (MonoidHom.fst M N), h.map (MonoidHom.snd M N)⟩, ?_⟩
  rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
  exact ⟨MulEquiv.prodUnits.symm (u, v), Prod.ext hu hv⟩

/-- The associates of a product of monoids are the product of the associates. -/
noncomputable def prodOrderIso : Associates (M × N) ≃o Associates M × Associates N :=
  OrderIso.ofBijective (fun a ↦ (map (MonoidHom.fst M N) a, map (MonoidHom.snd M N) a))
    ⟨fun a b ↦ by
      obtain ⟨a, rfl⟩ := mk_surjective a
      obtain ⟨b, rfl⟩ := mk_surjective b
      simp only [map_mk, mk_eq_mk_iff_associated, Prod.mk.injEq]
      exact fun h ↦ associated_prod_iff.2 h,
    by
      rintro ⟨a, b⟩
      obtain ⟨a, rfl⟩ := mk_surjective a
      obtain ⟨b, rfl⟩ := mk_surjective b
      exact ⟨Associates.mk (a, b), by simp⟩⟩
    (by
      simp only [forall_associated, map_mk, mk_le_mk_iff_dvd, Prod.mk_le_mk]
      exact fun a b ↦ by simp [prod_dvd_iff])

@[simp] lemma prodOrderIso_mk (a : M) (b : N) :
    prodOrderIso (Associates.mk (a, b)) = (Associates.mk a, Associates.mk b) := rfl

end CommMonoid

section Group
variable {G : Type*} [Group G]

/-- The associates of a group are trivial. -/
instance : Unique (Associates G) where
  default := 1
  uniq := forall_associated.2 fun _ ↦ mk_eq_one.2 <| Group.isUnit _

end Group

section Multiplicative
variable {A : Type*} [AddCommMonoid A] [LE A] [Subsingleton (AddUnits A)]

omit [Subsingleton (AddUnits A)] in
lemma ofAdd_dvd_ofAdd (le_iff : ∀ a b : A, a ≤ b ↔ ∃ c, b = a + c) {a b : A} :
    Multiplicative.ofAdd a ∣ Multiplicative.ofAdd b ↔ a ≤ b := by
  rw [le_iff]
  exact ⟨fun ⟨c, hc⟩ ↦ ⟨Multiplicative.toAdd c, hc⟩, fun ⟨c, hc⟩ ↦ ⟨Multiplicative.ofAdd c, hc⟩⟩

instance : Subsingleton (Multiplicative A)ˣ :=
  subsingleton_of_forall_eq 1 fun u ↦ by
    have : (⟨Multiplicative.toAdd u.val, Multiplicative.toAdd u.inv, congrArg Multiplicative.toAdd
      u.val_inv, congrArg Multiplicative.toAdd u.inv_val⟩ : AddUnits A) = 0 :=
      Subsingleton.elim _ _
    exact Units.ext (congrArg (·.val) this)

/-- The associates of `Multiplicative A` are order isomorphic to `A`, when `A` has no nontrivial
additive units and `≤` is divisibility. -/
noncomputable def multiplicativeOrderIso (le_iff : ∀ a b : A, a ≤ b ↔ ∃ c, b = a + c) :
    Associates (Multiplicative A) ≃o A :=
  (OrderIso.ofBijective (fun a : A ↦ Associates.mk (Multiplicative.ofAdd a))
    ⟨fun a b h ↦ by
      obtain ⟨u, hu⟩ := mk_eq_mk_iff_associated.1 h
      obtain rfl : u = 1 := Subsingleton.elim (α := Units (Multiplicative A)) _ _
      simpa using hu,
    fun x ↦ by
      obtain ⟨x, rfl⟩ := mk_surjective x
      exact ⟨Multiplicative.toAdd x, rfl⟩⟩
    (fun a b ↦ by simp [mk_le_mk_iff_dvd, ofAdd_dvd_ofAdd le_iff])).symm

end Multiplicative

section WithZero
variable {M : Type*} [CommMonoid M]

/-- The associates of `WithZero M` are `WithTop` of the associates of `M`. -/
noncomputable def withZeroOrderIso : Associates (WithZero M) ≃o WithTop (Associates M) where
  toFun := Quotient.lift
    (WithZero.recZeroCoe (⊤ : WithTop (Associates M)) fun a ↦ (Associates.mk a : Associates M))
    fun a b h ↦ by
      induction a using WithZero.recZeroCoe <;> induction b using WithZero.recZeroCoe
      · rfl
      · exact absurd ((associated_zero_iff_eq_zero _).1 h.symm) WithZero.coe_ne_zero
      · exact absurd ((associated_zero_iff_eq_zero _).1 h) WithZero.coe_ne_zero
      · exact congrArg (WithTop.some : Associates M → _)
          (mk_eq_mk_iff_associated.2 (WithZero.associated_coe_iff.1 h))
  invFun := WithTop.recTopCoe (0 : Associates (WithZero M))
    fun a ↦ map (WithZero.coeMonoidHom (α := M)) a
  left_inv := forall_associated.2 fun z ↦ by
    induction z using WithZero.recZeroCoe with
    | zero => rfl
    | coe a => rfl
  right_inv x := by
    induction x using WithTop.recTopCoe with
    | top => rfl
    | coe a =>
      obtain ⟨a, rfl⟩ := mk_surjective a
      rfl
  map_rel_iff' {x y} := by
    obtain ⟨x, rfl⟩ := mk_surjective x
    obtain ⟨y, rfl⟩ := mk_surjective y
    induction x using WithZero.recZeroCoe <;> induction y using WithZero.recZeroCoe
    · exact iff_of_true le_rfl le_rfl
    · rename_i b
      change (⊤ : WithTop (Associates M)) ≤ ((Associates.mk b : Associates M) : WithTop _) ↔
        Associates.mk (0 : WithZero M) ≤ Associates.mk (b : WithZero M)
      refine iff_of_false (WithTop.not_top_le_coe _) fun h ↦ ?_
      exact WithZero.coe_ne_zero (zero_dvd_iff.1 (mk_le_mk_iff_dvd.1 h))
    · rename_i a
      change ((Associates.mk a : Associates M) : WithTop _) ≤ (⊤ : WithTop (Associates M)) ↔
        Associates.mk (a : WithZero M) ≤ Associates.mk (0 : WithZero M)
      exact iff_of_true le_top (mk_le_mk_iff_dvd.2 (dvd_zero _))
    · rename_i a b
      change ((Associates.mk a : Associates M) : WithTop (Associates M)) ≤
        ((Associates.mk b : Associates M) : WithTop (Associates M)) ↔
        Associates.mk (a : WithZero M) ≤ Associates.mk (b : WithZero M)
      simp [mk_le_mk_iff_dvd]

end WithZero

end Associates
