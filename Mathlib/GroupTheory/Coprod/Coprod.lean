/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, David Wärn, Joachim Breitner
-/
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.GroupTheory.Congruence
import Mathlib.GroupTheory.Subgroup.Basic

#align_import group_theory.free_product from "leanprover-community/mathlib"@"9114ddffa023340c9ec86965e00cdd6fe26fcdf6"

/-!
# The coproduct (a.k.a. the free product) of groups or monoids

Given a pair, `M` and `N` of monoids,
we define their coproduct (a.k.a. free product) `Monoid.Coprod M N`, or `M ∗ N`.
This file defines binary coproducts, the coproduct of an indexed family
is called `Monoid.CoprodI`

When `M` and `N` are groups, `Monoid.Coprod M N` is also a group
(and the coproduct in the category of groups).

## Main definitions

- `Monoid.Coprod`: the free product, defined as a quotient of a free monoid.
- `Monoid.Coprod.inl {i} : M →* Monoid.Coprod M N`.
- `Monoid.CoprodI.lift : (M →* P) → (N →* P) → (Monoid.CoprodI M →* N)`: the universal property.


## Notation

- `M ∗ N`: The free product of monoids `M` and `N`

## References

[van der Waerden, *Free products of groups*][MR25465]

-/


open Set

variable (M N : Type*) [Monoid M] [Monoid N]

/-- A relation on the free monoid on alphabet `Σ i, M i`,
relating `⟨i, 1⟩` with `1` and `⟨i, x⟩ * ⟨i, y⟩` with `⟨i, x * y⟩`. -/
inductive Monoid.Coprod.Rel : FreeMonoid (M ⊕ N) → FreeMonoid (M ⊕ N) → Prop
  | of_one_left : Monoid.Coprod.Rel (FreeMonoid.of (.inl 1)) 1
  | of_one_right : Monoid.Coprod.Rel (FreeMonoid.of (.inr 1)) 1
  | of_mul_left (x y : M) :
    Monoid.Coprod.Rel (FreeMonoid.of (.inl x) * FreeMonoid.of (.inl y))
      (FreeMonoid.of (.inl (x * y)))
  | of_mul_right (x y : N) :
    Monoid.Coprod.Rel (FreeMonoid.of (.inr x) * FreeMonoid.of (.inr y))
      (FreeMonoid.of (.inr (x * y)))

/-- The free product (categorical coproduct) of a pair of monoids. -/
def Monoid.Coprod : Type _ := (conGen (Monoid.Coprod.Rel M N)).Quotient

--Porting note: could not de derived
instance : Monoid (Monoid.Coprod M N) :=
  by delta Monoid.Coprod; infer_instance

instance : Inhabited (Monoid.Coprod M N) :=
  ⟨1⟩

namespace Monoid.Coprod

variable {M N}

-- Precedence set to the same as that of `⊕`
@[inherit_doc]
scoped infixr:30 " ∗ " => Monoid.Coprod

/-- The left inclusion into the free product. -/
def inl : M →* M ∗ N where
  toFun x := Con.mk' _ (FreeMonoid.of <| .inl x)
  map_one' := (Con.eq _).mpr (ConGen.Rel.of _ _ Coprod.Rel.of_one_left)
  map_mul' x y := Eq.symm <| (Con.eq _).mpr (ConGen.Rel.of _ _ (Coprod.Rel.of_mul_left x y))

/-- The right inclusion into the free product. -/
def inr : N →* M ∗ N where
  toFun x := Con.mk' _ (FreeMonoid.of <| .inr x)
  map_one' := (Con.eq _).mpr (ConGen.Rel.of _ _ Coprod.Rel.of_one_right)
  map_mul' x y := Eq.symm <| (Con.eq _).mpr (ConGen.Rel.of _ _ (Coprod.Rel.of_mul_right x y))

theorem inl_apply (m : M) : (inl m : M ∗ N) = Con.mk' _ (FreeMonoid.of <| .inl m) :=
  rfl

theorem inr_apply (n : N) : (inr n : M ∗ N) = Con.mk' _ (FreeMonoid.of <| .inr n) :=
  rfl

variable {P : Type*} [Monoid P]

/-- See note [partially-applied ext lemmas]. -/
@[ext 1100]
theorem ext_hom (f g : M ∗ N →* P)
  (hl : f.comp (inl : M →* _) = g.comp inl)
  (hr : f.comp (inr : N →* _) = g.comp inr) : f = g :=
  (MonoidHom.cancel_right Con.mk'_surjective).mp <|
    FreeMonoid.hom_eq fun x => by
      simp only [FunLike.ext_iff] at hl hr
      cases x
      · exact hl _
      · exact hr _

/-- A map out of the free product corresponds to a family of maps out of the summands. This is the
universal property of the free product, characterizing it as a categorical coproduct. -/
def lift (left : M →* P) (right : N →* P) : M ∗ N →* P :=
    Con.lift _ (FreeMonoid.lift (Sum.elim left right)) <|
      Con.conGen_le <| by
        simp_rw [Con.rel_eq_coe, Con.ker_rel]
        intro x y h
        induction h <;> simp

@[simp]
theorem lift_inl (left : M →* P) (right : N →* P) (m : M) :
    lift left right (inl m) = left m := rfl

@[simp]
theorem lift_inr (left : M →* P) (right : N →* P) (n : N) :
    lift left right (inr n) = right n := rfl

@[elab_as_elim]
theorem induction_on {C : M ∗ N → Prop} (m : M ∗ N)
    (h_inl : ∀ (m : M), C (inl m))
    (h_inr : ∀ (n : N), C (inr n))
    (h_mul : ∀ x y, C x → C y → C (x * y)) : C m := by
  let S : Submonoid (M ∗ N) :=
    { carrier := setOf C
      mul_mem' := h_mul _ _
      one_mem' := by simpa using h_inl 1 }
  have : C _ := Subtype.prop (lift (inl.codRestrict S (h_inl)) (inr.codRestrict S (h_inr)) m)
  convert this
  change MonoidHom.id _ m = S.subtype.comp _ m
  congr
  ext
  · rfl
  · rfl

theorem inl_leftInverse :
    Function.LeftInverse (lift (MonoidHom.id _) 1) (inl : M →* M ∗ N) := fun x => by
  simp only [lift_inl, MonoidHom.id_apply]

theorem inr_leftInverse :
    Function.LeftInverse (lift 1 (MonoidHom.id _)) (inr : N →* M ∗ N) := fun x => by
  simp only [lift_inr, MonoidHom.id_apply]

theorem inl_injective : Function.Injective (inl : M →* M ∗ N) :=
  inl_leftInverse.injective

theorem inr_injective : Function.Injective (inr : N →* M ∗ N) :=
  inr_leftInverse.injective

theorem lift_mrange_le (left : M →* P) (right : N →* P) {s : Submonoid P}
    (hleft : MonoidHom.mrange left ≤ s)
    (hright : MonoidHom.mrange right ≤ s) :
    MonoidHom.mrange (lift left right) ≤ s := by
  rintro _ ⟨x, rfl⟩
  induction' x using Coprod.induction_on with i x x y hx hy
  · simp only [lift_inl, SetLike.mem_coe]
    exact hleft (Set.mem_range_self _)
  · simp only [lift_inr, SetLike.mem_coe]
    exact hright (Set.mem_range_self _)
  · simp only [map_mul, SetLike.mem_coe]
    exact s.mul_mem hx hy

theorem mrange_eq_sup (left : M →* P) (right : N →* P) :
    MonoidHom.mrange (lift left right) = MonoidHom.mrange left ⊔ MonoidHom.mrange right := by
  refine le_antisymm (lift_mrange_le left right le_sup_left le_sup_right) ?_
  refine sup_le ?_ ?_
  · rintro _ ⟨x, rfl⟩
    exact ⟨inl x, lift_inl _ _ _⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨inr x, lift_inr _ _ _⟩

section Group

variable (G H : Type*) [Group G] [Group H]

instance : Inv (G ∗ H)
    where inv :=
    MulOpposite.unop ∘
      lift ((inl : G →* _).op.comp (MulEquiv.inv' G).toMonoidHom)
           ((inr : H →* _).op.comp (MulEquiv.inv' H).toMonoidHom)

theorem inv_def (x : G ∗ H) :
    x⁻¹ =
      MulOpposite.unop
      (lift ((inl : G →* G ∗ H).op.comp (MulEquiv.inv' G).toMonoidHom)
           ((inr : H →* G ∗ H).op.comp (MulEquiv.inv' H).toMonoidHom) x) :=
  rfl

instance : Group (G ∗ H) :=
  { toInv := inferInstanceAs (Inv (G ∗ H))
    toMonoid := inferInstanceAs (Monoid (G ∗ H))
    mul_left_inv := by
      intro m
      rw [inv_def]
      induction m using Coprod.induction_on with
      | h_inl m =>
        change inl _⁻¹ * inl _ = 1
        rw [← inl.map_mul, mul_left_inv, inl.map_one]
      | h_inr m =>
        change inr _⁻¹ * inr _ = 1
        rw [← inr.map_mul, mul_left_inv, inr.map_one]
      | h_mul x y ihx ihy =>
        rw [MonoidHom.map_mul, MulOpposite.unop_mul, mul_assoc, ← mul_assoc _ x y, ihx, one_mul,
          ihy] }

variable {G H}

theorem lift_range_le {N} [Group N]
    (left : G →* N) (right : H →* N) {s : Subgroup N}
    (hleft : left.range ≤ s) (hright : right.range ≤ s) :
    (lift left right).range ≤ s := by
  rw [← Subgroup.toSubmonoid_le]
  exact lift_mrange_le left right hleft hright

theorem range_eq_sup {N} [Group N] (left : G →* N) (right : H →* N) :
    (lift left right).range = left.range ⊔ right.range := by
  refine le_antisymm (lift_range_le left right le_sup_left le_sup_right) ?_
  refine sup_le ?_ ?_
  · rintro _ ⟨x, rfl⟩
    exact ⟨inl x, lift_inl _ _ _⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨inr x, lift_inr _ _ _⟩

end Group

end Monoid.Coprod
