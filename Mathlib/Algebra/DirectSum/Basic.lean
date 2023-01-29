/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

! This file was ported from Lean 3 source module algebra.direct_sum.basic
! leanprover-community/mathlib commit f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Dfinsupp.Basic
import Mathbin.GroupTheory.Submonoid.Operations

/-!
# Direct sum

This file defines the direct sum of abelian groups, indexed by a discrete type.

## Notation

`⨁ i, β i` is the n-ary direct sum `direct_sum`.
This notation is in the `direct_sum` locale, accessible after `open_locale direct_sum`.

## References

* https://en.wikipedia.org/wiki/Direct_sum
-/


open BigOperators

universe u v w u₁

variable (ι : Type v) [dec_ι : DecidableEq ι] (β : ι → Type w)

/-- `direct_sum β` is the direct sum of a family of additive commutative monoids `β i`.

Note: `open_locale direct_sum` will enable the notation `⨁ i, β i` for `direct_sum β`. -/
def DirectSum [∀ i, AddCommMonoid (β i)] : Type _ :=
  Π₀ i, β i deriving AddCommMonoid, Inhabited
#align direct_sum DirectSum

instance [∀ i, AddCommMonoid (β i)] : CoeFun (DirectSum ι β) fun _ => ∀ i : ι, β i :=
  Dfinsupp.hasCoeToFun

-- mathport name: direct_sum
scoped[DirectSum] notation3"⨁ "(...)", "r:(scoped f => DirectSum _ f) => r

namespace DirectSum

variable {ι}

section AddCommGroup

variable [∀ i, AddCommGroup (β i)]

instance : AddCommGroup (DirectSum ι β) :=
  Dfinsupp.addCommGroup

variable {β}

@[simp]
theorem sub_apply (g₁ g₂ : ⨁ i, β i) (i : ι) : (g₁ - g₂) i = g₁ i - g₂ i :=
  rfl
#align direct_sum.sub_apply DirectSum.sub_apply

end AddCommGroup

variable [∀ i, AddCommMonoid (β i)]

@[simp]
theorem zero_apply (i : ι) : (0 : ⨁ i, β i) i = 0 :=
  rfl
#align direct_sum.zero_apply DirectSum.zero_apply

variable {β}

@[simp]
theorem add_apply (g₁ g₂ : ⨁ i, β i) (i : ι) : (g₁ + g₂) i = g₁ i + g₂ i :=
  rfl
#align direct_sum.add_apply DirectSum.add_apply

variable (β)

include dec_ι

/-- `mk β s x` is the element of `⨁ i, β i` that is zero outside `s`
and has coefficient `x i` for `i` in `s`. -/
def mk (s : Finset ι) : (∀ i : (↑s : Set ι), β i.1) →+ ⨁ i, β i
    where
  toFun := Dfinsupp.mk s
  map_add' _ _ := Dfinsupp.mk_add
  map_zero' := Dfinsupp.mk_zero
#align direct_sum.mk DirectSum.mk

/-- `of i` is the natural inclusion map from `β i` to `⨁ i, β i`. -/
def of (i : ι) : β i →+ ⨁ i, β i :=
  Dfinsupp.singleAddHom β i
#align direct_sum.of DirectSum.of

@[simp]
theorem of_eq_same (i : ι) (x : β i) : (of _ i x) i = x :=
  Dfinsupp.single_eq_same
#align direct_sum.of_eq_same DirectSum.of_eq_same

theorem of_eq_of_ne (i j : ι) (x : β i) (h : i ≠ j) : (of _ i x) j = 0 :=
  Dfinsupp.single_eq_of_ne h
#align direct_sum.of_eq_of_ne DirectSum.of_eq_of_ne

@[simp]
theorem support_zero [∀ (i : ι) (x : β i), Decidable (x ≠ 0)] : (0 : ⨁ i, β i).support = ∅ :=
  Dfinsupp.support_zero
#align direct_sum.support_zero DirectSum.support_zero

@[simp]
theorem support_of [∀ (i : ι) (x : β i), Decidable (x ≠ 0)] (i : ι) (x : β i) (h : x ≠ 0) :
    (of _ i x).support = {i} :=
  Dfinsupp.support_single_ne_zero h
#align direct_sum.support_of DirectSum.support_of

theorem support_of_subset [∀ (i : ι) (x : β i), Decidable (x ≠ 0)] {i : ι} {b : β i} :
    (of _ i b).support ⊆ {i} :=
  Dfinsupp.support_single_subset
#align direct_sum.support_of_subset DirectSum.support_of_subset

theorem sum_support_of [∀ (i : ι) (x : β i), Decidable (x ≠ 0)] (x : ⨁ i, β i) :
    (∑ i in x.support, of β i (x i)) = x :=
  Dfinsupp.sum_single
#align direct_sum.sum_support_of DirectSum.sum_support_of

variable {β}

theorem mk_injective (s : Finset ι) : Function.Injective (mk β s) :=
  Dfinsupp.mk_injective s
#align direct_sum.mk_injective DirectSum.mk_injective

theorem of_injective (i : ι) : Function.Injective (of β i) :=
  Dfinsupp.single_injective
#align direct_sum.of_injective DirectSum.of_injective

@[elab_as_elim]
protected theorem induction_on {C : (⨁ i, β i) → Prop} (x : ⨁ i, β i) (H_zero : C 0)
    (H_basic : ∀ (i : ι) (x : β i), C (of β i x)) (H_plus : ∀ x y, C x → C y → C (x + y)) : C x :=
  by
  apply Dfinsupp.induction x H_zero
  intro i b f h1 h2 ih
  solve_by_elim
#align direct_sum.induction_on DirectSum.induction_on

/-- If two additive homomorphisms from `⨁ i, β i` are equal on each `of β i y`,
then they are equal. -/
theorem add_hom_ext {γ : Type _} [AddMonoid γ] ⦃f g : (⨁ i, β i) →+ γ⦄
    (H : ∀ (i : ι) (y : β i), f (of _ i y) = g (of _ i y)) : f = g :=
  Dfinsupp.add_hom_ext H
#align direct_sum.add_hom_ext DirectSum.add_hom_ext

/-- If two additive homomorphisms from `⨁ i, β i` are equal on each `of β i y`,
then they are equal.

See note [partially-applied ext lemmas]. -/
@[ext]
theorem add_hom_ext' {γ : Type _} [AddMonoid γ] ⦃f g : (⨁ i, β i) →+ γ⦄
    (H : ∀ i : ι, f.comp (of _ i) = g.comp (of _ i)) : f = g :=
  add_hom_ext fun i => AddMonoidHom.congr_fun <| H i
#align direct_sum.add_hom_ext' DirectSum.add_hom_ext'

variable {γ : Type u₁} [AddCommMonoid γ]

section ToAddMonoid

variable (φ : ∀ i, β i →+ γ) (ψ : (⨁ i, β i) →+ γ)

/-- `to_add_monoid φ` is the natural homomorphism from `⨁ i, β i` to `γ`
induced by a family `φ` of homomorphisms `β i → γ`. -/
def toAddMonoid : (⨁ i, β i) →+ γ :=
  Dfinsupp.liftAddHom φ
#align direct_sum.to_add_monoid DirectSum.toAddMonoid

@[simp]
theorem toAddMonoid_of (i) (x : β i) : toAddMonoid φ (of β i x) = φ i x :=
  Dfinsupp.liftAddHom_apply_single φ i x
#align direct_sum.to_add_monoid_of DirectSum.toAddMonoid_of

theorem toAddMonoid.unique (f : ⨁ i, β i) : ψ f = toAddMonoid (fun i => ψ.comp (of β i)) f :=
  by
  congr
  ext
  simp [to_add_monoid, of]
#align direct_sum.to_add_monoid.unique DirectSum.toAddMonoid.unique

end ToAddMonoid

section FromAddMonoid

/-- `from_add_monoid φ` is the natural homomorphism from `γ` to `⨁ i, β i`
induced by a family `φ` of homomorphisms `γ → β i`.

Note that this is not an isomorphism. Not every homomorphism `γ →+ ⨁ i, β i` arises in this way. -/
def fromAddMonoid : (⨁ i, γ →+ β i) →+ γ →+ ⨁ i, β i :=
  to_add_monoid fun i => AddMonoidHom.compHom (of β i)
#align direct_sum.from_add_monoid DirectSum.fromAddMonoid

@[simp]
theorem fromAddMonoid_of (i : ι) (f : γ →+ β i) : fromAddMonoid (of _ i f) = (of _ i).comp f :=
  by
  rw [from_add_monoid, to_add_monoid_of]
  rfl
#align direct_sum.from_add_monoid_of DirectSum.fromAddMonoid_of

theorem fromAddMonoid_of_apply (i : ι) (f : γ →+ β i) (x : γ) :
    fromAddMonoid (of _ i f) x = of _ i (f x) := by rw [from_add_monoid_of, AddMonoidHom.coe_comp]
#align direct_sum.from_add_monoid_of_apply DirectSum.fromAddMonoid_of_apply

end FromAddMonoid

variable (β)

-- TODO: generalize this to remove the assumption `S ⊆ T`.
/-- `set_to_set β S T h` is the natural homomorphism `⨁ (i : S), β i → ⨁ (i : T), β i`,
where `h : S ⊆ T`. -/
def setToSet (S T : Set ι) (H : S ⊆ T) : (⨁ i : S, β i) →+ ⨁ i : T, β i :=
  to_add_monoid fun i => of (fun i : Subtype T => β i) ⟨↑i, H i.Prop⟩
#align direct_sum.set_to_set DirectSum.setToSet

variable {β}

omit dec_ι

instance unique [∀ i, Subsingleton (β i)] : Unique (⨁ i, β i) :=
  Dfinsupp.unique
#align direct_sum.unique DirectSum.unique

/-- A direct sum over an empty type is trivial. -/
instance uniqueOfIsEmpty [IsEmpty ι] : Unique (⨁ i, β i) :=
  Dfinsupp.uniqueOfIsEmpty
#align direct_sum.unique_of_is_empty DirectSum.uniqueOfIsEmpty

/-- The natural equivalence between `⨁ _ : ι, M` and `M` when `unique ι`. -/
protected def id (M : Type v) (ι : Type _ := PUnit) [AddCommMonoid M] [Unique ι] :
    (⨁ _ : ι, M) ≃+ M :=
  {
    DirectSum.toAddMonoid fun _ =>
      AddMonoidHom.id
        M with
    toFun := DirectSum.toAddMonoid fun _ => AddMonoidHom.id M
    invFun := of (fun _ => M) default
    left_inv := fun x =>
      DirectSum.induction_on x (by rw [AddMonoidHom.map_zero, AddMonoidHom.map_zero])
        (fun p x => by rw [Unique.default_eq p, to_add_monoid_of] <;> rfl) fun x y ihx ihy => by
        rw [AddMonoidHom.map_add, AddMonoidHom.map_add, ihx, ihy]
    right_inv := fun x => toAddMonoid_of _ _ _ }
#align direct_sum.id DirectSum.id

section CongrLeft

variable {κ : Type _}

/-- Reindexing terms of a direct sum.-/
def equivCongrLeft (h : ι ≃ κ) : (⨁ i, β i) ≃+ ⨁ k, β (h.symm k) :=
  { Dfinsupp.equivCongrLeft h with map_add' := Dfinsupp.comapDomain'_add _ _ }
#align direct_sum.equiv_congr_left DirectSum.equivCongrLeft

@[simp]
theorem equivCongrLeft_apply (h : ι ≃ κ) (f : ⨁ i, β i) (k : κ) :
    equivCongrLeft h f k = f (h.symm k) :=
  Dfinsupp.comapDomain'_apply _ _ _ _
#align direct_sum.equiv_congr_left_apply DirectSum.equivCongrLeft_apply

end CongrLeft

section Option

variable {α : Option ι → Type w} [∀ i, AddCommMonoid (α i)]

include dec_ι

/-- Isomorphism obtained by separating the term of index `none` of a direct sum over `option ι`.-/
@[simps]
noncomputable def addEquivProdDirectSum : (⨁ i, α i) ≃+ α none × ⨁ i, α (some i) :=
  { Dfinsupp.equivProdDfinsupp with map_add' := Dfinsupp.equivProdDfinsupp_add }
#align direct_sum.add_equiv_prod_direct_sum DirectSum.addEquivProdDirectSum

end Option

section Sigma

variable {α : ι → Type u} {δ : ∀ i, α i → Type w} [∀ i j, AddCommMonoid (δ i j)]

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/-- The natural map between `⨁ (i : Σ i, α i), δ i.1 i.2` and `⨁ i (j : α i), δ i j`.-/
noncomputable def sigmaCurry : (⨁ i : Σi, _, δ i.1 i.2) →+ ⨁ (i) (j), δ i j
    where
  toFun := @Dfinsupp.sigmaCurry _ _ δ _
  map_zero' := Dfinsupp.sigmaCurry_zero
  map_add' f g := @Dfinsupp.sigmaCurry_add _ _ δ _ f g
#align direct_sum.sigma_curry DirectSum.sigmaCurry

@[simp]
theorem sigmaCurry_apply (f : ⨁ i : Σi, _, δ i.1 i.2) (i : ι) (j : α i) :
    sigmaCurry f i j = f ⟨i, j⟩ :=
  @Dfinsupp.sigmaCurry_apply _ _ δ _ f i j
#align direct_sum.sigma_curry_apply DirectSum.sigmaCurry_apply

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/-- The natural map between `⨁ i (j : α i), δ i j` and `Π₀ (i : Σ i, α i), δ i.1 i.2`, inverse of
`curry`.-/
def sigmaUncurry [∀ i, DecidableEq (α i)] [∀ i j, DecidableEq (δ i j)] :
    (⨁ (i) (j), δ i j) →+ ⨁ i : Σi, _, δ i.1 i.2
    where
  toFun := Dfinsupp.sigmaUncurry
  map_zero' := Dfinsupp.sigmaUncurry_zero
  map_add' := Dfinsupp.sigmaUncurry_add
#align direct_sum.sigma_uncurry DirectSum.sigmaUncurry

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem sigmaUncurry_apply [∀ i, DecidableEq (α i)] [∀ i j, DecidableEq (δ i j)]
    (f : ⨁ (i) (j), δ i j) (i : ι) (j : α i) : sigmaUncurry f ⟨i, j⟩ = f i j :=
  Dfinsupp.sigmaUncurry_apply f i j
#align direct_sum.sigma_uncurry_apply DirectSum.sigmaUncurry_apply

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/-- The natural map between `⨁ (i : Σ i, α i), δ i.1 i.2` and `⨁ i (j : α i), δ i j`.-/
noncomputable def sigmaCurryEquiv [∀ i, DecidableEq (α i)] [∀ i j, DecidableEq (δ i j)] :
    (⨁ i : Σi, _, δ i.1 i.2) ≃+ ⨁ (i) (j), δ i j :=
  { sigmaCurry, Dfinsupp.sigmaCurryEquiv with }
#align direct_sum.sigma_curry_equiv DirectSum.sigmaCurryEquiv

end Sigma

/-- The canonical embedding from `⨁ i, A i` to `M` where `A` is a collection of `add_submonoid M`
indexed by `ι`.

When `S = submodule _ M`, this is available as a `linear_map`, `direct_sum.coe_linear_map`. -/
protected def coeAddMonoidHom {M S : Type _} [DecidableEq ι] [AddCommMonoid M] [SetLike S M]
    [AddSubmonoidClass S M] (A : ι → S) : (⨁ i, A i) →+ M :=
  toAddMonoid fun i => AddSubmonoidClass.Subtype (A i)
#align direct_sum.coe_add_monoid_hom DirectSum.coeAddMonoidHom

@[simp]
theorem coeAddMonoidHom_of {M S : Type _} [DecidableEq ι] [AddCommMonoid M] [SetLike S M]
    [AddSubmonoidClass S M] (A : ι → S) (i : ι) (x : A i) :
    DirectSum.coeAddMonoidHom A (of (fun i => A i) i x) = x :=
  toAddMonoid_of _ _ _
#align direct_sum.coe_add_monoid_hom_of DirectSum.coeAddMonoidHom_of

theorem coe_of_apply {M S : Type _} [DecidableEq ι] [AddCommMonoid M] [SetLike S M]
    [AddSubmonoidClass S M] {A : ι → S} (i j : ι) (x : A i) :
    (of _ i x j : M) = if i = j then x else 0 :=
  by
  obtain rfl | h := Decidable.eq_or_ne i j
  · rw [DirectSum.of_eq_same, if_pos rfl]
  · rw [DirectSum.of_eq_of_ne _ _ _ _ h, if_neg h, ZeroMemClass.coe_zero]
#align direct_sum.coe_of_apply DirectSum.coe_of_apply

/-- The `direct_sum` formed by a collection of additive submonoids (or subgroups, or submodules) of
`M` is said to be internal if the canonical map `(⨁ i, A i) →+ M` is bijective.

For the alternate statement in terms of independence and spanning, see
`direct_sum.subgroup_is_internal_iff_independent_and_supr_eq_top` and
`direct_sum.is_internal_submodule_iff_independent_and_supr_eq_top`. -/
def IsInternal {M S : Type _} [DecidableEq ι] [AddCommMonoid M] [SetLike S M]
    [AddSubmonoidClass S M] (A : ι → S) : Prop :=
  Function.Bijective (DirectSum.coeAddMonoidHom A)
#align direct_sum.is_internal DirectSum.IsInternal

theorem IsInternal.addSubmonoid_supᵢ_eq_top {M : Type _} [DecidableEq ι] [AddCommMonoid M]
    (A : ι → AddSubmonoid M) (h : IsInternal A) : supᵢ A = ⊤ :=
  by
  rw [AddSubmonoid.supᵢ_eq_mrange_dfinsupp_sumAddHom, AddMonoidHom.mrange_top_iff_surjective]
  exact Function.Bijective.surjective h
#align direct_sum.is_internal.add_submonoid_supr_eq_top DirectSum.IsInternal.addSubmonoid_supᵢ_eq_top

end DirectSum

