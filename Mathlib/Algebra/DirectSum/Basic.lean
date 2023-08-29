/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Data.DFinsupp.Basic
import Mathlib.GroupTheory.Submonoid.Operations

#align_import algebra.direct_sum.basic from "leanprover-community/mathlib"@"f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c"

/-!
# Direct sum

This file defines the direct sum of abelian groups, indexed by a discrete type.

## Notation

`⨁ i, β i` is the n-ary direct sum `DirectSum`.
This notation is in the `DirectSum` locale, accessible after `open DirectSum`.

## References

* https://en.wikipedia.org/wiki/Direct_sum
-/

open BigOperators

universe u v w u₁

variable (ι : Type v) [dec_ι : DecidableEq ι] (β : ι → Type w)

/-- `DirectSum β` is the direct sum of a family of additive commutative monoids `β i`.

Note: `open DirectSum` will enable the notation `⨁ i, β i` for `DirectSum β`. -/
def DirectSum [∀ i, AddCommMonoid (β i)] : Type _ :=
  -- Porting note: Failed to synthesize
  -- Π₀ i, β i deriving AddCommMonoid, Inhabited
  -- See https://github.com/leanprover-community/mathlib4/issues/5020
  Π₀ i, β i
#align direct_sum DirectSum

-- Porting note: Added inhabited instance manually
instance [∀ i, AddCommMonoid (β i)] : Inhabited (DirectSum ι β) :=
  inferInstanceAs (Inhabited (Π₀ i, β i))

-- Porting note: Added addCommMonoid instance manually
instance [∀ i, AddCommMonoid (β i)] : AddCommMonoid (DirectSum ι β) :=
  inferInstanceAs (AddCommMonoid (Π₀ i, β i))

instance [∀ i, AddCommMonoid (β i)] : FunLike (DirectSum ι β) _ fun i : ι => β i :=
  inferInstanceAs (FunLike (Π₀ i, β i) _ _)

instance [∀ i, AddCommMonoid (β i)] : CoeFun (DirectSum ι β) fun _ => ∀ i : ι, β i :=
  inferInstanceAs (CoeFun (Π₀ i, β i) fun _ => ∀ i : ι, β i)

-- Porting note: scoped does not work with notation3; TODO rewrite as lean4 notation?
-- scoped[DirectSum]
/-- `⨁ i, f i` is notation for `DirectSum _ f` and equals the direct sum of `fun i ↦ f i`.
Taking the direct sum over multiple arguments is possible, e.g. `⨁ (i) (j), f i j`. -/
notation3 "⨁ "(...)", "r:(scoped f => DirectSum _ f) => r

-- Porting note: The below recreates some of the lean3 notation, not fully yet
-- section
-- open Std.ExtendedBinder
-- syntax (name := bigdirectsum) "⨁ " extBinders ", " term : term
-- macro_rules (kind := bigdirectsum)
--   | `(⨁ $_:ident, $y:ident → $z:ident) => `(DirectSum _ (fun $y ↦ $z))
--   | `(⨁ $x:ident, $p) => `(DirectSum _ (fun $x ↦ $p))
--   | `(⨁ $_:ident : $t:ident, $p) => `(DirectSum _ (fun $t ↦ $p))
--   | `(⨁ ($x:ident) ($y:ident), $p) => `(DirectSum _ (fun $x ↦ fun $y ↦ $p))
-- end

namespace DirectSum

variable {ι}

section AddCommGroup

variable [∀ i, AddCommGroup (β i)]

instance : AddCommGroup (DirectSum ι β) :=
  inferInstanceAs (AddCommGroup (Π₀ i, β i))
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

-- Porting note: commented out
-- include dec_ι

/-- `mk β s x` is the element of `⨁ i, β i` that is zero outside `s`
and has coefficient `x i` for `i` in `s`. -/
def mk (s : Finset ι) : (∀ i : (↑s : Set ι), β i.1) →+ ⨁ i, β i
    where
  toFun := DFinsupp.mk s
  map_add' _ _ := DFinsupp.mk_add
  map_zero' := DFinsupp.mk_zero
#align direct_sum.mk DirectSum.mk

/-- `of i` is the natural inclusion map from `β i` to `⨁ i, β i`. -/
def of (i : ι) : β i →+ ⨁ i, β i :=
  DFinsupp.singleAddHom β i
#align direct_sum.of DirectSum.of

@[simp]
theorem of_eq_same (i : ι) (x : β i) : (of _ i x) i = x :=
  DFinsupp.single_eq_same
#align direct_sum.of_eq_same DirectSum.of_eq_same

theorem of_eq_of_ne (i j : ι) (x : β i) (h : i ≠ j) : (of _ i x) j = 0 :=
  DFinsupp.single_eq_of_ne h
#align direct_sum.of_eq_of_ne DirectSum.of_eq_of_ne

@[simp]
theorem support_zero [∀ (i : ι) (x : β i), Decidable (x ≠ 0)] : (0 : ⨁ i, β i).support = ∅ :=
  DFinsupp.support_zero
#align direct_sum.support_zero DirectSum.support_zero

@[simp]
theorem support_of [∀ (i : ι) (x : β i), Decidable (x ≠ 0)] (i : ι) (x : β i) (h : x ≠ 0) :
    (of _ i x).support = {i} :=
  DFinsupp.support_single_ne_zero h
#align direct_sum.support_of DirectSum.support_of

theorem support_of_subset [∀ (i : ι) (x : β i), Decidable (x ≠ 0)] {i : ι} {b : β i} :
    (of _ i b).support ⊆ {i} :=
  DFinsupp.support_single_subset
#align direct_sum.support_of_subset DirectSum.support_of_subset

theorem sum_support_of [∀ (i : ι) (x : β i), Decidable (x ≠ 0)] (x : ⨁ i, β i) :
    (∑ i in x.support, of β i (x i)) = x :=
  DFinsupp.sum_single
#align direct_sum.sum_support_of DirectSum.sum_support_of

variable {β}

theorem mk_injective (s : Finset ι) : Function.Injective (mk β s) :=
  DFinsupp.mk_injective s
#align direct_sum.mk_injective DirectSum.mk_injective

theorem of_injective (i : ι) : Function.Injective (of β i) :=
  DFinsupp.single_injective
#align direct_sum.of_injective DirectSum.of_injective

@[elab_as_elim]
protected theorem induction_on {C : (⨁ i, β i) → Prop} (x : ⨁ i, β i) (H_zero : C 0)
    (H_basic : ∀ (i : ι) (x : β i), C (of β i x))
    (H_plus : ∀ x y, C x → C y → C (x + y)) : C x := by
  apply DFinsupp.induction x H_zero
  -- ⊢ ∀ (i : ι) (b : (fun i => β i) i) (f : Π₀ (i : ι), (fun i => β i) i), ↑f i =  …
  intro i b f h1 h2 ih
  -- ⊢ C (DFinsupp.single i b + f)
  solve_by_elim
  -- 🎉 no goals
#align direct_sum.induction_on DirectSum.induction_on

/-- If two additive homomorphisms from `⨁ i, β i` are equal on each `of β i y`,
then they are equal. -/
theorem addHom_ext {γ : Type*} [AddMonoid γ] ⦃f g : (⨁ i, β i) →+ γ⦄
    (H : ∀ (i : ι) (y : β i), f (of _ i y) = g (of _ i y)) : f = g :=
  DFinsupp.addHom_ext H
#align direct_sum.add_hom_ext DirectSum.addHom_ext

/-- If two additive homomorphisms from `⨁ i, β i` are equal on each `of β i y`,
then they are equal.

See note [partially-applied ext lemmas]. -/
@[ext high]
theorem addHom_ext' {γ : Type*} [AddMonoid γ] ⦃f g : (⨁ i, β i) →+ γ⦄
    (H : ∀ i : ι, f.comp (of _ i) = g.comp (of _ i)) : f = g :=
  addHom_ext fun i => FunLike.congr_fun <| H i
#align direct_sum.add_hom_ext' DirectSum.addHom_ext'

variable {γ : Type u₁} [AddCommMonoid γ]

section ToAddMonoid

variable (φ : ∀ i, β i →+ γ) (ψ : (⨁ i, β i) →+ γ)

-- Porting note: The elaborator is struggling with `liftAddHom`. Passing it `β` explicitly helps.
-- This applies to roughly the remainder of the file.

/-- `toAddMonoid φ` is the natural homomorphism from `⨁ i, β i` to `γ`
induced by a family `φ` of homomorphisms `β i → γ`. -/
def toAddMonoid : (⨁ i, β i) →+ γ :=
  DFinsupp.liftAddHom (β := β) φ
#align direct_sum.to_add_monoid DirectSum.toAddMonoid

@[simp]
theorem toAddMonoid_of (i) (x : β i) : toAddMonoid φ (of β i x) = φ i x :=
  DFinsupp.liftAddHom_apply_single φ i x
#align direct_sum.to_add_monoid_of DirectSum.toAddMonoid_of

theorem toAddMonoid.unique (f : ⨁ i, β i) : ψ f = toAddMonoid (fun i => ψ.comp (of β i)) f := by
  congr
  -- ⊢ ψ = toAddMonoid fun i => AddMonoidHom.comp ψ (of β i)
  -- Porting note: ext applies addHom_ext' here, which isn't what we want.
  apply DFinsupp.addHom_ext'
  -- ⊢ ∀ (x : ι), AddMonoidHom.comp ψ (DFinsupp.singleAddHom (fun i => (fun i => β  …
  simp [toAddMonoid, of]
  -- 🎉 no goals
#align direct_sum.to_add_monoid.unique DirectSum.toAddMonoid.unique

end ToAddMonoid

section FromAddMonoid

/-- `fromAddMonoid φ` is the natural homomorphism from `γ` to `⨁ i, β i`
induced by a family `φ` of homomorphisms `γ → β i`.

Note that this is not an isomorphism. Not every homomorphism `γ →+ ⨁ i, β i` arises in this way. -/
def fromAddMonoid : (⨁ i, γ →+ β i) →+ γ →+ ⨁ i, β i :=
  toAddMonoid fun i => AddMonoidHom.compHom (of β i)
#align direct_sum.from_add_monoid DirectSum.fromAddMonoid

@[simp]
theorem fromAddMonoid_of (i : ι) (f : γ →+ β i) : fromAddMonoid (of _ i f) = (of _ i).comp f := by
  rw [fromAddMonoid, toAddMonoid_of]
  -- ⊢ ↑(↑AddMonoidHom.compHom (of β i)) f = AddMonoidHom.comp (of β i) f
  rfl
  -- 🎉 no goals
#align direct_sum.from_add_monoid_of DirectSum.fromAddMonoid_of

theorem fromAddMonoid_of_apply (i : ι) (f : γ →+ β i) (x : γ) :
    fromAddMonoid (of _ i f) x = of _ i (f x) := by
      rw [fromAddMonoid_of, AddMonoidHom.coe_comp, Function.comp]
      -- 🎉 no goals
#align direct_sum.from_add_monoid_of_apply DirectSum.fromAddMonoid_of_apply

end FromAddMonoid

variable (β)

-- TODO: generalize this to remove the assumption `S ⊆ T`.
/-- `setToSet β S T h` is the natural homomorphism `⨁ (i : S), β i → ⨁ (i : T), β i`,
where `h : S ⊆ T`. -/
def setToSet (S T : Set ι) (H : S ⊆ T) : (⨁ i : S, β i) →+ ⨁ i : T, β i :=
  toAddMonoid fun i => of (fun i : Subtype T => β i) ⟨↑i, H i.2⟩
#align direct_sum.set_to_set DirectSum.setToSet

variable {β}

-- Porting note: commented out
-- omit dec_ι

instance unique [∀ i, Subsingleton (β i)] : Unique (⨁ i, β i) :=
  DFinsupp.unique
#align direct_sum.unique DirectSum.unique

/-- A direct sum over an empty type is trivial. -/
instance uniqueOfIsEmpty [IsEmpty ι] : Unique (⨁ i, β i) :=
  DFinsupp.uniqueOfIsEmpty
#align direct_sum.unique_of_is_empty DirectSum.uniqueOfIsEmpty

/-- The natural equivalence between `⨁ _ : ι, M` and `M` when `Unique ι`. -/
protected def id (M : Type v) (ι : Type* := PUnit) [AddCommMonoid M] [Unique ι] :
    (⨁ _ : ι, M) ≃+ M :=
  {
    DirectSum.toAddMonoid fun _ =>
      AddMonoidHom.id
        M with
    toFun := DirectSum.toAddMonoid fun _ => AddMonoidHom.id M
    invFun := of (fun _ => M) default
    left_inv := fun x =>
      DirectSum.induction_on x (by rw [AddMonoidHom.map_zero, AddMonoidHom.map_zero])
                                   -- 🎉 no goals
        (fun p x => by rw [Unique.default_eq p, toAddMonoid_of]; rfl) fun x y ihx ihy => by
                       -- ⊢ ↑(of (fun x => M) p) (↑(AddMonoidHom.id M) x) = ↑(of (fun i => M) p) x
                                                                 -- 🎉 no goals
        rw [AddMonoidHom.map_add, AddMonoidHom.map_add, ihx, ihy]
        -- 🎉 no goals
    right_inv := fun x => toAddMonoid_of _ _ _ }
#align direct_sum.id DirectSum.id

section CongrLeft

variable {κ : Type*}

/-- Reindexing terms of a direct sum.-/
def equivCongrLeft (h : ι ≃ κ) : (⨁ i, β i) ≃+ ⨁ k, β (h.symm k) :=
  { DFinsupp.equivCongrLeft h with map_add' := DFinsupp.comapDomain'_add _ h.right_inv}
#align direct_sum.equiv_congr_left DirectSum.equivCongrLeft

@[simp]
theorem equivCongrLeft_apply (h : ι ≃ κ) (f : ⨁ i, β i) (k : κ) :
    equivCongrLeft h f k = f (h.symm k) := by
  exact DFinsupp.comapDomain'_apply _ h.right_inv _ _
  -- 🎉 no goals
#align direct_sum.equiv_congr_left_apply DirectSum.equivCongrLeft_apply

end CongrLeft

section Option

variable {α : Option ι → Type w} [∀ i, AddCommMonoid (α i)]

-- Porting note: commented out
-- include dec_ι

/-- Isomorphism obtained by separating the term of index `none` of a direct sum over `Option ι`.-/
@[simps]
noncomputable def addEquivProdDirectSum : (⨁ i, α i) ≃+ α none × ⨁ i, α (some i) :=
  { DFinsupp.equivProdDFinsupp with map_add' := DFinsupp.equivProdDFinsupp_add }
#align direct_sum.add_equiv_prod_direct_sum DirectSum.addEquivProdDirectSum

end Option

section Sigma

variable {α : ι → Type u} {δ : ∀ i, α i → Type w} [∀ i j, AddCommMonoid (δ i j)]

/-- The natural map between `⨁ (i : Σ i, α i), δ i.1 i.2` and `⨁ i (j : α i), δ i j`.-/
def sigmaCurry : (⨁ i : Σ _i, _, δ i.1 i.2) →+ ⨁ (i) (j), δ i j
    where
  toFun := DFinsupp.sigmaCurry (δ := δ)
  map_zero' := DFinsupp.sigmaCurry_zero
  map_add' f g := DFinsupp.sigmaCurry_add f g
#align direct_sum.sigma_curry DirectSum.sigmaCurry

@[simp]
theorem sigmaCurry_apply (f : ⨁ i : Σ _i, _, δ i.1 i.2) (i : ι) (j : α i) :
    sigmaCurry f i j = f ⟨i, j⟩ :=
  DFinsupp.sigmaCurry_apply (δ := δ) _ i j
#align direct_sum.sigma_curry_apply DirectSum.sigmaCurry_apply

/-- The natural map between `⨁ i (j : α i), δ i j` and `Π₀ (i : Σ i, α i), δ i.1 i.2`, inverse of
`curry`.-/
def sigmaUncurry [∀ i, DecidableEq (α i)] [∀ i j, DecidableEq (δ i j)] :
    (⨁ (i) (j), δ i j) →+ ⨁ i : Σ _i, _, δ i.1 i.2
    where
  toFun := DFinsupp.sigmaUncurry
  map_zero' := DFinsupp.sigmaUncurry_zero
  map_add' := DFinsupp.sigmaUncurry_add
#align direct_sum.sigma_uncurry DirectSum.sigmaUncurry

@[simp]
theorem sigmaUncurry_apply [∀ i, DecidableEq (α i)] [∀ i j, DecidableEq (δ i j)]
    (f : ⨁ (i) (j), δ i j) (i : ι) (j : α i) : sigmaUncurry f ⟨i, j⟩ = f i j :=
  DFinsupp.sigmaUncurry_apply f i j
#align direct_sum.sigma_uncurry_apply DirectSum.sigmaUncurry_apply

/-- The natural map between `⨁ (i : Σ i, α i), δ i.1 i.2` and `⨁ i (j : α i), δ i j`.-/
def sigmaCurryEquiv [∀ i, DecidableEq (α i)] [∀ i j, DecidableEq (δ i j)] :
    (⨁ i : Σ _i, _, δ i.1 i.2) ≃+ ⨁ (i) (j), δ i j :=
  { sigmaCurry, DFinsupp.sigmaCurryEquiv with }
#align direct_sum.sigma_curry_equiv DirectSum.sigmaCurryEquiv

end Sigma

/-- The canonical embedding from `⨁ i, A i` to `M` where `A` is a collection of `AddSubmonoid M`
indexed by `ι`.

When `S = Submodule _ M`, this is available as a `LinearMap`, `DirectSum.coe_linearMap`. -/
protected def coeAddMonoidHom {M S : Type*} [DecidableEq ι] [AddCommMonoid M] [SetLike S M]
    [AddSubmonoidClass S M] (A : ι → S) : (⨁ i, A i) →+ M :=
  toAddMonoid fun i => AddSubmonoidClass.subtype (A i)
#align direct_sum.coe_add_monoid_hom DirectSum.coeAddMonoidHom

@[simp]
theorem coeAddMonoidHom_of {M S : Type*} [DecidableEq ι] [AddCommMonoid M] [SetLike S M]
    [AddSubmonoidClass S M] (A : ι → S) (i : ι) (x : A i) :
    DirectSum.coeAddMonoidHom A (of (fun i => A i) i x) = x :=
  toAddMonoid_of _ _ _
#align direct_sum.coe_add_monoid_hom_of DirectSum.coeAddMonoidHom_of

theorem coe_of_apply {M S : Type*} [DecidableEq ι] [AddCommMonoid M] [SetLike S M]
    [AddSubmonoidClass S M] {A : ι → S} (i j : ι) (x : A i) :
    (of (fun i ↦ {x // x ∈ A i}) i x j : M) = if i = j then x else 0 := by
  obtain rfl | h := Decidable.eq_or_ne i j
  -- ⊢ ↑(↑(↑(of (fun i => { x // x ∈ A i }) i) x) i) = ↑(if i = i then x else 0)
  · rw [DirectSum.of_eq_same, if_pos rfl]
    -- 🎉 no goals
  · rw [DirectSum.of_eq_of_ne _ _ _ _ h, if_neg h, ZeroMemClass.coe_zero, ZeroMemClass.coe_zero]
    -- 🎉 no goals
#align direct_sum.coe_of_apply DirectSum.coe_of_apply

/-- The `DirectSum` formed by a collection of additive submonoids (or subgroups, or submodules) of
`M` is said to be internal if the canonical map `(⨁ i, A i) →+ M` is bijective.

For the alternate statement in terms of independence and spanning, see
`DirectSum.subgroup_isInternal_iff_independent_and_supr_eq_top` and
`DirectSum.isInternalSubmodule_iff_independent_and_supr_eq_top`. -/
def IsInternal {M S : Type*} [DecidableEq ι] [AddCommMonoid M] [SetLike S M]
    [AddSubmonoidClass S M] (A : ι → S) : Prop :=
  Function.Bijective (DirectSum.coeAddMonoidHom A)
#align direct_sum.is_internal DirectSum.IsInternal

theorem IsInternal.addSubmonoid_iSup_eq_top {M : Type*} [DecidableEq ι] [AddCommMonoid M]
    (A : ι → AddSubmonoid M) (h : IsInternal A) : iSup A = ⊤ := by
  rw [AddSubmonoid.iSup_eq_mrange_dfinsupp_sumAddHom, AddMonoidHom.mrange_top_iff_surjective]
  -- ⊢ Function.Surjective ↑(DFinsupp.sumAddHom fun i => AddSubmonoid.subtype (A i))
  exact Function.Bijective.surjective h
  -- 🎉 no goals
#align direct_sum.is_internal.add_submonoid_supr_eq_top DirectSum.IsInternal.addSubmonoid_iSup_eq_top

end DirectSum
