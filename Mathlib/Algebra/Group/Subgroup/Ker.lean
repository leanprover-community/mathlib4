/-
Copyright (c) 2020 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Tactic.ApplyFun

/-!
# Kernel and range of group homomorphisms

We define and prove results about the kernel and range of group homomorphisms.

Special thanks goes to Amelia Livingston and Yury Kudryashov for their help and inspiration.

## Main definitions

Notation used here:

- `G N` are `Group`s

- `x` is an element of type `G`

- `f g : N →* G` are group homomorphisms

Definitions in the file:

* `MonoidHom.range f` : the range of the group homomorphism `f` is a subgroup

* `MonoidHom.ker f` : the kernel of a group homomorphism `f` is the subgroup of elements `x : G`
  such that `f x = 1`

* `MonoidHom.eqLocus f g` : given group homomorphisms `f`, `g`, the elements of `G` such that
  `f x = g x` form a subgroup of `G`

## Implementation notes

Subgroup inclusion is denoted `≤` rather than `⊆`, although `∈` is defined as
membership of a subgroup's underlying set.

## Tags
subgroup, subgroups
-/

assert_not_exists OrderedAddCommMonoid Multiset Ring

open Function
open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']
variable {A : Type*} [AddGroup A]

namespace MonoidHom

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

open Subgroup

/-- The range of a monoid homomorphism from a group is a subgroup. -/
@[to_additive /-- The range of an `AddMonoidHom` from an `AddGroup` is an `AddSubgroup`. -/]
def range (f : G →* N) : Subgroup N :=
  Subgroup.copy ((⊤ : Subgroup G).map f) (Set.range f) (by simp)

@[to_additive (attr := simp)]
theorem coe_range (f : G →* N) : (f.range : Set N) = Set.range f :=
  rfl

@[to_additive (attr := simp)]
theorem mem_range {f : G →* N} {y : N} : y ∈ f.range ↔ ∃ x, f x = y :=
  Iff.rfl

@[to_additive]
theorem range_eq_map (f : G →* N) : f.range = (⊤ : Subgroup G).map f := by ext; simp

@[to_additive]
instance range_isMulCommutative {G : Type*} [CommGroup G] {N : Type*} [Group N] (f : G →* N) :
    IsMulCommutative f.range :=
  range_eq_map f ▸ Subgroup.map_isMulCommutative ⊤ f

@[deprecated (since := "2025-04-09")] alias range_isCommutative := range_isMulCommutative
@[deprecated (since := "2025-04-09")] alias _root_.AddMonoidHom.range_isCommutative :=
  _root_.AddMonoidHom.range_isAddCommutative

@[to_additive (attr := simp)]
theorem restrict_range (f : G →* N) : (f.restrict K).range = K.map f := by
  simp_rw [SetLike.ext_iff, mem_range, mem_map, restrict_apply, SetLike.exists,
    exists_prop, forall_const]

/-- The canonical surjective group homomorphism `G →* f(G)` induced by a group
homomorphism `G →* N`. -/
@[to_additive
      /-- The canonical surjective `AddGroup` homomorphism `G →+ f(G)` induced by a group
      homomorphism `G →+ N`. -/]
def rangeRestrict (f : G →* N) : G →* f.range :=
  codRestrict f _ fun x => ⟨x, rfl⟩

@[to_additive (attr := simp)]
theorem coe_rangeRestrict (f : G →* N) (g : G) : (f.rangeRestrict g : N) = f g :=
  rfl

@[to_additive]
theorem coe_comp_rangeRestrict (f : G →* N) :
    ((↑) : f.range → N) ∘ (⇑f.rangeRestrict : G → f.range) = f :=
  rfl

@[to_additive]
theorem subtype_comp_rangeRestrict (f : G →* N) : f.range.subtype.comp f.rangeRestrict = f :=
  ext <| f.coe_rangeRestrict

@[to_additive]
theorem rangeRestrict_surjective (f : G →* N) : Function.Surjective f.rangeRestrict :=
  fun ⟨_, g, rfl⟩ => ⟨g, rfl⟩

@[to_additive (attr := simp)]
lemma rangeRestrict_injective_iff {f : G →* N} : Injective f.rangeRestrict ↔ Injective f := by
  convert Set.injective_codRestrict _

@[to_additive]
theorem map_range (g : N →* P) (f : G →* N) : f.range.map g = (g.comp f).range := by
  rw [range_eq_map, range_eq_map]; exact (⊤ : Subgroup G).map_map g f

@[to_additive]
lemma range_comp (g : N →* P) (f : G →* N) : (g.comp f).range = f.range.map g := (map_range ..).symm

@[to_additive]
theorem range_eq_top {N} [Group N] {f : G →* N} :
    f.range = (⊤ : Subgroup N) ↔ Function.Surjective f :=
  SetLike.ext'_iff.trans <| Iff.trans (by rw [coe_range, coe_top]) Set.range_eq_univ

/-- The range of a surjective monoid homomorphism is the whole of the codomain. -/
@[to_additive (attr := simp)
  /-- The range of a surjective `AddMonoid` homomorphism is the whole of the codomain. -/]
theorem range_eq_top_of_surjective {N} [Group N] (f : G →* N) (hf : Function.Surjective f) :
    f.range = (⊤ : Subgroup N) :=
  range_eq_top.2 hf

@[to_additive (attr := simp)]
theorem range_one : (1 : G →* N).range = ⊥ :=
  SetLike.ext fun x => by simpa using @comm _ (· = ·) _ 1 x

@[to_additive (attr := simp)]
theorem _root_.Subgroup.range_subtype (H : Subgroup G) : H.subtype.range = H :=
  SetLike.coe_injective <| (coe_range _).trans <| Subtype.range_coe

@[to_additive]
alias _root_.Subgroup.subtype_range := Subgroup.range_subtype

@[to_additive (attr := simp)]
theorem _root_.Subgroup.inclusion_range {H K : Subgroup G} (h_le : H ≤ K) :
    (inclusion h_le).range = H.subgroupOf K :=
  Subgroup.ext fun g => Set.ext_iff.mp (Set.range_inclusion h_le) g

@[to_additive]
theorem subgroupOf_range_eq_of_le {G₁ G₂ : Type*} [Group G₁] [Group G₂] {K : Subgroup G₂}
    (f : G₁ →* G₂) (h : f.range ≤ K) :
    f.range.subgroupOf K = (f.codRestrict K fun x => h ⟨x, rfl⟩).range := by
  ext k
  refine exists_congr ?_
  simp [Subtype.ext_iff]

/-- Computable alternative to `MonoidHom.ofInjective`. -/
@[to_additive /-- Computable alternative to `AddMonoidHom.ofInjective`. -/]
def ofLeftInverse {f : G →* N} {g : N →* G} (h : Function.LeftInverse g f) : G ≃* f.range :=
  { f.rangeRestrict with
    toFun := f.rangeRestrict
    invFun := g ∘ f.range.subtype
    left_inv := h
    right_inv := by
      rintro ⟨x, y, rfl⟩
      solve_by_elim }

@[to_additive (attr := simp)]
theorem ofLeftInverse_apply {f : G →* N} {g : N →* G} (h : Function.LeftInverse g f) (x : G) :
    ↑(ofLeftInverse h x) = f x :=
  rfl

@[to_additive (attr := simp)]
theorem ofLeftInverse_symm_apply {f : G →* N} {g : N →* G} (h : Function.LeftInverse g f)
    (x : f.range) : (ofLeftInverse h).symm x = g x :=
  rfl

/-- The range of an injective group homomorphism is isomorphic to its domain. -/
@[to_additive /-- The range of an injective additive group homomorphism is isomorphic to its
domain. -/]
noncomputable def ofInjective {f : G →* N} (hf : Function.Injective f) : G ≃* f.range :=
  MulEquiv.ofBijective (f.codRestrict f.range fun x => ⟨x, rfl⟩)
    ⟨fun _ _ h => hf (Subtype.ext_iff.mp h), by
      rintro ⟨x, y, rfl⟩
      exact ⟨y, rfl⟩⟩

@[to_additive]
theorem ofInjective_apply {f : G →* N} (hf : Function.Injective f) {x : G} :
    ↑(ofInjective hf x) = f x :=
  rfl

@[to_additive (attr := simp)]
theorem apply_ofInjective_symm {f : G →* N} (hf : Function.Injective f) (x : f.range) :
    f ((ofInjective hf).symm x) = x :=
  Subtype.ext_iff.1 <| (ofInjective hf).apply_symm_apply x

@[simp]
theorem coe_toAdditive_range (f : G →* G') :
    (MonoidHom.toAdditive f).range = Subgroup.toAddSubgroup f.range := rfl

@[simp]
theorem coe_toMultiplicative_range {A A' : Type*} [AddGroup A] [AddGroup A'] (f : A →+ A') :
    (AddMonoidHom.toMultiplicative f).range = AddSubgroup.toSubgroup f.range := rfl

section Ker

variable {M : Type*} [MulOneClass M]

/-- The multiplicative kernel of a monoid homomorphism is the subgroup of elements `x : G` such that
`f x = 1` -/
@[to_additive
      /-- The additive kernel of an `AddMonoid` homomorphism is the `AddSubgroup` of elements
      such that `f x = 0` -/]
def ker (f : G →* M) : Subgroup G :=
  { MonoidHom.mker f with
    inv_mem' := fun {x} (hx : f x = 1) =>
      calc
        f x⁻¹ = f x * f x⁻¹ := by rw [hx, one_mul]
        _ = 1 := by rw [← map_mul, mul_inv_cancel, map_one] }

@[to_additive (attr := simp)]
theorem ker_toSubmonoid (f : G →* M) : f.ker.toSubmonoid = MonoidHom.mker f := rfl

@[to_additive (attr := simp)]
theorem mem_ker {f : G →* M} {x : G} : x ∈ f.ker ↔ f x = 1 :=
  Iff.rfl

@[to_additive]
theorem div_mem_ker_iff (f : G →* N) {x y : G} : x / y ∈ ker f ↔ f x = f y := by
  rw [mem_ker, map_div, div_eq_one]

@[to_additive]
theorem coe_ker (f : G →* M) : (f.ker : Set G) = (f : G → M) ⁻¹' {1} :=
  rfl

@[to_additive (attr := simp)]
theorem ker_toHomUnits {M} [Monoid M] (f : G →* M) : f.toHomUnits.ker = f.ker := by
  ext x
  simp [mem_ker, Units.ext_iff]

@[to_additive]
theorem eq_iff (f : G →* M) {x y : G} : f x = f y ↔ y⁻¹ * x ∈ f.ker := by
  constructor <;> intro h
  · rw [mem_ker, map_mul, h, ← map_mul, inv_mul_cancel, map_one]
  · rw [← one_mul x, ← mul_inv_cancel y, mul_assoc, map_mul, mem_ker.1 h, mul_one]

@[to_additive]
instance decidableMemKer [DecidableEq M] (f : G →* M) : DecidablePred (· ∈ f.ker) := fun x =>
  decidable_of_iff (f x = 1) f.mem_ker

@[to_additive]
theorem comap_ker {P : Type*} [MulOneClass P] (g : N →* P) (f : G →* N) :
    g.ker.comap f = (g.comp f).ker :=
  rfl

@[to_additive (attr := simp)]
theorem comap_bot (f : G →* N) : (⊥ : Subgroup N).comap f = f.ker :=
  rfl

@[to_additive (attr := simp)]
theorem ker_restrict (f : G →* N) : (f.restrict K).ker = f.ker.subgroupOf K :=
  rfl

@[to_additive (attr := simp)]
theorem ker_codRestrict {S} [SetLike S N] [SubmonoidClass S N] (f : G →* N) (s : S)
    (h : ∀ x, f x ∈ s) : (f.codRestrict s h).ker = f.ker :=
  SetLike.ext fun _x => Subtype.ext_iff

@[to_additive (attr := simp)]
theorem ker_rangeRestrict (f : G →* N) : ker (rangeRestrict f) = ker f :=
  ker_codRestrict _ _ _

@[to_additive (attr := simp)]
theorem ker_one : (1 : G →* M).ker = ⊤ :=
  SetLike.ext fun _x => eq_self_iff_true _

@[to_additive (attr := simp)]
theorem ker_id : (MonoidHom.id G).ker = ⊥ :=
  rfl

@[to_additive] theorem ker_eq_top_iff {f : G →* M} : f.ker = ⊤ ↔ f = 1 := by
  simp [ker, ← top_le_iff, SetLike.le_def, f.ext_iff]

@[to_additive] theorem range_eq_bot_iff {f : G →* G'} : f.range = ⊥ ↔ f = 1 := by
  rw [← le_bot_iff, f.range_eq_map, map_le_iff_le_comap, top_le_iff, comap_bot, ker_eq_top_iff]

@[to_additive]
theorem ker_eq_bot_iff (f : G →* M) : f.ker = ⊥ ↔ Function.Injective f :=
  ⟨fun h x y hxy => by rwa [eq_iff, h, mem_bot, inv_mul_eq_one, eq_comm] at hxy, fun h =>
    bot_unique fun _ hx => h (hx.trans f.map_one.symm)⟩

@[to_additive (attr := simp)]
theorem _root_.Subgroup.ker_subtype (H : Subgroup G) : H.subtype.ker = ⊥ :=
  H.subtype.ker_eq_bot_iff.mpr Subtype.coe_injective

@[to_additive (attr := simp)]
theorem _root_.Subgroup.ker_inclusion {H K : Subgroup G} (h : H ≤ K) : (inclusion h).ker = ⊥ :=
  (inclusion h).ker_eq_bot_iff.mpr (Set.inclusion_injective h)

@[to_additive ker_prod]
theorem ker_prod {M N : Type*} [MulOneClass M] [MulOneClass N] (f : G →* M) (g : G →* N) :
    (f.prod g).ker = f.ker ⊓ g.ker :=
  SetLike.ext fun _ => Prod.mk_eq_one

@[deprecated (since := "2025-03-11")]
alias _root_.AddMonoidHom.ker_sum := AddMonoidHom.ker_prod

@[to_additive]
theorem range_le_ker_iff (f : G →* G') (g : G' →* G'') : f.range ≤ g.ker ↔ g.comp f = 1 :=
  ⟨fun h => ext fun x => h ⟨x, rfl⟩, by rintro h _ ⟨y, rfl⟩; exact DFunLike.congr_fun h y⟩

@[to_additive]
instance (priority := 100) normal_ker (f : G →* M) : f.ker.Normal :=
  ⟨fun x hx y => by
    rw [mem_ker, map_mul, map_mul, mem_ker.1 hx, mul_one, map_mul_eq_one f (mul_inv_cancel y)]⟩

@[simp]
theorem coe_toAdditive_ker (f : G →* G') :
    (MonoidHom.toAdditive f).ker = Subgroup.toAddSubgroup f.ker := rfl

@[simp]
theorem coe_toMultiplicative_ker {A A' : Type*} [AddGroup A] [AddZeroClass A'] (f : A →+ A') :
    (AddMonoidHom.toMultiplicative f).ker = AddSubgroup.toSubgroup f.ker := rfl

end Ker

section EqLocus

variable {M : Type*} [Monoid M]

/-- The subgroup of elements `x : G` such that `f x = g x` -/
@[to_additive /-- The additive subgroup of elements `x : G` such that `f x = g x` -/]
def eqLocus (f g : G →* M) : Subgroup G :=
  { eqLocusM f g with inv_mem' := eq_on_inv f g }

@[to_additive (attr := simp)]
theorem eqLocus_same (f : G →* N) : f.eqLocus f = ⊤ :=
  SetLike.ext fun _ => eq_self_iff_true _

/-- If two monoid homomorphisms are equal on a set, then they are equal on its subgroup closure. -/
@[to_additive
      /-- If two monoid homomorphisms are equal on a set, then they are equal on its subgroup
      closure. -/]
theorem eqOn_closure {f g : G →* M} {s : Set G} (h : Set.EqOn f g s) : Set.EqOn f g (closure s) :=
  show closure s ≤ f.eqLocus g from (closure_le _).2 h

@[to_additive]
theorem eq_of_eqOn_top {f g : G →* M} (h : Set.EqOn f g (⊤ : Subgroup G)) : f = g :=
  ext fun _x => h trivial

@[to_additive]
theorem eq_of_eqOn_dense {s : Set G} (hs : closure s = ⊤) {f g : G →* M} (h : s.EqOn f g) : f = g :=
  eq_of_eqOn_top <| hs ▸ eqOn_closure h

end EqLocus

end MonoidHom

namespace Subgroup

variable {N : Type*} [Group N] (H : Subgroup G)

@[to_additive]
theorem map_eq_bot_iff {f : G →* N} : H.map f = ⊥ ↔ H ≤ f.ker :=
  (gc_map_comap f).l_eq_bot

@[to_additive]
theorem map_eq_bot_iff_of_injective {f : G →* N} (hf : Function.Injective f) :
    H.map f = ⊥ ↔ H = ⊥ := by rw [map_eq_bot_iff, f.ker_eq_bot_iff.mpr hf, le_bot_iff]

open MonoidHom

variable (f : G →* N)

@[to_additive]
theorem map_le_range (H : Subgroup G) : map f H ≤ f.range :=
  (range_eq_map f).symm ▸ map_mono le_top

@[to_additive]
theorem map_subtype_le {H : Subgroup G} (K : Subgroup H) : K.map H.subtype ≤ H :=
  (K.map_le_range H.subtype).trans_eq H.range_subtype

@[to_additive]
theorem ker_le_comap (H : Subgroup N) : f.ker ≤ comap f H :=
  comap_bot f ▸ comap_mono bot_le

@[to_additive]
theorem map_comap_eq (H : Subgroup N) : map f (comap f H) = f.range ⊓ H :=
  SetLike.ext' <| by
    rw [coe_map, coe_comap, Set.image_preimage_eq_inter_range, coe_inf, coe_range, Set.inter_comm]

@[to_additive]
theorem comap_map_eq (H : Subgroup G) : comap f (map f H) = H ⊔ f.ker := by
  refine le_antisymm ?_ (sup_le (le_comap_map _ _) (ker_le_comap _ _))
  intro x hx; simp only [mem_map, mem_comap] at hx
  rcases hx with ⟨y, hy, hy'⟩
  rw [← mul_inv_cancel_left y x]
  exact mul_mem_sup hy (by simp [mem_ker, hy'])

@[to_additive]
theorem map_comap_eq_self {f : G →* N} {H : Subgroup N} (h : H ≤ f.range) :
    map f (comap f H) = H := by
  rwa [map_comap_eq, inf_eq_right]

@[to_additive]
theorem map_comap_eq_self_of_surjective {f : G →* N} (h : Function.Surjective f) (H : Subgroup N) :
    map f (comap f H) = H :=
  map_comap_eq_self (range_eq_top.2 h ▸ le_top)

@[to_additive]
theorem comap_le_comap_of_le_range {f : G →* N} {K L : Subgroup N} (hf : K ≤ f.range) :
    K.comap f ≤ L.comap f ↔ K ≤ L :=
  ⟨(map_comap_eq_self hf).ge.trans ∘ map_le_iff_le_comap.mpr, comap_mono⟩

@[to_additive]
theorem comap_le_comap_of_surjective {f : G →* N} {K L : Subgroup N} (hf : Function.Surjective f) :
    K.comap f ≤ L.comap f ↔ K ≤ L :=
  comap_le_comap_of_le_range (range_eq_top.2 hf ▸ le_top)

@[to_additive]
theorem comap_lt_comap_of_surjective {f : G →* N} {K L : Subgroup N} (hf : Function.Surjective f) :
    K.comap f < L.comap f ↔ K < L := by simp_rw [lt_iff_le_not_ge, comap_le_comap_of_surjective hf]

@[to_additive]
theorem comap_injective {f : G →* N} (h : Function.Surjective f) : Function.Injective (comap f) :=
  fun K L => by simp only [le_antisymm_iff, comap_le_comap_of_surjective h, imp_self]

@[to_additive]
theorem comap_map_eq_self {f : G →* N} {H : Subgroup G} (h : f.ker ≤ H) :
    comap f (map f H) = H := by
  rwa [comap_map_eq, sup_eq_left]

@[to_additive]
theorem comap_map_eq_self_of_injective {f : G →* N} (h : Function.Injective f) (H : Subgroup G) :
    comap f (map f H) = H :=
  comap_map_eq_self (((ker_eq_bot_iff _).mpr h).symm ▸ bot_le)

@[to_additive]
theorem map_le_map_iff {f : G →* N} {H K : Subgroup G} : H.map f ≤ K.map f ↔ H ≤ K ⊔ f.ker := by
  rw [map_le_iff_le_comap, comap_map_eq]

@[to_additive]
theorem map_le_map_iff' {f : G →* N} {H K : Subgroup G} :
    H.map f ≤ K.map f ↔ H ⊔ f.ker ≤ K ⊔ f.ker := by
  simp only [map_le_map_iff, sup_le_iff, le_sup_right, and_true]

@[to_additive]
theorem map_eq_map_iff {f : G →* N} {H K : Subgroup G} :
    H.map f = K.map f ↔ H ⊔ f.ker = K ⊔ f.ker := by simp only [le_antisymm_iff, map_le_map_iff']

@[to_additive]
theorem map_eq_range_iff {f : G →* N} {H : Subgroup G} :
    H.map f = f.range ↔ Codisjoint H f.ker := by
  rw [f.range_eq_map, map_eq_map_iff, codisjoint_iff, top_sup_eq]

@[to_additive]
theorem map_le_map_iff_of_injective {f : G →* N} (hf : Function.Injective f) {H K : Subgroup G} :
    H.map f ≤ K.map f ↔ H ≤ K := by rw [map_le_iff_le_comap, comap_map_eq_self_of_injective hf]

@[to_additive (attr := simp)]
theorem map_subtype_le_map_subtype {G' : Subgroup G} {H K : Subgroup G'} :
    H.map G'.subtype ≤ K.map G'.subtype ↔ H ≤ K :=
  map_le_map_iff_of_injective G'.subtype_injective

/-- Subgroups of the subgroup `H` are considered as subgroups that are less than or equal to
`H`. -/
@[to_additive (attr := simps apply_coe) /-- Additive subgroups of the subgroup `H` are considered as
additive subgroups that are less than or equal to `H`. -/]
def MapSubtype.orderIso (H : Subgroup G) : Subgroup ↥H ≃o { H' : Subgroup G // H' ≤ H } where
  toFun H' := ⟨H'.map H.subtype, map_subtype_le H'⟩
  invFun sH' := sH'.1.subgroupOf H
  left_inv H' := comap_map_eq_self_of_injective H.subtype_injective H'
  right_inv sH' := Subtype.ext (map_subgroupOf_eq_of_le sH'.2)
  map_rel_iff' := by simp

@[to_additive (attr := simp)]
lemma MapSubtype.orderIso_symm_apply (H : Subgroup G) (sH' : { H' : Subgroup G // H' ≤ H }) :
    (MapSubtype.orderIso H).symm sH' = sH'.1.subgroupOf H :=
  rfl

@[to_additive]
protected lemma «forall» {H : Subgroup G} {P : Subgroup H → Prop} :
    (∀ H' : Subgroup H, P H') ↔ (∀ H' ≤ H, P (H'.subgroupOf H)) := by
  simp [(MapSubtype.orderIso H).forall_congr_left]

@[to_additive]
theorem map_lt_map_iff_of_injective {f : G →* N} (hf : Function.Injective f) {H K : Subgroup G} :
    H.map f < K.map f ↔ H < K :=
  lt_iff_lt_of_le_iff_le' (map_le_map_iff_of_injective hf) (map_le_map_iff_of_injective hf)

@[to_additive (attr := simp)]
theorem map_subtype_lt_map_subtype {G' : Subgroup G} {H K : Subgroup G'} :
    H.map G'.subtype < K.map G'.subtype ↔ H < K :=
  map_lt_map_iff_of_injective G'.subtype_injective

@[to_additive]
theorem map_injective {f : G →* N} (h : Function.Injective f) : Function.Injective (map f) :=
  Function.LeftInverse.injective <| comap_map_eq_self_of_injective h

/-- Given `f(A) = f(B)`, `ker f ≤ A`, and `ker f ≤ B`, deduce that `A = B`. -/
@[to_additive /-- Given `f(A) = f(B)`, `ker f ≤ A`, and `ker f ≤ B`, deduce that `A = B`. -/]
theorem map_injective_of_ker_le {H K : Subgroup G} (hH : f.ker ≤ H) (hK : f.ker ≤ K)
    (hf : map f H = map f K) : H = K := by
  apply_fun comap f at hf
  rwa [comap_map_eq, comap_map_eq, sup_of_le_left hH, sup_of_le_left hK] at hf

@[to_additive]
theorem ker_subgroupMap : (f.subgroupMap H).ker = f.ker.subgroupOf H :=
  ext fun _ ↦ Subtype.ext_iff

@[to_additive]
theorem closure_preimage_eq_top (s : Set G) : closure ((closure s).subtype ⁻¹' s) = ⊤ := by
  simp

@[to_additive]
theorem comap_sup_eq_of_le_range {H K : Subgroup N} (hH : H ≤ f.range) (hK : K ≤ f.range) :
    comap f H ⊔ comap f K = comap f (H ⊔ K) :=
  map_injective_of_ker_le f ((ker_le_comap f H).trans le_sup_left) (ker_le_comap f (H ⊔ K))
    (by
      rw [map_comap_eq, map_sup, map_comap_eq, map_comap_eq, inf_eq_right.mpr hH,
        inf_eq_right.mpr hK, inf_eq_right.mpr (sup_le hH hK)])

@[to_additive]
theorem comap_sup_eq (H K : Subgroup N) (hf : Function.Surjective f) :
    comap f H ⊔ comap f K = comap f (H ⊔ K) :=
  comap_sup_eq_of_le_range f (range_eq_top.2 hf ▸ le_top) (range_eq_top.2 hf ▸ le_top)

@[to_additive]
theorem sup_subgroupOf_eq {H K L : Subgroup G} (hH : H ≤ L) (hK : K ≤ L) :
    H.subgroupOf L ⊔ K.subgroupOf L = (H ⊔ K).subgroupOf L :=
  comap_sup_eq_of_le_range L.subtype (hH.trans_eq L.range_subtype.symm)
     (hK.trans_eq L.range_subtype.symm)

@[to_additive]
theorem codisjoint_subgroupOf_sup (H K : Subgroup G) :
    Codisjoint (H.subgroupOf (H ⊔ K)) (K.subgroupOf (H ⊔ K)) := by
  rw [codisjoint_iff, sup_subgroupOf_eq, subgroupOf_self]
  exacts [le_sup_left, le_sup_right]

@[to_additive]
theorem subgroupOf_sup (A A' B : Subgroup G) (hA : A ≤ B) (hA' : A' ≤ B) :
    (A ⊔ A').subgroupOf B = A.subgroupOf B ⊔ A'.subgroupOf B := by
  refine
    map_injective_of_ker_le B.subtype (ker_le_comap _ _)
      (le_trans (ker_le_comap B.subtype _) le_sup_left) ?_
  simp only [subgroupOf, map_comap_eq, map_sup, range_subtype]
  rw [inf_of_le_right (sup_le hA hA'), inf_of_le_right hA', inf_of_le_right hA]

end Subgroup
