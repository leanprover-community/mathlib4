/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov, Yakov Pechersky, Jireh Loreaux
-/
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.Subsemigroup.Basic
import Mathlib.Algebra.Group.TypeTags

/-!
# Operations on `Subsemigroup`s

In this file we define various operations on `Subsemigroup`s and `MulHom`s.

## Main definitions

### Conversion between multiplicative and additive definitions

* `Subsemigroup.toAddSubsemigroup`, `Subsemigroup.toAddSubsemigroup'`,
  `AddSubsemigroup.toSubsemigroup`, `AddSubsemigroup.toSubsemigroup'`:
  convert between multiplicative and additive subsemigroups of `M`,
  `Multiplicative M`, and `Additive M`. These are stated as `OrderIso`s.

### (Commutative) semigroup structure on a subsemigroup

* `Subsemigroup.toSemigroup`, `Subsemigroup.toCommSemigroup`: a subsemigroup inherits a
  (commutative) semigroup structure.

### Operations on subsemigroups

* `Subsemigroup.comap`: preimage of a subsemigroup under a semigroup homomorphism as a subsemigroup
  of the domain;
* `Subsemigroup.map`: image of a subsemigroup under a semigroup homomorphism as a subsemigroup of
  the codomain;
* `Subsemigroup.prod`: product of two subsemigroups `s : Subsemigroup M` and `t : Subsemigroup N`
  as a subsemigroup of `M × N`;

### Semigroup homomorphisms between subsemigroups

* `Subsemigroup.subtype`: embedding of a subsemigroup into the ambient semigroup.
* `Subsemigroup.inclusion`: given two subsemigroups `S`, `T` such that `S ≤ T`, `S.inclusion T` is
  the inclusion of `S` into `T` as a semigroup homomorphism;
* `MulEquiv.subsemigroupCongr`: converts a proof of `S = T` into a semigroup isomorphism between
  `S` and `T`.
* `Subsemigroup.prodEquiv`: semigroup isomorphism between `s.prod t` and `s × t`;

### Operations on `MulHom`s

* `MulHom.srange`: range of a semigroup homomorphism as a subsemigroup of the codomain;
* `MulHom.restrict`: restrict a semigroup homomorphism to a subsemigroup;
* `MulHom.codRestrict`: restrict the codomain of a semigroup homomorphism to a subsemigroup;
* `MulHom.srangeRestrict`: restrict a semigroup homomorphism to its range;

### Implementation notes

This file follows closely `GroupTheory/Submonoid/Operations.lean`, omitting only that which is
necessary.

## Tags

subsemigroup, range, product, map, comap
-/

assert_not_exists MonoidWithZero

variable {M N P σ : Type*}

/-!
### Conversion to/from `Additive`/`Multiplicative`
-/


section

variable [Mul M]

/-- Subsemigroups of semigroup `M` are isomorphic to additive subsemigroups of `Additive M`. -/
@[simps]
def Subsemigroup.toAddSubsemigroup : Subsemigroup M ≃o AddSubsemigroup (Additive M) where
  toFun S :=
    { carrier := Additive.toMul ⁻¹' S
      add_mem' := S.mul_mem' }
  invFun S :=
    { carrier := Additive.ofMul ⁻¹' S
      mul_mem' := S.add_mem' }
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- Additive subsemigroups of an additive semigroup `Additive M` are isomorphic to subsemigroups
of `M`. -/
abbrev AddSubsemigroup.toSubsemigroup' : AddSubsemigroup (Additive M) ≃o Subsemigroup M :=
  Subsemigroup.toAddSubsemigroup.symm

theorem Subsemigroup.toAddSubsemigroup_closure (S : Set M) :
    Subsemigroup.toAddSubsemigroup (Subsemigroup.closure S) =
    AddSubsemigroup.closure (Additive.toMul ⁻¹' S) :=
  le_antisymm
    (Subsemigroup.toAddSubsemigroup.le_symm_apply.1 <|
      Subsemigroup.closure_le.2 (AddSubsemigroup.subset_closure (M := Additive M)))
    (AddSubsemigroup.closure_le.2 (Subsemigroup.subset_closure (M := M)))

theorem AddSubsemigroup.toSubsemigroup'_closure (S : Set (Additive M)) :
    AddSubsemigroup.toSubsemigroup' (AddSubsemigroup.closure S) =
      Subsemigroup.closure (Additive.ofMul ⁻¹' S) :=
  le_antisymm
    (AddSubsemigroup.toSubsemigroup'.le_symm_apply.1 <|
      AddSubsemigroup.closure_le.2 (Subsemigroup.subset_closure (M := M)))
    (Subsemigroup.closure_le.2 <| AddSubsemigroup.subset_closure (M := Additive M))

end

section

variable {A : Type*} [Add A]

/-- Additive subsemigroups of an additive semigroup `A` are isomorphic to
multiplicative subsemigroups of `Multiplicative A`. -/
@[simps]
def AddSubsemigroup.toSubsemigroup : AddSubsemigroup A ≃o Subsemigroup (Multiplicative A) where
  toFun S :=
    { carrier := Multiplicative.toAdd ⁻¹' S
      mul_mem' := S.add_mem' }
  invFun S :=
    { carrier := Multiplicative.ofAdd ⁻¹' S
      add_mem' := S.mul_mem' }
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- Subsemigroups of a semigroup `Multiplicative A` are isomorphic to additive subsemigroups
of `A`. -/
abbrev Subsemigroup.toAddSubsemigroup' : Subsemigroup (Multiplicative A) ≃o AddSubsemigroup A :=
  AddSubsemigroup.toSubsemigroup.symm

theorem AddSubsemigroup.toSubsemigroup_closure (S : Set A) :
    AddSubsemigroup.toSubsemigroup (AddSubsemigroup.closure S) =
      Subsemigroup.closure (Multiplicative.toAdd ⁻¹' S) :=
  le_antisymm
    (AddSubsemigroup.toSubsemigroup.to_galoisConnection.l_le <|
      AddSubsemigroup.closure_le.2 <| Subsemigroup.subset_closure (M := Multiplicative A))
    (Subsemigroup.closure_le.2 <| AddSubsemigroup.subset_closure (M := A))

theorem Subsemigroup.toAddSubsemigroup'_closure (S : Set (Multiplicative A)) :
    Subsemigroup.toAddSubsemigroup' (Subsemigroup.closure S) =
      AddSubsemigroup.closure (Multiplicative.ofAdd ⁻¹' S) :=
  le_antisymm
    (Subsemigroup.toAddSubsemigroup'.to_galoisConnection.l_le <|
      Subsemigroup.closure_le.2 <| AddSubsemigroup.subset_closure (M := A))
    (AddSubsemigroup.closure_le.2 <| Subsemigroup.subset_closure (M := Multiplicative A))

end

namespace Subsemigroup

open Set

/-!
### `comap` and `map`
-/


variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

/-- The preimage of a subsemigroup along a semigroup homomorphism is a subsemigroup. -/
@[to_additive
      "The preimage of an `AddSubsemigroup` along an `AddSemigroup` homomorphism is an
      `AddSubsemigroup`."]
def comap (f : M →ₙ* N) (S : Subsemigroup N) :
    Subsemigroup M where
  carrier := f ⁻¹' S
  mul_mem' ha hb := show f (_ * _) ∈ S by rw [map_mul]; exact mul_mem ha hb

@[to_additive (attr := simp)]
theorem coe_comap (S : Subsemigroup N) (f : M →ₙ* N) : (S.comap f : Set M) = f ⁻¹' S :=
  rfl

@[to_additive (attr := simp)]
theorem mem_comap {S : Subsemigroup N} {f : M →ₙ* N} {x : M} : x ∈ S.comap f ↔ f x ∈ S :=
  Iff.rfl

@[to_additive]
theorem comap_comap (S : Subsemigroup P) (g : N →ₙ* P) (f : M →ₙ* N) :
    (S.comap g).comap f = S.comap (g.comp f) :=
  rfl

@[to_additive (attr := simp)]
theorem comap_id (S : Subsemigroup P) : S.comap (MulHom.id _) = S :=
  ext (by simp)

/-- The image of a subsemigroup along a semigroup homomorphism is a subsemigroup. -/
@[to_additive
      "The image of an `AddSubsemigroup` along an `AddSemigroup` homomorphism is
      an `AddSubsemigroup`."]
def map (f : M →ₙ* N) (S : Subsemigroup M) : Subsemigroup N where
  carrier := f '' S
  mul_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x * y, @mul_mem (Subsemigroup M) M _ _ _ _ _ _ hx hy, by rw [map_mul]⟩

@[to_additive (attr := simp)]
theorem coe_map (f : M →ₙ* N) (S : Subsemigroup M) : (S.map f : Set N) = f '' S :=
  rfl

@[to_additive (attr := simp)]
theorem mem_map {f : M →ₙ* N} {S : Subsemigroup M} {y : N} : y ∈ S.map f ↔ ∃ x ∈ S, f x = y :=
  mem_image _ _ _

@[to_additive]
theorem mem_map_of_mem (f : M →ₙ* N) {S : Subsemigroup M} {x : M} (hx : x ∈ S) : f x ∈ S.map f :=
  mem_image_of_mem f hx

@[to_additive]
theorem apply_coe_mem_map (f : M →ₙ* N) (S : Subsemigroup M) (x : S) : f x ∈ S.map f :=
  mem_map_of_mem f x.prop

@[to_additive]
theorem map_map (g : N →ₙ* P) (f : M →ₙ* N) : (S.map f).map g = S.map (g.comp f) :=
  SetLike.coe_injective <| image_image _ _ _

-- The simpNF linter says that the LHS can be simplified via `Subsemigroup.mem_map`.
-- However this is a higher priority lemma.
-- https://github.com/leanprover/std4/issues/207
@[to_additive (attr := simp, nolint simpNF)]
theorem mem_map_iff_mem {f : M →ₙ* N} (hf : Function.Injective f) {S : Subsemigroup M} {x : M} :
    f x ∈ S.map f ↔ x ∈ S :=
  hf.mem_set_image

@[to_additive]
theorem map_le_iff_le_comap {f : M →ₙ* N} {S : Subsemigroup M} {T : Subsemigroup N} :
    S.map f ≤ T ↔ S ≤ T.comap f :=
  image_subset_iff

@[to_additive]
theorem gc_map_comap (f : M →ₙ* N) : GaloisConnection (map f) (comap f) := fun _ _ =>
  map_le_iff_le_comap

@[to_additive]
theorem map_le_of_le_comap {T : Subsemigroup N} {f : M →ₙ* N} : S ≤ T.comap f → S.map f ≤ T :=
  (gc_map_comap f).l_le

@[to_additive]
theorem le_comap_of_map_le {T : Subsemigroup N} {f : M →ₙ* N} : S.map f ≤ T → S ≤ T.comap f :=
  (gc_map_comap f).le_u

@[to_additive]
theorem le_comap_map {f : M →ₙ* N} : S ≤ (S.map f).comap f :=
  (gc_map_comap f).le_u_l _

@[to_additive]
theorem map_comap_le {S : Subsemigroup N} {f : M →ₙ* N} : (S.comap f).map f ≤ S :=
  (gc_map_comap f).l_u_le _

@[to_additive]
theorem monotone_map {f : M →ₙ* N} : Monotone (map f) :=
  (gc_map_comap f).monotone_l

@[to_additive]
theorem monotone_comap {f : M →ₙ* N} : Monotone (comap f) :=
  (gc_map_comap f).monotone_u

@[to_additive (attr := simp)]
theorem map_comap_map {f : M →ₙ* N} : ((S.map f).comap f).map f = S.map f :=
  (gc_map_comap f).l_u_l_eq_l _

@[to_additive (attr := simp)]
theorem comap_map_comap {S : Subsemigroup N} {f : M →ₙ* N} :
    ((S.comap f).map f).comap f = S.comap f :=
  (gc_map_comap f).u_l_u_eq_u _

@[to_additive]
theorem map_sup (S T : Subsemigroup M) (f : M →ₙ* N) : (S ⊔ T).map f = S.map f ⊔ T.map f :=
  (gc_map_comap f).l_sup

@[to_additive]
theorem map_iSup {ι : Sort*} (f : M →ₙ* N) (s : ι → Subsemigroup M) :
    (iSup s).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f).l_iSup

@[to_additive]
theorem comap_inf (S T : Subsemigroup N) (f : M →ₙ* N) : (S ⊓ T).comap f = S.comap f ⊓ T.comap f :=
  (gc_map_comap f).u_inf

@[to_additive]
theorem comap_iInf {ι : Sort*} (f : M →ₙ* N) (s : ι → Subsemigroup N) :
    (iInf s).comap f = ⨅ i, (s i).comap f :=
  (gc_map_comap f).u_iInf

@[to_additive (attr := simp)]
theorem map_bot (f : M →ₙ* N) : (⊥ : Subsemigroup M).map f = ⊥ :=
  (gc_map_comap f).l_bot

@[to_additive (attr := simp)]
theorem comap_top (f : M →ₙ* N) : (⊤ : Subsemigroup N).comap f = ⊤ :=
  (gc_map_comap f).u_top

@[to_additive (attr := simp)]
theorem map_id (S : Subsemigroup M) : S.map (MulHom.id M) = S :=
  ext fun _ => ⟨fun ⟨_, h, rfl⟩ => h, fun h => ⟨_, h, rfl⟩⟩

section GaloisCoinsertion

variable {ι : Type*} {f : M →ₙ* N}

/-- `map f` and `comap f` form a `GaloisCoinsertion` when `f` is injective. -/
@[to_additive " `map f` and `comap f` form a `GaloisCoinsertion` when `f` is injective. "]
def gciMapComap (hf : Function.Injective f) : GaloisCoinsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisCoinsertion fun S x => by simp [mem_comap, mem_map, hf.eq_iff]

variable (hf : Function.Injective f)
include hf

@[to_additive]
theorem comap_map_eq_of_injective (S : Subsemigroup M) : (S.map f).comap f = S :=
  (gciMapComap hf).u_l_eq _

@[to_additive]
theorem comap_surjective_of_injective : Function.Surjective (comap f) :=
  (gciMapComap hf).u_surjective

@[to_additive]
theorem map_injective_of_injective : Function.Injective (map f) :=
  (gciMapComap hf).l_injective

@[to_additive]
theorem comap_inf_map_of_injective (S T : Subsemigroup M) : (S.map f ⊓ T.map f).comap f = S ⊓ T :=
  (gciMapComap hf).u_inf_l _ _

@[to_additive]
theorem comap_iInf_map_of_injective (S : ι → Subsemigroup M) :
    (⨅ i, (S i).map f).comap f = iInf S :=
  (gciMapComap hf).u_iInf_l _

@[to_additive]
theorem comap_sup_map_of_injective (S T : Subsemigroup M) : (S.map f ⊔ T.map f).comap f = S ⊔ T :=
  (gciMapComap hf).u_sup_l _ _

@[to_additive]
theorem comap_iSup_map_of_injective (S : ι → Subsemigroup M) :
    (⨆ i, (S i).map f).comap f = iSup S :=
  (gciMapComap hf).u_iSup_l _

@[to_additive]
theorem map_le_map_iff_of_injective {S T : Subsemigroup M} : S.map f ≤ T.map f ↔ S ≤ T :=
  (gciMapComap hf).l_le_l_iff

@[to_additive]
theorem map_strictMono_of_injective : StrictMono (map f) :=
  (gciMapComap hf).strictMono_l

end GaloisCoinsertion

section GaloisInsertion

variable {ι : Type*} {f : M →ₙ* N} (hf : Function.Surjective f)
include hf

/-- `map f` and `comap f` form a `GaloisInsertion` when `f` is surjective. -/
@[to_additive " `map f` and `comap f` form a `GaloisInsertion` when `f` is surjective. "]
def giMapComap : GaloisInsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisInsertion fun S x h =>
    let ⟨y, hy⟩ := hf x
    mem_map.2 ⟨y, by simp [hy, h]⟩

@[to_additive]
theorem map_comap_eq_of_surjective (S : Subsemigroup N) : (S.comap f).map f = S :=
  (giMapComap hf).l_u_eq _

@[to_additive]
theorem map_surjective_of_surjective : Function.Surjective (map f) :=
  (giMapComap hf).l_surjective

@[to_additive]
theorem comap_injective_of_surjective : Function.Injective (comap f) :=
  (giMapComap hf).u_injective

@[to_additive]
theorem map_inf_comap_of_surjective (S T : Subsemigroup N) :
    (S.comap f ⊓ T.comap f).map f = S ⊓ T :=
  (giMapComap hf).l_inf_u _ _

@[to_additive]
theorem map_iInf_comap_of_surjective (S : ι → Subsemigroup N) :
    (⨅ i, (S i).comap f).map f = iInf S :=
  (giMapComap hf).l_iInf_u _

@[to_additive]
theorem map_sup_comap_of_surjective (S T : Subsemigroup N) :
    (S.comap f ⊔ T.comap f).map f = S ⊔ T :=
  (giMapComap hf).l_sup_u _ _

@[to_additive]
theorem map_iSup_comap_of_surjective (S : ι → Subsemigroup N) :
    (⨆ i, (S i).comap f).map f = iSup S :=
  (giMapComap hf).l_iSup_u _

@[to_additive]
theorem comap_le_comap_iff_of_surjective {S T : Subsemigroup N} : S.comap f ≤ T.comap f ↔ S ≤ T :=
  (giMapComap hf).u_le_u_iff

@[to_additive]
theorem comap_strictMono_of_surjective : StrictMono (comap f) :=
  (giMapComap hf).strictMono_u

end GaloisInsertion

end Subsemigroup

namespace MulMemClass

variable {A : Type*} [Mul M] [SetLike A M] [hA : MulMemClass A M] (S' : A)

-- lower priority so other instances are found first
/-- A submagma of a magma inherits a multiplication. -/
@[to_additive "An additive submagma of an additive magma inherits an addition."]
instance (priority := 900) mul : Mul S' :=
  ⟨fun a b => ⟨a.1 * b.1, mul_mem a.2 b.2⟩⟩

-- lower priority so later simp lemmas are used first; to appease simp_nf
@[to_additive (attr := simp low, norm_cast)]
theorem coe_mul (x y : S') : (↑(x * y) : M) = ↑x * ↑y :=
  rfl

-- lower priority so later simp lemmas are used first; to appease simp_nf
@[to_additive (attr := simp low)]
theorem mk_mul_mk (x y : M) (hx : x ∈ S') (hy : y ∈ S') :
    (⟨x, hx⟩ : S') * ⟨y, hy⟩ = ⟨x * y, mul_mem hx hy⟩ :=
  rfl

@[to_additive]
theorem mul_def (x y : S') : x * y = ⟨x * y, mul_mem x.2 y.2⟩ :=
  rfl

/-- A subsemigroup of a semigroup inherits a semigroup structure. -/
@[to_additive "An `AddSubsemigroup` of an `AddSemigroup` inherits an `AddSemigroup` structure."]
instance toSemigroup {M : Type*} [Semigroup M] {A : Type*} [SetLike A M] [MulMemClass A M]
    (S : A) : Semigroup S :=
  Subtype.coe_injective.semigroup Subtype.val fun _ _ => rfl

/-- A subsemigroup of a `CommSemigroup` is a `CommSemigroup`. -/
@[to_additive "An `AddSubsemigroup` of an `AddCommSemigroup` is an `AddCommSemigroup`."]
instance toCommSemigroup {M} [CommSemigroup M] {A : Type*} [SetLike A M] [MulMemClass A M]
    (S : A) : CommSemigroup S :=
  Subtype.coe_injective.commSemigroup Subtype.val fun _ _ => rfl

/-- The natural semigroup hom from a subsemigroup of semigroup `M` to `M`. -/
@[to_additive "The natural semigroup hom from an `AddSubsemigroup` of
`AddSubsemigroup` `M` to `M`."]
def subtype : S' →ₙ* M where
  toFun := Subtype.val; map_mul' := fun _ _ => rfl

@[to_additive (attr := simp)]
theorem coe_subtype : (MulMemClass.subtype S' : S' → M) = Subtype.val :=
  rfl

end MulMemClass

namespace Subsemigroup

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

/-- The top subsemigroup is isomorphic to the semigroup. -/
@[to_additive (attr := simps)
  "The top additive subsemigroup is isomorphic to the additive semigroup."]
def topEquiv : (⊤ : Subsemigroup M) ≃* M where
  toFun x := x
  invFun x := ⟨x, mem_top x⟩
  left_inv x := x.eta _
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[to_additive (attr := simp)]
theorem topEquiv_toMulHom :
    ((topEquiv : _ ≃* M) : _ →ₙ* M) = MulMemClass.subtype (⊤ : Subsemigroup M) :=
  rfl

/-- A subsemigroup is isomorphic to its image under an injective function -/
@[to_additive "An additive subsemigroup is isomorphic to its image under an injective function"]
noncomputable def equivMapOfInjective (f : M →ₙ* N) (hf : Function.Injective f) : S ≃* S.map f :=
  { Equiv.Set.image f S hf with map_mul' := fun _ _ => Subtype.ext (map_mul f _ _) }

@[to_additive (attr := simp)]
theorem coe_equivMapOfInjective_apply (f : M →ₙ* N) (hf : Function.Injective f) (x : S) :
    (equivMapOfInjective S f hf x : N) = f x :=
  rfl

@[to_additive (attr := simp)]
theorem closure_closure_coe_preimage {s : Set M} :
    closure ((Subtype.val : closure s → M) ⁻¹' s) = ⊤ :=
  eq_top_iff.2 fun x =>
    Subtype.recOn x fun _ hx' _ => closure_induction'
      (p := fun y hy ↦ (⟨y, hy⟩ : closure s) ∈ closure (((↑) : closure s → M) ⁻¹' s))
        (fun _ hg => subset_closure hg) (fun _ _ _ _ => Subsemigroup.mul_mem _) hx'

/-- Given `Subsemigroup`s `s`, `t` of semigroups `M`, `N` respectively, `s × t` as a subsemigroup
of `M × N`. -/
@[to_additive prod
      "Given `AddSubsemigroup`s `s`, `t` of `AddSemigroup`s `A`, `B` respectively,
      `s × t` as an `AddSubsemigroup` of `A × B`."]
def prod (s : Subsemigroup M) (t : Subsemigroup N) : Subsemigroup (M × N) where
  carrier := s ×ˢ t
  mul_mem' hp hq := ⟨s.mul_mem hp.1 hq.1, t.mul_mem hp.2 hq.2⟩

@[to_additive coe_prod]
theorem coe_prod (s : Subsemigroup M) (t : Subsemigroup N) :
    (s.prod t : Set (M × N)) = (s : Set M) ×ˢ (t : Set N) :=
  rfl

@[to_additive mem_prod]
theorem mem_prod {s : Subsemigroup M} {t : Subsemigroup N} {p : M × N} :
    p ∈ s.prod t ↔ p.1 ∈ s ∧ p.2 ∈ t :=
  Iff.rfl

@[to_additive prod_mono]
theorem prod_mono {s₁ s₂ : Subsemigroup M} {t₁ t₂ : Subsemigroup N} (hs : s₁ ≤ s₂) (ht : t₁ ≤ t₂) :
    s₁.prod t₁ ≤ s₂.prod t₂ :=
  Set.prod_mono hs ht

@[to_additive prod_top]
theorem prod_top (s : Subsemigroup M) : s.prod (⊤ : Subsemigroup N) = s.comap (MulHom.fst M N) :=
  ext fun x => by simp [mem_prod, MulHom.coe_fst]

@[to_additive top_prod]
theorem top_prod (s : Subsemigroup N) : (⊤ : Subsemigroup M).prod s = s.comap (MulHom.snd M N) :=
  ext fun x => by simp [mem_prod, MulHom.coe_snd]

@[to_additive (attr := simp) top_prod_top]
theorem top_prod_top : (⊤ : Subsemigroup M).prod (⊤ : Subsemigroup N) = ⊤ :=
  (top_prod _).trans <| comap_top _

@[to_additive bot_prod_bot]
theorem bot_prod_bot : (⊥ : Subsemigroup M).prod (⊥ : Subsemigroup N) = ⊥ :=
  SetLike.coe_injective <| by simp [coe_prod]

/-- The product of subsemigroups is isomorphic to their product as semigroups. -/
@[to_additive prodEquiv
    "The product of additive subsemigroups is isomorphic to their product as additive semigroups"]
def prodEquiv (s : Subsemigroup M) (t : Subsemigroup N) : s.prod t ≃* s × t :=
  { (Equiv.Set.prod (s : Set M) (t : Set N)) with
    map_mul' := fun _ _ => rfl }

open MulHom

@[to_additive]
theorem mem_map_equiv {f : M ≃* N} {K : Subsemigroup M} {x : N} :
    x ∈ K.map (f : M →ₙ* N) ↔ f.symm x ∈ K :=
  @Set.mem_image_equiv _ _ (K : Set M) f.toEquiv x

@[to_additive]
theorem map_equiv_eq_comap_symm (f : M ≃* N) (K : Subsemigroup M) :
    K.map (f : M →ₙ* N) = K.comap (f.symm : N →ₙ* M) :=
  SetLike.coe_injective (f.toEquiv.image_eq_preimage K)

@[to_additive]
theorem comap_equiv_eq_map_symm (f : N ≃* M) (K : Subsemigroup M) :
    K.comap (f : N →ₙ* M) = K.map (f.symm : M →ₙ* N) :=
  (map_equiv_eq_comap_symm f.symm K).symm

@[to_additive (attr := simp)]
theorem map_equiv_top (f : M ≃* N) : (⊤ : Subsemigroup M).map (f : M →ₙ* N) = ⊤ :=
  SetLike.coe_injective <| Set.image_univ.trans f.surjective.range_eq

@[to_additive le_prod_iff]
theorem le_prod_iff {s : Subsemigroup M} {t : Subsemigroup N} {u : Subsemigroup (M × N)} :
    u ≤ s.prod t ↔ u.map (fst M N) ≤ s ∧ u.map (snd M N) ≤ t := by
  constructor
  · intro h
    constructor
    · rintro x ⟨⟨y1, y2⟩, ⟨hy1, rfl⟩⟩
      exact (h hy1).1
    · rintro x ⟨⟨y1, y2⟩, ⟨hy1, rfl⟩⟩
      exact (h hy1).2
  · rintro ⟨hH, hK⟩ ⟨x1, x2⟩ h
    exact ⟨hH ⟨_, h, rfl⟩, hK ⟨_, h, rfl⟩⟩

end Subsemigroup

namespace MulHom

open Subsemigroup

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

/-- The range of a semigroup homomorphism is a subsemigroup. See Note [range copy pattern]. -/
@[to_additive "The range of an `AddHom` is an `AddSubsemigroup`."]
def srange (f : M →ₙ* N) : Subsemigroup N :=
  ((⊤ : Subsemigroup M).map f).copy (Set.range f) Set.image_univ.symm

@[to_additive (attr := simp)]
theorem coe_srange (f : M →ₙ* N) : (f.srange : Set N) = Set.range f :=
  rfl

@[to_additive (attr := simp)]
theorem mem_srange {f : M →ₙ* N} {y : N} : y ∈ f.srange ↔ ∃ x, f x = y :=
  Iff.rfl

@[to_additive]
private theorem srange_mk_aux_mul {f : M → N} (hf : ∀ (x y : M), f (x * y) = f x * f y)
    {x y : N} (hx : x ∈ Set.range f) (hy : y ∈ Set.range f) :
    x * y ∈ Set.range f :=
  (srange ⟨f, hf⟩).mul_mem hx hy

@[to_additive (attr := simp)] theorem srange_mk (f : M → N) (hf) :
    srange ⟨f, hf⟩ = ⟨Set.range f, srange_mk_aux_mul hf⟩ := rfl

@[to_additive]
theorem srange_eq_map (f : M →ₙ* N) : f.srange = (⊤ : Subsemigroup M).map f :=
  copy_eq _

@[to_additive]
theorem map_srange (g : N →ₙ* P) (f : M →ₙ* N) : f.srange.map g = (g.comp f).srange := by
  simpa only [srange_eq_map] using (⊤ : Subsemigroup M).map_map g f

@[to_additive]
theorem srange_top_iff_surjective {N} [Mul N] {f : M →ₙ* N} :
    f.srange = (⊤ : Subsemigroup N) ↔ Function.Surjective f :=
  SetLike.ext'_iff.trans <| Iff.trans (by rw [coe_srange, coe_top]) Set.range_iff_surjective

/-- The range of a surjective semigroup hom is the whole of the codomain. -/
@[to_additive (attr := simp)
  "The range of a surjective `AddSemigroup` hom is the whole of the codomain."]
theorem srange_top_of_surjective {N} [Mul N] (f : M →ₙ* N) (hf : Function.Surjective f) :
    f.srange = (⊤ : Subsemigroup N) :=
  srange_top_iff_surjective.2 hf

@[to_additive]
theorem mclosure_preimage_le (f : M →ₙ* N) (s : Set N) : closure (f ⁻¹' s) ≤ (closure s).comap f :=
  closure_le.2 fun _ hx => SetLike.mem_coe.2 <| mem_comap.2 <| subset_closure hx

/-- The image under a semigroup hom of the subsemigroup generated by a set equals the subsemigroup
generated by the image of the set. -/
@[to_additive
      "The image under an `AddSemigroup` hom of the `AddSubsemigroup` generated by a set
      equals the `AddSubsemigroup` generated by the image of the set."]
theorem map_mclosure (f : M →ₙ* N) (s : Set M) : (closure s).map f = closure (f '' s) :=
  le_antisymm
    (map_le_iff_le_comap.2 <|
      le_trans (closure_mono <| Set.subset_preimage_image _ _) (mclosure_preimage_le _ _))
    (closure_le.2 <| Set.image_subset _ subset_closure)

/-- Restriction of a semigroup hom to a subsemigroup of the domain. -/
@[to_additive "Restriction of an AddSemigroup hom to an `AddSubsemigroup` of the domain."]
def restrict {N : Type*} [Mul N] [SetLike σ M] [MulMemClass σ M] (f : M →ₙ* N) (S : σ) : S →ₙ* N :=
  f.comp (MulMemClass.subtype S)

@[to_additive (attr := simp)]
theorem restrict_apply {N : Type*} [Mul N] [SetLike σ M] [MulMemClass σ M] (f : M →ₙ* N) {S : σ}
    (x : S) : f.restrict S x = f x :=
  rfl

/-- Restriction of a semigroup hom to a subsemigroup of the codomain. -/
@[to_additive (attr := simps)
  "Restriction of an `AddSemigroup` hom to an `AddSubsemigroup` of the codomain."]
def codRestrict [SetLike σ N] [MulMemClass σ N] (f : M →ₙ* N) (S : σ) (h : ∀ x, f x ∈ S) :
    M →ₙ* S where
  toFun n := ⟨f n, h n⟩
  map_mul' x y := Subtype.eq (map_mul f x y)

/-- Restriction of a semigroup hom to its range interpreted as a subsemigroup. -/
@[to_additive "Restriction of an `AddSemigroup` hom to its range interpreted as a subsemigroup."]
def srangeRestrict {N} [Mul N] (f : M →ₙ* N) : M →ₙ* f.srange :=
  (f.codRestrict f.srange) fun x => ⟨x, rfl⟩

@[to_additive (attr := simp)]
theorem coe_srangeRestrict {N} [Mul N] (f : M →ₙ* N) (x : M) : (f.srangeRestrict x : N) = f x :=
  rfl

@[to_additive]
theorem srangeRestrict_surjective (f : M →ₙ* N) : Function.Surjective f.srangeRestrict :=
  fun ⟨_, ⟨x, rfl⟩⟩ => ⟨x, rfl⟩

@[to_additive prod_map_comap_prod']
theorem prod_map_comap_prod' {M' : Type*} {N' : Type*} [Mul M'] [Mul N'] (f : M →ₙ* N)
    (g : M' →ₙ* N') (S : Subsemigroup N) (S' : Subsemigroup N') :
    (S.prod S').comap (prodMap f g) = (S.comap f).prod (S'.comap g) :=
  SetLike.coe_injective <| Set.preimage_prod_map_prod f g _ _

/-- The `MulHom` from the preimage of a subsemigroup to itself. -/
@[to_additive (attr := simps)
  "The `AddHom` from the preimage of an additive subsemigroup to itself."]
def subsemigroupComap (f : M →ₙ* N) (N' : Subsemigroup N) :
    N'.comap f →ₙ* N' where
  toFun x := ⟨f x, x.prop⟩
  map_mul' x y := Subtype.eq <| map_mul (M := M) (N := N) f x y

/-- The `MulHom` from a subsemigroup to its image.
See `MulEquiv.subsemigroupMap` for a variant for `MulEquiv`s. -/
@[to_additive (attr := simps)
      "the `AddHom` from an additive subsemigroup to its image. See
      `AddEquiv.addSubsemigroupMap` for a variant for `AddEquiv`s."]
def subsemigroupMap (f : M →ₙ* N) (M' : Subsemigroup M) :
    M' →ₙ* M'.map f where
  toFun x := ⟨f x, ⟨x, x.prop, rfl⟩⟩
  map_mul' x y := Subtype.eq <| map_mul (M := M) (N := N) f x y

@[to_additive]
theorem subsemigroupMap_surjective (f : M →ₙ* N) (M' : Subsemigroup M) :
    Function.Surjective (f.subsemigroupMap M') := by
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

end MulHom

namespace Subsemigroup

open MulHom

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

@[to_additive (attr := simp)]
theorem srange_fst [Nonempty N] : (fst M N).srange = ⊤ :=
  (fst M N).srange_top_of_surjective <| Prod.fst_surjective

@[to_additive (attr := simp)]
theorem srange_snd [Nonempty M] : (snd M N).srange = ⊤ :=
  (snd M N).srange_top_of_surjective <| Prod.snd_surjective

@[to_additive prod_eq_top_iff]
theorem prod_eq_top_iff [Nonempty M] [Nonempty N] {s : Subsemigroup M} {t : Subsemigroup N} :
    s.prod t = ⊤ ↔ s = ⊤ ∧ t = ⊤ := by
  simp only [eq_top_iff, le_prod_iff, ← (gc_map_comap _).le_iff_le, ← srange_eq_map, srange_fst,
    srange_snd]

/-- The semigroup hom associated to an inclusion of subsemigroups. -/
@[to_additive "The `AddSemigroup` hom associated to an inclusion of subsemigroups."]
def inclusion {S T : Subsemigroup M} (h : S ≤ T) : S →ₙ* T :=
  (MulMemClass.subtype S).codRestrict _ fun x => h x.2

@[to_additive (attr := simp)]
theorem range_subtype (s : Subsemigroup M) : (MulMemClass.subtype s).srange = s :=
  SetLike.coe_injective <| (coe_srange _).trans <| Subtype.range_coe

@[to_additive]
theorem eq_top_iff' : S = ⊤ ↔ ∀ x : M, x ∈ S :=
  eq_top_iff.trans ⟨fun h m => h <| mem_top m, fun h m _ => h m⟩

end Subsemigroup

namespace MulEquiv

variable [Mul M] [Mul N] {S T : Subsemigroup M}

/-- Makes the identity isomorphism from a proof that two subsemigroups of a multiplicative
    semigroup are equal. -/
@[to_additive
      "Makes the identity additive isomorphism from a proof two
      subsemigroups of an additive semigroup are equal."]
def subsemigroupCongr (h : S = T) : S ≃* T :=
  { Equiv.setCongr <| congr_arg _ h with map_mul' := fun _ _ => rfl }

-- this name is primed so that the version to `f.range` instead of `f.srange` can be unprimed.
/-- A semigroup homomorphism `f : M →ₙ* N` with a left-inverse `g : N → M` defines a multiplicative
equivalence between `M` and `f.srange`.

This is a bidirectional version of `MulHom.srangeRestrict`. -/
@[to_additive (attr := simps (config := { simpRhs := true }))
      "An additive semigroup homomorphism `f : M →+ N` with a left-inverse
      `g : N → M` defines an additive equivalence between `M` and `f.srange`.
      This is a bidirectional version of `AddHom.srangeRestrict`. "]
def ofLeftInverse (f : M →ₙ* N) {g : N → M} (h : Function.LeftInverse g f) : M ≃* f.srange :=
  { f.srangeRestrict with
    toFun := f.srangeRestrict
    invFun := g ∘ MulMemClass.subtype f.srange
    left_inv := h
    right_inv := fun x =>
      Subtype.ext <|
        let ⟨x', hx'⟩ := MulHom.mem_srange.mp x.prop
        show f (g x) = x by rw [← hx', h x'] }

/-- A `MulEquiv` `φ` between two semigroups `M` and `N` induces a `MulEquiv` between
a subsemigroup `S ≤ M` and the subsemigroup `φ(S) ≤ N`.
See `MulHom.subsemigroupMap` for a variant for `MulHom`s. -/
@[to_additive (attr := simps)
      "An `AddEquiv` `φ` between two additive semigroups `M` and `N` induces an `AddEquiv`
      between a subsemigroup `S ≤ M` and the subsemigroup `φ(S) ≤ N`.
      See `AddHom.addSubsemigroupMap` for a variant for `AddHom`s."]
def subsemigroupMap (e : M ≃* N) (S : Subsemigroup M) : S ≃* S.map (e : M →ₙ* N) :=
  { -- we restate this for `simps` to avoid `⇑e.symm.toEquiv x`
    (e : M →ₙ* N).subsemigroupMap S,
    (e : M ≃ N).image S with
    toFun := fun x => ⟨e x, _⟩
    invFun := fun x => ⟨e.symm x, _⟩ }

end MulEquiv

namespace Subsemigroup

variable [Mul M] [Mul N]

@[to_additive]
theorem map_comap_eq (f : M →ₙ* N) (S : Subsemigroup N) : (S.comap f).map f = S ⊓ f.srange :=
  SetLike.coe_injective Set.image_preimage_eq_inter_range

@[to_additive]
theorem map_comap_eq_self {f : M →ₙ* N} {S : Subsemigroup N} (h : S ≤ f.srange) :
    (S.comap f).map f = S := by
  simpa only [inf_of_le_left h] using map_comap_eq f S

end Subsemigroup
