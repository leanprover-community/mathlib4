/-
Copyright (c) 2020 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.TypeTags.Hom

/-!
# `map` and `comap` for subgroups

We prove results about images and preimages of subgroups under group homomorphisms. The bundled
subgroups use bundled monoid homomorphisms.

Special thanks goes to Amelia Livingston and Yury Kudryashov for their help and inspiration.

## Main definitions

Notation used here:

- `G N` are `Group`s

- `H` is a `Subgroup` of `G`

- `x` is an element of type `G` or type `A`

- `f g : N →* G` are group homomorphisms

- `s k` are sets of elements of type `G`

Definitions in the file:

* `Subgroup.comap H f` : the preimage of a subgroup `H` along the group homomorphism `f` is also a
  subgroup

* `Subgroup.map f H` : the image of a subgroup `H` along the group homomorphism `f` is also a
  subgroup

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

namespace Subgroup

variable (H K : Subgroup G) {k : Set G}

open Set

variable {N : Type*} [Group N] {P : Type*} [Group P]

/-- The preimage of a subgroup along a monoid homomorphism is a subgroup. -/
@[to_additive
      /-- The preimage of an `AddSubgroup` along an `AddMonoid` homomorphism
      is an `AddSubgroup`. -/]
def comap {N : Type*} [Group N] (f : G →* N) (H : Subgroup N) : Subgroup G :=
  { H.toSubmonoid.comap f with
    carrier := f ⁻¹' H
    inv_mem' := fun {a} ha => show f a⁻¹ ∈ H by rw [f.map_inv]; exact H.inv_mem ha }

@[to_additive (attr := simp)]
theorem coe_comap (K : Subgroup N) (f : G →* N) : (K.comap f : Set G) = f ⁻¹' K :=
  rfl

@[to_additive (attr := simp)]
theorem mem_comap {K : Subgroup N} {f : G →* N} {x : G} : x ∈ K.comap f ↔ f x ∈ K :=
  Iff.rfl

@[to_additive]
theorem comap_mono {f : G →* N} {K K' : Subgroup N} : K ≤ K' → comap f K ≤ comap f K' :=
  preimage_mono

@[to_additive]
theorem comap_comap (K : Subgroup P) (g : N →* P) (f : G →* N) :
    (K.comap g).comap f = K.comap (g.comp f) :=
  rfl

@[to_additive (attr := simp)]
theorem comap_id (K : Subgroup N) : K.comap (MonoidHom.id _) = K := by
  ext
  rfl

@[simp]
theorem toAddSubgroup_comap {G₂ : Type*} [Group G₂] (f : G →* G₂) (s : Subgroup G₂) :
    s.toAddSubgroup.comap (MonoidHom.toAdditive f) = Subgroup.toAddSubgroup (s.comap f) := rfl

@[simp]
theorem _root_.AddSubgroup.toSubgroup_comap {A A₂ : Type*} [AddGroup A] [AddGroup A₂]
    (f : A →+ A₂) (s : AddSubgroup A₂) :
    s.toSubgroup.comap (AddMonoidHom.toMultiplicative f) = AddSubgroup.toSubgroup (s.comap f) := rfl

/-- The image of a subgroup along a monoid homomorphism is a subgroup. -/
@[to_additive
      /-- The image of an `AddSubgroup` along an `AddMonoid` homomorphism
      is an `AddSubgroup`. -/]
def map (f : G →* N) (H : Subgroup G) : Subgroup N :=
  { H.toSubmonoid.map f with
    carrier := f '' H
    inv_mem' := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x⁻¹, H.inv_mem hx, f.map_inv x⟩ }

@[to_additive (attr := simp)]
theorem coe_map (f : G →* N) (K : Subgroup G) : (K.map f : Set N) = f '' K :=
  rfl

@[to_additive (attr := simp)]
theorem map_toSubmonoid (f : G →* G') (K : Subgroup G) :
    (Subgroup.map f K).toSubmonoid = Submonoid.map f K.toSubmonoid := rfl

@[to_additive (attr := simp)]
theorem mem_map {f : G →* N} {K : Subgroup G} {y : N} : y ∈ K.map f ↔ ∃ x ∈ K, f x = y := Iff.rfl

@[to_additive]
theorem mem_map_of_mem (f : G →* N) {K : Subgroup G} {x : G} (hx : x ∈ K) : f x ∈ K.map f :=
  mem_image_of_mem f hx

@[to_additive]
theorem apply_coe_mem_map (f : G →* N) (K : Subgroup G) (x : K) : f x ∈ K.map f :=
  mem_map_of_mem f x.prop

@[to_additive (attr := gcongr)]
theorem map_mono {f : G →* N} {K K' : Subgroup G} : K ≤ K' → map f K ≤ map f K' :=
  image_mono

@[to_additive (attr := simp)]
theorem map_id : K.map (MonoidHom.id G) = K :=
  SetLike.coe_injective <| image_id _

@[to_additive]
theorem map_map (g : N →* P) (f : G →* N) : (K.map f).map g = K.map (g.comp f) :=
  SetLike.coe_injective <| image_image _ _ _

@[to_additive (attr := simp)]
theorem map_one_eq_bot : K.map (1 : G →* N) = ⊥ :=
  eq_bot_iff.mpr <| by
    rintro x ⟨y, _, rfl⟩
    simp

@[to_additive]
theorem mem_map_equiv {f : G ≃* N} {K : Subgroup G} {x : N} :
    x ∈ K.map f.toMonoidHom ↔ f.symm x ∈ K :=
  Set.mem_image_equiv

-- The simpNF linter says that the LHS can be simplified via `Subgroup.mem_map`.
-- However this is a higher priority lemma.
-- It seems the side condition `hf` is not applied by `simpNF`.
-- https://github.com/leanprover/std4/issues/207
@[to_additive (attr := simp 1100, nolint simpNF)]
theorem mem_map_iff_mem {f : G →* N} (hf : Function.Injective f) {K : Subgroup G} {x : G} :
    f x ∈ K.map f ↔ x ∈ K :=
  hf.mem_set_image

@[to_additive]
theorem map_equiv_eq_comap_symm' (f : G ≃* N) (K : Subgroup G) :
    K.map f.toMonoidHom = K.comap f.symm.toMonoidHom :=
  SetLike.coe_injective (f.toEquiv.image_eq_preimage K)

@[to_additive]
theorem map_equiv_eq_comap_symm (f : G ≃* N) (K : Subgroup G) :
    K.map f = K.comap (G := N) f.symm :=
  map_equiv_eq_comap_symm' _ _

@[to_additive]
theorem comap_equiv_eq_map_symm (f : N ≃* G) (K : Subgroup G) :
    K.comap (G := N) f = K.map f.symm :=
  (map_equiv_eq_comap_symm f.symm K).symm

@[to_additive]
theorem comap_equiv_eq_map_symm' (f : N ≃* G) (K : Subgroup G) :
    K.comap f.toMonoidHom = K.map f.symm.toMonoidHom :=
  (map_equiv_eq_comap_symm f.symm K).symm

@[to_additive]
theorem map_symm_eq_iff_map_eq {H : Subgroup N} {e : G ≃* N} :
    H.map ↑e.symm = K ↔ K.map ↑e = H := by
  constructor <;> rintro rfl
  · rw [map_map, ← MulEquiv.coe_monoidHom_trans, MulEquiv.symm_trans_self,
      MulEquiv.coe_monoidHom_refl, map_id]
  · rw [map_map, ← MulEquiv.coe_monoidHom_trans, MulEquiv.self_trans_symm,
      MulEquiv.coe_monoidHom_refl, map_id]

@[to_additive]
theorem map_le_iff_le_comap {f : G →* N} {K : Subgroup G} {H : Subgroup N} :
    K.map f ≤ H ↔ K ≤ H.comap f :=
  image_subset_iff

@[to_additive]
theorem gc_map_comap (f : G →* N) : GaloisConnection (map f) (comap f) := fun _ _ =>
  map_le_iff_le_comap

@[to_additive]
theorem map_sup (H K : Subgroup G) (f : G →* N) : (H ⊔ K).map f = H.map f ⊔ K.map f :=
  (gc_map_comap f).l_sup

@[to_additive]
theorem map_iSup {ι : Sort*} (f : G →* N) (s : ι → Subgroup G) :
    (iSup s).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f).l_iSup

@[to_additive]
theorem map_inf (H K : Subgroup G) (f : G →* N) (hf : Function.Injective f) :
    (H ⊓ K).map f = H.map f ⊓ K.map f := SetLike.coe_injective (Set.image_inter hf)

@[to_additive]
theorem map_iInf {ι : Sort*} [Nonempty ι] (f : G →* N) (hf : Function.Injective f)
    (s : ι → Subgroup G) : (iInf s).map f = ⨅ i, (s i).map f := by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ s)

@[to_additive]
theorem comap_sup_comap_le (H K : Subgroup N) (f : G →* N) :
    comap f H ⊔ comap f K ≤ comap f (H ⊔ K) :=
  Monotone.le_map_sup (fun _ _ => comap_mono) H K

@[to_additive]
theorem iSup_comap_le {ι : Sort*} (f : G →* N) (s : ι → Subgroup N) :
    ⨆ i, (s i).comap f ≤ (iSup s).comap f :=
  Monotone.le_map_iSup fun _ _ => comap_mono

@[to_additive]
theorem comap_inf (H K : Subgroup N) (f : G →* N) : (H ⊓ K).comap f = H.comap f ⊓ K.comap f :=
  (gc_map_comap f).u_inf

@[to_additive]
theorem comap_iInf {ι : Sort*} (f : G →* N) (s : ι → Subgroup N) :
    (iInf s).comap f = ⨅ i, (s i).comap f :=
  (gc_map_comap f).u_iInf

@[to_additive]
theorem map_inf_le (H K : Subgroup G) (f : G →* N) : map f (H ⊓ K) ≤ map f H ⊓ map f K :=
  le_inf (map_mono inf_le_left) (map_mono inf_le_right)

@[to_additive]
theorem map_inf_eq (H K : Subgroup G) (f : G →* N) (hf : Function.Injective f) :
    map f (H ⊓ K) = map f H ⊓ map f K := by
  rw [← SetLike.coe_set_eq]
  simp [Set.image_inter hf]

@[to_additive (attr := simp)]
theorem map_bot (f : G →* N) : (⊥ : Subgroup G).map f = ⊥ :=
  (gc_map_comap f).l_bot

@[to_additive]
lemma disjoint_map {f : G →* N} (hf : Function.Injective f) {H K : Subgroup G} (h : Disjoint H K) :
    Disjoint (H.map f) (K.map f) := by
  rw [disjoint_iff, ← map_inf _ _ f hf, disjoint_iff.mp h, map_bot]

@[to_additive]
theorem map_top_of_surjective (f : G →* N) (h : Function.Surjective f) : Subgroup.map f ⊤ = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy⟩ := h x
  exact ⟨y, trivial, hy⟩

@[to_additive]
lemma codisjoint_map {f : G →* N} (hf : Function.Surjective f)
    {H K : Subgroup G} (h : Codisjoint H K) : Codisjoint (H.map f) (K.map f) := by
  rw [codisjoint_iff, ← map_sup, codisjoint_iff.mp h, map_top_of_surjective _ hf]

@[to_additive (attr := simp)]
lemma map_equiv_top {F : Type*} [EquivLike F G N] [MulEquivClass F G N] (f : F) :
    map (f : G →* N) ⊤ = ⊤ :=
  map_top_of_surjective _ (EquivLike.surjective f)

@[to_additive (attr := simp)]
theorem comap_top (f : G →* N) : (⊤ : Subgroup N).comap f = ⊤ :=
  (gc_map_comap f).u_top

/-- For any subgroups `H` and `K`, view `H ⊓ K` as a subgroup of `K`. -/
@[to_additive /-- For any subgroups `H` and `K`, view `H ⊓ K` as a subgroup of `K`. -/]
def subgroupOf (H K : Subgroup G) : Subgroup K :=
  H.comap K.subtype

/-- If `H ≤ K`, then `H` as a subgroup of `K` is isomorphic to `H`. -/
@[to_additive (attr := simps)
/-- If `H ≤ K`, then `H` as a subgroup of `K` is isomorphic to `H`. -/]
def subgroupOfEquivOfLe {G : Type*} [Group G] {H K : Subgroup G} (h : H ≤ K) :
    H.subgroupOf K ≃* H where
  toFun g := ⟨g.1, g.2⟩
  invFun g := ⟨⟨g.1, h g.2⟩, g.2⟩
  map_mul' _g _h := rfl

@[to_additive (attr := simp)]
theorem comap_subtype (H K : Subgroup G) : H.comap K.subtype = H.subgroupOf K :=
  rfl

@[to_additive (attr := simp)]
theorem comap_inclusion_subgroupOf {K₁ K₂ : Subgroup G} (h : K₁ ≤ K₂) (H : Subgroup G) :
    (H.subgroupOf K₂).comap (inclusion h) = H.subgroupOf K₁ :=
  rfl

@[to_additive]
theorem coe_subgroupOf (H K : Subgroup G) : (H.subgroupOf K : Set K) = K.subtype ⁻¹' H :=
  rfl

@[to_additive]
theorem mem_subgroupOf {H K : Subgroup G} {h : K} : h ∈ H.subgroupOf K ↔ (h : G) ∈ H :=
  Iff.rfl

-- TODO(kmill): use `K ⊓ H` order for RHS to match `Subtype.image_preimage_coe`
@[to_additive (attr := simp)]
theorem subgroupOf_map_subtype (H K : Subgroup G) : (H.subgroupOf K).map K.subtype = H ⊓ K :=
  SetLike.ext' <| by refine Subtype.image_preimage_coe _ _ |>.trans ?_; apply Set.inter_comm

@[to_additive]
theorem map_subgroupOf_eq_of_le {H K : Subgroup G} (h : H ≤ K) :
    (H.subgroupOf K).map K.subtype = H := by
  rwa [subgroupOf_map_subtype, inf_eq_left]

@[to_additive (attr := simp)]
theorem bot_subgroupOf : (⊥ : Subgroup G).subgroupOf H = ⊥ :=
  Eq.symm (Subgroup.ext fun _g => Subtype.ext_iff)

@[to_additive (attr := simp)]
theorem top_subgroupOf : (⊤ : Subgroup G).subgroupOf H = ⊤ :=
  rfl

@[to_additive]
theorem subgroupOf_bot_eq_bot : H.subgroupOf ⊥ = ⊥ :=
  Subsingleton.elim _ _

@[to_additive]
theorem subgroupOf_bot_eq_top : H.subgroupOf ⊥ = ⊤ :=
  Subsingleton.elim _ _

@[to_additive (attr := simp)]
theorem subgroupOf_self : H.subgroupOf H = ⊤ :=
  top_unique fun g _hg => g.2

@[to_additive (attr := simp)]
theorem subgroupOf_inj {H₁ H₂ K : Subgroup G} :
    H₁.subgroupOf K = H₂.subgroupOf K ↔ H₁ ⊓ K = H₂ ⊓ K := by
  simpa only [SetLike.ext_iff, mem_inf, mem_subgroupOf, and_congr_left_iff] using Subtype.forall

@[to_additive (attr := simp)]
theorem inf_subgroupOf_right (H K : Subgroup G) : (H ⊓ K).subgroupOf K = H.subgroupOf K :=
  subgroupOf_inj.2 (inf_right_idem _ _)

@[to_additive (attr := simp)]
theorem inf_subgroupOf_left (H K : Subgroup G) : (K ⊓ H).subgroupOf K = H.subgroupOf K := by
  rw [inf_comm, inf_subgroupOf_right]

@[to_additive (attr := simp)]
theorem subgroupOf_eq_bot {H K : Subgroup G} : H.subgroupOf K = ⊥ ↔ Disjoint H K := by
  rw [disjoint_iff, ← bot_subgroupOf, subgroupOf_inj, bot_inf_eq]

@[to_additive (attr := simp)]
theorem subgroupOf_eq_top {H K : Subgroup G} : H.subgroupOf K = ⊤ ↔ K ≤ H := by
  rw [← top_subgroupOf, subgroupOf_inj, top_inf_eq, inf_eq_right]

variable (H : Subgroup G)

@[to_additive]
instance map_isMulCommutative (f : G →* G') [IsMulCommutative H] : IsMulCommutative (H.map f) :=
  ⟨⟨by
      rintro ⟨-, a, ha, rfl⟩ ⟨-, b, hb, rfl⟩
      rw [Subtype.ext_iff, coe_mul, coe_mul, Subtype.coe_mk, Subtype.coe_mk, ← map_mul, ← map_mul]
      exact congr_arg f (Subtype.ext_iff.mp (mul_comm (⟨a, ha⟩ : H) ⟨b, hb⟩))⟩⟩

@[deprecated (since := "2025-04-09")] alias map_isCommutative := map_isMulCommutative
@[deprecated (since := "2025-04-09")] alias _root_.AddSubgroup.map_isCommutative :=
  AddSubgroup.map_isAddCommutative

@[to_additive]
theorem comap_injective_isMulCommutative {f : G' →* G} (hf : Injective f) [IsMulCommutative H] :
    IsMulCommutative (H.comap f) :=
  ⟨⟨fun a b =>
      Subtype.ext
        (by
          have := mul_comm (⟨f a, a.2⟩ : H) (⟨f b, b.2⟩ : H)
          rwa [Subtype.ext_iff, coe_mul, coe_mul, coe_mk, coe_mk, ← map_mul, ← map_mul,
            hf.eq_iff] at this)⟩⟩

@[deprecated (since := "2025-04-09")] alias comap_injective_isCommutative :=
  comap_injective_isMulCommutative
@[deprecated (since := "2025-04-09")] alias _root_.AddSubgroup.comap_injective_isCommutative :=
  AddSubgroup.comap_injective_isAddCommutative

@[to_additive]
instance subgroupOf_isMulCommutative [IsMulCommutative H] : IsMulCommutative (H.subgroupOf K) :=
  H.comap_injective_isMulCommutative Subtype.coe_injective

@[deprecated (since := "2025-04-09")] alias subgroupOf_isCommutative := subgroupOf_isMulCommutative
@[deprecated (since := "2025-04-09")] alias _root_.AddSubgroup.addSubgroupOf_isCommutative :=
  AddSubgroup.addSubgroupOf_isAddCommutative

end Subgroup

namespace MulEquiv
variable {H : Type*} [Group H]

/--
An isomorphism of groups gives an order isomorphism between the lattices of subgroups,
defined by sending subgroups to their inverse images.

See also `MulEquiv.mapSubgroup` which maps subgroups to their forward images.
-/
@[to_additive (attr := simps)
/-- An isomorphism of groups gives an order isomorphism between the lattices of subgroups,
defined by sending subgroups to their inverse images.

See also `AddEquiv.mapAddSubgroup` which maps subgroups to their forward images. -/]
def comapSubgroup (f : G ≃* H) : Subgroup H ≃o Subgroup G where
  toFun := Subgroup.comap f
  invFun := Subgroup.comap f.symm
  left_inv sg := by simp [Subgroup.comap_comap]
  right_inv sh := by simp [Subgroup.comap_comap]
  map_rel_iff' {sg1 sg2} :=
    ⟨fun h => by simpa [Subgroup.comap_comap] using
      Subgroup.comap_mono (f := (f.symm : H →* G)) h, Subgroup.comap_mono⟩

@[to_additive (attr := simp, norm_cast)]
lemma coe_comapSubgroup (e : G ≃* H) : comapSubgroup e = Subgroup.comap e.toMonoidHom := rfl

@[to_additive (attr := simp)]
lemma symm_comapSubgroup (e : G ≃* H) : (comapSubgroup e).symm = comapSubgroup e.symm := rfl

/--
An isomorphism of groups gives an order isomorphism between the lattices of subgroups,
defined by sending subgroups to their forward images.

See also `MulEquiv.comapSubgroup` which maps subgroups to their inverse images.
-/
@[to_additive (attr := simps)
/-- An isomorphism of groups gives an order isomorphism between the lattices of subgroups,
defined by sending subgroups to their forward images.

See also `AddEquiv.comapAddSubgroup` which maps subgroups to their inverse images. -/]
def mapSubgroup {H : Type*} [Group H] (f : G ≃* H) : Subgroup G ≃o Subgroup H where
  toFun := Subgroup.map f
  invFun := Subgroup.map f.symm
  left_inv sg := by simp [Subgroup.map_map]
  right_inv sh := by simp [Subgroup.map_map]
  map_rel_iff' {sg1 sg2} :=
    ⟨fun h => by simpa [Subgroup.map_map] using
      Subgroup.map_mono (f := (f.symm : H →* G)) h, Subgroup.map_mono⟩

@[to_additive (attr := simp, norm_cast)]
lemma coe_mapSubgroup (e : G ≃* H) : mapSubgroup e = Subgroup.map e.toMonoidHom := rfl

@[to_additive (attr := simp)]
lemma symm_mapSubgroup (e : G ≃* H) : (mapSubgroup e).symm = mapSubgroup e.symm := rfl

end MulEquiv

namespace Subgroup

open MonoidHom

variable {N : Type*} [Group N] (f : G →* N)

@[to_additive (attr := simp, norm_cast)]
lemma comap_toSubmonoid (e : G ≃* N) (s : Subgroup N) :
    (s.comap e).toSubmonoid = s.toSubmonoid.comap e.toMonoidHom := rfl

@[to_additive]
theorem map_comap_le (H : Subgroup N) : map f (comap f H) ≤ H :=
  (gc_map_comap f).l_u_le _

@[to_additive]
theorem le_comap_map (H : Subgroup G) : H ≤ comap f (map f H) :=
  (gc_map_comap f).le_u_l _

@[to_additive]
theorem map_eq_comap_of_inverse {f : G →* N} {g : N →* G} (hl : Function.LeftInverse g f)
    (hr : Function.RightInverse g f) (H : Subgroup G) : map f H = comap g H :=
  SetLike.ext' <| by rw [coe_map, coe_comap, Set.image_eq_preimage_of_inverse hl hr]

/-- A subgroup is isomorphic to its image under an injective function. If you have an isomorphism,
use `MulEquiv.subgroupMap` for better definitional equalities. -/
@[to_additive
      /-- An additive subgroup is isomorphic to its image under an injective function. If you
      have an isomorphism, use `AddEquiv.addSubgroupMap` for better definitional equalities. -/]
noncomputable def equivMapOfInjective (H : Subgroup G) (f : G →* N) (hf : Function.Injective f) :
    H ≃* H.map f :=
  { Equiv.Set.image f H hf with map_mul' := fun _ _ => Subtype.ext (f.map_mul _ _) }

@[to_additive (attr := simp)]
theorem coe_equivMapOfInjective_apply (H : Subgroup G) (f : G →* N) (hf : Function.Injective f)
    (h : H) : (equivMapOfInjective H f hf h : N) = f h :=
  rfl

end Subgroup

variable {N : Type*} [Group N]

namespace MonoidHom

/-- The `MonoidHom` from the preimage of a subgroup to itself. -/
@[to_additive (attr := simps!) /-- the `AddMonoidHom` from the preimage of an
additive subgroup to itself. -/]
def subgroupComap (f : G →* G') (H' : Subgroup G') : H'.comap f →* H' :=
  f.submonoidComap H'.toSubmonoid

@[to_additive]
lemma subgroupComap_surjective_of_surjective (f : G →* G') (H' : Subgroup G') (hf : Surjective f) :
    Surjective (f.subgroupComap H') :=
  f.submonoidComap_surjective_of_surjective H'.toSubmonoid hf

/-- The `MonoidHom` from a subgroup to its image. -/
@[to_additive (attr := simps!) /-- the `AddMonoidHom` from an additive subgroup to its image -/]
def subgroupMap (f : G →* G') (H : Subgroup G) : H →* H.map f :=
  f.submonoidMap H.toSubmonoid

@[to_additive]
theorem subgroupMap_surjective (f : G →* G') (H : Subgroup G) :
    Function.Surjective (f.subgroupMap H) :=
  f.submonoidMap_surjective H.toSubmonoid

end MonoidHom

namespace MulEquiv

variable {H K : Subgroup G}

/-- Makes the identity isomorphism from a proof two subgroups of a multiplicative
group are equal. -/
@[to_additive
      /-- Makes the identity additive isomorphism from a proof
      two subgroups of an additive group are equal. -/]
def subgroupCongr (h : H = K) : H ≃* K :=
  { Equiv.setCongr <| congr_arg _ h with map_mul' := fun _ _ => rfl }

@[to_additive (attr := simp)]
lemma subgroupCongr_apply (h : H = K) (x) :
    (MulEquiv.subgroupCongr h x : G) = x := rfl

@[to_additive (attr := simp)]
lemma subgroupCongr_symm_apply (h : H = K) (x) :
    ((MulEquiv.subgroupCongr h).symm x : G) = x := rfl

/-- A subgroup is isomorphic to its image under an isomorphism. If you only have an injective map,
use `Subgroup.equivMapOfInjective`. -/
@[to_additive
      /-- An additive subgroup is isomorphic to its image under an isomorphism. If you only
      have an injective map, use `AddSubgroup.equivMapOfInjective`. -/]
def subgroupMap (e : G ≃* G') (H : Subgroup G) : H ≃* H.map (e : G →* G') :=
  MulEquiv.submonoidMap (e : G ≃* G') H.toSubmonoid

@[to_additive (attr := simp)]
theorem coe_subgroupMap_apply (e : G ≃* G') (H : Subgroup G) (g : H) :
    ((subgroupMap e H g : H.map (e : G →* G')) : G') = e g :=
  rfl

@[to_additive (attr := simp)]
theorem subgroupMap_symm_apply (e : G ≃* G') (H : Subgroup G) (g : H.map (e : G →* G')) :
    (e.subgroupMap H).symm g = ⟨e.symm g, SetLike.mem_coe.1 <| Set.mem_image_equiv.1 g.2⟩ :=
  rfl

end MulEquiv

namespace MonoidHom

open Subgroup

@[to_additive]
theorem closure_preimage_le (f : G →* N) (s : Set N) : closure (f ⁻¹' s) ≤ (closure s).comap f :=
  (closure_le _).2 fun x hx => by rw [SetLike.mem_coe, mem_comap]; exact subset_closure hx

/-- The image under a monoid homomorphism of the subgroup generated by a set equals the subgroup
generated by the image of the set. -/
@[to_additive
      /-- The image under an `AddMonoid` hom of the `AddSubgroup` generated by a set equals
      the `AddSubgroup` generated by the image of the set. -/]
theorem map_closure (f : G →* N) (s : Set G) : (closure s).map f = closure (f '' s) :=
  Set.image_preimage.l_comm_of_u_comm (gc_map_comap f) (Subgroup.gi N).gc (Subgroup.gi G).gc
    fun _ ↦ rfl

@[to_additive]
lemma surjOn_iff_le_map {f : G →* N} {H : Subgroup G} {K : Subgroup N} :
    Set.SurjOn f H K ↔ K ≤ H.map f :=
  Iff.rfl

end MonoidHom

namespace Subgroup

@[to_additive (attr := simp)]
theorem equivMapOfInjective_coe_mulEquiv (H : Subgroup G) (e : G ≃* G') :
    H.equivMapOfInjective (e : G →* G') (EquivLike.injective e) = e.subgroupMap H := by
  ext
  rfl

end Subgroup
