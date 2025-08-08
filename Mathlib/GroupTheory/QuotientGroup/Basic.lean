/-
Copyright (c) 2018 Kevin Buzzard, Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Patrick Massot
-/
-- This file is to a certain extent based on `quotient_module.lean` by Johannes Hölzl.

import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.GroupTheory.Congruence.Hom
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# Quotients of groups by normal subgroups

This files develops the basic theory of quotients of groups by normal subgroups. In particular it
proves Noether's first and second isomorphism theorems.

## Main statements

* `QuotientGroup.quotientKerEquivRange`: Noether's first isomorphism theorem, an explicit
  isomorphism `G/ker φ → range φ` for every group homomorphism `φ : G →* H`.
* `QuotientGroup.quotientInfEquivProdNormalizerQuotient`: Noether's second isomorphism
  theorem, an explicit isomorphism between `H/(H ∩ N)` and `(HN)/N` given a subgroup `H`
  that lies in the normalizer `N_G(N)` of a subgroup `N` of a group `G`.
* `QuotientGroup.quotientQuotientEquivQuotient`: Noether's third isomorphism theorem,
  the canonical isomorphism between `(G / N) / (M / N)` and `G / M`, where `N ≤ M`.
* `QuotientGroup.comapMk'OrderIso`: The correspondence theorem, a lattice
  isomorphism between the lattice of subgroups of `G ⧸ N` and the sublattice
  of subgroups of `G` containing `N`.

## Tags

isomorphism theorems, quotient groups
-/

open Function
open scoped Pointwise

universe u v w x
namespace QuotientGroup

variable {G : Type u} [Group G] (N : Subgroup G) [nN : N.Normal] {H : Type v} [Group H]
  {M : Type x} [Monoid M]

open scoped Pointwise in
@[to_additive]
theorem sound (U : Set (G ⧸ N)) (g : N.op) :
    g • (mk' N) ⁻¹' U = (mk' N) ⁻¹' U := by
  ext x
  simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem]
  congr! 1
  exact Quotient.sound ⟨g⁻¹, rfl⟩

-- for commutative groups we don't need normality assumption

local notation " Q " => G ⧸ N

@[to_additive (attr := simp)]
theorem mk_prod {G ι : Type*} [CommGroup G] (N : Subgroup G) (s : Finset ι) {f : ι → G} :
    ((Finset.prod s f : G) : G ⧸ N) = Finset.prod s (fun i => (f i : G ⧸ N)) :=
  map_prod (QuotientGroup.mk' N) _ _

@[to_additive QuotientAddGroup.strictMono_comap_prod_map]
theorem strictMono_comap_prod_map :
    StrictMono fun H : Subgroup G ↦ (H.comap N.subtype, H.map (mk' N)) :=
  strictMono_comap_prod_image N

variable (φ : G →* H)

open MonoidHom

/-- The induced map from the quotient by the kernel to the codomain. -/
@[to_additive /-- The induced map from the quotient by the kernel to the codomain. -/]
def kerLift : G ⧸ ker φ →* H :=
  lift _ φ fun _g => mem_ker.mp

@[to_additive (attr := simp)]
theorem kerLift_mk (g : G) : (kerLift φ) g = φ g :=
  rfl

@[to_additive (attr := simp)]
theorem kerLift_mk' (g : G) : (kerLift φ) (mk g) = φ g :=
  lift_mk' _ _ _

@[to_additive]
theorem kerLift_injective : Injective (kerLift φ) := fun a b =>
  Quotient.inductionOn₂' a b fun a b (h : φ a = φ b) =>
    Quotient.sound' <| by rw [leftRel_apply, mem_ker, φ.map_mul, ← h, φ.map_inv, inv_mul_cancel]

-- Note that `ker φ` isn't definitionally `ker (φ.rangeRestrict)`
-- so there is a bit of annoying code duplication here
/-- The induced map from the quotient by the kernel to the range. -/
@[to_additive /-- The induced map from the quotient by the kernel to the range. -/]
def rangeKerLift : G ⧸ ker φ →* φ.range :=
  lift _ φ.rangeRestrict fun g hg => mem_ker.mp <| by rwa [ker_rangeRestrict]

@[to_additive]
theorem rangeKerLift_injective : Injective (rangeKerLift φ) := fun a b =>
  Quotient.inductionOn₂' a b fun a b (h : φ.rangeRestrict a = φ.rangeRestrict b) =>
    Quotient.sound' <| by
      rw [leftRel_apply, ← ker_rangeRestrict, mem_ker, φ.rangeRestrict.map_mul, ← h,
        φ.rangeRestrict.map_inv, inv_mul_cancel]

@[to_additive]
theorem rangeKerLift_surjective : Surjective (rangeKerLift φ) := by
  rintro ⟨_, g, rfl⟩
  use mk g
  rfl

/-- **Noether's first isomorphism theorem** (a definition): the canonical isomorphism between
`G/(ker φ)` to `range φ`. -/
@[to_additive /-- The first isomorphism theorem (a definition): the canonical isomorphism between
`G/(ker φ)` to `range φ`. -/]
noncomputable def quotientKerEquivRange : G ⧸ ker φ ≃* range φ :=
  MulEquiv.ofBijective (rangeKerLift φ) ⟨rangeKerLift_injective φ, rangeKerLift_surjective φ⟩

/-- The canonical isomorphism `G/(ker φ) ≃* H` induced by a homomorphism `φ : G →* H`
with a right inverse `ψ : H → G`. -/
@[to_additive (attr := simps) /-- The canonical isomorphism `G/(ker φ) ≃+ H` induced by a
homomorphism `φ : G →+ H` with a right inverse `ψ : H → G`. -/]
def quotientKerEquivOfRightInverse (ψ : H → G) (hφ : RightInverse ψ φ) : G ⧸ ker φ ≃* H :=
  { kerLift φ with
    toFun := kerLift φ
    invFun := mk ∘ ψ
    left_inv := fun x => kerLift_injective φ (by rw [Function.comp_apply, kerLift_mk', hφ])
    right_inv := hφ }

/-- The canonical isomorphism `G/⊥ ≃* G`. -/
@[to_additive (attr := simps!) /-- The canonical isomorphism `G/⊥ ≃+ G`. -/]
def quotientBot : G ⧸ (⊥ : Subgroup G) ≃* G :=
  quotientKerEquivOfRightInverse (MonoidHom.id G) id fun _x => rfl

/-- The canonical isomorphism `G/(ker φ) ≃* H` induced by a surjection `φ : G →* H`.

For a `computable` version, see `QuotientGroup.quotientKerEquivOfRightInverse`.
-/
@[to_additive /-- The canonical isomorphism `G/(ker φ) ≃+ H` induced by a surjection `φ : G →+ H`.
For a `computable` version, see `QuotientAddGroup.quotientKerEquivOfRightInverse`. -/]
noncomputable def quotientKerEquivOfSurjective (hφ : Surjective φ) : G ⧸ ker φ ≃* H :=
  quotientKerEquivOfRightInverse φ _ hφ.hasRightInverse.choose_spec

/-- If two normal subgroups `M` and `N` of `G` are the same, their quotient groups are
isomorphic. -/
@[to_additive /-- If two normal subgroups `M` and `N` of `G` are the same, their quotient groups are
isomorphic. -/]
def quotientMulEquivOfEq {M N : Subgroup G} [M.Normal] [N.Normal] (h : M = N) : G ⧸ M ≃* G ⧸ N :=
  { Subgroup.quotientEquivOfEq h with
    map_mul' := fun q r => Quotient.inductionOn₂' q r fun _g _h => rfl }

@[to_additive (attr := simp)]
theorem quotientMulEquivOfEq_mk {M N : Subgroup G} [M.Normal] [N.Normal] (h : M = N) (x : G) :
    QuotientGroup.quotientMulEquivOfEq h (QuotientGroup.mk x) = QuotientGroup.mk x :=
  rfl

/-- Let `A', A, B', B` be subgroups of `G`. If `A' ≤ B'` and `A ≤ B`,
then there is a map `A / (A' ⊓ A) →* B / (B' ⊓ B)` induced by the inclusions. -/
@[to_additive /-- Let `A', A, B', B` be subgroups of `G`. If `A' ≤ B'` and `A ≤ B`, then there is a
map `A / (A' ⊓ A) →+ B / (B' ⊓ B)` induced by the inclusions. -/]
def quotientMapSubgroupOfOfLe {A' A B' B : Subgroup G} [_hAN : (A'.subgroupOf A).Normal]
    [_hBN : (B'.subgroupOf B).Normal] (h' : A' ≤ B') (h : A ≤ B) :
    A ⧸ A'.subgroupOf A →* B ⧸ B'.subgroupOf B :=
  map _ _ (Subgroup.inclusion h) <| Subgroup.comap_mono h'

@[to_additive (attr := simp)]
theorem quotientMapSubgroupOfOfLe_mk {A' A B' B : Subgroup G} [_hAN : (A'.subgroupOf A).Normal]
    [_hBN : (B'.subgroupOf B).Normal] (h' : A' ≤ B') (h : A ≤ B) (x : A) :
    quotientMapSubgroupOfOfLe h' h x = ↑(Subgroup.inclusion h x : B) :=
  rfl

/-- Let `A', A, B', B` be subgroups of `G`.
If `A' = B'` and `A = B`, then the quotients `A / (A' ⊓ A)` and `B / (B' ⊓ B)` are isomorphic.

Applying this equiv is nicer than rewriting along the equalities, since the type of
`(A'.subgroupOf A : Subgroup A)` depends on `A`.
-/
@[to_additive /-- Let `A', A, B', B` be subgroups of `G`. If `A' = B'` and `A = B`, then the
quotients `A / (A' ⊓ A)` and `B / (B' ⊓ B)` are isomorphic. Applying this equiv is nicer than
rewriting along the equalities, since the type of `(A'.addSubgroupOf A : AddSubgroup A)` depends on
`A`. -/]
def equivQuotientSubgroupOfOfEq {A' A B' B : Subgroup G} [hAN : (A'.subgroupOf A).Normal]
    [hBN : (B'.subgroupOf B).Normal] (h' : A' = B') (h : A = B) :
    A ⧸ A'.subgroupOf A ≃* B ⧸ B'.subgroupOf B :=
  (quotientMapSubgroupOfOfLe h'.le h.le).toMulEquiv (quotientMapSubgroupOfOfLe h'.ge h.ge)
    (by ext ⟨x, hx⟩; rfl)
    (by ext ⟨x, hx⟩; rfl)

section ZPow

variable {A B C : Type u} [CommGroup A] [CommGroup B] [CommGroup C]
variable (f : A →* B) (g : B →* A) (e : A ≃* B) (d : B ≃* C) (n : ℤ)

/-- The map of quotients by powers of an integer induced by a group homomorphism. -/
@[to_additive /-- The map of quotients by multiples of an integer induced by an additive group
homomorphism. -/]
def homQuotientZPowOfHom :
    A ⧸ (zpowGroupHom n : A →* A).range →* B ⧸ (zpowGroupHom n : B →* B).range :=
  lift _ ((mk' _).comp f) fun g ⟨h, (hg : h ^ n = g)⟩ =>
    (eq_one_iff _).mpr ⟨f h, by
      simp only [← hg, map_zpow, zpowGroupHom_apply]⟩

@[to_additive (attr := simp)]
theorem homQuotientZPowOfHom_id : homQuotientZPowOfHom (MonoidHom.id A) n = MonoidHom.id _ :=
  monoidHom_ext _ rfl

@[to_additive (attr := simp)]
theorem homQuotientZPowOfHom_comp :
    homQuotientZPowOfHom (f.comp g) n =
      (homQuotientZPowOfHom f n).comp (homQuotientZPowOfHom g n) :=
  monoidHom_ext _ rfl

@[to_additive (attr := simp)]
theorem homQuotientZPowOfHom_comp_of_rightInverse (i : Function.RightInverse g f) :
    (homQuotientZPowOfHom f n).comp (homQuotientZPowOfHom g n) = MonoidHom.id _ :=
  monoidHom_ext _ <| MonoidHom.ext fun x => congrArg _ <| i x

/-- The equivalence of quotients by powers of an integer induced by a group isomorphism. -/
@[to_additive /-- The equivalence of quotients by multiples of an integer induced by an additive
group isomorphism. -/]
def equivQuotientZPowOfEquiv :
    A ⧸ (zpowGroupHom n : A →* A).range ≃* B ⧸ (zpowGroupHom n : B →* B).range :=
  MonoidHom.toMulEquiv _ _
    (homQuotientZPowOfHom_comp_of_rightInverse (e.symm : B →* A) (e : A →* B) n e.left_inv)
    (homQuotientZPowOfHom_comp_of_rightInverse (e : A →* B) (e.symm : B →* A) n e.right_inv)
    -- Porting note: had to explicitly coerce the `MulEquiv`s to `MonoidHom`s

@[to_additive (attr := simp)]
theorem equivQuotientZPowOfEquiv_refl :
    MulEquiv.refl (A ⧸ (zpowGroupHom n : A →* A).range) =
      equivQuotientZPowOfEquiv (MulEquiv.refl A) n := by
  ext x
  rw [← Quotient.out_eq' x]
  rfl

@[to_additive (attr := simp)]
theorem equivQuotientZPowOfEquiv_symm :
    (equivQuotientZPowOfEquiv e n).symm = equivQuotientZPowOfEquiv e.symm n :=
  rfl

@[to_additive (attr := simp)]
theorem equivQuotientZPowOfEquiv_trans :
    (equivQuotientZPowOfEquiv e n).trans (equivQuotientZPowOfEquiv d n) =
      equivQuotientZPowOfEquiv (e.trans d) n := by
  ext x
  rw [← Quotient.out_eq' x]
  rfl

end ZPow

section SndIsomorphismThm

open Subgroup

/-- **Noether's second isomorphism theorem**: given a subgroup `N` of `G` and a
subgroup `H` of the normalizer of `N` in `G`,
defines an isomorphism between `H/(H ∩ N)` and `(HN)/N`. -/
@[to_additive /-- Noether's second isomorphism theorem: given a subgroup `N` of `G` and a
subgroup `H` of the normalizer of `N` in `G`,
defines an isomorphism between `H/(H ∩ N)` and `(H + N)/N` -/]
noncomputable def quotientInfEquivProdNormalizerQuotient (H N : Subgroup G)
    (hLE : H ≤ N.normalizer) :
    letI := Subgroup.normal_subgroupOf_of_le_normalizer hLE
    letI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hLE
    H ⧸ N.subgroupOf H ≃* (H ⊔ N : Subgroup G) ⧸ N.subgroupOf (H ⊔ N) :=
  letI := Subgroup.normal_subgroupOf_of_le_normalizer hLE
  letI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hLE
  let
    φ :-- φ is the natural homomorphism H →* (HN)/N.
      H →*
      _ ⧸ N.subgroupOf (H ⊔ N) :=
    (mk' <| N.subgroupOf (H ⊔ N)).comp (inclusion le_sup_left)
  have φ_surjective : Surjective φ := fun x =>
    x.inductionOn' <| by
      rintro ⟨y, hy : y ∈ (H ⊔ N)⟩
      rw [← SetLike.mem_coe] at hy
      rw [coe_mul_of_left_le_normalizer_right H N hLE] at hy
      rcases hy with ⟨h, hh, n, hn, rfl⟩
      use ⟨h, hh⟩
      let _ : Setoid ↑(H ⊔ N) :=
        (@leftRel ↑(H ⊔ N) (H ⊔ N : Subgroup G).toGroup (N.subgroupOf (H ⊔ N)))
      -- Porting note: Lean couldn't find this automatically
      refine Quotient.eq.mpr ?_
      change leftRel _ _ _
      rw [leftRel_apply]
      change h⁻¹ * (h * n) ∈ N
      rwa [← mul_assoc, inv_mul_cancel, one_mul]
  (quotientMulEquivOfEq (by simp [φ, ← comap_ker])).trans
    (quotientKerEquivOfSurjective φ φ_surjective)

/-- **Noether's second isomorphism theorem**: given two subgroups `H` and `N` of a group `G`,
where `N` is normal, defines an isomorphism between `H/(H ∩ N)` and `(HN)/N`. -/
@[to_additive /-- Noether's second isomorphism theorem: given two subgroups `H` and `N` of a group
`G`, where `N` is normal, defines an isomorphism between `H/(H ∩ N)` and `(H + N)/N`. -/]
noncomputable def quotientInfEquivProdNormalQuotient (H N : Subgroup G) [hN : N.Normal] :
    H ⧸ N.subgroupOf H ≃* (H ⊔ N : Subgroup G) ⧸ N.subgroupOf (H ⊔ N) :=
  quotientInfEquivProdNormalizerQuotient H N le_normalizer_of_normal

end SndIsomorphismThm

section ThirdIsoThm

variable (M : Subgroup G) [nM : M.Normal]

@[to_additive]
instance map_normal : (M.map (QuotientGroup.mk' N)).Normal :=
  nM.map _ mk_surjective

variable (h : N ≤ M)

/-- The map from the third isomorphism theorem for groups: `(G / N) / (M / N) → G / M`. -/
@[to_additive /-- The map from the third isomorphism theorem for additive groups:
`(A / N) / (M / N) → A / M`. -/]
def quotientQuotientEquivQuotientAux : (G ⧸ N) ⧸ M.map (mk' N) →* G ⧸ M :=
  lift (M.map (mk' N)) (map N M (MonoidHom.id G) h)
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [mem_ker, map_mk' N M _ _ x]
      exact (QuotientGroup.eq_one_iff _).mpr hx)

@[to_additive (attr := simp)]
theorem quotientQuotientEquivQuotientAux_mk (x : G ⧸ N) :
    quotientQuotientEquivQuotientAux N M h x = QuotientGroup.map N M (MonoidHom.id G) h x :=
  QuotientGroup.lift_mk' _ _ x

@[to_additive]
theorem quotientQuotientEquivQuotientAux_mk_mk (x : G) :
    quotientQuotientEquivQuotientAux N M h (x : G ⧸ N) = x :=
  QuotientGroup.lift_mk' (M.map (mk' N)) _ x

/-- **Noether's third isomorphism theorem** for groups: `(G / N) / (M / N) ≃* G / M`. -/
@[to_additive
/-- **Noether's third isomorphism theorem** for additive groups: `(A / N) / (M / N) ≃+ A / M`. -/]
def quotientQuotientEquivQuotient : (G ⧸ N) ⧸ M.map (QuotientGroup.mk' N) ≃* G ⧸ M :=
  MonoidHom.toMulEquiv (quotientQuotientEquivQuotientAux N M h)
    (QuotientGroup.map _ _ (QuotientGroup.mk' N) (Subgroup.le_comap_map _ _))
    (by ext; simp)
    (by ext; simp)

end ThirdIsoThm

section CorrespTheorem

-- All these theorems are primed because `QuotientGroup.mk'` is.
set_option linter.docPrime false

@[to_additive]
theorem le_comap_mk' (N : Subgroup G) [N.Normal] (H : Subgroup (G ⧸ N)) :
    N ≤ Subgroup.comap (QuotientGroup.mk' N) H := by
  simpa using Subgroup.comap_mono (f := mk' N) bot_le

@[to_additive (attr := simp)]
theorem comap_map_mk' (N H : Subgroup G) [N.Normal] :
    Subgroup.comap (mk' N) (Subgroup.map (mk' N) H) = N ⊔ H := by
  simp [Subgroup.comap_map_eq, sup_comm]

/-- The **correspondence theorem**, or lattice theorem,
or fourth isomorphism theorem for multiplicative groups -/
@[to_additive /-- The **correspondence theorem**, or lattice theorem,
  or fourth isomorphism theorem for additive groups -/]
def comapMk'OrderIso (N : Subgroup G) [hn : N.Normal] :
    Subgroup (G ⧸ N) ≃o { H : Subgroup G // N ≤ H } where
  toFun H' := ⟨Subgroup.comap (mk' N) H', le_comap_mk' N _⟩
  invFun H := Subgroup.map (mk' N) H
  left_inv H' := Subgroup.map_comap_eq_self <| by simp
  right_inv := fun ⟨H, hH⟩ => Subtype.ext_val <| by simpa
  map_rel_iff' := Subgroup.comap_le_comap_of_surjective <| mk'_surjective _

end CorrespTheorem

section trivial

@[to_additive]
theorem subsingleton_quotient_top : Subsingleton (G ⧸ (⊤ : Subgroup G)) := by
  dsimp [HasQuotient.Quotient, QuotientGroup.instHasQuotientSubgroup, Quotient]
  rw [leftRel_eq]
  exact Trunc.instSubsingletonTrunc

/-- If the quotient by a subgroup gives a singleton then the subgroup is the whole group. -/
@[to_additive /-- If the quotient by an additive subgroup gives a singleton then the additive
subgroup is the whole additive group. -/]
theorem subgroup_eq_top_of_subsingleton (H : Subgroup G) (h : Subsingleton (G ⧸ H)) : H = ⊤ :=
  top_unique fun x _ => by
    have this : 1⁻¹ * x ∈ H := QuotientGroup.eq.1 (Subsingleton.elim _ _)
    rwa [inv_one, one_mul] at this

end trivial

@[to_additive]
theorem comap_comap_center {H₁ : Subgroup G} [H₁.Normal] {H₂ : Subgroup (G ⧸ H₁)} [H₂.Normal] :
    ((Subgroup.center ((G ⧸ H₁) ⧸ H₂)).comap (mk' H₂)).comap (mk' H₁) =
      (Subgroup.center (G ⧸ H₂.comap (mk' H₁))).comap (mk' (H₂.comap (mk' H₁))) := by
  ext x
  simp only [mk'_apply, Subgroup.mem_comap, Subgroup.mem_center_iff, forall_mk, ← mk_mul,
    eq_iff_div_mem, mk_div]

end QuotientGroup

namespace QuotientAddGroup

variable {R : Type*} [NonAssocRing R] (N : AddSubgroup R) [N.Normal]

@[simp]
theorem mk_nat_mul (n : ℕ) (a : R) : ((n * a : R) : R ⧸ N) = n • ↑a := by
  rw [← nsmul_eq_mul, mk_nsmul N a n]

@[simp]
theorem mk_int_mul (n : ℤ) (a : R) : ((n * a : R) : R ⧸ N) = n • ↑a := by
  rw [← zsmul_eq_mul, mk_zsmul N a n]

end QuotientAddGroup
