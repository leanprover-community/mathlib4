/-
Copyright (c) 2018 Kevin Buzzard, Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Patrick Massot
-/
-- This file is to a certain extent based on `quotient_module.lean` by Johannes Hölzl.

import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.GroupTheory.Congruence.Hom
import Mathlib.GroupTheory.Coset.Defs

/-!
# Quotients of groups by normal subgroups

This file defines the group structure on the quotient by a normal subgroup.

## Main definitions

* `QuotientGroup.Quotient.Group`: the group structure on `G/N` given a normal subgroup `N` of `G`.
* `mk'`: the canonical group homomorphism `G →* G/N` given a normal subgroup `N` of `G`.
* `lift φ`: the group homomorphism `G/N →* H` given a group homomorphism `φ : G →* H` such that
  `N ⊆ ker φ`.
* `map f`: the group homomorphism `G/N →* H/M` given a group homomorphism `f : G →* H` such that
  `N ⊆ f⁻¹(M)`.

## Tags

quotient groups
-/

open Function
open scoped Pointwise

universe u v w x
namespace QuotientGroup

variable {G : Type u} [Group G] (N : Subgroup G) [nN : N.Normal] {H : Type v} [Group H]
  {M : Type x} [Monoid M]

/-- The congruence relation generated by a normal subgroup. -/
@[to_additive "The additive congruence relation generated by a normal additive subgroup."]
protected def con : Con G where
  toSetoid := leftRel N
  mul' := fun {a b c d} hab hcd => by
    rw [leftRel_eq] at hab hcd ⊢
    dsimp only
    calc
      c⁻¹ * (a⁻¹ * b) * c⁻¹⁻¹ * (c⁻¹ * d) ∈ N := N.mul_mem (nN.conj_mem _ hab _) hcd
      _ = (a * c)⁻¹ * (b * d) := by
        simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left]

@[to_additive]
instance Quotient.group : Group (G ⧸ N) :=
  (QuotientGroup.con N).group

/--
The congruence relation defined by the kernel of a group homomorphism is equal to its kernel
as a congruence relation.
-/
@[to_additive QuotientAddGroup.con_ker_eq_addConKer
"The additive congruence relation defined by the kernel of an additive group homomorphism is
equal to its kernel as an additive congruence relation."]
theorem con_ker_eq_conKer (f : G →* M) : QuotientGroup.con f.ker = Con.ker f := by
  ext
  rw [QuotientGroup.con, Con.rel_mk, Setoid.comm', leftRel_apply, Con.ker_rel, MonoidHom.eq_iff]

/-- The group homomorphism from `G` to `G/N`. -/
@[to_additive "The additive group homomorphism from `G` to `G/N`."]
def mk' : G →* G ⧸ N :=
  MonoidHom.mk' QuotientGroup.mk fun _ _ => rfl

@[to_additive (attr := simp)]
theorem coe_mk' : (mk' N : G → G ⧸ N) = mk :=
  rfl

@[to_additive (attr := simp)]
theorem mk'_apply (x : G) : mk' N x = x :=
  rfl

@[to_additive]
theorem mk'_surjective : Surjective <| mk' N :=
  @mk_surjective _ _ N

@[to_additive]
theorem mk'_eq_mk' {x y : G} : mk' N x = mk' N y ↔ ∃ z ∈ N, x * z = y :=
  QuotientGroup.eq.trans <| by
    simp only [← _root_.eq_inv_mul_iff_mul_eq, exists_prop, exists_eq_right]

/-- Two `MonoidHom`s from a quotient group are equal if their compositions with
`QuotientGroup.mk'` are equal.

See note [partially-applied ext lemmas]. -/
@[to_additive (attr := ext 1100) "Two `AddMonoidHom`s from an additive quotient group are equal if
 their compositions with `AddQuotientGroup.mk'` are equal.

 See note [partially-applied ext lemmas]. "]
theorem monoidHom_ext ⦃f g : G ⧸ N →* M⦄ (h : f.comp (mk' N) = g.comp (mk' N)) : f = g :=
  MonoidHom.ext fun x => QuotientGroup.induction_on x <| (DFunLike.congr_fun h :)

@[to_additive (attr := simp)]
theorem eq_one_iff {N : Subgroup G} [N.Normal] (x : G) : (x : G ⧸ N) = 1 ↔ x ∈ N := by
  refine QuotientGroup.eq.trans ?_
  rw [mul_one, Subgroup.inv_mem_iff]

/- Note: `range_mk'` is a lemma about the primed constructor `QuotientGroup.mk'`, not a
  modified version of some `range_mk`. -/
set_option linter.docPrime false in
@[to_additive (attr := simp)]
theorem range_mk' : (QuotientGroup.mk' N).range = ⊤ :=
  MonoidHom.range_eq_top.mpr (mk'_surjective N)

@[to_additive]
theorem ker_le_range_iff {I : Type w} [MulOneClass I] (f : G →* H) [f.range.Normal] (g : H →* I) :
    g.ker ≤ f.range ↔ (mk' f.range).comp g.ker.subtype = 1 :=
  ⟨fun h => MonoidHom.ext fun ⟨_, hx⟩ => (eq_one_iff _).mpr <| h hx,
    fun h x hx => (eq_one_iff _).mp <| by exact DFunLike.congr_fun h ⟨x, hx⟩⟩

@[to_additive (attr := simp)]
theorem ker_mk' : MonoidHom.ker (QuotientGroup.mk' N : G →* G ⧸ N) = N :=
  Subgroup.ext eq_one_iff
-- Porting note: I think this is misnamed without the prime

@[to_additive]
theorem eq_iff_div_mem {N : Subgroup G} [nN : N.Normal] {x y : G} :
    (x : G ⧸ N) = y ↔ x / y ∈ N := by
  refine eq_comm.trans (QuotientGroup.eq.trans ?_)
  rw [nN.mem_comm_iff, div_eq_mul_inv]

-- for commutative groups we don't need normality assumption

@[to_additive]
instance Quotient.commGroup {G : Type*} [CommGroup G] (N : Subgroup G) : CommGroup (G ⧸ N) :=
  { toGroup := have := N.normal_of_comm; QuotientGroup.Quotient.group N
    mul_comm := fun a b => Quotient.inductionOn₂' a b fun a b => congr_arg mk (mul_comm a b) }

local notation " Q " => G ⧸ N

@[to_additive (attr := simp)]
theorem mk_one : ((1 : G) : Q) = 1 :=
  rfl

@[to_additive (attr := simp)]
theorem mk_mul (a b : G) : ((a * b : G) : Q) = a * b :=
  rfl

@[to_additive (attr := simp)]
theorem mk_inv (a : G) : ((a⁻¹ : G) : Q) = (a : Q)⁻¹ :=
  rfl

@[to_additive (attr := simp)]
theorem mk_div (a b : G) : ((a / b : G) : Q) = a / b :=
  rfl

@[to_additive (attr := simp)]
theorem mk_pow (a : G) (n : ℕ) : ((a ^ n : G) : Q) = (a : Q) ^ n :=
  rfl

@[to_additive (attr := simp)]
theorem mk_zpow (a : G) (n : ℤ) : ((a ^ n : G) : Q) = (a : Q) ^ n :=
  rfl

@[to_additive (attr := simp)] lemma map_mk'_self : N.map (mk' N) = ⊥ := by aesop

/--
The subgroup defined by the class of `1` for a congruence relation on a group.
-/
@[to_additive
"The `AddSubgroup` defined by the class of `0` for an additive congruence relation
on an `AddGroup`."]
protected def _root_.Con.subgroup (c : Con G) : Subgroup G where
  carrier := { x | c x 1 }
  one_mem' := c.refl 1
  mul_mem' hx hy := by simpa using c.mul hx hy
  inv_mem' h := by simpa using c.inv h

@[to_additive (attr := simp)]
theorem _root_.Con.mem_subgroup_iff {c : Con G} {x : G} :
    x ∈ c.subgroup ↔ c x 1 := Iff.rfl

@[to_additive]
instance (c : Con G) : c.subgroup.Normal :=
  ⟨fun x hx g ↦ by simpa using (c.mul (c.mul (c.refl g) hx) (c.refl g⁻¹))⟩

@[to_additive (attr := simp)]
theorem _root_.Con.subgroup_quotientGroupCon (H : Subgroup G) [H.Normal] :
    (QuotientGroup.con H).subgroup = H := by
  ext
  simp [QuotientGroup.con, leftRel_apply]

@[to_additive (attr := simp)]
theorem con_subgroup (c : Con G) :
    QuotientGroup.con c.subgroup = c := by
  ext x y
  rw [QuotientGroup.con, Con.rel_mk, leftRel_apply, Con.mem_subgroup_iff]
  exact ⟨fun h ↦ by simpa using c.mul (c.refl x) (c.symm h),
    fun h ↦ by simpa using c.mul (c.refl x⁻¹) (c.symm h)⟩

/--
The normal subgroups correspond to the congruence relations on a group.
-/
@[to_additive (attr := simps) AddSubgroup.orderIsoAddCon
"The normal subgroups correspond to the additive congruence relations on an `AddGroup`."]
def _root_.Subgroup.orderIsoCon :
    { N : Subgroup G // N.Normal } ≃o Con G where
  toFun N := letI : N.val.Normal := N.prop; QuotientGroup.con N
  invFun c := ⟨c.subgroup, inferInstance⟩
  left_inv := fun ⟨N, _⟩ ↦ Subtype.mk_eq_mk.mpr (Con.subgroup_quotientGroupCon N)
  right_inv c := QuotientGroup.con_subgroup c
  map_rel_iff' := by
    simp only [QuotientGroup.con, Equiv.coe_fn_mk, Con.le_def, Con.rel_mk, leftRel_apply]
    refine ⟨fun h x _ ↦ ?_, fun hle _ _ h ↦ hle h⟩
    specialize @h 1 x
    simp_all

@[to_additive (attr := simp)]
lemma con_le_iff {N M : Subgroup G} [N.Normal] [M.Normal] :
    QuotientGroup.con N ≤ QuotientGroup.con M ↔ N ≤ M :=
  (Subgroup.orderIsoCon.map_rel_iff (a := ⟨N, inferInstance⟩) (b := ⟨M, inferInstance⟩))

@[to_additive (attr := gcongr)]
lemma con_mono {N M : Subgroup G} [hN : N.Normal] [hM : M.Normal] (h : N ≤ M) :
    QuotientGroup.con N ≤ QuotientGroup.con M :=
  con_le_iff.mpr h

/-- A group homomorphism `φ : G →* M` with `N ⊆ ker(φ)` descends (i.e. `lift`s) to a
group homomorphism `G/N →* M`. -/
@[to_additive "An `AddGroup` homomorphism `φ : G →+ M` with `N ⊆ ker(φ)` descends (i.e. `lift`s)
 to a group homomorphism `G/N →* M`."]
def lift (φ : G →* M) (HN : N ≤ φ.ker) : Q →* M :=
  (QuotientGroup.con N).lift φ <| con_ker_eq_conKer φ ▸ con_mono HN

@[to_additive (attr := simp)]
theorem lift_mk {φ : G →* M} (HN : N ≤ φ.ker) (g : G) : lift N φ HN (g : Q) = φ g :=
  rfl

@[to_additive (attr := simp)]
theorem lift_mk' {φ : G →* M} (HN : N ≤ φ.ker) (g : G) : lift N φ HN (mk g : Q) = φ g :=
  rfl
-- TODO: replace `mk` with `mk'`)

@[to_additive (attr := simp)]
theorem lift_quot_mk {φ : G →* M} (HN : N ≤ φ.ker) (g : G) :
    lift N φ HN (Quot.mk _ g : Q) = φ g :=
  rfl

/-- A group homomorphism `f : G →* H` induces a map `G/N →* H/M` if `N ⊆ f⁻¹(M)`. -/
@[to_additive
      "An `AddGroup` homomorphism `f : G →+ H` induces a map `G/N →+ H/M` if `N ⊆ f⁻¹(M)`."]
def map (M : Subgroup H) [M.Normal] (f : G →* H) (h : N ≤ M.comap f) : G ⧸ N →* H ⧸ M := by
  refine QuotientGroup.lift N ((mk' M).comp f) ?_
  intro x hx
  refine QuotientGroup.eq.2 ?_
  rw [mul_one, Subgroup.inv_mem_iff]
  exact h hx

@[to_additive (attr := simp)]
theorem map_mk (M : Subgroup H) [M.Normal] (f : G →* H) (h : N ≤ M.comap f) (x : G) :
    map N M f h ↑x = ↑(f x) :=
  rfl

@[to_additive]
theorem map_mk' (M : Subgroup H) [M.Normal] (f : G →* H) (h : N ≤ M.comap f) (x : G) :
    map N M f h (mk' _ x) = ↑(f x) :=
  rfl

@[to_additive]
theorem map_id_apply (h : N ≤ Subgroup.comap (MonoidHom.id _) N := (Subgroup.comap_id N).le) (x) :
    map N N (MonoidHom.id _) h x = x :=
  induction_on x fun _x => rfl

@[to_additive (attr := simp)]
theorem map_id (h : N ≤ Subgroup.comap (MonoidHom.id _) N := (Subgroup.comap_id N).le) :
    map N N (MonoidHom.id _) h = MonoidHom.id _ :=
  MonoidHom.ext (map_id_apply N h)

@[to_additive (attr := simp)]
theorem map_map {I : Type*} [Group I] (M : Subgroup H) (O : Subgroup I) [M.Normal] [O.Normal]
    (f : G →* H) (g : H →* I) (hf : N ≤ Subgroup.comap f M) (hg : M ≤ Subgroup.comap g O)
    (hgf : N ≤ Subgroup.comap (g.comp f) O :=
      hf.trans ((Subgroup.comap_mono hg).trans_eq (Subgroup.comap_comap _ _ _)))
    (x : G ⧸ N) : map M O g hg (map N M f hf x) = map N O (g.comp f) hgf x := by
  refine induction_on x fun x => ?_
  simp only [map_mk, MonoidHom.comp_apply]

@[to_additive (attr := simp)]
theorem map_comp_map {I : Type*} [Group I] (M : Subgroup H) (O : Subgroup I) [M.Normal] [O.Normal]
    (f : G →* H) (g : H →* I) (hf : N ≤ Subgroup.comap f M) (hg : M ≤ Subgroup.comap g O)
    (hgf : N ≤ Subgroup.comap (g.comp f) O :=
      hf.trans ((Subgroup.comap_mono hg).trans_eq (Subgroup.comap_comap _ _ _))) :
    (map M O g hg).comp (map N M f hf) = map N O (g.comp f) hgf :=
  MonoidHom.ext (map_map N M O f g hf hg hgf)

section Pointwise
open Set

@[to_additive (attr := simp)] lemma image_coe : ((↑) : G → Q) '' N = 1 :=
  congr_arg ((↑) : Subgroup Q → Set Q) <| map_mk'_self N

@[to_additive]
lemma preimage_image_coe (s : Set G) : ((↑) : G → Q) ⁻¹' ((↑) '' s) = N * s := by
  ext a
  constructor
  · rintro ⟨b, hb, h⟩
    refine ⟨a / b, (QuotientGroup.eq_one_iff _).1 ?_, b, hb, div_mul_cancel _ _⟩
    simp only [h, QuotientGroup.mk_div, div_self']
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨b, hb, ?_⟩
    simpa only [QuotientGroup.mk_mul, right_eq_mul, QuotientGroup.eq_one_iff]

@[to_additive]
lemma image_coe_inj {s t : Set G} : ((↑) : G → Q) '' s = ((↑) : G → Q) '' t ↔ ↑N * s = N * t := by
  simp_rw [← preimage_image_coe]
  exact QuotientGroup.mk_surjective.preimage_injective.eq_iff.symm

end Pointwise

section congr

variable (G' : Subgroup G) (H' : Subgroup H) [Subgroup.Normal G'] [Subgroup.Normal H']

/-- `QuotientGroup.congr` lifts the isomorphism `e : G ≃ H` to `G ⧸ G' ≃ H ⧸ H'`,
given that `e` maps `G` to `H`. -/
@[to_additive "`QuotientAddGroup.congr` lifts the isomorphism `e : G ≃ H` to `G ⧸ G' ≃ H ⧸ H'`,
 given that `e` maps `G` to `H`."]
def congr (e : G ≃* H) (he : G'.map e = H') : G ⧸ G' ≃* H ⧸ H' :=
  { map G' H' e (he ▸ G'.le_comap_map (e : G →* H)) with
    toFun := map G' H' e (he ▸ G'.le_comap_map (e : G →* H))
    invFun := map H' G' e.symm (he ▸ (G'.map_equiv_eq_comap_symm e).le)
    left_inv := fun x => by
      rw [map_map G' H' G' e e.symm (he ▸ G'.le_comap_map (e : G →* H))
        (he ▸ (G'.map_equiv_eq_comap_symm e).le)]
      simp only [map_map, ← MulEquiv.coe_monoidHom_trans, MulEquiv.self_trans_symm,
        MulEquiv.coe_monoidHom_refl, map_id_apply]
    right_inv := fun x => by
      rw [map_map H' G' H' e.symm e (he ▸ (G'.map_equiv_eq_comap_symm e).le)
        (he ▸ G'.le_comap_map (e : G →* H)) ]
      simp only [← MulEquiv.coe_monoidHom_trans, MulEquiv.symm_trans_self,
        MulEquiv.coe_monoidHom_refl, map_id_apply] }

@[simp]
theorem congr_mk (e : G ≃* H) (he : G'.map ↑e = H') (x) : congr G' H' e he (mk x) = e x :=
  rfl

theorem congr_mk' (e : G ≃* H) (he : G'.map ↑e = H') (x) :
    congr G' H' e he (mk' G' x) = mk' H' (e x) :=
  rfl

@[simp]
theorem congr_apply (e : G ≃* H) (he : G'.map ↑e = H') (x : G) :
    congr G' H' e he x = mk' H' (e x) :=
  rfl

@[simp]
theorem congr_refl (he : G'.map (MulEquiv.refl G : G →* G) = G' := Subgroup.map_id G') :
    congr G' G' (MulEquiv.refl G) he = MulEquiv.refl (G ⧸ G') := by
  ext ⟨x⟩
  rfl

@[simp]
theorem congr_symm (e : G ≃* H) (he : G'.map ↑e = H') :
    (congr G' H' e he).symm = congr H' G' e.symm ((Subgroup.map_symm_eq_iff_map_eq _).mpr he) :=
  rfl

end congr

end QuotientGroup
