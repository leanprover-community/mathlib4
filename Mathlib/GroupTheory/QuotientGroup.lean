/-
Copyright (c) 2018 Kevin Buzzard, Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Patrick Massot

This file is to a certain extent based on `quotient_module.lean` by Johannes Hölzl.
-/
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.Congruence.Basic
import Mathlib.GroupTheory.Coset

/-!
# Quotients of groups by normal subgroups

This files develops the basic theory of quotients of groups by normal subgroups. In particular it
proves Noether's first and second isomorphism theorems.

## Main definitions

* `mk'`: the canonical group homomorphism `G →* G/N` given a normal subgroup `N` of `G`.
* `lift φ`: the group homomorphism `G/N →* H` given a group homomorphism `φ : G →* H` such that
  `N ⊆ ker φ`.
* `map f`: the group homomorphism `G/N →* H/M` given a group homomorphism `f : G →* H` such that
  `N ⊆ f⁻¹(M)`.

## Main statements

* `QuotientGroup.quotientKerEquivRange`: Noether's first isomorphism theorem, an explicit
  isomorphism `G/ker φ → range φ` for every group homomorphism `φ : G →* H`.
* `QuotientGroup.quotientInfEquivProdNormalQuotient`: Noether's second isomorphism theorem, an
  explicit isomorphism between `H/(H ∩ N)` and `(HN)/N` given a subgroup `H` and a normal subgroup
  `N` of a group `G`.
* `QuotientGroup.quotientQuotientEquivQuotient`: Noether's third isomorphism theorem,
  the canonical isomorphism between `(G / N) / (M / N)` and `G / M`, where `N ≤ M`.

## Tags

isomorphism theorems, quotient groups
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
  mul' := @fun a b c d hab hcd => by
    rw [leftRel_eq] at hab hcd ⊢
    dsimp only
    calc
      (a * c)⁻¹ * (b * d) = c⁻¹ * (a⁻¹ * b) * c⁻¹⁻¹ * (c⁻¹ * d) := by
        simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left]
      _ ∈ N := N.mul_mem (nN.conj_mem _ hab _) hcd

@[to_additive]
instance Quotient.group : Group (G ⧸ N) :=
  (QuotientGroup.con N).group

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
  QuotientGroup.eq'.trans <| by
    simp only [← _root_.eq_inv_mul_iff_mul_eq, exists_prop, exists_eq_right]

open scoped Pointwise in
@[to_additive]
theorem sound (U : Set (G ⧸ N)) (g : N.op) :
    g • (mk' N) ⁻¹' U = (mk' N) ⁻¹' U := by
  ext x
  simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem]
  congr! 1
  exact Quotient.sound ⟨g⁻¹, rfl⟩

/-- Two `MonoidHom`s from a quotient group are equal if their compositions with
`QuotientGroup.mk'` are equal.

See note [partially-applied ext lemmas]. -/
@[to_additive (attr := ext 1100) "Two `AddMonoidHom`s from an additive quotient group are equal if
 their compositions with `AddQuotientGroup.mk'` are equal.

 See note [partially-applied ext lemmas]. "]
theorem monoidHom_ext ⦃f g : G ⧸ N →* M⦄ (h : f.comp (mk' N) = g.comp (mk' N)) : f = g :=
  MonoidHom.ext fun x => QuotientGroup.induction_on x <| (DFunLike.congr_fun h : _)

@[to_additive (attr := simp)]
theorem eq_one_iff {N : Subgroup G} [nN : N.Normal] (x : G) : (x : G ⧸ N) = 1 ↔ x ∈ N := by
  refine QuotientGroup.eq.trans ?_
  rw [mul_one, Subgroup.inv_mem_iff]

@[to_additive]
theorem ker_le_range_iff {I : Type w} [Group I] (f : G →* H) [f.range.Normal] (g : H →* I) :
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

@[to_additive (attr := simp)]
theorem mk_prod {G ι : Type*} [CommGroup G] (N : Subgroup G) (s : Finset ι) {f : ι → G} :
    ((Finset.prod s f : G) : G ⧸ N) = Finset.prod s (fun i => (f i : G ⧸ N)) :=
  map_prod (QuotientGroup.mk' N) _ _

@[to_additive (attr := simp)] lemma map_mk'_self : N.map (mk' N) = ⊥ := by aesop

/-- A group homomorphism `φ : G →* M` with `N ⊆ ker(φ)` descends (i.e. `lift`s) to a
group homomorphism `G/N →* M`. -/
@[to_additive "An `AddGroup` homomorphism `φ : G →+ M` with `N ⊆ ker(φ)` descends (i.e. `lift`s)
 to a group homomorphism `G/N →* M`."]
def lift (φ : G →* M) (HN : N ≤ φ.ker) : Q →* M :=
  (QuotientGroup.con N).lift φ fun x y h => by
    simp only [QuotientGroup.con, leftRel_apply, Con.rel_mk] at h
    rw [Con.ker_rel]
    calc
      φ x = φ (y * (x⁻¹ * y)⁻¹) := by rw [mul_inv_rev, inv_inv, mul_inv_cancel_left]
      _ = φ y := by rw [φ.map_mul, HN (N.inv_mem h), mul_one]

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
  induction_on' x fun _x => rfl

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
  refine induction_on' x fun x => ?_
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
    simpa only [QuotientGroup.mk_mul, self_eq_mul_left, QuotientGroup.eq_one_iff]

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

variable (φ : G →* H)

open MonoidHom

/-- The induced map from the quotient by the kernel to the codomain. -/
@[to_additive "The induced map from the quotient by the kernel to the codomain."]
def kerLift : G ⧸ ker φ →* H :=
  lift _ φ fun _g => φ.mem_ker.mp

@[to_additive (attr := simp)]
theorem kerLift_mk (g : G) : (kerLift φ) g = φ g :=
  lift_mk _ _ _

@[to_additive (attr := simp)]
theorem kerLift_mk' (g : G) : (kerLift φ) (mk g) = φ g :=
  lift_mk' _ _ _

@[to_additive]
theorem kerLift_injective : Injective (kerLift φ) := fun a b =>
  Quotient.inductionOn₂' a b fun a b (h : φ a = φ b) =>
    Quotient.sound' <| by rw [leftRel_apply, mem_ker, φ.map_mul, ← h, φ.map_inv, inv_mul_self]

-- Note that `ker φ` isn't definitionally `ker (φ.rangeRestrict)`
-- so there is a bit of annoying code duplication here
/-- The induced map from the quotient by the kernel to the range. -/
@[to_additive "The induced map from the quotient by the kernel to the range."]
def rangeKerLift : G ⧸ ker φ →* φ.range :=
  lift _ φ.rangeRestrict fun g hg => (mem_ker _).mp <| by rwa [ker_rangeRestrict]

@[to_additive]
theorem rangeKerLift_injective : Injective (rangeKerLift φ) := fun a b =>
  Quotient.inductionOn₂' a b fun a b (h : φ.rangeRestrict a = φ.rangeRestrict b) =>
    Quotient.sound' <| by
      rw [leftRel_apply, ← ker_rangeRestrict, mem_ker, φ.rangeRestrict.map_mul, ← h,
        φ.rangeRestrict.map_inv, inv_mul_self]

@[to_additive]
theorem rangeKerLift_surjective : Surjective (rangeKerLift φ) := by
  rintro ⟨_, g, rfl⟩
  use mk g
  rfl

/-- **Noether's first isomorphism theorem** (a definition): the canonical isomorphism between
`G/(ker φ)` to `range φ`. -/
@[to_additive "The first isomorphism theorem (a definition): the canonical isomorphism between
`G/(ker φ)` to `range φ`."]
noncomputable def quotientKerEquivRange : G ⧸ ker φ ≃* range φ :=
  MulEquiv.ofBijective (rangeKerLift φ) ⟨rangeKerLift_injective φ, rangeKerLift_surjective φ⟩

/-- The canonical isomorphism `G/(ker φ) ≃* H` induced by a homomorphism `φ : G →* H`
with a right inverse `ψ : H → G`. -/
@[to_additive (attr := simps) "The canonical isomorphism `G/(ker φ) ≃+ H` induced by a homomorphism
`φ : G →+ H` with a right inverse `ψ : H → G`."]
def quotientKerEquivOfRightInverse (ψ : H → G) (hφ : RightInverse ψ φ) : G ⧸ ker φ ≃* H :=
  { kerLift φ with
    toFun := kerLift φ
    invFun := mk ∘ ψ
    left_inv := fun x => kerLift_injective φ (by rw [Function.comp_apply, kerLift_mk', hφ])
    right_inv := hφ }

/-- The canonical isomorphism `G/⊥ ≃* G`. -/
@[to_additive (attr := simps!) "The canonical isomorphism `G/⊥ ≃+ G`."]
def quotientBot : G ⧸ (⊥ : Subgroup G) ≃* G :=
  quotientKerEquivOfRightInverse (MonoidHom.id G) id fun _x => rfl

/-- The canonical isomorphism `G/(ker φ) ≃* H` induced by a surjection `φ : G →* H`.

For a `computable` version, see `QuotientGroup.quotientKerEquivOfRightInverse`.
-/
@[to_additive "The canonical isomorphism `G/(ker φ) ≃+ H` induced by a surjection `φ : G →+ H`.
For a `computable` version, see `QuotientAddGroup.quotientKerEquivOfRightInverse`."]
noncomputable def quotientKerEquivOfSurjective (hφ : Surjective φ) : G ⧸ ker φ ≃* H :=
  quotientKerEquivOfRightInverse φ _ hφ.hasRightInverse.choose_spec

/-- If two normal subgroups `M` and `N` of `G` are the same, their quotient groups are
isomorphic. -/
@[to_additive "If two normal subgroups `M` and `N` of `G` are the same, their quotient groups are
isomorphic."]
def quotientMulEquivOfEq {M N : Subgroup G} [M.Normal] [N.Normal] (h : M = N) : G ⧸ M ≃* G ⧸ N :=
  { Subgroup.quotientEquivOfEq h with
    map_mul' := fun q r => Quotient.inductionOn₂' q r fun _g _h => rfl }

@[to_additive (attr := simp)]
theorem quotientMulEquivOfEq_mk {M N : Subgroup G} [M.Normal] [N.Normal] (h : M = N) (x : G) :
    QuotientGroup.quotientMulEquivOfEq h (QuotientGroup.mk x) = QuotientGroup.mk x :=
  rfl

/-- Let `A', A, B', B` be subgroups of `G`. If `A' ≤ B'` and `A ≤ B`,
then there is a map `A / (A' ⊓ A) →* B / (B' ⊓ B)` induced by the inclusions. -/
@[to_additive "Let `A', A, B', B` be subgroups of `G`. If `A' ≤ B'` and `A ≤ B`, then there is a map
`A / (A' ⊓ A) →+ B / (B' ⊓ B)` induced by the inclusions."]
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
@[to_additive "Let `A', A, B', B` be subgroups of `G`. If `A' = B'` and `A = B`, then the quotients
`A / (A' ⊓ A)` and `B / (B' ⊓ B)` are isomorphic. Applying this equiv is nicer than rewriting along
the equalities, since the type of `(A'.addSubgroupOf A : AddSubgroup A)` depends on on `A`. "]
def equivQuotientSubgroupOfOfEq {A' A B' B : Subgroup G} [hAN : (A'.subgroupOf A).Normal]
    [hBN : (B'.subgroupOf B).Normal] (h' : A' = B') (h : A = B) :
    A ⧸ A'.subgroupOf A ≃* B ⧸ B'.subgroupOf B :=
  MonoidHom.toMulEquiv (quotientMapSubgroupOfOfLe h'.le h.le) (quotientMapSubgroupOfOfLe h'.ge h.ge)
    (by ext ⟨x, hx⟩; rfl)
    (by ext ⟨x, hx⟩; rfl)

section ZPow

variable {A B C : Type u} [CommGroup A] [CommGroup B] [CommGroup C]
variable (f : A →* B) (g : B →* A) (e : A ≃* B) (d : B ≃* C) (n : ℤ)

/-- The map of quotients by powers of an integer induced by a group homomorphism. -/
@[to_additive "The map of quotients by multiples of an integer induced by an additive group
homomorphism."]
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
@[to_additive "The equivalence of quotients by multiples of an integer induced by an additive group
isomorphism."]
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

/-- **Noether's second isomorphism theorem**: given two subgroups `H` and `N` of a group `G`, where
`N` is normal, defines an isomorphism between `H/(H ∩ N)` and `(HN)/N`. -/
@[to_additive "The second isomorphism theorem: given two subgroups `H` and `N` of a group `G`, where
`N` is normal, defines an isomorphism between `H/(H ∩ N)` and `(H + N)/N`"]
noncomputable def quotientInfEquivProdNormalQuotient (H N : Subgroup G) [N.Normal] :
    H ⧸ N.subgroupOf H ≃* _ ⧸ N.subgroupOf (H ⊔ N) :=
  let
    φ :-- φ is the natural homomorphism H →* (HN)/N.
      H →*
      _ ⧸ N.subgroupOf (H ⊔ N) :=
    (mk' <| N.subgroupOf (H ⊔ N)).comp (inclusion le_sup_left)
  have φ_surjective : Surjective φ := fun x =>
    x.inductionOn' <| by
      rintro ⟨y, hy : y ∈ (H ⊔ N)⟩
      rw [← SetLike.mem_coe] at hy
      rw [mul_normal H N] at hy
      rcases hy with ⟨h, hh, n, hn, rfl⟩
      use ⟨h, hh⟩
      let _ : Setoid ↑(H ⊔ N) :=
        (@leftRel ↑(H ⊔ N) (H ⊔ N : Subgroup G).toGroup (N.subgroupOf (H ⊔ N)))
      -- Porting note: Lean couldn't find this automatically
      refine Quotient.eq.mpr ?_
      change Setoid.r _ _
      rw [leftRel_apply]
      change h⁻¹ * (h * n) ∈ N
      rwa [← mul_assoc, inv_mul_self, one_mul]
  (quotientMulEquivOfEq (by simp [φ, ← comap_ker])).trans
    (quotientKerEquivOfSurjective φ φ_surjective)

end SndIsomorphismThm

section ThirdIsoThm

variable (M : Subgroup G) [nM : M.Normal]

@[to_additive]
instance map_normal : (M.map (QuotientGroup.mk' N)).Normal :=
  nM.map _ mk_surjective

variable (h : N ≤ M)

/-- The map from the third isomorphism theorem for groups: `(G / N) / (M / N) → G / M`. -/
@[to_additive "The map from the third isomorphism theorem for additive groups:
`(A / N) / (M / N) → A / M`."]
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
      "**Noether's third isomorphism theorem** for additive groups: `(A / N) / (M / N) ≃+ A / M`."]
def quotientQuotientEquivQuotient : (G ⧸ N) ⧸ M.map (QuotientGroup.mk' N) ≃* G ⧸ M :=
  MonoidHom.toMulEquiv (quotientQuotientEquivQuotientAux N M h)
    (QuotientGroup.map _ _ (QuotientGroup.mk' N) (Subgroup.le_comap_map _ _))
    (by ext; simp)
    (by ext; simp)

end ThirdIsoThm

section trivial

@[to_additive]
theorem subsingleton_quotient_top : Subsingleton (G ⧸ (⊤ : Subgroup G)) := by
  dsimp [HasQuotient.Quotient, QuotientGroup.instHasQuotientSubgroup, Quotient]
  rw [leftRel_eq]
  exact Trunc.instSubsingletonTrunc

/-- If the quotient by a subgroup gives a singleton then the subgroup is the whole group. -/
@[to_additive "If the quotient by an additive subgroup gives a singleton then the additive subgroup
is the whole additive group."]
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

namespace Group

open scoped Classical

open QuotientGroup Subgroup

variable {F G H : Type u} [Group F] [Group G] [Group H] [Fintype F] [Fintype H]
variable (f : F →* G) (g : G →* H)

/-- If `F` and `H` are finite such that `ker(G →* H) ≤ im(F →* G)`, then `G` is finite. -/
@[to_additive "If `F` and `H` are finite such that `ker(G →+ H) ≤ im(F →+ G)`, then `G` is finite."]
noncomputable def fintypeOfKerLeRange (h : g.ker ≤ f.range) : Fintype G :=
  @Fintype.ofEquiv _ _
    (@instFintypeProd _ _ (Fintype.ofInjective _ <| kerLift_injective g) <|
      Fintype.ofInjective _ <| inclusion_injective h)
    groupEquivQuotientProdSubgroup.symm

/-- If `F` and `H` are finite such that `ker(G →* H) = im(F →* G)`, then `G` is finite. -/
@[to_additive "If `F` and `H` are finite such that `ker(G →+ H) = im(F →+ G)`, then `G` is finite."]
noncomputable def fintypeOfKerEqRange (h : g.ker = f.range) : Fintype G :=
  fintypeOfKerLeRange _ _ h.le

/-- If `ker(G →* H)` and `H` are finite, then `G` is finite. -/
@[to_additive "If `ker(G →+ H)` and `H` are finite, then `G` is finite."]
noncomputable def fintypeOfKerOfCodom [Fintype g.ker] : Fintype G :=
  fintypeOfKerLeRange ((topEquiv : _ ≃* G).toMonoidHom.comp <| inclusion le_top) g fun x hx =>
    ⟨⟨x, hx⟩, rfl⟩

/-- If `F` and `coker(F →* G)` are finite, then `G` is finite. -/
@[to_additive "If `F` and `coker(F →+ G)` are finite, then `G` is finite."]
noncomputable def fintypeOfDomOfCoker [Normal f.range] [Fintype <| G ⧸ f.range] : Fintype G :=
  fintypeOfKerLeRange _ (mk' f.range) fun x => (eq_one_iff x).mp

@[to_additive]
lemma _root_.Finite.of_finite_quot_finite_subgroup {H : Subgroup G}
    (hH : Set.Finite (H : Set G)) (h : Finite (G ⧸ H)) : Finite G := by
  have : Finite H := hH
  exact Finite.of_equiv _ (groupEquivQuotientProdSubgroup (s := H)).symm

end Group
