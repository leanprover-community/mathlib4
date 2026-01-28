/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

/-!
# Duality for finite abelian groups

Let `G` be a finite abelian group.

For `M` a commutative monoid that has enough `n`th roots of unity, where `n` is the exponent of `G`,
the main results in this file are:
* `CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity`: Homomorphisms `G →* Mˣ` separate
  elements of `G`.
* `CommGroup.monoidHom_mulEquiv_self_of_hasEnoughRootsOfUnity`: `G` is isomorphic to `G →* Mˣ`.

For `R` a commutative domain that has enough `n`th roots of unity, where `n` is the exponent of `G`,
the main results in this file are:
* `CommGroup.monoidHomMonoidHomEquiv`: `G` is isomorphic to its double dual `(G →* Rˣ) →* Rˣ`.
* `CommGroup.subgroupOrderIsoSubgroupMonoidHom`: the order reversing bijection that sends a
  subgroup of `G` to its dual subgroup in `G →* Rˣ`.
-/

@[expose] public noncomputable section

namespace CommGroup

open MonoidHom

private
lemma dvd_exponent {ι G : Type*} [Finite ι] [Monoid G] {n : ι → ℕ}
    (e : G ≃* ((i : ι) → Multiplicative (ZMod (n i)))) (i : ι) :
    n i ∣ Monoid.exponent G := by
  classical -- to get `DecidableEq ι`
  have : n i = orderOf (e.symm <| Pi.mulSingle i <| .ofAdd 1) := by
    simpa only [MulEquiv.orderOf_eq, orderOf_piMulSingle, orderOf_ofAdd_eq_addOrderOf]
      using (ZMod.addOrderOf_one (n i)).symm
  exact this ▸ Monoid.order_dvd_exponent _

variable (G M : Type*) [CommGroup G] [Finite G] [CommMonoid M]

private
lemma exists_apply_ne_one_aux
    (H : ∀ n : ℕ, n ∣ Monoid.exponent G → ∀ a : ZMod n, a ≠ 0 →
      ∃ φ : Multiplicative (ZMod n) →* M, φ (.ofAdd a) ≠ 1)
    {a : G} (ha : a ≠ 1) :
    ∃ φ : G →* M, φ a ≠ 1 := by
  obtain ⟨ι, _, n, _, h⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite G
  let e := h.some
  obtain ⟨i, hi⟩ : ∃ i : ι, e a i ≠ 1 := by
    contrapose! ha
    exact (MulEquiv.map_eq_one_iff e).mp <| funext ha
  obtain ⟨φi, hφi⟩ := H (n i) (dvd_exponent e i) ((e a i).toAdd) hi
  use (φi.comp (Pi.evalMonoidHom (fun (i : ι) ↦ Multiplicative (ZMod (n i))) i)).comp e
  simpa only [coe_comp, coe_coe, Function.comp_apply, Pi.evalMonoidHom_apply, ne_eq] using hφi

variable [hM : HasEnoughRootsOfUnity M (Monoid.exponent G)]

/-- If `G` is a finite commutative group of exponent `n` and `M` is a commutative monoid
with enough `n`th roots of unity, then for each `a ≠ 1` in `G`, there exists a
group homomorphism `φ : G → Mˣ` such that `φ a ≠ 1`. -/
theorem exists_apply_ne_one_of_hasEnoughRootsOfUnity {a : G} (ha : a ≠ 1) :
    ∃ φ : G →* Mˣ, φ a ≠ 1 := by
  refine exists_apply_ne_one_aux G Mˣ (fun n hn a ha₀ ↦ ?_) ha
  have : NeZero n := ⟨fun H ↦ NeZero.ne _ <| Nat.eq_zero_of_zero_dvd (H ▸ hn)⟩
  have := HasEnoughRootsOfUnity.of_dvd M hn
  exact ZMod.exists_monoidHom_apply_ne_one (HasEnoughRootsOfUnity.exists_primitiveRoot M n) ha₀

variable {M} in
@[simp]
 theorem forall_apply_eq_apply_iff {g g' : G} :
    (∀ φ : G →* Mˣ, φ g = φ g') ↔ g = g' := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  simp_rw (config := {singlePass := true}) [← mul_inv_eq_one, ← map_inv, ← map_mul] at h ⊢
  contrapose! h
  exact exists_apply_ne_one_of_hasEnoughRootsOfUnity G M h

/-- A finite commutative group `G` is (noncanonically) isomorphic to the group `G →* Mˣ`
when `M` is a commutative monoid with enough `n`th roots of unity, where `n` is the exponent
of `G`. -/
theorem monoidHom_mulEquiv_of_hasEnoughRootsOfUnity : Nonempty ((G →* Mˣ) ≃* G) := by
  classical -- to get `DecidableEq ι`
  obtain ⟨ι, _, n, ⟨h₁, h₂⟩⟩ := equiv_prod_multiplicative_zmod_of_finite G
  let e := h₂.some
  let e' := Pi.monoidHomMulEquiv (fun i ↦ Multiplicative (ZMod (n i))) Mˣ
  have : ∀ i, NeZero (n i) := fun i ↦ NeZero.of_gt (h₁ i)
  have inst i : HasEnoughRootsOfUnity M <| Nat.card <| Multiplicative <| ZMod (n i) := by
    have hdvd : Nat.card (Multiplicative (ZMod (n i))) ∣ Monoid.exponent G := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
        using dvd_exponent e i
    exact HasEnoughRootsOfUnity.of_dvd M hdvd
  let E i := (IsCyclic.monoidHom_equiv_self (Multiplicative (ZMod (n i))) M).some
  exact ⟨e.monoidHomCongrLeft.trans <| e'.trans <| .trans (.piCongrRight E) e.symm⟩

theorem card_monoidHom_of_hasEnoughRootsOfUnity :
    Nat.card (G →* Mˣ) = Nat.card G :=
  Nat.card_congr (monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G M).some.toEquiv

variable {G}

/--
Let `G` be a finite commutative group and let `H` be a subgroup. If `M` is a commutative monoid
such that `G →* Mˣ` and `H →* Mˣ` are both finite (this is the case for example if `M` is a
commutative domain) and with enough `n`th roots of unity, where `n` is the exponent
of `G`, then any homomorphism `H →* Mˣ` can be extended to an homomorphism `G →* Mˣ`.
-/
theorem _root_.MonoidHom.restrict_surjective (H : Subgroup G) [Finite (G →* Mˣ)]
    [Finite (H →* Mˣ)] : Function.Surjective (MonoidHom.restrictHom H Mˣ) := by
  have : Fintype H := Fintype.ofFinite H
  have : HasEnoughRootsOfUnity M (Monoid.exponent H) :=
    hM.of_dvd M <| Monoid.exponent_submonoid_dvd H.toSubmonoid
  have : HasEnoughRootsOfUnity M (Monoid.exponent (G ⧸ H)) :=
    hM.of_dvd M <| Group.exponent_quotient_dvd H
  refine MonoidHom.surjective_of_card_ker_le_div _ (le_of_eq ?_)
  rw [card_monoidHom_of_hasEnoughRootsOfUnity, card_monoidHom_of_hasEnoughRootsOfUnity,
    H.card_eq_card_quotient_mul_card_subgroup,
    mul_div_cancel_right₀ _ (Fintype.card_eq_nat_card ▸ Fintype.card_ne_zero),
    ← card_monoidHom_of_hasEnoughRootsOfUnity (G ⧸ H) M,
    Nat.card_congr (restrictHomKerEquiv Mˣ H).toEquiv]

@[simp]
theorem forall_monoidHom_apply_eq_one_iff (H : Subgroup G) (x : G) :
    (∀ (φ : G →* Mˣ), (∀ y ∈ H, φ y = 1) → φ x = 1) ↔ x ∈ H := by
  have : HasEnoughRootsOfUnity M (Monoid.exponent (G ⧸ H)) :=
    hM.of_dvd M <| Group.exponent_quotient_dvd H
  refine ⟨fun h ↦ ?_, fun hx φ hφ ↦ hφ x hx⟩
  contrapose! h
  rw [← (QuotientGroup.eq_one_iff x).not] at h
  obtain ⟨ψ, hψ⟩ := exists_apply_ne_one_of_hasEnoughRootsOfUnity (G ⧸ H) M h
  refine ⟨ψ.comp (QuotientGroup.mk' H), fun x hx ↦ ?_, hψ⟩
  rw [coe_comp, Function.comp_apply, QuotientGroup.coe_mk', (QuotientGroup.eq_one_iff _).mpr hx,
    map_one]

variable (R : Type*) [CommRing R] [IsDomain R] [hR : HasEnoughRootsOfUnity R (Monoid.exponent G)]
variable (G) in
/-- The `MulEquiv` between the double dual `(G →* Rˣ) →* Rˣ` of a finite commutative group `G`
and itself  where `R` is a commutative domain with enough `n`th roots of unity, where `n` is the
exponent of `G`.
The image `g` of `η : (G →* Rˣ) →* Rˣ` is such that, for all `φ : G →* Rˣ`, we have `φ g = η g`,
see `CommGroup.apply_monoidHomMonoidHomEquiv`.
-/
@[simps! symm_apply_apply]
def monoidHomMonoidHomEquiv : ((G →* Rˣ) →* Rˣ) ≃* G :=
  have : HasEnoughRootsOfUnity R (Monoid.exponent (G →* Rˣ)) := by
    rwa [Monoid.exponent_eq_of_mulEquiv (monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G R).some]
  (MulEquiv.mk' (Equiv.ofBijective
    (fun g ↦ MonoidHom.mk ⟨fun φ ↦ φ g, one_apply _⟩ (by simp))
    (by
      refine (Nat.bijective_iff_injective_and_card _).mpr ⟨fun _ _ h ↦ ?_, ?_⟩
      · rwa [mk.injEq, OneHom.mk.injEq, funext_iff, forall_apply_eq_apply_iff] at h
      · rw [card_monoidHom_of_hasEnoughRootsOfUnity, card_monoidHom_of_hasEnoughRootsOfUnity]))
    (fun _ _ ↦ by ext; simp)).symm

@[simp]
theorem apply_monoidHomMonoidHomEquiv (φ : G →* Rˣ) (η : (G →* Rˣ) →* Rˣ) :
    φ (monoidHomMonoidHomEquiv G R η) = η φ := by
  rw [← monoidHomMonoidHomEquiv_symm_apply_apply G R (monoidHomMonoidHomEquiv G R η) φ,
    MulEquiv.symm_apply_apply]

variable (G) in
/--
The order reversing bijection that sends a subgroup of `G` to its dual subgroup in `G →* Rˣ` where
`G` is a finite commutative group and `R` is a commutative domain with enough `n`th roots of
unity, where `n` is the exponent of `G`.
-/
def subgroupOrderIsoSubgroupMonoidHom : Subgroup G ≃o (Subgroup (G →* Rˣ))ᵒᵈ where
  toFun H := OrderDual.toDual (restrictHom H Rˣ).ker
  invFun Φ := (monoidHomMonoidHomEquiv G R).mapSubgroup (restrictHom Φ.ofDual Rˣ).ker
  map_rel_iff' {H₁} {H₂} := by
    simp_rw (config := {singlePass := true}) [MulEquiv.mapSubgroup_apply, Equiv.coe_fn_mk,
      ge_iff_le, OrderDual.toDual_le_toDual, SetLike.le_def, mem_ker, restrictHom_apply,
      restrict_eq_one_iff, ← forall_monoidHom_apply_eq_one_iff R H₂]
    grind
  left_inv H := by
    ext x
    rw [MulEquiv.coe_mapSubgroup, Subgroup.mem_map_equiv, MonoidHom.mem_ker]
    simp
  right_inv Φ := by
    have : HasEnoughRootsOfUnity R (Monoid.exponent (G →* Rˣ)) := by
      rwa [Monoid.exponent_eq_of_mulEquiv (monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G R).some]
    ext φ
    rw [OrderDual.ofDual_toDual, mem_ker, restrictHom_apply, restrict_eq_one_iff]
    simp

@[simp]
theorem mem_subgroupOrderIsoSubgroupMonoidHom_iff (H : Subgroup G) (φ : G →* Rˣ) :
    φ ∈ (subgroupOrderIsoSubgroupMonoidHom G R H).ofDual ↔ ∀ g ∈ H, φ g = 1 := by
  simp [subgroupOrderIsoSubgroupMonoidHom]

@[simp]
theorem mem_subgroupOrderIsoSubgroupMonoidHom_symm_iff (Φ : Subgroup (G →* Rˣ)) (g : G) :
    g ∈ (subgroupOrderIsoSubgroupMonoidHom G R).symm (OrderDual.toDual Φ) ↔ ∀ φ ∈ Φ, φ g = 1 := by
  simp only [subgroupOrderIsoSubgroupMonoidHom, OrderIso.symm_mk, RelIso.coe_fn_mk,
    Equiv.coe_fn_symm_mk, OrderDual.ofDual_toDual, MulEquiv.coe_mapSubgroup,
    Subgroup.mem_map_equiv, mem_ker, restrictHom_apply, restrict_eq_one_iff,
    monoidHomMonoidHomEquiv_symm_apply_apply]

end CommGroup
