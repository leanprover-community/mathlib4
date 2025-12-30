import Mathlib.GroupTheory.FiniteAbelian.Duality

open CommGroup

@[to_additive]
theorem Monoid.exponent_dvd_of_submonoid {G : Type*} [Monoid G] (H : Submonoid G) :
    Monoid.exponent H ∣ Monoid.exponent G :=
  Monoid.exponent_dvd_of_monoidHom H.subtype H.subtype_injective

@[to_additive]
theorem Group.exponent_dvd_of_quotient {G : Type*} [Group G] (H : Subgroup G) [H.Normal] :
    Monoid.exponent (G ⧸ H) ∣ Monoid.exponent G :=
  MonoidHom.exponent_dvd (QuotientGroup.mk'_surjective H)

theorem CommGroup.monoidHom_card_of_hasEnoughRootsOfUnity (G M : Type*) [CommGroup G] [Finite G]
    [CommMonoid M] [HasEnoughRootsOfUnity M (Monoid.exponent G)] :
    Nat.card (G →* Mˣ) = Nat.card G :=
  Nat.card_congr (monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G M).some.toEquiv

/--
A version of `MonoidHom.restrict` as a homomorphism. This version is for restriction to a
`Submonoid`. See `MonoidHom.restrictHom` for a version for `Subgroup`.
-/
@[to_additive (attr := simps)
/--
A version of `AddMonoidHom.restrict` as a homomorphism. This version is for restriction to a
`AddSubmonoid`. See `AddMonoidHom.restrictHom` for a version for `AddSubgroup`.
-/]
def MonoidHom.restrictHom' (M : Type*) [Monoid M] (A : Type*) [CommMonoid A] (N : Submonoid M) :
    (M →* A) →* (N →* A) where
  toFun f := f.restrict N
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

/--
A version of `MonoidHom.restrict` as a homomorphism. This version is for restriction to a
`Subgroup`. See `MonoidHom.restrictHom'` for a version for `Submonoid`.
-/
@[to_additive (attr := simps)
/--
A version of `AddMonoidHom.restrict` as a homomorphism. This version is for restriction to a
`AddSubgroup`. See `AddMonoidHom.restrictHom'` for a version for `AddSubmonoid`.
-/]
def MonoidHom.restrictHom (G : Type*) [Group G] (A : Type*) [CommMonoid A] (H : Subgroup G) :
    (G →* A) →* (H →* A) where
  toFun f := f.restrict H
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

@[to_additive]
theorem MonoidHom.restrict_eq_one_iff {M : Type*} [Monoid M] {N : Type*} [MulOneClass N]
    {f : M →* N} {s : Submonoid M} :
    f.restrict s = 1 ↔ s ≤ MonoidHom.mker f := by
  simp [MonoidHom.ext_iff, SetLike.le_def]

@[to_additive]
theorem MonoidHom.restrictHom_eq_one_iff {G : Type*} [Group G] {A : Type*} [CommMonoid A]
    {H : Subgroup G} {f : G →* A} :
    f.restrictHom G A H = 1 ↔ H ≤ MonoidHom.ker f := MonoidHom.restrict_eq_one_iff

/--
The `MulEquiv` between the kernel of the restriction map to a normal subgroup `H` of homomorphism
of type `G →* A` and the group of homomorphisms `G ⧸ H →* A`.
-/
@[to_additive
/--
The `AddEquiv` between the kernel of the restriction map to a normal subgroup `H` of homomorphism
of type `G →+ A` and the group of homomorphisms `G ⧸ H →+ A`.
-/]
def MonoidHom.restrictHomKerEquiv (G : Type*) [Group G] (A : Type*) [CommGroup A]
    (H : Subgroup G) [H.Normal] : (MonoidHom.restrictHom G A H).ker ≃ (G ⧸ H →* A) where
  toFun := fun ⟨f, hf⟩ ↦ QuotientGroup.lift _ f
    (by rwa [mem_ker, MonoidHom.restrictHom_eq_one_iff] at hf)
  invFun := fun f ↦ ⟨f.comp (QuotientGroup.mk' H),
      MonoidHom.restrictHom_eq_one_iff.mpr <| QuotientGroup.le_comap_mk' H f.ker⟩
  left_inv _ := by simp
  right_inv _ := by ext; simp

instance (M R : Type*) [LeftCancelMonoid M] [CommRing R] [IsDomain R] [Finite M] :
    Finite (M →* Rˣ) := by
  let S := rootsOfUnity (Monoid.exponent M) R
  have : Finite (M →* S) := .of_injective _ DFunLike.coe_injective
  refine .of_surjective (fun f : M →* S ↦ (Subgroup.subtype _).comp f) fun f ↦ ?_
  have H a : f a ∈ S := by
    rw [mem_rootsOfUnity, ← map_pow, Monoid.pow_exponent_eq_one, map_one]
  exact ⟨.codRestrict f S H, MonoidHom.ext fun _ ↦ by simp⟩

/--
Let `G` be a finite abelian group and let `H` be a subgroup. If the ring `R` contains enough roots
of unity, then any homorphism `H →* Rˣ` can be extendend to a homomorphism `G → Rˣ`.
-/
theorem MonoidHom.restrict_surjective (G R : Type*) [CommGroup G] [Finite G] (H : Subgroup G)
    [CommRing R] [IsDomain R] [hR : HasEnoughRootsOfUnity R (Monoid.exponent G)] :
    Function.Surjective (fun f : G →* Rˣ ↦ MonoidHom.restrict f H) := by
  change Function.Surjective (MonoidHom.restrictHom G Rˣ H)
  have : Fintype H := Fintype.ofFinite H
  have : HasEnoughRootsOfUnity R (Monoid.exponent H) :=
    hR.of_dvd R <| Monoid.exponent_dvd_of_submonoid H.toSubmonoid
  have : HasEnoughRootsOfUnity R (Monoid.exponent (G ⧸ H)) :=
    hR.of_dvd R <| Group.exponent_dvd_of_quotient H
  apply MonoidHom.surjective_of_card_ker_le_div
  rw [Nat.card_congr (MonoidHom.restrictHomKerEquiv G Rˣ H),
    monoidHom_card_of_hasEnoughRootsOfUnity, monoidHom_card_of_hasEnoughRootsOfUnity,
    monoidHom_card_of_hasEnoughRootsOfUnity, Subgroup.card_eq_card_quotient_mul_card_subgroup H,
    mul_div_cancel_right₀]
  exact Fintype.card_eq_nat_card ▸ Fintype.card_ne_zero

