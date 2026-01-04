module

public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.NumberTheory.MulChar.Duality
public import Mathlib.Algebra.Group.Submonoid.Units

@[expose] public section

section Units

theorem IsUnit.coe {M S : Type*} [Monoid M] [SetLike S M] [SubmonoidClass S M] {N : S} {a : N}
    (ha : IsUnit a) :
    IsUnit (a : M) :=
  ha.map (SubmonoidClass.subtype N)

-- noncomputable def Units.mapRangeEquiv0 {M S : Type*} [Monoid M] [SetLike S M] [SubmonoidClass S M]
--     (N : S) : (Units.map (SubmonoidClass.subtype N)).range ≃* Nˣ :=
--   (MonoidHom.ofInjective (Units.map_injective <| SubmonoidClass.subtype_injective N)).symm

-- @[deprecated (since := "2026-01-03")] alias Units.mapRangeEquiv := Units.mapRangeEquiv0
-- @[simp]
-- theorem Units.mapRangeEquiv_coe_coe_symm_apply {M S : Type*} [Monoid M] [SetLike S M]
--     [SubmonoidClass S M] {N : S} (x : Nˣ) :
--     ((mapRangeEquiv N).symm x : Mˣ) = (x.val : M) := rfl

-- @[simp]
-- theorem Units.mapRangeEquiv_coe_coe_apply {M S : Type*} [Monoid M] [SetLike S M]
--       [SubmonoidClass S M] {N : S} (x : (Units.map (SubmonoidClass.subtype N)).range) :
--     ((Units.mapRangeEquiv N x).val : M) = x.val := by
--   rw [← MulEquiv.symm_apply_apply (Units.mapRangeEquiv N) x,
--     Units.mapRangeEquiv_coe_coe_symm_apply, MulEquiv.apply_symm_apply]

-- @[simp]
-- theorem toto {M : Type*} [Monoid M] (S : Submonoid M) (x) :
--     ((S.unitsEquivUnitsType x).val : M) = x.val := rfl

end Units

noncomputable section CommGroup

open CommGroup MonoidHom

variable {G : Type*} (M : Type*) [CommGroup G] [Finite G] [CommMonoid M]
  [hR : HasEnoughRootsOfUnity M (Monoid.exponent G)]

variable {M} in
@[simp]
theorem CommGroup.forall_apply_eq_apply_iff {g g' : G} :
    (∀ φ : G →* Mˣ, φ g = φ g') ↔ g = g' := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  simp_rw (config := {singlePass := true}) [← mul_inv_eq_one, ← map_inv, ← map_mul] at h ⊢
  contrapose! h
  exact exists_apply_ne_one_of_hasEnoughRootsOfUnity G M h

def CommGroup.monoidHomQuotientKerEquiv (H : Subgroup G) [Finite (G →* Mˣ)]
    [Finite (H →* Mˣ)] :
    (G →* Mˣ) ⧸ (MonoidHom.restrictHom Mˣ H).ker ≃* (H →* Mˣ) :=
  QuotientGroup.quotientKerEquivOfSurjective (restrictHom Mˣ H) <| restrict_surjective G M H

variable (G) in
@[simps! symm_apply_apply]
def CommGroup.monoidHomMonoidHomEquiv (R : Type*) [CommRing R] [IsDomain R]
    [hR : HasEnoughRootsOfUnity R (Monoid.exponent G)] :
    ((G →* Rˣ) →* Rˣ) ≃* G :=
  have : HasEnoughRootsOfUnity R (Monoid.exponent (G →* Rˣ)) := by
    rwa [Monoid.exponent_eq_of_mulEquiv (monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G R).some]
  (MulEquiv.mk' (Equiv.ofBijective
    (fun g ↦ MonoidHom.mk ⟨fun φ ↦ φ g, one_apply _⟩ (by simp))
    (by
      refine (Nat.bijective_iff_injective_and_card _).mpr ⟨fun _ _ h ↦ ?_, ?_⟩
      · rwa [mk.injEq, OneHom.mk.injEq, funext_iff, forall_apply_eq_apply_iff] at h
      · rw [monoidHom_card_of_hasEnoughRootsOfUnity, monoidHom_card_of_hasEnoughRootsOfUnity]
      ))
    (fun _ _ ↦ by ext; simp)).symm

-- theorem CommGroup.mapSubgroup_monoidHomMonoidHomEquiv (H : Subgroup G) (R : Type*) [CommRing R]
--     [IsDomain R] [hR : HasEnoughRootsOfUnity R (Monoid.exponent G)] :
--     (monoidHomMonoidHomEquiv G R).mapSubgroup
--       (restrictHom Rˣ (restrictHom Rˣ H).ker).ker = H := by
--   rw [eq_comm]
--   refine Subgroup.eq_of_le_of_card_ge (fun g hg ↦ ?_) ?_
--   · simp only [MulEquiv.mapSubgroup_apply, Subgroup.mem_map, mem_ker, restrictHom_apply,
--       restrict_eq_one_iff]
--     refine ⟨(monoidHomMonoidHomEquiv G R).symm g, fun φ hφ ↦ ?_, by simp⟩
--     simpa [monoidHomMonoidHomEquiv_symm_apply_apply] using hφ g hg
--   · have : HasEnoughRootsOfUnity R (Monoid.exponent ((G →* Rˣ) ⧸ (restrictHom Rˣ H).ker)) := by
--       refine hR.of_dvd _ <| dvd_trans (Group.exponent_dvd_of_quotient (restrictHom Rˣ H).ker) ?_
--       rw [Monoid.exponent_eq_of_mulEquiv (monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G R).some]
--     have : HasEnoughRootsOfUnity R (Monoid.exponent H) := by
--       refine hR.of_dvd _ <| Monoid.exponent_dvd_of_submonoid H.toSubmonoid
--     rw [MulEquiv.mapSubgroup_apply, ← SetLike.coe_sort_coe, Subgroup.coe_map,
--       Nat.card_image_of_injective, SetLike.coe_sort_coe,
--       Nat.card_congr (MonoidHom.restrictHomKerEquiv Rˣ (restrictHom Rˣ H).ker),
--       monoidHom_card_of_hasEnoughRootsOfUnity,
--       Nat.card_congr (monoidHomQuotientKerEquiv R H).toEquiv,
--       monoidHom_card_of_hasEnoughRootsOfUnity]
--     exact EquivLike.injective (monoidHomMonoidHomEquiv G R)

theorem CommGroup.mapSubgroup_monoidHomMonoidHomEquiv_symm (H : Subgroup G) (R : Type*) [CommRing R]
    [IsDomain R] [hR : HasEnoughRootsOfUnity R (Monoid.exponent G)] :
    (monoidHomMonoidHomEquiv G R).symm.mapSubgroup H =
      (restrictHom Rˣ (restrictHom Rˣ H).ker).ker := by
  rw [← MulEquiv.symm_mapSubgroup, OrderIso.symm_apply_eq]
  refine Subgroup.eq_of_le_of_card_ge (fun g hg ↦ ?_) ?_
  · simp only [MulEquiv.mapSubgroup_apply, Subgroup.mem_map, mem_ker, restrictHom_apply,
      restrict_eq_one_iff]
    refine ⟨(monoidHomMonoidHomEquiv G R).symm g, fun φ hφ ↦ ?_, by simp⟩
    simpa [monoidHomMonoidHomEquiv_symm_apply_apply] using hφ g hg
  · have : HasEnoughRootsOfUnity R (Monoid.exponent ((G →* Rˣ) ⧸ (restrictHom Rˣ H).ker)) := by
      refine hR.of_dvd _ <| dvd_trans (Group.exponent_dvd_of_quotient (restrictHom Rˣ H).ker) ?_
      rw [Monoid.exponent_eq_of_mulEquiv (monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G R).some]
    have : HasEnoughRootsOfUnity R (Monoid.exponent H) := by
      refine hR.of_dvd _ <| Monoid.exponent_dvd_of_submonoid H.toSubmonoid
    rw [MulEquiv.mapSubgroup_apply, ← SetLike.coe_sort_coe, Subgroup.coe_map,
      Nat.card_image_of_injective, SetLike.coe_sort_coe,
      Nat.card_congr (MonoidHom.restrictHomKerEquiv Rˣ (restrictHom Rˣ H).ker),
      monoidHom_card_of_hasEnoughRootsOfUnity,
      Nat.card_congr (monoidHomQuotientKerEquiv R H).toEquiv,
      monoidHom_card_of_hasEnoughRootsOfUnity]
    exact EquivLike.injective (monoidHomMonoidHomEquiv G R)

-- Mathlib.Topology.Algebra.PontryaginDual

end CommGroup

noncomputable section MulChar

open MulChar

theorem MulChar.forall_apply_eq_apply_iff {M R : Type*} [CommMonoid M] [CommRing R] [Finite M]
    [HasEnoughRootsOfUnity R (Monoid.exponent Mˣ)] {a b : Mˣ} :
    (∀ χ : MulChar M R, χ a = χ b) ↔ a = b := by
  simp only [← MulChar.coe_equivToUnitHom, ← Units.ext_iff]
  rw [equivToUnitHom.forall_congr_right (q := fun χ ↦ χ a = χ b)]
  exact CommGroup.forall_apply_eq_apply_iff

@[simps!]
def MulChar.restrict {R : Type*} {S : Type*} [CommMonoid R] [SetLike S R] [SubmonoidClass S R]
    (T : S) (R' : Type*) [CommMonoidWithZero R'] (χ : MulChar R R') : MulChar T R' :=
  ofUnitHom <| χ.toUnitHom.comp <| Units.map (SubmonoidClass.subtype T)

@[simp]
theorem MulChar.restrict_eq_one_iff {R : Type*} {S : Type*} [CommMonoid R] [SetLike S R]
    [SubmonoidClass S R] (T : S) (R' : Type*) [CommMonoidWithZero R'] (χ : MulChar R R') :
    χ.restrict T = 1 ↔ ∀ x : Tˣ, χ x = 1 := by
  simp [eq_one_iff]

@[simps!]
def MulChar.ofQuotient {R : Type*} [CommRing R] (I : Ideal R) (R' : Type*) [CommMonoidWithZero R']
    (χ : MulChar (R ⧸ I) R') : MulChar R R' :=
  ofUnitHom <| χ.toUnitHom.comp (Units.map (Ideal.Quotient.mk I).toMonoidHom)

@[simps]
def MulChar.restrictHom {R : Type*} {S : Type*} [CommMonoid R] [SetLike S R]
    [SubmonoidClass S R] (T : S) (R' : Type*) [CommMonoidWithZero R'] :
    MulChar R R' →* MulChar T R' where
  toFun := fun χ ↦ restrict T R' χ
  map_one' := by
    ext x
    rw [restrict_apply, if_pos x.isUnit, MulChar.one_apply x.isUnit.coe, one_apply_coe]
  map_mul' _ _ := by ext; simp

theorem MulChar.restrictHom_surjective (R : Type*) [Finite R] [CommMonoid R] (T : Submonoid R)
    (R' : Type*) [CommRing R'] [IsDomain R'] [HasEnoughRootsOfUnity R' (Monoid.exponent Rˣ)] :
    Function.Surjective (MulChar.restrictHom T R') := by
  rw [← EquivLike.surjective_comp MulChar.equivToUnitHom.symm,
    ← EquivLike.comp_surjective _ MulChar.equivToUnitHom,
    ← EquivLike.comp_surjective _ T.unitsEquivUnitsType.monoidHomCongrLeft.symm]
  convert MonoidHom.restrict_surjective (G := Rˣ) R' T.units
  ext φ x
  simp [MulEquiv.symm_monoidHomCongrLeft, Function.comp_apply, restrictHom_apply,
    MulEquiv.monoidHomCongrLeft_apply, MulEquiv.symm_symm, MonoidHom.coe_comp, MonoidHom.coe_coe,
    coe_equivToUnitHom, restrict_apply, Units.isUnit, ↓reduceIte, MonoidHom.restrictHom_apply,
    MonoidHom.restrict_apply]

theorem MulChar.quotientKerEquiv_aux {R : Type*} [CommMonoid R] [Finite R]
    (T : Submonoid R) (R' : Type*) [CommRing R'] [IsDomain R'] :
    Subgroup.map mulEquivToUnitHom.toMonoidHom (restrictHom T R').ker =
      (MonoidHom.restrictHom R'ˣ T.units).ker := by
  ext
  rw [Subgroup.mem_map_equiv, MonoidHom.mem_ker, MonoidHom.mem_ker,
    restrictHom_apply, MonoidHom.restrictHom_apply, restrict_eq_one_iff,
    MonoidHom.restrict_eq_one_iff, ← (Submonoid.unitsEquivUnitsType T).forall_congr_right]
  simp

def MulChar.quotientKerEquiv {R : Type*} [CommMonoid R] [Finite R] (T : Submonoid R) (R' : Type*)
    [CommRing R'] [IsDomain R'] [HasEnoughRootsOfUnity R' (Monoid.exponent Rˣ)] :
    MulChar R R' ⧸ (MulChar.restrictHom T R').ker ≃* MulChar T R' := by
  refine
    (QuotientGroup.congr (restrictHom T R').ker _ mulEquivToUnitHom rfl).trans <|
      (QuotientGroup.quotientMulEquivOfEq ?_).trans
        <| (CommGroup.monoidHomQuotientKerEquiv R' T.units).trans <|
            T.unitsEquivUnitsType.monoidHomCongrLeft.trans mulEquivToUnitHom.symm
  exact MulChar.quotientKerEquiv_aux T R'

variable (M R : Type*) [CommMonoid M] [CommRing R] [IsDomain R] [Finite M]
  [HasEnoughRootsOfUnity R (Monoid.exponent Mˣ)]

def MulChar.mulCharEquiv : MulChar (MulChar M R) R ≃* Mˣ :=
  mulEquivToUnitHom.trans <| toUnits.symm.monoidHomCongrLeft.trans <|
    mulEquivToUnitHom.monoidHomCongrLeft.trans <| CommGroup.monoidHomMonoidHomEquiv Mˣ R

@[simp]
theorem MulChar.mulCharEquiv_symm_apply_apply (m : Mˣ) (χ : MulChar M R) :
    (MulChar.mulCharEquiv M R).symm m χ = χ m := by
  unfold MulChar.mulCharEquiv
  simp [if_pos (Group.isUnit χ)]

theorem MulChar.mapSubgroup_mulCharEquiv (N : Submonoid M) :
    (MulChar.mulCharEquiv M R).symm.mapSubgroup N.units =
      (MulChar.restrictHom (MulChar.restrictHom N R).ker R).ker := by
  have := CommGroup.mapSubgroup_monoidHomMonoidHomEquiv_symm N.units R
  rw [← MulEquiv.symm_mapSubgroup, OrderIso.symm_apply_eq] at this ⊢
  rw [this]
  ext φ
  simp only [MulEquiv.coe_mapSubgroup, Subgroup.mem_map_equiv, MonoidHom.mem_ker,
    MonoidHom.restrictHom_apply, MonoidHom.restrict_eq_one_iff,
    CommGroup.monoidHomMonoidHomEquiv_symm_apply_apply, mulCharEquiv, MulEquiv.symm_trans_apply,
    MulEquiv.symm_monoidHomCongrLeft, MulEquiv.symm_symm, MulEquiv.monoidHomCongrLeft_apply,
    restrictHom_apply, restrict_eq_one_iff, mulEquivToUnitHom_symm_apply_apply, Group.isUnit,
    MonoidHom.coe_comp, MonoidHom.coe_coe, Function.comp_apply, toUnits_symm_apply,
    IsUnit.unit_spec, reduceDIte, Units.val_eq_one, ← toUnits.forall_congr_right,
    MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, val_toUnits_apply, Subtype.forall,
    ← N.unitsEquivUnitsType.forall_congr_right, Submonoid.val_unitsEquivUnitsType_apply_coe,
    Units.coeHom_apply, ← mulEquivToUnitHom.symm.forall_congr_right, MulEquiv.toEquiv_symm,
    MulEquiv.coe_toEquiv_symm, Units.isUnit, IsUnit.unit_of_val_units, MulEquiv.apply_symm_apply]

end MulChar
