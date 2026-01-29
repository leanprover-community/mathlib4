module

public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.NumberTheory.MulChar.Duality
public import Mathlib.Algebra.Group.Submonoid.Units

#exit

-- theorem Equiv.forall_mem_iff {α β : Type*} (s : Set α) (e : α ≃ β) (p : α → Prop) :
--     (∀ x ∈ s, p x) ↔ ∀ x ∈ e '' s, p (e.symm x) := by
--   constructor
--   · rintro h _ ⟨a, ha, rfl⟩
--     simpa using h a ha
--   · intro h x hx
--     simpa using h (e x) (Set.mem_image_of_mem e hx)

@[expose] public section

section mapSubgroup

@[simp]
theorem MulEquiv.mapSubgroup_trans {G H K : Type*} [Group G] [Group H] [Group K] (f : G ≃* H)
    (g : H ≃* K) : f.mapSubgroup.trans g.mapSubgroup = (f.trans g).mapSubgroup := by
  ext; simp

theorem MulEquiv.mapSubgroup_trans_apply {G H K : Type*} [Group G] [Group H] [Group K]
    (f : G ≃* H) (g : H ≃* K) (x : Subgroup G) :
    f.mapSubgroup.trans g.mapSubgroup x = (f.trans g).mapSubgroup x := by
  simp

end mapSubgroup

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
  [hM : HasEnoughRootsOfUnity M (Monoid.exponent G)]

-- variable {M} in
-- @[simp]
-- theorem CommGroup.forall_apply_eq_apply_iff {g g' : G} :
--     (∀ φ : G →* Mˣ, φ g = φ g') ↔ g = g' := by
--   refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
--   simp_rw (config := {singlePass := true}) [← mul_inv_eq_one, ← map_inv, ← map_mul] at h ⊢
--   contrapose! h
--   exact exists_apply_ne_one_of_hasEnoughRootsOfUnity G M h

theorem CommGroup_forall_monoidHom_apply_eq_one_iff (H : Subgroup G) (x : G) :
    (∀ (χ : G →* Mˣ), (∀ x ∈ H, χ x = 1) → χ x = 1) ↔ x ∈ H := by
  have : HasEnoughRootsOfUnity M (Monoid.exponent (G ⧸ H)) :=
    hM.of_dvd M <| Group.exponent_dvd_of_quotient H
  refine ⟨fun h ↦ ?_, fun hx χ hχ ↦ hχ x hx⟩
  contrapose! h
  rw [← (QuotientGroup.eq_one_iff x).not] at h
  obtain ⟨ψ, hψ⟩ := exists_apply_ne_one_of_hasEnoughRootsOfUnity (G ⧸ H) M h
  refine ⟨ψ.comp (QuotientGroup.mk' H), fun x hx ↦ ?_, hψ⟩
  rw [coe_comp, Function.comp_apply, QuotientGroup.coe_mk', (QuotientGroup.eq_one_iff _).mpr hx,
    map_one]

-- theorem CommGroup.forall_mem_restrictHom_ker_apply_eq_one_iff (H : Subgroup G) (x : G) :
--     (∀ χ ∈ (restrictHom Mˣ H).ker, χ x = 1) ↔ x ∈ H := by
--   simp
--   have : HasEnoughRootsOfUnity M (Monoid.exponent (G ⧸ H)) :=
--     hM.of_dvd M <| Group.exponent_dvd_of_quotient H
--   constructor
--   · intro h
--     contrapose! h
--     rw [← (QuotientGroup.eq_one_iff x).not] at h
--     obtain ⟨ψ, hψ⟩ := exists_apply_ne_one_of_hasEnoughRootsOfUnity (G ⧸ H) M h
--     refine ⟨ψ.comp (QuotientGroup.mk' H), ?_, ?_⟩
--     · rw [mem_ker, restrictHom_apply, restrict_eq_one_iff]
--       intro x hx
--       rw [coe_comp, Function.comp_apply, QuotientGroup.coe_mk', (QuotientGroup.eq_one_iff _).mpr hx,
--         map_one]
--     · simpa
--   · intro h χ hχ
--     rw [mem_ker, restrictHom_apply, restrict_eq_one_iff] at hχ
--     exact hχ x h

-- theorem CommGroup.restrictHom_ker_le_restrictHom_ker_iff {H₁ H₂ : Subgroup G} :
--     (restrictHom Mˣ H₂).ker ≤ (restrictHom Mˣ H₁).ker ↔ H₁ ≤ H₂ := by
--   simp_rw [SetLike.le_def, ← forall_mem_restrictHom_ker_apply_eq_one_iff M H₂, mem_ker,
--     restrictHom_apply, restrict_eq_one_iff]
--   exact ⟨fun  h x hx χ hχ ↦ mem_ker.mp (h hχ x hx), fun h χ hχ x hx ↦ h hx _ hχ⟩

-- Is this really useful?
-- def CommGroup.monoidHomQuotientKerEquiv (H : Subgroup G) [Finite (G →* Mˣ)]
--     [Finite (H →* Mˣ)] :
--     (G →* Mˣ) ⧸ (MonoidHom.restrictHom Mˣ H).ker ≃* (H →* Mˣ) :=
--   QuotientGroup.quotientKerEquivOfSurjective (restrictHom Mˣ H) <| restrict_surjective G M H

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

@[simp]
theorem CommGroup.apply_monoidHomMonoidHomEquiv (R : Type*) [CommRing R] [IsDomain R]
    [hR : HasEnoughRootsOfUnity R (Monoid.exponent G)] (φ : G →* Rˣ) (η : (G →* Rˣ) →* Rˣ) :
    φ (monoidHomMonoidHomEquiv G R η) = η φ := by
  rw [← monoidHomMonoidHomEquiv_symm_apply_apply G R (monoidHomMonoidHomEquiv G R η) φ,
    MulEquiv.symm_apply_apply]

-- theorem CommGroup.mapSubgroup_restrictHom_ker (R : Type*) [CommRing R] [IsDomain R]
--     [hR : HasEnoughRootsOfUnity R (Monoid.exponent G)] (H : Subgroup (G →* Rˣ)) :
--     (monoidHomMonoidHomEquiv G R).mapSubgroup (restrictHom Rˣ H).ker = ⨅ χ ∈ H, χ.ker := by
--   ext
--   rw [MulEquiv.coe_mapSubgroup, Subgroup.mem_map_equiv, MonoidHom.mem_ker]
--   simp [restrictHom_apply, restrict_eq_one_iff]

-- @[simp]
-- theorem CommGroup.forall_mem_monoidHomMonoidHomEquiv_restrictHom_ker_apply_eq_one_iff (R : Type*)
--     [CommRing R] [IsDomain R] [hR : HasEnoughRootsOfUnity R (Monoid.exponent G)]
--     (Φ : Subgroup (G →* Rˣ)) (φ : G →* Rˣ) :
--     (∀ g ∈ (monoidHomMonoidHomEquiv G R).mapSubgroup (restrictHom Rˣ Φ).ker, φ g = 1) ↔ φ ∈ Φ := by
--   have : HasEnoughRootsOfUnity R (Monoid.exponent (G →* Rˣ)) := by
--     rwa [Monoid.exponent_eq_of_mulEquiv (monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G R).some]
--   simpa using forall_mem_restrictHom_ker_apply_eq_one_iff R Φ φ

variable (G) in
@[simps apply symm_apply]
def CommGroup.subgroupOrderIsoSubgroupMonoidHom (R : Type*) [CommRing R] [IsDomain R]
    [hR : HasEnoughRootsOfUnity R (Monoid.exponent G)] :
    Subgroup G ≃o (Subgroup (G →* Rˣ))ᵒᵈ where
  toFun H := OrderDual.toDual (restrictHom Rˣ H).ker
  invFun Φ := (monoidHomMonoidHomEquiv G R).mapSubgroup (restrictHom Rˣ Φ.ofDual).ker
  left_inv H := by
    ext x
    simp_rw [mapSubgroup_restrictHom_ker]
    simpa using forall_mem_restrictHom_ker_apply_eq_one_iff R H x
  right_inv Φ := by
    ext φ
    simpa only [OrderDual.ofDual_toDual, mem_ker, restrictHom_apply, restrict_eq_one_iff]
      using forall_mem_monoidHomMonoidHomEquiv_restrictHom_ker_apply_eq_one_iff R Φ.ofDual φ
  map_rel_iff' := by
    intro H₁ H₂
    simp only [MulEquiv.mapSubgroup_apply, Equiv.coe_fn_mk, ge_iff_le, OrderDual.toDual_le_toDual]
    exact restrictHom_ker_le_restrictHom_ker_iff R

theorem CommGroup.forall_mem_subgroupOrderIsoSubgroupMonoidHom_apply_eq_one_iff (R : Type*)
    [CommRing R] [IsDomain R] [hR : HasEnoughRootsOfUnity R (Monoid.exponent G)] (H : Subgroup G)
    (g : G) :
    (∀ φ ∈ (subgroupOrderIsoSubgroupMonoidHom G R H).ofDual, φ g = 1) ↔ g ∈ H :=
  forall_mem_restrictHom_ker_apply_eq_one_iff R H g

theorem CommGroup.forall_mem_subgroupOrderIsoSubgroupMonoidHom_symm_apply_eq_one_iff (R : Type*)
    [CommRing R] [IsDomain R] [hR : HasEnoughRootsOfUnity R (Monoid.exponent G)]
    (Φ : Subgroup (G →* Rˣ)) (φ : G →* Rˣ) :
    (∀ g ∈ (subgroupOrderIsoSubgroupMonoidHom G R).symm (OrderDual.toDual Φ), φ g = 1) ↔ φ ∈ Φ :=
  forall_mem_monoidHomMonoidHomEquiv_restrictHom_ker_apply_eq_one_iff R Φ φ


-- Rephrase this one as below if needed
-- theorem CommGroup.mapSubgroup_monoidHomMonoidHomEquiv_symm (H : Subgroup G) (R : Type*) [CommRing R]
--     [IsDomain R] [hR : HasEnoughRootsOfUnity R (Monoid.exponent G)] :
--     (monoidHomMonoidHomEquiv G R).symm.mapSubgroup H =
--       (restrictHom Rˣ (restrictHom Rˣ H).ker).ker := by
--   rw [← MulEquiv.symm_mapSubgroup, OrderIso.symm_apply_eq]
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

-- Mathlib.Topology.Algebra.PontryaginDual

end CommGroup

noncomputable section MulChar

open MulChar

theorem MulChar.inv_apply'' {R' : Type*} [CommMonoidWithZero R'] {R : Type*} [CommMonoid R]
    (χ : MulChar R R') (a : Rˣ) :
    χ⁻¹ a = χ (a⁻¹ : Rˣ) := by
  rw [inv_apply_eq_inv]
  have h := IsUnit.map χ a.isUnit
  apply_fun (χ a * ·) using IsUnit.mul_right_injective h
  simp [Ring.mul_inverse_cancel _ h, ← map_mul, Units.mul_inv, MulChar.map_one]

def MulChar.ker' {R : Type*} [CommMonoid R] (R' : Type*) [CommMonoidWithZero R']
    (χ : MulChar R R') :
    Subgroup Rˣ where
  carrier := {x | χ x = 1}
  mul_mem' hx hy := by
    rw [Set.mem_setOf_eq] at hx hy ⊢
    rw [Units.val_mul, map_mul, hx, hy, mul_one]
  one_mem' := by simp
  inv_mem' {x} hx := by
    rw [Set.mem_setOf_eq] at hx ⊢
    rw [← MulChar.inv_apply'', inv_apply_eq_inv, hx, Ring.inverse_one]

def MulChar.ker {R : Type*} [CommMonoid R] (R' : Type*) [CommMonoidWithZero R']
    (χ : MulChar R R') : Subgroup Rˣ := χ.toUnitHom.ker

@[simp]
theorem MulChar.mem_ker_iff {R : Type*} [CommMonoid R] (R' : Type*) [CommMonoidWithZero R']
    {χ : MulChar R R'} {x : Rˣ} :
    x ∈ χ.ker ↔ χ x = 1 := by
  unfold ker
  simp [Units.ext_iff]

theorem MulChar.forall_apply_eq_apply_iff {M R : Type*} [CommMonoid M] [CommRing R] [Finite M]
    [HasEnoughRootsOfUnity R (Monoid.exponent Mˣ)] {a b : Mˣ} :
    (∀ χ : MulChar M R, χ a = χ b) ↔ a = b := by
  simp only [← MulChar.coe_equivToUnitHom, ← Units.ext_iff]
  rw [equivToUnitHom.forall_congr_right (q := fun χ ↦ χ a = χ b)]
  exact CommGroup.forall_apply_eq_apply_iff

@[simps!]
def MulChar.restrict {R : Type*} {S : Type*} [CommMonoid R] [SetLike S R] [SubmonoidClass S R]
    (R' : Type*) [CommMonoidWithZero R'] (T : S) (χ : MulChar R R') : MulChar T R' :=
  ofUnitHom <| χ.toUnitHom.comp <| Units.map (SubmonoidClass.subtype T)

@[simp]
theorem MulChar.restrict_eq_one_iff {R : Type*} {S : Type*} [CommMonoid R] [SetLike S R]
    [SubmonoidClass S R] (R' : Type*) (T : S) [CommMonoidWithZero R'] (χ : MulChar R R') :
    χ.restrict R' T = 1 ↔ ∀ x : Tˣ, χ x = 1 := by
  simp [eq_one_iff]

theorem MulChar.restrict_ofUnitHom {R : Type*} [CommMonoid R] {R' : Type*} [CommMonoidWithZero R']
    (f : Rˣ →* R'ˣ) (S : Submonoid R) :
    restrict R' S (ofUnitHom f) =
      ofUnitHom ((f.restrict S.units).comp S.unitsEquivUnitsType.symm) := by
  ext x
  simp only [ofUnitHom_eq, restrict_apply, Units.isUnit, reduceIte, equivToUnitHom_symm_coe,
    MonoidHom.coe_comp, MonoidHom.coe_coe, Function.comp_apply, MonoidHom.restrict_apply]
  rw [← Submonoid.val_unitsEquivUnitsType_symm_apply_coe S x, equivToUnitHom_symm_coe]

theorem MulChar.restrict_toUnitHom {R : Type*} [CommMonoid R] {R' : Type*} [CommMonoidWithZero R']
    (S : Submonoid R) (χ : MulChar R R') :
    (restrict R' S χ).toUnitHom =
      (((χ.toUnitHom).restrict S.units).comp S.unitsEquivUnitsType.symm) := by
  rw [toUnitHom_eq, show χ = ofUnitHom χ.toUnitHom by ext; simp, restrict_ofUnitHom]
  simp

@[simps!]
def MulChar.ofQuotient {R : Type*} [CommRing R] (I : Ideal R) (R' : Type*) [CommMonoidWithZero R']
    (χ : MulChar (R ⧸ I) R') : MulChar R R' :=
  ofUnitHom <| χ.toUnitHom.comp (Units.map (Ideal.Quotient.mk I).toMonoidHom)

@[simps]
def MulChar.restrictHom {R : Type*} {S : Type*} [CommMonoid R] [SetLike S R]
    [SubmonoidClass S R] (R' : Type*) [CommMonoidWithZero R'] (T : S) :
    MulChar R R' →* MulChar T R' where
  toFun := fun χ ↦ restrict R' T χ
  map_one' := by
    ext x
    rw [restrict_apply, if_pos x.isUnit, MulChar.one_apply x.isUnit.coe, one_apply_coe]
  map_mul' _ _ := by ext; simp

theorem MulChar.mulEquivToUnitHom_map_restricHom_ker {R : Type*} [CommMonoid R] (R' : Type*)
    [CommMonoidWithZero R'] (T : Submonoid R) :
    mulEquivToUnitHom.mapSubgroup (restrictHom R' T).ker =
      (MonoidHom.restrictHom R'ˣ T.units).ker := by
  ext
  rw [MulEquiv.coe_mapSubgroup, Subgroup.mem_map_equiv, MonoidHom.mem_ker, MonoidHom.mem_ker,
    restrictHom_apply, MonoidHom.restrictHom_apply, restrict_eq_one_iff,
    MonoidHom.restrict_eq_one_iff, ← (Submonoid.unitsEquivUnitsType T).forall_congr_right]
  simp

theorem MulChar.restrictHom_surjective (R : Type*) [Finite R] [CommMonoid R] (T : Submonoid R)
    (R' : Type*) [CommRing R'] [IsDomain R'] [HasEnoughRootsOfUnity R' (Monoid.exponent Rˣ)] :
    Function.Surjective (MulChar.restrictHom R' T) := by
  intro χ
  obtain ⟨ψ, hψ⟩ := (χ.toUnitHom.comp T.unitsEquivUnitsType).restrict_surjective Rˣ R' T.units
  refine ⟨MulChar.ofUnitHom ψ, ?_⟩
  ext
  rw [MonoidHom.restrictHom_apply] at hψ
  rw [restrictHom_apply, restrict_ofUnitHom, hψ]
  simp

-- This is proved already in `MulChar.mulEquivToUnitHom_map_restricHom_ker`
theorem MulChar.quotientKerEquiv_aux {R : Type*} [CommMonoid R] (T : Submonoid R) (R' : Type*)
    [CommRing R'] :
    Subgroup.map mulEquivToUnitHom.toMonoidHom (restrictHom R' T).ker =
      (MonoidHom.restrictHom R'ˣ T.units).ker := by
  ext
  rw [Subgroup.mem_map_equiv, MonoidHom.mem_ker, MonoidHom.mem_ker,
    restrictHom_apply, MonoidHom.restrictHom_apply, restrict_eq_one_iff,
    MonoidHom.restrict_eq_one_iff, ← (Submonoid.unitsEquivUnitsType T).forall_congr_right]
  simp

def MulChar.quotientKerEquiv {R : Type*} [CommMonoid R] [Finite R] (T : Submonoid R) (R' : Type*)
    [CommRing R'] [IsDomain R'] [HasEnoughRootsOfUnity R' (Monoid.exponent Rˣ)] :
    MulChar R R' ⧸ (MulChar.restrictHom R' T).ker ≃* MulChar T R' := by
  refine
    (QuotientGroup.congr (restrictHom R' T).ker _ mulEquivToUnitHom rfl).trans <|
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

theorem MulChar.map_mulCharEquiv_restrictHom_ker (Y : Subgroup (MulChar M R)) :
    (MulChar.mulCharEquiv M R).mapSubgroup (MulChar.restrictHom R Y).ker = ⨅ χ ∈ Y, χ.ker := by
  ext
  rw [MulEquiv.coe_mapSubgroup, Subgroup.mem_map_equiv, MonoidHom.mem_ker]
  simp [restrictHom_apply, restrict_eq_one_iff, ← toUnits.forall_congr_right]

def MulChar.subgroupOrderIsoSubgroupMulChar :
    Subgroup (MulChar M R) ≃o (Subgroup (MulChar (MulChar M R) R))ᵒᵈ :=
  haveI : HasEnoughRootsOfUnity R (Monoid.exponent (MulChar M R)) := by
    rwa [Monoid.exponent_eq_of_mulEquiv mulEquivToUnitHom,
      Monoid.exponent_eq_of_mulEquiv
        (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity Mˣ R).some]
  (CommGroup.subgroupOrderIsoSubgroupMonoidHom (MulChar M R) R).trans <|
   toUnits.monoidHomCongrLeft.mapSubgroup.dual.trans mulEquivToUnitHom.mapSubgroup.dual.symm

@[simp]
theorem MulChar.subgroupOrderIsoSubgroupMulChar_apply (Y : Subgroup (MulChar M R)) :
     MulChar.subgroupOrderIsoSubgroupMulChar M R Y = OrderDual.toDual (restrictHom R Y).ker := by
  unfold subgroupOrderIsoSubgroupMulChar
  simp only [OrderIso.trans_apply, OrderIso.dual_apply, OrderIso.dual_symm_apply,
    OrderDual.ofDual_toDual, EmbeddingLike.apply_eq_iff_eq]
  rw [← EquivLike.apply_eq_iff_eq (MulChar.mulEquivToUnitHom
    (R := MulChar M R) (R' := R)).mapSubgroup]
  erw [OrderIso.apply_symm_apply, mulEquivToUnitHom_map_restricHom_ker]
  rw [CommGroup.subgroupOrderIsoSubgroupMonoidHom_apply, OrderDual.ofDual_toDual]
  ext φ
  erw [Subgroup.mem_map_equiv]
  simp_rw [MonoidHom.mem_ker, MonoidHom.restrictHom_apply, MonoidHom.restrict_eq_one_iff]
  rw [← toUnits.forall_congr_right]
  simp

theorem MulChar.forall_mem_subgroupOrderIsoSubgroupMulChar_apply_eq_one_iff
    (Y : Subgroup (MulChar M R)) (χ : MulChar M R) :
    (∀ η ∈ (subgroupOrderIsoSubgroupMulChar M R Y).ofDual, η χ = 1) ↔ χ ∈ Y := sorry

theorem MulChar.forall_mem_subgroupOrderIsoSubgroupMulChar_symm_apply_eq_one_iff
    (E : Subgroup (MulChar (MulChar M R) R)) (η : MulChar (MulChar M R) R) :
    (∀ χ ∈ (subgroupOrderIsoSubgroupMulChar M R).symm (OrderDual.toDual E), η χ = 1) ↔
      η ∈ E := by
  sorry

-- theorem MulChar.mapSubgroup_mulCharEquiv (N : Submonoid M) :
--     (MulChar.mulCharEquiv M R).symm.mapSubgroup N.units =
--       (MulChar.restrictHom (MulChar.restrictHom N R).ker R).ker := by
--   have := CommGroup.mapSubgroup_monoidHomMonoidHomEquiv_symm N.units R
--   rw [← MulEquiv.symm_mapSubgroup, OrderIso.symm_apply_eq] at this ⊢
--   rw [this]
--   ext φ
--   simp only [MulEquiv.coe_mapSubgroup, Subgroup.mem_map_equiv, MonoidHom.mem_ker,
--     MonoidHom.restrictHom_apply, MonoidHom.restrict_eq_one_iff,
--     CommGroup.monoidHomMonoidHomEquiv_symm_apply_apply, mulCharEquiv, MulEquiv.symm_trans_apply,
--     MulEquiv.symm_monoidHomCongrLeft, MulEquiv.symm_symm, MulEquiv.monoidHomCongrLeft_apply,
--     restrictHom_apply, restrict_eq_one_iff, mulEquivToUnitHom_symm_apply_apply, Group.isUnit,
--     MonoidHom.coe_comp, MonoidHom.coe_coe, Function.comp_apply, toUnits_symm_apply,
--     IsUnit.unit_spec, reduceDIte, Units.val_eq_one, ← toUnits.forall_congr_right,
--     MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, val_toUnits_apply, Subtype.forall,
--     ← N.unitsEquivUnitsType.forall_congr_right, Submonoid.val_unitsEquivUnitsType_apply_coe,
--     Units.coeHom_apply, ← mulEquivToUnitHom.symm.forall_congr_right, MulEquiv.toEquiv_symm,
--     MulEquiv.coe_toEquiv_symm, Units.isUnit, IsUnit.unit_of_val_units, MulEquiv.apply_symm_apply]

end MulChar
