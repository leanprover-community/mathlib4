/-
Copyright (c) 2020 Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Patrick Lutz, Yongle Hu, Jingting Wang
-/
import Mathlib.FieldTheory.Fixed
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# Galois Extensions

In this file we define Galois extensions as extensions which are both separable and normal.

## Main definitions

- `IsGalois F E` where `E` is an extension of `F`
- `fixedField H` where `H : Subgroup (E ≃ₐ[F] E)`
- `fixingSubgroup K` where `K : IntermediateField F E`
- `intermediateFieldEquivSubgroup` where `E/F` is finite dimensional and Galois

## Main results

- `IntermediateField.fixingSubgroup_fixedField` : If `E/F` is finite dimensional (but not
  necessarily Galois) then `fixingSubgroup (fixedField H) = H`
- `IsGalois.fixedField_fixingSubgroup`: If `E/F` is finite dimensional and Galois
  then `fixedField (fixingSubgroup K) = K`

Together, these two results prove the Galois correspondence.

- `IsGalois.tfae` : Equivalent characterizations of a Galois extension of finite degree

## Additional results

- Instances for `Algebra.IsQuadraticExtension`: a quadratic extension is Galois (if separable)
  with cyclic and thus abelian Galois group.

-/


open scoped Polynomial IntermediateField

open Module AlgEquiv IntermediateField

section

variable (F : Type*) [Field F] (E : Type*) [Field E] [Algebra F E]

/-- A field extension E/F is Galois if it is both separable and normal. Note that in mathlib
a separable extension of fields is by definition algebraic. -/
@[stacks 09I0]
class IsGalois : Prop where
  [to_isSeparable : Algebra.IsSeparable F E]
  [to_normal : Normal F E]

variable {F E}

theorem isGalois_iff : IsGalois F E ↔ Algebra.IsSeparable F E ∧ Normal F E :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h =>
    { to_isSeparable := h.1
      to_normal := h.2 }⟩

attribute [instance 100] IsGalois.to_isSeparable IsGalois.to_normal

-- see Note [lower instance priority]
variable (F E)

namespace IsGalois

instance self : IsGalois F F :=
  ⟨⟩

variable {E}

theorem integral [IsGalois F E] (x : E) : IsIntegral F x :=
  to_normal.isIntegral x

theorem separable [IsGalois F E] (x : E) : IsSeparable F x :=
  Algebra.IsSeparable.isSeparable F x

theorem splits [IsGalois F E] (x : E) : (minpoly F x).Splits (algebraMap F E) :=
  Normal.splits' x

variable (E)

/-- Let $E$ be a field. Let $G$ be a finite group acting on $E$.
Then the extension $E / E^G$ is Galois. -/
@[stacks 09I3 "first part"]
instance of_fixed_field (G : Type*) [Group G] [Finite G] [MulSemiringAction G E] :
    IsGalois (FixedPoints.subfield G E) E :=
  ⟨⟩

theorem IntermediateField.AdjoinSimple.card_aut_eq_finrank [FiniteDimensional F E] {α : E}
    (hα : IsIntegral F α) (h_sep : IsSeparable F α)
    (h_splits : (minpoly F α).Splits (algebraMap F F⟮α⟯)) :
    Nat.card (F⟮α⟯ ≃ₐ[F] F⟮α⟯) = finrank F F⟮α⟯ := by
  rw [IntermediateField.adjoin.finrank hα]
  rw [← IntermediateField.card_algHom_adjoin_integral F hα h_sep h_splits]
  exact Nat.card_congr (algEquivEquivAlgHom F F⟮α⟯)

/-- Let $E / F$ be a finite extension of fields. If $E$ is Galois over $F$, then
$|\text{Aut}(E/F)| = [E : F]$. -/
@[stacks 09I1 "'only if' part"]
theorem card_aut_eq_finrank [FiniteDimensional F E] [IsGalois F E] :
    Nat.card (E ≃ₐ[F] E) = finrank F E := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F E
  let iso : F⟮α⟯ ≃ₐ[F] E :=
    { toFun := fun e => e.val
      invFun := fun e => ⟨e, by rw [hα]; exact IntermediateField.mem_top⟩
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have H : IsIntegral F α := IsGalois.integral F α
  have h_sep : IsSeparable F α := IsGalois.separable F α
  have h_splits : (minpoly F α).Splits (algebraMap F E) := IsGalois.splits F α
  replace h_splits : Polynomial.Splits (algebraMap F F⟮α⟯) (minpoly F α) := by
    simpa using
      Polynomial.splits_comp_of_splits (algebraMap F E) iso.symm.toAlgHom.toRingHom h_splits
  rw [← LinearEquiv.finrank_eq iso.toLinearEquiv]
  rw [← IntermediateField.AdjoinSimple.card_aut_eq_finrank F E H h_sep h_splits]
  apply Nat.card_congr
  exact Equiv.mk (fun ϕ => iso.trans (ϕ.trans iso.symm)) fun ϕ => iso.symm.trans (ϕ.trans iso)

/-- A galois extension with finite galois group is finite dimensional.
The dimension is then equal to the order of the galois group via `IsGalois.card_aut_eq_finrank`. -/
lemma finiteDimensional_of_finite [IsGalois F E] [Finite (E ≃ₐ[F] E)] : FiniteDimensional F E := by
  by_contra H
  obtain ⟨K, h₁, h₂⟩ := exists_lt_finrank_of_infinite_dimensional H (Nat.card (E ≃ₐ[F] E))
  let K' := normalClosure F K E
  have : IsGalois F K' := ⟨⟩
  have := Nat.card_le_card_of_surjective _
    (AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := K') (E := E))
  rw [IsGalois.card_aut_eq_finrank] at this
  exact (this.trans_lt h₂).not_ge (finrank_le_of_le_right K.le_normalClosure)

end IsGalois

end

section IsGaloisTower

variable (F K E : Type*) [Field F] [Field K] [Field E] {E' : Type*} [Field E'] [Algebra F E']
variable [Algebra F K] [Algebra F E] [Algebra K E] [IsScalarTower F K E]

/-- Let $E / K / F$ be a tower of field extensions.
If $E$ is Galois over $F$, then $E$ is Galois over $K$. -/
@[stacks 09I2]
theorem IsGalois.tower_top_of_isGalois [IsGalois F E] : IsGalois K E :=
  { to_isSeparable := Algebra.isSeparable_tower_top_of_isSeparable F K E
    to_normal := Normal.tower_top_of_normal F K E }

variable {F E}

-- see Note [lower instance priority]
instance (priority := 100) IsGalois.tower_top_intermediateField (K : IntermediateField F E)
    [IsGalois F E] : IsGalois K E :=
  IsGalois.tower_top_of_isGalois F K E

theorem isGalois_iff_isGalois_bot : IsGalois (⊥ : IntermediateField F E) E ↔ IsGalois F E := by
  constructor
  · intro h
    exact IsGalois.tower_top_of_isGalois (⊥ : IntermediateField F E) F E
  · intro h; infer_instance

theorem IsGalois.of_algEquiv [IsGalois F E] (f : E ≃ₐ[F] E') : IsGalois F E' :=
  { to_isSeparable := Algebra.IsSeparable.of_algHom F E f.symm
    to_normal := Normal.of_algEquiv f }

theorem AlgEquiv.transfer_galois (f : E ≃ₐ[F] E') : IsGalois F E ↔ IsGalois F E' :=
  ⟨fun _ => IsGalois.of_algEquiv f, fun _ => IsGalois.of_algEquiv f.symm⟩

theorem isGalois_iff_isGalois_top : IsGalois F (⊤ : IntermediateField F E) ↔ IsGalois F E :=
  (IntermediateField.topEquiv : (⊤ : IntermediateField F E) ≃ₐ[F] E).transfer_galois

instance isGalois_bot : IsGalois F (⊥ : IntermediateField F E) :=
  (IntermediateField.botEquiv F E).transfer_galois.mpr (IsGalois.self F)

theorem IsGalois.of_equiv_equiv {M N : Type*} [Field N] [Field M] [Algebra M N]
    [Algebra.IsAlgebraic F E] [h : IsGalois F E] {f : F ≃+* M} {g : E ≃+* N}
    (hcomp : (algebraMap M N).comp f = (g : E →+* N).comp (algebraMap F E)) :
    IsGalois M N :=
  isGalois_iff.mpr ⟨Algebra.IsSeparable.of_equiv_equiv f g hcomp, Normal.of_equiv_equiv hcomp⟩

end IsGaloisTower

section GaloisCorrespondence

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]
variable (H : Subgroup (E ≃ₐ[F] E)) (K : IntermediateField F E)

/-- The intermediate field of fixed points fixed by a monoid action that commutes with the
`F`-action on `E`. -/
def FixedPoints.intermediateField (M : Type*) [Monoid M] [MulSemiringAction M E]
    [SMulCommClass M F E] : IntermediateField F E :=
  { FixedPoints.subfield M E with
    carrier := MulAction.fixedPoints M E
    algebraMap_mem' := fun a g => smul_algebraMap g a }

@[simp] lemma FixedPoints.mem_intermediateField_iff
    {M : Type*} [Monoid M] [MulSemiringAction M E] [SMulCommClass M F E] {x : E} :
    x ∈ FixedPoints.intermediateField (F := F) M ↔ ∀ m : M, m • x = x := .rfl

namespace IntermediateField

/-- The intermediate field fixed by a subgroup. -/
def fixedField : IntermediateField F E :=
  FixedPoints.intermediateField H

@[simp] lemma mem_fixedField_iff (x) :
    x ∈ fixedField H ↔ ∀ f ∈ H, f x = x := by
  change x ∈ MulAction.fixedPoints H E ↔ _
  simp only [MulAction.mem_fixedPoints, Subtype.forall, Subgroup.mk_smul, AlgEquiv.smul_def]

@[simp] lemma fixedField_bot : fixedField (⊥ : Subgroup (E ≃ₐ[F] E)) = ⊤ := by
  ext
  simp

theorem finrank_fixedField_eq_card [FiniteDimensional F E] :
    finrank (fixedField H) E = Nat.card H := by
  have := Fintype.ofFinite H
  rw [Nat.card_eq_fintype_card]
  exact FixedPoints.finrank_eq_card H E

/-- The subgroup fixing an intermediate field. -/
nonrec def fixingSubgroup : Subgroup (E ≃ₐ[F] E) :=
  fixingSubgroup (E ≃ₐ[F] E) (K : Set E)

theorem le_iff_le : K ≤ fixedField H ↔ H ≤ fixingSubgroup K :=
  ⟨fun h g hg x => h (Subtype.mem x) ⟨g, hg⟩, fun h x hx g => h (Subtype.mem g) ⟨x, hx⟩⟩

/-- The map `K ↦ Gal(E/K)` is inclusion-reversing. -/
theorem fixingSubgroup_le {K1 K2 : IntermediateField F E} (h12 : K1 ≤ K2) :
    K2.fixingSubgroup ≤ K1.fixingSubgroup :=
  fun _ hσ ⟨x, hx⟩ ↦ hσ ⟨x, h12 hx⟩

@[deprecated (since := "2025-05-02")] alias fixingSubgroup.antimono := fixingSubgroup_le

theorem fixedField_le {H1 H2 : Subgroup (E ≃ₐ[F] E)} (h12 : H1 ≤ H2) :
    fixedField H2 ≤ fixedField H1 :=
  fun _ hσ ⟨x, hx⟩ ↦ hσ ⟨x, h12 hx⟩

lemma fixingSubgroup_antitone : Antitone (@fixingSubgroup F _ E _ _) :=
  fun _ _ ↦ fixingSubgroup_le

@[deprecated (since := "2025-05-02")] alias fixingSubgroup_anti := fixingSubgroup_antitone

lemma fixedField_antitone : Antitone (@fixedField F _ E _ _) :=
  fun _ _ ↦ fixedField_le

@[simp] lemma mem_fixingSubgroup_iff (σ) : σ ∈ fixingSubgroup K ↔ ∀ x ∈ K, σ x = x :=
  _root_.mem_fixingSubgroup_iff _

@[simp] lemma fixingSubgroup_top : fixingSubgroup (⊤ : IntermediateField F E) = ⊥ := by
  ext
  simp [DFunLike.ext_iff]

@[simp] lemma fixingSubgroup_bot : fixingSubgroup (⊥ : IntermediateField F E) = ⊤ := by
  ext
  simp [mem_bot]

theorem fixingSubgroup_sup {K L : IntermediateField F E} :
    (K ⊔ L).fixingSubgroup = K.fixingSubgroup ⊓ L.fixingSubgroup := by
  ext φ
  exact ⟨fun h ↦ ⟨fixingSubgroup_antitone le_sup_left h, fixingSubgroup_antitone le_sup_right h⟩,
    by simp [← Subgroup.zpowers_le, ← IntermediateField.le_iff_le]⟩

/-- The fixing subgroup of `K : IntermediateField F E` is isomorphic to `E ≃ₐ[K] E`. -/
def fixingSubgroupEquiv : fixingSubgroup K ≃* E ≃ₐ[K] E where
  toFun ϕ := { AlgEquiv.toRingEquiv (ϕ : E ≃ₐ[F] E) with commutes' := ϕ.mem }
  invFun ϕ := ⟨ϕ.restrictScalars _, ϕ.commutes⟩
  map_mul' _ _ := by ext; rfl

theorem fixingSubgroup_fixedField [FiniteDimensional F E] : fixingSubgroup (fixedField H) = H := by
  have H_le : H ≤ fixingSubgroup (fixedField H) := (le_iff_le _ _).mp le_rfl
  classical
  suffices Nat.card H = Nat.card (fixingSubgroup (fixedField H)) by
    exact SetLike.coe_injective (Set.eq_of_inclusion_surjective
      ((Nat.bijective_iff_injective_and_card (Set.inclusion H_le)).mpr
        ⟨Set.inclusion_injective H_le, this⟩).2).symm
  apply Nat.card_congr
  refine (FixedPoints.toAlgHomEquiv H E).trans ?_
  refine (algEquivEquivAlgHom (fixedField H) E).toEquiv.symm.trans ?_
  exact (fixingSubgroupEquiv (fixedField H)).toEquiv.symm

/--
A subgroup is isomorphic to the Galois group of its fixed field.
-/
def subgroupEquivAlgEquiv [FiniteDimensional F E] (H : Subgroup (E ≃ₐ[F] E)) :
    H ≃* E ≃ₐ[IntermediateField.fixedField H] E :=
 (MulEquiv.subgroupCongr (fixingSubgroup_fixedField H).symm).trans (fixingSubgroupEquiv _)

instance fixedField.smul : SMul K (fixedField (fixingSubgroup K)) where
  smul x y := ⟨x * y, fun ϕ => by
    rw [smul_mul', show ϕ • (x : E) = ↑x from ϕ.2 x, show ϕ • (y : E) = ↑y from y.2 ϕ]⟩

instance fixedField.algebra : Algebra K (fixedField (fixingSubgroup K)) where
  algebraMap :=
  { toFun x := ⟨x, fun ϕ => Subtype.mem ϕ x⟩
    map_zero' := rfl
    map_add' _ _ := rfl
    map_one' := rfl
    map_mul' _ _ := rfl }
  commutes' _ _ := mul_comm _ _
  smul_def' _ _ := rfl

instance fixedField.isScalarTower : IsScalarTower K (fixedField (fixingSubgroup K)) E :=
  ⟨fun _ _ _ => mul_assoc _ _ _⟩

end IntermediateField

namespace IsGalois

theorem fixedField_fixingSubgroup [FiniteDimensional F E] [h : IsGalois F E] :
    IntermediateField.fixedField (IntermediateField.fixingSubgroup K) = K := by
  have K_le : K ≤ IntermediateField.fixedField (IntermediateField.fixingSubgroup K) :=
    (IntermediateField.le_iff_le _ _).mpr le_rfl
  suffices
    finrank K E = finrank (IntermediateField.fixedField (IntermediateField.fixingSubgroup K)) E by
    exact (IntermediateField.eq_of_le_of_finrank_eq' K_le this).symm
  classical
  rw [IntermediateField.finrank_fixedField_eq_card,
    Nat.card_congr (IntermediateField.fixingSubgroupEquiv K).toEquiv]
  exact (card_aut_eq_finrank K E).symm

@[simp] lemma fixedField_top [IsGalois F E] [FiniteDimensional F E] :
    fixedField (⊤ : Subgroup (E ≃ₐ[F] E)) = ⊥ := by
  rw [← fixingSubgroup_bot, fixedField_fixingSubgroup]

theorem mem_bot_iff_fixed [IsGalois F E] [FiniteDimensional F E] (x : E) :
    x ∈ (⊥ : IntermediateField F E) ↔ ∀ f : E ≃ₐ[F] E, f x = x := by
  rw [← fixedField_top, mem_fixedField_iff]
  simp only [Subgroup.mem_top, forall_const]

theorem mem_range_algebraMap_iff_fixed [IsGalois F E] [FiniteDimensional F E] (x : E) :
    x ∈ Set.range (algebraMap F E) ↔ ∀ f : E ≃ₐ[F] E, f x = x :=
  mem_bot_iff_fixed x

theorem card_fixingSubgroup_eq_finrank [FiniteDimensional F E] [IsGalois F E] :
    Nat.card (IntermediateField.fixingSubgroup K) = finrank K E := by
  conv_rhs => rw [← fixedField_fixingSubgroup K, IntermediateField.finrank_fixedField_eq_card]

/-- The Galois correspondence from intermediate fields to subgroups. -/
@[stacks 09DW]
def intermediateFieldEquivSubgroup [FiniteDimensional F E] [IsGalois F E] :
    IntermediateField F E ≃o (Subgroup (E ≃ₐ[F] E))ᵒᵈ where
  toFun := IntermediateField.fixingSubgroup
  invFun := IntermediateField.fixedField
  left_inv K := fixedField_fixingSubgroup K
  right_inv H := IntermediateField.fixingSubgroup_fixedField H
  map_rel_iff' {K L} := by
    rw [← fixedField_fixingSubgroup L, IntermediateField.le_iff_le, fixedField_fixingSubgroup L]
    rfl

/-- The Galois correspondence as a `GaloisInsertion`. -/
def galoisInsertionIntermediateFieldSubgroup [FiniteDimensional F E] :
    GaloisInsertion (OrderDual.toDual ∘
      (IntermediateField.fixingSubgroup : IntermediateField F E → Subgroup (E ≃ₐ[F] E)))
      ((IntermediateField.fixedField : Subgroup (E ≃ₐ[F] E) → IntermediateField F E) ∘
        OrderDual.toDual) where
  choice K _ := IntermediateField.fixingSubgroup K
  gc K H := (IntermediateField.le_iff_le H K).symm
  le_l_u H := le_of_eq (IntermediateField.fixingSubgroup_fixedField H).symm
  choice_eq _ _ := rfl

/-- The Galois correspondence as a `GaloisCoinsertion`. -/
def galoisCoinsertionIntermediateFieldSubgroup [FiniteDimensional F E] [IsGalois F E] :
    GaloisCoinsertion (OrderDual.toDual ∘
      (IntermediateField.fixingSubgroup : IntermediateField F E → Subgroup (E ≃ₐ[F] E)))
      ((IntermediateField.fixedField : Subgroup (E ≃ₐ[F] E) → IntermediateField F E) ∘
        OrderDual.toDual) :=
  OrderIso.toGaloisCoinsertion intermediateFieldEquivSubgroup

end IsGalois

section

/-In this section we prove that the normal subgroups correspond to the Galois subextensions
in the Galois correspondence and its related results. -/

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

open IntermediateField

open scoped Pointwise

lemma IntermediateField.restrictNormalHom_ker (E : IntermediateField K L) [Normal K E] :
    (restrictNormalHom E).ker = E.fixingSubgroup := by
  simp only [Subgroup.ext_iff, MonoidHom.mem_ker, AlgEquiv.ext_iff, one_apply, Subtype.ext_iff,
    restrictNormalHom_apply, Subtype.forall, mem_fixingSubgroup_iff, implies_true]

namespace IsGalois

variable (E : IntermediateField K L)

/-- If `H` is a normal Subgroup of `Gal(L / K)`, then `fixedField H` is Galois over `K`. -/
instance of_fixedField_normal_subgroup [IsGalois K L]
    (H : Subgroup (L ≃ₐ[K] L)) [hn : Subgroup.Normal H] : IsGalois K (fixedField H) where
  to_isSeparable := Algebra.isSeparable_tower_bot_of_isSeparable K (fixedField H) L
  to_normal := by
    apply normal_iff_forall_map_le'.mpr
    rintro σ x ⟨a, ha, rfl⟩ τ
    exact (symm_apply_eq σ).mp (ha ⟨σ⁻¹ * τ * σ, Subgroup.Normal.conj_mem' hn τ.1 τ.2 σ⟩)

/-- If `H` is a normal Subgroup of `Gal(L / K)`, then `Gal(fixedField H / K)` is isomorphic to
`Gal(L / K) ⧸ H`. -/
noncomputable def normalAutEquivQuotient [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup (L ≃ₐ[K] L)) [Subgroup.Normal H] :
    (L ≃ₐ[K] L) ⧸ H ≃* ((fixedField H) ≃ₐ[K] (fixedField H)) :=
  (QuotientGroup.quotientMulEquivOfEq ((fixingSubgroup_fixedField H).symm.trans
  (fixedField H).restrictNormalHom_ker.symm)).trans <|
  QuotientGroup.quotientKerEquivOfSurjective (restrictNormalHom (fixedField H)) <|
  restrictNormalHom_surjective L

lemma normalAutEquivQuotient_apply [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup (L ≃ₐ[K] L)) [Subgroup.Normal H] (σ : (L ≃ₐ[K] L)) :
    normalAutEquivQuotient H σ = (restrictNormalHom (fixedField H)) σ := rfl

open scoped Pointwise

@[simp]
theorem map_fixingSubgroup (σ : L ≃ₐ[K] L) :
    (E.map σ).fixingSubgroup = (MulAut.conj σ) • E.fixingSubgroup := by
  ext τ
  simp only [coe_map, AlgHom.coe_coe, Set.mem_image, SetLike.mem_coe, AlgEquiv.smul_def,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← symm_apply_eq,
    IntermediateField.fixingSubgroup, mem_fixingSubgroup_iff]
  rfl

/-- Let `E` be an intermediateField of a Galois extension `L / K`. If `E / K` is
Galois extension, then `E.fixingSubgroup` is a normal subgroup of `Gal(L / K)`. -/
instance fixingSubgroup_normal_of_isGalois [IsGalois K L] [IsGalois K E] :
    E.fixingSubgroup.Normal := by
  apply Subgroup.Normal.of_conjugate_fixed (fun σ ↦ ?_)
  rw [← map_fixingSubgroup, normal_iff_forall_map_eq'.mp inferInstance σ]

end IsGalois

end

end GaloisCorrespondence

section GaloisEquivalentDefinitions

variable (F : Type*) [Field F] (E : Type*) [Field E] [Algebra F E]

namespace IsGalois

theorem is_separable_splitting_field [FiniteDimensional F E] [IsGalois F E] :
    ∃ p : F[X], p.Separable ∧ p.IsSplittingField F E := by
  obtain ⟨α, h1⟩ := Field.exists_primitive_element F E
  use minpoly F α, separable F α, IsGalois.splits F α
  rw [eq_top_iff, ← IntermediateField.top_toSubalgebra, ← h1]
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_integral (integral F α)]
  apply Algebra.adjoin_mono
  rw [Set.singleton_subset_iff, Polynomial.mem_rootSet]
  exact ⟨minpoly.ne_zero (integral F α), minpoly.aeval _ _⟩

theorem of_fixedField_eq_bot [FiniteDimensional F E]
    (h : IntermediateField.fixedField (⊤ : Subgroup (E ≃ₐ[F] E)) = ⊥) : IsGalois F E := by
  rw [← isGalois_iff_isGalois_bot, ← h]
  classical exact IsGalois.of_fixed_field E (⊤ : Subgroup (E ≃ₐ[F] E))

/-- Let $E / F$ be a finite extension of fields. If $|\text{Aut}(E/F)| = [E : F]$, then
$E$ is Galois over $F$. -/
@[stacks 09I1 "'if' part"]
theorem of_card_aut_eq_finrank [FiniteDimensional F E]
    (h : Nat.card (E ≃ₐ[F] E) = finrank F E) : IsGalois F E := by
  apply of_fixedField_eq_bot
  have p : 0 < finrank (IntermediateField.fixedField (⊤ : Subgroup (E ≃ₐ[F] E))) E := finrank_pos
  classical
  rw [← IntermediateField.finrank_eq_one_iff, ← mul_left_inj' (ne_of_lt p).symm,
    finrank_mul_finrank, ← h, one_mul, IntermediateField.finrank_fixedField_eq_card]
  apply Nat.card_congr
  exact { toFun := fun g => ⟨g, Subgroup.mem_top g⟩, invFun := (↑) }

variable {F} {E}
variable {p : F[X]}

theorem of_separable_splitting_field_aux [hFE : FiniteDimensional F E] [sp : p.IsSplittingField F E]
    (hp : p.Separable) (K : Type*) [Field K] [Algebra F K] [Algebra K E] [IsScalarTower F K E]
    {x : E} (hx : x ∈ p.aroots E) :
    Nat.card (K⟮x⟯.restrictScalars F →ₐ[F] E) = Nat.card (K →ₐ[F] E) * finrank K K⟮x⟯ := by
  have h : IsIntegral K x := (isIntegral_of_noetherian (IsNoetherian.iff_fg.2 hFE) x).tower_top
  have h1 : p ≠ 0 := fun hp => by
    rw [hp, Polynomial.aroots_zero] at hx
    exact Multiset.notMem_zero x hx
  have h2 : minpoly K x ∣ p.map (algebraMap F K) := by
    apply minpoly.dvd
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← Polynomial.eval_map, ←
      IsScalarTower.algebraMap_eq]
    exact (Polynomial.mem_roots (Polynomial.map_ne_zero h1)).mp hx
  let key_equiv : (K⟮x⟯.restrictScalars F →ₐ[F] E) ≃
      Σ f : K →ₐ[F] E, @AlgHom K K⟮x⟯ E _ _ _ _ (RingHom.toAlgebra f) := by
    change (K⟮x⟯ →ₐ[F] E) ≃ Σ f : K →ₐ[F] E, _
    exact algHomEquivSigma
  haveI : ∀ f : K →ₐ[F] E, Finite (@AlgHom K K⟮x⟯ E _ _ _ _ (RingHom.toAlgebra f)) := fun f => by
    have := Finite.of_equiv _ key_equiv
    apply Finite.of_injective (Sigma.mk f) fun _ _ H => eq_of_heq (Sigma.ext_iff.mp H).2
  have : FiniteDimensional F K := FiniteDimensional.left F K E
  rw [Nat.card_congr key_equiv, Nat.card_sigma, IntermediateField.adjoin.finrank h,
    Nat.card_eq_fintype_card]
  apply Finset.sum_const_nat
  intro f _
  rw [← @IntermediateField.card_algHom_adjoin_integral K _ E _ _ x E _ (RingHom.toAlgebra f) h]
  · exact Polynomial.Separable.of_dvd ((Polynomial.separable_map (algebraMap F K)).mpr hp) h2
  · refine Polynomial.splits_of_splits_of_dvd _ (Polynomial.map_ne_zero h1) ?_ h2
    rw [Polynomial.splits_map_iff, ← IsScalarTower.algebraMap_eq]
    exact sp.splits

theorem of_separable_splitting_field [sp : p.IsSplittingField F E] (hp : p.Separable) :
    IsGalois F E := by
  haveI hFE : FiniteDimensional F E := Polynomial.IsSplittingField.finiteDimensional E p
  letI := Classical.decEq E
  let s := p.rootSet E
  have adjoin_root : IntermediateField.adjoin F s = ⊤ := by
    apply IntermediateField.toSubalgebra_injective
    rw [IntermediateField.top_toSubalgebra, ← top_le_iff, ← sp.adjoin_rootSet]
    apply IntermediateField.algebra_adjoin_le_adjoin
  let P : IntermediateField F E → Prop := fun K => Nat.card (K →ₐ[F] E) = finrank F K
  suffices P (IntermediateField.adjoin F s) by
    rw [adjoin_root] at this
    apply of_card_aut_eq_finrank
    rw [← Eq.trans this (LinearEquiv.finrank_eq IntermediateField.topEquiv.toLinearEquiv)]
    exact Nat.card_congr ((algEquivEquivAlgHom F E).toEquiv.trans
      (IntermediateField.topEquiv.symm.arrowCongr AlgEquiv.refl))
  apply IntermediateField.induction_on_adjoin_finset _ P
  · have key := IntermediateField.card_algHom_adjoin_integral F (K := E)
      (show IsIntegral F (0 : E) from isIntegral_zero)
    rw [IsSeparable, minpoly.zero, Polynomial.natDegree_X] at key
    specialize key Polynomial.separable_X (Polynomial.splits_X (algebraMap F E))
    rw [← @Subalgebra.finrank_bot F E _ _ _, ← IntermediateField.bot_toSubalgebra] at key
    refine Eq.trans ?_ key
    apply Nat.card_congr
    rw [IntermediateField.adjoin_zero]
  intro K x hx hK
  simp only [P] at *
  rw [of_separable_splitting_field_aux hp K (Multiset.mem_toFinset.mp hx), hK, finrank_mul_finrank]
  symm
  refine LinearEquiv.finrank_eq ?_
  rfl

/-- Equivalent characterizations of a Galois extension of finite degree. -/
theorem tfae [FiniteDimensional F E] : List.TFAE [
    IsGalois F E,
    IntermediateField.fixedField (⊤ : Subgroup (E ≃ₐ[F] E)) = ⊥,
    Nat.card (E ≃ₐ[F] E) = finrank F E,
    ∃ p : F[X], p.Separable ∧ p.IsSplittingField F E] := by
  tfae_have 1 → 2 := fun h ↦ OrderIso.map_bot (@intermediateFieldEquivSubgroup F _ E _ _ _ h).symm
  tfae_have 1 → 3 := fun _ ↦ card_aut_eq_finrank F E
  tfae_have 1 → 4 := fun _ ↦ is_separable_splitting_field F E
  tfae_have 2 → 1 := of_fixedField_eq_bot F E
  tfae_have 3 → 1 := of_card_aut_eq_finrank F E
  tfae_have 4 → 1 := fun ⟨h, hp1, _⟩ ↦ of_separable_splitting_field hp1
  tfae_finish

end IsGalois

end GaloisEquivalentDefinitions

section normalClosure

variable (k K F : Type*) [Field k] [Field K] [Field F] [Algebra k K] [Algebra k F] [Algebra K F]
  [IsScalarTower k K F] [IsGalois k F]

/-- Let $F / K / k$ be a tower of field extensions. If $F$ is Galois over $k$,
then the normal closure of $K$ over $k$ in $F$ is Galois over $k$. -/
@[stacks 0EXM]
instance IsGalois.normalClosure : IsGalois k (normalClosure k K F) where
  to_isSeparable := Algebra.isSeparable_tower_bot_of_isSeparable k _ F

end normalClosure

section IsAlgClosure

instance (priority := 100) IsAlgClosure.isGalois (k K : Type*) [Field k] [Field K] [Algebra k K]
    [IsAlgClosure k K] [CharZero k] : IsGalois k K where

end IsAlgClosure


section restrictRestrictAlgEquivMapHom

namespace IntermediateField

/--
The map from the `Gal(E/L)` to `Gal(K/F)` where `E/L/F` and `E/K/F` are two towers of
extensions induced by the restriction to `K`. Note that we do require `K/F` to be normal but not
`E/L`. If this is the case (and everything is finite dimensional) and `K ∩ L = F` then this
map is surjective, see `IntermediateField.restrictRestrictMapHom_surjective`.
This map is injective if the compositum of `K` and `L` is `E`,
see `IntermediateField.restrictRestrictAlgEquivMapHom_injective`.
-/
noncomputable def restrictRestrictAlgEquivMapHom (F K L E : Type*) [Field F] [Field K] [Field L]
    [Field E] [Algebra F K] [Algebra F L] [Algebra F E] [Algebra K E] [Algebra L E]
    [IsScalarTower F K E] [IsScalarTower F L E] [Normal F K] :
    (E ≃ₐ[L] E) →* (K ≃ₐ[F] K) :=
  (AlgEquiv.restrictNormalHom K).comp (MulSemiringAction.toAlgAut (E ≃ₐ[L] E) F E)

variable {F E : Type*} [Field F] [Field E] [Algebra F E] (K L : IntermediateField F E) [Normal F K]

@[simp]
theorem restrictRestrictAlgEquivMapHom_apply (φ : E ≃ₐ[L] E) (x : K) :
    restrictRestrictAlgEquivMapHom F K L E φ x = φ x := by
  simp [restrictRestrictAlgEquivMapHom, AlgEquiv.restrictNormalHom_apply]

theorem restrictRestrictAlgEquivMapHom_injective (h : K ⊔ L = ⊤) :
    Function.Injective (restrictRestrictAlgEquivMapHom F K L E) := by
  refine (injective_iff_map_eq_one _).mpr fun φ hφ ↦ ?_
  suffices h : MulSemiringAction.toAlgAut (E ≃ₐ[↥L] E) F E φ = 1 by rwa [AlgEquiv.ext_iff] at h ⊢
  rw [← Subgroup.mem_bot, ← fixingSubgroup_top, ← h, fixingSubgroup_sup]
  exact ⟨fun x ↦ (hφ ▸ restrictRestrictAlgEquivMapHom_apply K L φ x).symm, φ.commutes⟩

theorem restrictRestrictAlgEquivMapHom_surjective [FiniteDimensional F K] [FiniteDimensional L E]
    [IsGalois L E] (h : K ⊓ L = ⊥) :
    Function.Surjective (restrictRestrictAlgEquivMapHom F K L E) := by
  suffices fixedField (restrictRestrictAlgEquivMapHom F K L E).range = ⊥ from
     MonoidHom.range_eq_top.mp <|
      fixingSubgroup_fixedField (restrictRestrictAlgEquivMapHom F K L E).range ▸
        this ▸ fixingSubgroup_bot
  refine eq_bot_iff.mpr fun ⟨x, hx₁⟩ hx₂ ↦ ?_
  obtain ⟨⟨y, hy⟩, rfl⟩ : x ∈ Set.range (algebraMap L E) := by
    refine mem_bot.mp <| (IsGalois.mem_bot_iff_fixed _).mpr fun φ ↦ ?_
    rw [← restrictRestrictAlgEquivMapHom_apply K L φ ⟨x, hx₁⟩]
    rw [mem_fixedField_iff] at hx₂
    exact congr_arg ((↑) : K → E) <| hx₂ (restrictRestrictAlgEquivMapHom F K L E φ) ⟨φ, rfl⟩
  obtain ⟨z, rfl⟩ : y ∈ (⊥ : IntermediateField F E) := h ▸ mem_inf.mpr ⟨hx₁, hy⟩
  exact mem_bot.mp ⟨z, rfl⟩

end IntermediateField

end restrictRestrictAlgEquivMapHom

namespace Algebra

variable (F K : Type*) [Field F] [Field K] [Algebra F K] [IsQuadraticExtension F K]

/--
A quadratic separable extension is Galois.
-/
instance IsQuadraticExtension.isGalois [Algebra.IsSeparable F K] : IsGalois F K where

/--
A quadratic extension has cyclic Galois group.
-/
instance IsQuadraticExtension.isCyclic : IsCyclic (K ≃ₐ[F] K) := by
  have := finrank_eq_two F K ▸ AlgEquiv.card_le
  rw [← Nat.card_eq_fintype_card] at this
  interval_cases h : Nat.card (K ≃ₐ[F] K)
  · simp_all
  · exact @isCyclic_of_subsingleton _ _ (Finite.card_le_one_iff_subsingleton.mp h.le)
  · exact isCyclic_of_prime_card h

/--
A quadratic extension has abelian Galois group.
-/
instance IsQuadraticExtension.isMulCommutative_galoisGroup :
    IsMulCommutative (K ≃ₐ[F] K) := ⟨IsCyclic.commutative⟩

end Algebra
