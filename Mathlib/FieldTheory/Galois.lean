/-
Copyright (c) 2020 Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Patrick Lutz
-/
import Mathlib.FieldTheory.Fixed
import Mathlib.FieldTheory.NormalClosure
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.GroupTheory.GroupAction.FixingSubgroup

#align_import field_theory.galois from "leanprover-community/mathlib"@"9fb8964792b4237dac6200193a0d533f1b3f7423"

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
- `IntermediateField.fixedField_fixingSubgroup`: If `E/F` is finite dimensional and Galois
  then `fixedField (fixingSubgroup K) = K`

Together, these two results prove the Galois correspondence.

- `IsGalois.tfae` : Equivalent characterizations of a Galois extension of finite degree
-/


open scoped Polynomial

open FiniteDimensional AlgEquiv

section

variable (F : Type*) [Field F] (E : Type*) [Field E] [Algebra F E]

/-- A field extension E/F is Galois if it is both separable and normal. Note that in mathlib
a separable extension of fields is by definition algebraic. -/
class IsGalois : Prop where
  [to_isSeparable : IsSeparable F E]
  [to_normal : Normal F E]
#align is_galois IsGalois

variable {F E}

theorem isGalois_iff : IsGalois F E ↔ IsSeparable F E ∧ Normal F E :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h =>
    { to_isSeparable := h.1
      to_normal := h.2 }⟩
#align is_galois_iff isGalois_iff

attribute [instance 100] IsGalois.to_isSeparable IsGalois.to_normal

-- see Note [lower instance priority]
variable (F E)

namespace IsGalois

instance self : IsGalois F F :=
  ⟨⟩
#align is_galois.self IsGalois.self

variable {E}

theorem integral [IsGalois F E] (x : E) : IsIntegral F x :=
  to_normal.isIntegral x
#align is_galois.integral IsGalois.integral

theorem separable [IsGalois F E] (x : E) : (minpoly F x).Separable :=
  IsSeparable.separable F x
#align is_galois.separable IsGalois.separable

theorem splits [IsGalois F E] (x : E) : (minpoly F x).Splits (algebraMap F E) :=
  Normal.splits' x
#align is_galois.splits IsGalois.splits

variable (E)

instance of_fixed_field (G : Type*) [Group G] [Finite G] [MulSemiringAction G E] :
    IsGalois (FixedPoints.subfield G E) E :=
  ⟨⟩
#align is_galois.of_fixed_field IsGalois.of_fixed_field

theorem IntermediateField.AdjoinSimple.card_aut_eq_finrank [FiniteDimensional F E] {α : E}
    (hα : IsIntegral F α) (h_sep : (minpoly F α).Separable)
    (h_splits : (minpoly F α).Splits (algebraMap F F⟮α⟯)) :
    Fintype.card (F⟮α⟯ ≃ₐ[F] F⟮α⟯) = finrank F F⟮α⟯ := by
  letI : Fintype (F⟮α⟯ →ₐ[F] F⟮α⟯) := IntermediateField.fintypeOfAlgHomAdjoinIntegral F hα
  -- ⊢ Fintype.card ({ x // x ∈ F⟮α⟯ } ≃ₐ[F] { x // x ∈ F⟮α⟯ }) = finrank F { x //  …
  rw [IntermediateField.adjoin.finrank hα]
  -- ⊢ Fintype.card ({ x // x ∈ F⟮α⟯ } ≃ₐ[F] { x // x ∈ F⟮α⟯ }) = Polynomial.natDeg …
  rw [← IntermediateField.card_algHom_adjoin_integral F hα h_sep h_splits]
  -- ⊢ Fintype.card ({ x // x ∈ F⟮α⟯ } ≃ₐ[F] { x // x ∈ F⟮α⟯ }) = Fintype.card ({ x …
  exact Fintype.card_congr (algEquivEquivAlgHom F F⟮α⟯)
  -- 🎉 no goals
#align is_galois.intermediate_field.adjoin_simple.card_aut_eq_finrank IsGalois.IntermediateField.AdjoinSimple.card_aut_eq_finrank

theorem card_aut_eq_finrank [FiniteDimensional F E] [IsGalois F E] :
    Fintype.card (E ≃ₐ[F] E) = finrank F E := by
  cases' Field.exists_primitive_element F E with α hα
  -- ⊢ Fintype.card (E ≃ₐ[F] E) = finrank F E
  let iso : F⟮α⟯ ≃ₐ[F] E :=
    { toFun := fun e => e.val
      invFun := fun e => ⟨e, by rw [hα]; exact IntermediateField.mem_top⟩
      left_inv := fun _ => by ext; rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have H : IsIntegral F α := IsGalois.integral F α
  -- ⊢ Fintype.card (E ≃ₐ[F] E) = finrank F E
  have h_sep : (minpoly F α).Separable := IsGalois.separable F α
  -- ⊢ Fintype.card (E ≃ₐ[F] E) = finrank F E
  have h_splits : (minpoly F α).Splits (algebraMap F E) := IsGalois.splits F α
  -- ⊢ Fintype.card (E ≃ₐ[F] E) = finrank F E
  replace h_splits : Polynomial.Splits (algebraMap F F⟮α⟯) (minpoly F α)
  -- ⊢ Polynomial.Splits (algebraMap F { x // x ∈ F⟮α⟯ }) (minpoly F α)
  · simpa using
      Polynomial.splits_comp_of_splits (algebraMap F E) iso.symm.toAlgHom.toRingHom h_splits
  rw [← LinearEquiv.finrank_eq iso.toLinearEquiv]
  -- ⊢ Fintype.card (E ≃ₐ[F] E) = finrank F { x // x ∈ F⟮α⟯ }
  rw [← IntermediateField.AdjoinSimple.card_aut_eq_finrank F E H h_sep h_splits]
  -- ⊢ Fintype.card (E ≃ₐ[F] E) = Fintype.card ({ x // x ∈ F⟮α⟯ } ≃ₐ[F] { x // x ∈  …
  apply Fintype.card_congr
  -- ⊢ (E ≃ₐ[F] E) ≃ { x // x ∈ F⟮α⟯ } ≃ₐ[F] { x // x ∈ F⟮α⟯ }
  apply Equiv.mk (fun ϕ => iso.trans (ϕ.trans iso.symm)) fun ϕ => iso.symm.trans (ϕ.trans iso)
  -- ⊢ Function.LeftInverse (fun ϕ => AlgEquiv.trans (AlgEquiv.symm iso) (AlgEquiv. …
  · intro ϕ; ext1; simp only [trans_apply, apply_symm_apply]
    -- ⊢ (fun ϕ => AlgEquiv.trans (AlgEquiv.symm iso) (AlgEquiv.trans ϕ iso)) ((fun ϕ …
             -- ⊢ ↑((fun ϕ => AlgEquiv.trans (AlgEquiv.symm iso) (AlgEquiv.trans ϕ iso)) ((fun …
                   -- 🎉 no goals
  · intro ϕ; ext1; simp only [trans_apply, symm_apply_apply]
    -- ⊢ (fun ϕ => AlgEquiv.trans iso (AlgEquiv.trans ϕ (AlgEquiv.symm iso))) ((fun ϕ …
             -- ⊢ ↑((fun ϕ => AlgEquiv.trans iso (AlgEquiv.trans ϕ (AlgEquiv.symm iso))) ((fun …
                   -- 🎉 no goals
#align is_galois.card_aut_eq_finrank IsGalois.card_aut_eq_finrank

end IsGalois

end

section IsGaloisTower

variable (F K E : Type*) [Field F] [Field K] [Field E] {E' : Type*} [Field E'] [Algebra F E']

variable [Algebra F K] [Algebra F E] [Algebra K E] [IsScalarTower F K E]

theorem IsGalois.tower_top_of_isGalois [IsGalois F E] : IsGalois K E :=
  { to_isSeparable := isSeparable_tower_top_of_isSeparable F K E
    to_normal := Normal.tower_top_of_normal F K E }
#align is_galois.tower_top_of_is_galois IsGalois.tower_top_of_isGalois

variable {F E}

-- see Note [lower instance priority]
instance (priority := 100) IsGalois.tower_top_intermediateField (K : IntermediateField F E)
    [IsGalois F E] : IsGalois K E :=
  IsGalois.tower_top_of_isGalois F K E
#align is_galois.tower_top_intermediate_field IsGalois.tower_top_intermediateField

theorem isGalois_iff_isGalois_bot : IsGalois (⊥ : IntermediateField F E) E ↔ IsGalois F E := by
  constructor
  -- ⊢ IsGalois { x // x ∈ ⊥ } E → IsGalois F E
  · intro h
    -- ⊢ IsGalois F E
    exact IsGalois.tower_top_of_isGalois (⊥ : IntermediateField F E) F E
    -- 🎉 no goals
  · intro h; infer_instance
    -- ⊢ IsGalois { x // x ∈ ⊥ } E
             -- 🎉 no goals
#align is_galois_iff_is_galois_bot isGalois_iff_isGalois_bot

theorem IsGalois.of_algEquiv [IsGalois F E] (f : E ≃ₐ[F] E') : IsGalois F E' :=
  { to_isSeparable := IsSeparable.of_algHom F E f.symm
    to_normal := Normal.of_algEquiv f }
#align is_galois.of_alg_equiv IsGalois.of_algEquiv

theorem AlgEquiv.transfer_galois (f : E ≃ₐ[F] E') : IsGalois F E ↔ IsGalois F E' :=
  ⟨fun _ => IsGalois.of_algEquiv f, fun _ => IsGalois.of_algEquiv f.symm⟩
#align alg_equiv.transfer_galois AlgEquiv.transfer_galois

theorem isGalois_iff_isGalois_top : IsGalois F (⊤ : IntermediateField F E) ↔ IsGalois F E :=
  (IntermediateField.topEquiv : (⊤ : IntermediateField F E) ≃ₐ[F] E).transfer_galois
#align is_galois_iff_is_galois_top isGalois_iff_isGalois_top

instance isGalois_bot : IsGalois F (⊥ : IntermediateField F E) :=
  (IntermediateField.botEquiv F E).transfer_galois.mpr (IsGalois.self F)
#align is_galois_bot isGalois_bot

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
    algebraMap_mem' := fun a g => by rw [Algebra.algebraMap_eq_smul_one, smul_comm, smul_one] }
                                     -- 🎉 no goals
#align fixed_points.intermediate_field FixedPoints.intermediateField

namespace IntermediateField

/-- The intermediate field fixed by a subgroup -/
def fixedField : IntermediateField F E :=
  FixedPoints.intermediateField H
#align intermediate_field.fixed_field IntermediateField.fixedField

theorem finrank_fixedField_eq_card [FiniteDimensional F E] [DecidablePred (· ∈ H)] :
    finrank (fixedField H) E = Fintype.card H :=
  FixedPoints.finrank_eq_card H E
#align intermediate_field.finrank_fixed_field_eq_card IntermediateField.finrank_fixedField_eq_card

/-- The subgroup fixing an intermediate field -/
nonrec def fixingSubgroup : Subgroup (E ≃ₐ[F] E) :=
  fixingSubgroup (E ≃ₐ[F] E) (K : Set E)
#align intermediate_field.fixing_subgroup IntermediateField.fixingSubgroup

theorem le_iff_le : K ≤ fixedField H ↔ H ≤ fixingSubgroup K :=
  ⟨fun h g hg x => h (Subtype.mem x) ⟨g, hg⟩, fun h x hx g => h (Subtype.mem g) ⟨x, hx⟩⟩
#align intermediate_field.le_iff_le IntermediateField.le_iff_le

/-- The fixing subgroup of `K : IntermediateField F E` is isomorphic to `E ≃ₐ[K] E` -/
def fixingSubgroupEquiv : fixingSubgroup K ≃* E ≃ₐ[K] E where
  toFun ϕ := { AlgEquiv.toRingEquiv (ϕ : E ≃ₐ[F] E) with commutes' := ϕ.mem }
  invFun ϕ := ⟨ϕ.restrictScalars _, ϕ.commutes⟩
  left_inv _ := by ext; rfl
                   -- ⊢ ↑↑((fun ϕ => { val := AlgEquiv.restrictScalars F ϕ, property := (_ : ∀ (r :  …
                        -- 🎉 no goals
  right_inv _ := by ext; rfl
                    -- ⊢ ↑((fun ϕ =>
                         -- 🎉 no goals
  map_mul' _ _ := by ext; rfl
                     -- ⊢ ↑(Equiv.toFun
                          -- 🎉 no goals
#align intermediate_field.fixing_subgroup_equiv IntermediateField.fixingSubgroupEquiv

theorem fixingSubgroup_fixedField [FiniteDimensional F E] : fixingSubgroup (fixedField H) = H := by
  have H_le : H ≤ fixingSubgroup (fixedField H) := (le_iff_le _ _).mp le_rfl
  -- ⊢ fixingSubgroup (fixedField H) = H
  classical
  suffices Fintype.card H = Fintype.card (fixingSubgroup (fixedField H)) by
    exact SetLike.coe_injective (Set.eq_of_inclusion_surjective
      ((Fintype.bijective_iff_injective_and_card (Set.inclusion H_le)).mpr
        ⟨Set.inclusion_injective H_le, this⟩).2).symm
  apply Fintype.card_congr
  refine' (FixedPoints.toAlgHomEquiv H E).trans _
  refine' (algEquivEquivAlgHom (fixedField H) E).toEquiv.symm.trans _
  exact (fixingSubgroupEquiv (fixedField H)).toEquiv.symm
#align intermediate_field.fixing_subgroup_fixed_field IntermediateField.fixingSubgroup_fixedField

-- Porting note: added `fixedField.smul` for `fixedField.isScalarTower`
instance fixedField.smul : SMul K (fixedField (fixingSubgroup K)) where
  smul x y := ⟨x * y, fun ϕ => by
    rw [smul_mul', show ϕ • (x : E) = ↑x from ϕ.2 x, show ϕ • (y : E) = ↑y from y.2 ϕ]⟩
    -- 🎉 no goals

instance fixedField.algebra : Algebra K (fixedField (fixingSubgroup K)) where
  toFun x := ⟨x, fun ϕ => Subtype.mem ϕ x⟩
  map_zero' := rfl
  map_add' _ _ := rfl
  map_one' := rfl
  map_mul' _ _ := rfl
  commutes' _ _ := mul_comm _ _
  smul_def' _ _ := rfl
#align intermediate_field.fixed_field.algebra IntermediateField.fixedField.algebra

instance fixedField.isScalarTower : IsScalarTower K (fixedField (fixingSubgroup K)) E :=
  ⟨fun _ _ _ => mul_assoc _ _ _⟩
#align intermediate_field.fixed_field.is_scalar_tower IntermediateField.fixedField.isScalarTower

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
    Fintype.card_congr (IntermediateField.fixingSubgroupEquiv K).toEquiv]
  exact (card_aut_eq_finrank K E).symm
#align is_galois.fixed_field_fixing_subgroup IsGalois.fixedField_fixingSubgroup

theorem card_fixingSubgroup_eq_finrank [DecidablePred (· ∈ IntermediateField.fixingSubgroup K)]
    [FiniteDimensional F E] [IsGalois F E] :
    Fintype.card (IntermediateField.fixingSubgroup K) = finrank K E := by
  conv_rhs => rw [← fixedField_fixingSubgroup K, IntermediateField.finrank_fixedField_eq_card]
  -- 🎉 no goals
#align is_galois.card_fixing_subgroup_eq_finrank IsGalois.card_fixingSubgroup_eq_finrank

/-- The Galois correspondence from intermediate fields to subgroups -/
def intermediateFieldEquivSubgroup [FiniteDimensional F E] [IsGalois F E] :
    IntermediateField F E ≃o (Subgroup (E ≃ₐ[F] E))ᵒᵈ where
  toFun := IntermediateField.fixingSubgroup
  invFun := IntermediateField.fixedField
  left_inv K := fixedField_fixingSubgroup K
  right_inv H := IntermediateField.fixingSubgroup_fixedField H
  map_rel_iff' {K L} := by
    rw [← fixedField_fixingSubgroup L, IntermediateField.le_iff_le, fixedField_fixingSubgroup L]
    -- ⊢ ↑{ toFun := IntermediateField.fixingSubgroup, invFun := IntermediateField.fi …
    rfl
    -- 🎉 no goals
#align is_galois.intermediate_field_equiv_subgroup IsGalois.intermediateFieldEquivSubgroup

/-- The Galois correspondence as a `GaloisInsertion` -/
def galoisInsertionIntermediateFieldSubgroup [FiniteDimensional F E] :
    GaloisInsertion (OrderDual.toDual ∘
      (IntermediateField.fixingSubgroup : IntermediateField F E → Subgroup (E ≃ₐ[F] E)))
      ((IntermediateField.fixedField : Subgroup (E ≃ₐ[F] E) → IntermediateField F E) ∘
        OrderDual.toDual) where
  choice K _ := IntermediateField.fixingSubgroup K
  gc K H := (IntermediateField.le_iff_le H K).symm
  le_l_u H := le_of_eq (IntermediateField.fixingSubgroup_fixedField H).symm
  choice_eq _ _ := rfl
#align is_galois.galois_insertion_intermediate_field_subgroup IsGalois.galoisInsertionIntermediateFieldSubgroup

/-- The Galois correspondence as a `GaloisCoinsertion` -/
def galoisCoinsertionIntermediateFieldSubgroup [FiniteDimensional F E] [IsGalois F E] :
    GaloisCoinsertion (OrderDual.toDual ∘
      (IntermediateField.fixingSubgroup : IntermediateField F E → Subgroup (E ≃ₐ[F] E)))
      ((IntermediateField.fixedField : Subgroup (E ≃ₐ[F] E) → IntermediateField F E) ∘
        OrderDual.toDual) where
  choice H _ := IntermediateField.fixedField H
  gc K H := (IntermediateField.le_iff_le H K).symm
  u_l_le K := le_of_eq (fixedField_fixingSubgroup K)
  choice_eq _ _ := rfl
#align is_galois.galois_coinsertion_intermediate_field_subgroup IsGalois.galoisCoinsertionIntermediateFieldSubgroup

end IsGalois

end GaloisCorrespondence

section GaloisEquivalentDefinitions

variable (F : Type*) [Field F] (E : Type*) [Field E] [Algebra F E]

namespace IsGalois

theorem is_separable_splitting_field [FiniteDimensional F E] [IsGalois F E] :
    ∃ p : F[X], p.Separable ∧ p.IsSplittingField F E := by
  cases' Field.exists_primitive_element F E with α h1
  -- ⊢ ∃ p, Polynomial.Separable p ∧ Polynomial.IsSplittingField F E p
  use minpoly F α, separable F α, IsGalois.splits F α
  -- ⊢ Algebra.adjoin F (Polynomial.rootSet (minpoly F α) E) = ⊤
  rw [eq_top_iff, ← IntermediateField.top_toSubalgebra, ← h1]
  -- ⊢ F⟮α⟯.toSubalgebra ≤ Algebra.adjoin F (Polynomial.rootSet (minpoly F α) E)
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_integral (integral F α)]
  -- ⊢ Algebra.adjoin F {α} ≤ Algebra.adjoin F (Polynomial.rootSet (minpoly F α) E)
  apply Algebra.adjoin_mono
  -- ⊢ {α} ⊆ Polynomial.rootSet (minpoly F α) E
  rw [Set.singleton_subset_iff, Polynomial.mem_rootSet]
  -- ⊢ minpoly F α ≠ 0 ∧ ↑(Polynomial.aeval α) (minpoly F α) = 0
  exact ⟨minpoly.ne_zero (integral F α), minpoly.aeval _ _⟩
  -- 🎉 no goals
#align is_galois.is_separable_splitting_field IsGalois.is_separable_splitting_field

theorem of_fixedField_eq_bot [FiniteDimensional F E]
    (h : IntermediateField.fixedField (⊤ : Subgroup (E ≃ₐ[F] E)) = ⊥) : IsGalois F E := by
  rw [← isGalois_iff_isGalois_bot, ← h]
  -- ⊢ IsGalois { x // x ∈ IntermediateField.fixedField ⊤ } E
  classical exact IsGalois.of_fixed_field E (⊤ : Subgroup (E ≃ₐ[F] E))
  -- 🎉 no goals
#align is_galois.of_fixed_field_eq_bot IsGalois.of_fixedField_eq_bot

theorem of_card_aut_eq_finrank [FiniteDimensional F E]
    (h : Fintype.card (E ≃ₐ[F] E) = finrank F E) : IsGalois F E := by
  apply of_fixedField_eq_bot
  -- ⊢ IntermediateField.fixedField ⊤ = ⊥
  have p : 0 < finrank (IntermediateField.fixedField (⊤ : Subgroup (E ≃ₐ[F] E))) E := finrank_pos
  -- ⊢ IntermediateField.fixedField ⊤ = ⊥
  classical
  rw [← IntermediateField.finrank_eq_one_iff, ← mul_left_inj' (ne_of_lt p).symm,
    finrank_mul_finrank, ← h, one_mul, IntermediateField.finrank_fixedField_eq_card]
  apply Fintype.card_congr
  exact
    { toFun := fun g => ⟨g, Subgroup.mem_top g⟩
      invFun := (↑)
      left_inv := fun g => rfl
      right_inv := fun _ => by ext; rfl }
#align is_galois.of_card_aut_eq_finrank IsGalois.of_card_aut_eq_finrank

variable {F} {E}

variable {p : F[X]}

theorem of_separable_splitting_field_aux [hFE : FiniteDimensional F E] [sp : p.IsSplittingField F E]
    (hp : p.Separable) (K : Type*) [Field K] [Algebra F K] [Algebra K E] [IsScalarTower F K E]
    {x : E} (hx : x ∈ (p.map (algebraMap F E)).roots)
    -- these are both implied by `hFE`, but as they carry data this makes the lemma more general
    [Fintype (K →ₐ[F] E)]
    [Fintype (K⟮x⟯.restrictScalars F →ₐ[F] E)] :
    Fintype.card (K⟮x⟯.restrictScalars F →ₐ[F] E) = Fintype.card (K →ₐ[F] E) * finrank K K⟮x⟯ := by
  have h : IsIntegral K x :=
    isIntegral_of_isScalarTower (isIntegral_of_noetherian (IsNoetherian.iff_fg.2 hFE) x)
  have h1 : p ≠ 0 := fun hp => by
    rw [hp, Polynomial.map_zero, Polynomial.roots_zero] at hx
    exact Multiset.not_mem_zero x hx
  have h2 : minpoly K x ∣ p.map (algebraMap F K) := by
    apply minpoly.dvd
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← Polynomial.eval_map, ←
      IsScalarTower.algebraMap_eq]
    exact (Polynomial.mem_roots (Polynomial.map_ne_zero h1)).mp hx
  let key_equiv : (K⟮x⟯.restrictScalars F →ₐ[F] E) ≃
      Σ f : K →ₐ[F] E, @AlgHom K K⟮x⟯ E _ _ _ _ (RingHom.toAlgebra f) := by
    change (K⟮x⟯ →ₐ[F] E) ≃ Σ f : K →ₐ[F] E, _
    exact algHomEquivSigma
  haveI : ∀ f : K →ₐ[F] E, Fintype (@AlgHom K K⟮x⟯ E _ _ _ _ (RingHom.toAlgebra f)) := fun f => by
    have := Fintype.ofEquiv _ key_equiv
    apply Fintype.ofInjective (Sigma.mk f) fun _ _ H => eq_of_heq (Sigma.ext_iff.mp H).2
  rw [Fintype.card_congr key_equiv, Fintype.card_sigma, IntermediateField.adjoin.finrank h]
  -- ⊢ (Finset.sum Finset.univ fun a => Fintype.card ({ x_1 // x_1 ∈ K⟮x⟯ } →ₐ[K] E …
  apply Finset.sum_const_nat
  -- ⊢ ∀ (x_1 : K →ₐ[F] E), x_1 ∈ Finset.univ → Fintype.card ({ x_2 // x_2 ∈ K⟮x⟯ } …
  intro f _
  -- ⊢ Fintype.card ({ x_1 // x_1 ∈ K⟮x⟯ } →ₐ[K] E) = Polynomial.natDegree (minpoly …
  rw [← @IntermediateField.card_algHom_adjoin_integral K _ E _ _ x E _ (RingHom.toAlgebra f) h]
  · congr!
    -- 🎉 no goals
  · exact Polynomial.Separable.of_dvd ((Polynomial.separable_map (algebraMap F K)).mpr hp) h2
    -- 🎉 no goals
  · refine' Polynomial.splits_of_splits_of_dvd _ (Polynomial.map_ne_zero h1) _ h2
    -- ⊢ Polynomial.Splits (algebraMap K E) (Polynomial.map (algebraMap F K) p)
    -- Porting note: use unification instead of synthesis for one argument of `algebraMap_eq`
    rw [Polynomial.splits_map_iff, ← @IsScalarTower.algebraMap_eq _ _ _ _ _ _ _ (_) _ _]
    -- ⊢ Polynomial.Splits (algebraMap F E) p
    exact sp.splits
    -- 🎉 no goals
#align is_galois.of_separable_splitting_field_aux IsGalois.of_separable_splitting_field_aux

theorem of_separable_splitting_field [sp : p.IsSplittingField F E] (hp : p.Separable) :
    IsGalois F E := by
  haveI hFE : FiniteDimensional F E := Polynomial.IsSplittingField.finiteDimensional E p
  -- ⊢ IsGalois F E
  letI := Classical.decEq E
  -- ⊢ IsGalois F E
  let s := (p.map (algebraMap F E)).roots.toFinset
  -- ⊢ IsGalois F E
  have adjoin_root : IntermediateField.adjoin F (s : Set E) = ⊤ := by
    apply IntermediateField.toSubalgebra_injective
    rw [IntermediateField.top_toSubalgebra, ← top_le_iff, ← sp.adjoin_rootSet]
    apply IntermediateField.algebra_adjoin_le_adjoin
  let P : IntermediateField F E → Prop := fun K => Fintype.card (K →ₐ[F] E) = finrank F K
  -- ⊢ IsGalois F E
  suffices P (IntermediateField.adjoin F ↑s) by
    rw [adjoin_root] at this
    apply of_card_aut_eq_finrank
    rw [← Eq.trans this (LinearEquiv.finrank_eq IntermediateField.topEquiv.toLinearEquiv)]
    exact Fintype.card_congr ((algEquivEquivAlgHom F E).toEquiv.trans
      (IntermediateField.topEquiv.symm.arrowCongr AlgEquiv.refl))
  apply IntermediateField.induction_on_adjoin_finset s P
  -- ⊢ P ⊥
  · have key := IntermediateField.card_algHom_adjoin_integral F (K := E)
      (show IsIntegral F (0 : E) from isIntegral_zero)
    rw [minpoly.zero, Polynomial.natDegree_X] at key
    -- ⊢ P ⊥
    specialize key Polynomial.separable_X (Polynomial.splits_X (algebraMap F E))
    -- ⊢ P ⊥
    rw [← @Subalgebra.finrank_bot F E _ _ _, ← IntermediateField.bot_toSubalgebra] at key
    -- ⊢ P ⊥
    refine' Eq.trans _ key
    -- ⊢ Fintype.card ({ x // x ∈ ⊥ } →ₐ[F] E) = Fintype.card ({ x // x ∈ F⟮0⟯ } →ₐ[F …
    -- Porting note: use unification instead of synthesis for one argument of `card_congr`
    apply @Fintype.card_congr _ _ _ (_) _
    -- ⊢ ({ x // x ∈ ⊥ } →ₐ[F] E) ≃ ({ x // x ∈ F⟮0⟯ } →ₐ[F] E)
    rw [IntermediateField.adjoin_zero]
    -- 🎉 no goals
  intro K x hx hK
  -- ⊢ P (IntermediateField.restrictScalars F { x // x ∈ K }⟮x⟯)
  simp only at *
  -- ⊢ Fintype.card ({ x_1 // x_1 ∈ IntermediateField.restrictScalars F { x // x ∈  …
  -- Porting note: need to specify two implicit arguments of `finrank_mul_finrank`
  rw [of_separable_splitting_field_aux hp K (Multiset.mem_toFinset.mp hx), hK,
    @finrank_mul_finrank _ _ _ _ _ _ _ K⟮x⟯.module _ K⟮x⟯.isScalarTower _]
  symm
  -- ⊢ finrank F { x_1 // x_1 ∈ IntermediateField.restrictScalars F { x // x ∈ K }⟮ …
  refine' LinearEquiv.finrank_eq _
  -- ⊢ { x_1 // x_1 ∈ IntermediateField.restrictScalars F { x // x ∈ K }⟮x⟯ } ≃ₗ[F] …
  rfl
  -- 🎉 no goals
#align is_galois.of_separable_splitting_field IsGalois.of_separable_splitting_field

/-- Equivalent characterizations of a Galois extension of finite degree-/
theorem tfae [FiniteDimensional F E] :
    List.TFAE [IsGalois F E, IntermediateField.fixedField (⊤ : Subgroup (E ≃ₐ[F] E)) = ⊥,
      Fintype.card (E ≃ₐ[F] E) = finrank F E, ∃ p: F[X], p.Separable ∧ p.IsSplittingField F E] := by
  tfae_have 1 → 2
  -- ⊢ IsGalois F E → IntermediateField.fixedField ⊤ = ⊥
  · exact fun h => OrderIso.map_bot (@intermediateFieldEquivSubgroup F _ E _ _ _ h).symm
    -- 🎉 no goals
  tfae_have 1 → 3
  -- ⊢ IsGalois F E → Fintype.card (E ≃ₐ[F] E) = finrank F E
  · intro; exact card_aut_eq_finrank F E
    -- ⊢ Fintype.card (E ≃ₐ[F] E) = finrank F E
           -- 🎉 no goals
  tfae_have 1 → 4
  -- ⊢ IsGalois F E → ∃ p, Polynomial.Separable p ∧ Polynomial.IsSplittingField F E p
  · intro; exact is_separable_splitting_field F E
    -- ⊢ ∃ p, Polynomial.Separable p ∧ Polynomial.IsSplittingField F E p
           -- 🎉 no goals
  tfae_have 2 → 1
  -- ⊢ IntermediateField.fixedField ⊤ = ⊥ → IsGalois F E
  · exact of_fixedField_eq_bot F E
    -- 🎉 no goals
  tfae_have 3 → 1
  -- ⊢ Fintype.card (E ≃ₐ[F] E) = finrank F E → IsGalois F E
  · exact of_card_aut_eq_finrank F E
    -- 🎉 no goals
  tfae_have 4 → 1
  -- ⊢ (∃ p, Polynomial.Separable p ∧ Polynomial.IsSplittingField F E p) → IsGalois …
  · rintro ⟨h, hp1, _⟩; exact of_separable_splitting_field hp1
    -- ⊢ IsGalois F E
                        -- 🎉 no goals
  tfae_finish
  -- 🎉 no goals
#align is_galois.tfae IsGalois.tfae

end IsGalois

end GaloisEquivalentDefinitions

section normalClosure

variable (k K F : Type*) [Field k] [Field K] [Field F] [Algebra k K] [Algebra k F] [Algebra K F]
  [IsScalarTower k K F] [IsGalois k F]

instance IsGalois.normalClosure : IsGalois k (normalClosure k K F)
    where to_isSeparable := isSeparable_tower_bot_of_isSeparable k _ F
#align is_galois.normal_closure IsGalois.normalClosure

end normalClosure

section IsAlgClosure

instance (priority := 100) IsAlgClosure.isGalois (k K : Type*) [Field k] [Field K] [Algebra k K]
    [IsAlgClosure k K] [CharZero k] : IsGalois k K where
#align is_alg_closure.is_galois IsAlgClosure.isGalois

end IsAlgClosure
