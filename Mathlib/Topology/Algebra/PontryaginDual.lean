/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Algebra.Group.CompactOpen

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Pontryagin dual

This file defines the Pontryagin dual of a topological group. The Pontryagin dual of a topological
group `A` is the topological group of continuous homomorphisms `A →* Circle` with the compact-open
topology. For example, `ℤ` and `Circle` are Pontryagin duals of each other. This is an example of
Pontryagin duality, which states that a locally compact abelian topological group is canonically
isomorphic to its double dual.

## Main definitions

* `PontryaginDual A`: The group of continuous homomorphisms `A →* Circle`.
* `AddPontryaginDual A`: The additive version for additive groups, the group of continuous
  additive homomorphisms `A →+ Additive Circle`.
* `AddPontryaginDual.toAddChar χ`: The additive character `A → Circle` associated with
  `χ : AddPontryaginDual A`, which turns addition in `A` into multiplication in `Circle`.

## Implementation notes

`AddPontryaginDual` and its basic API are generated from `PontryaginDual` by `to_additive`.
Since `to_additive` can only translate a constant to a constant, we introduce the abbreviation
`AdditiveCircle := Additive Circle` and register it as the additive version of `Circle`.
-/

@[expose] public section

open scoped Pointwise
open Real

noncomputable section

/-! ### The circle as an additive group -/

/-- The circle group, written additively. This abbreviation for `Additive Circle` exists so that
`to_additive` can translate `Circle` to it. -/
abbrev AdditiveCircle : Type :=
  Additive Circle

namespace AdditiveCircle

instance instAddCommGroup : AddCommGroup AdditiveCircle := inferInstance

instance instTopologicalSpace : TopologicalSpace AdditiveCircle := inferInstance

instance instIsTopologicalAddGroup : IsTopologicalAddGroup AdditiveCircle := inferInstance

end AdditiveCircle

attribute [to_additive existing AdditiveCircle] Circle
attribute [to_additive existing] Circle.instCommGroup Circle.instIsTopologicalGroup
attribute [to_additive existing AdditiveCircle.instTopologicalSpace] instTopologicalSpaceCircle

section PontryaginDual

variable (A B C G H : Type*) [Monoid A] [Monoid B] [Monoid C] [CommGroup G] [Group H]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]

/-- The Pontryagin dual of `A` is the group of continuous homomorphism `A → Circle`. -/
@[to_additive AddPontryaginDual
/-- The additive Pontryagin dual of `A` is the group of continuous additive homomorphisms
`A → Additive Circle`. -/]
def PontryaginDual :=
  A →ₜ* Circle

@[to_additive instTopologicalSpaceAddPontryaginDual]
instance : TopologicalSpace (PontryaginDual A) :=
  inferInstanceAs (TopologicalSpace (A →ₜ* Circle))

instance [LocallyCompactSpace H] : LocallyCompactSpace (PontryaginDual H) := by
  let Vn : ℕ → Set Circle := fun n ↦ Circle.centeredArc (π / 2 ^ (n + 1))
  have hVn : ∀ n x, x ∈ Vn n ↔ |Complex.arg x| < π / 2 ^ (n + 1) :=
    fun n x ↦ Circle.mem_centeredArc (z := x)
      (div_le_self pi_nonneg (one_le_pow₀ one_le_two))
  refine ContinuousMonoidHom.locallyCompactSpace_of_hasBasis Vn ?_ ?_
  · intro n x h1 h2
    rw [hVn] at h1 h2 ⊢
    rwa [Circle.coe_mul, Complex.arg_mul x.coe_ne_zero x.coe_ne_zero,
      ← two_mul, abs_mul, abs_two, ← lt_div_iff₀' two_pos, div_div, ← pow_succ] at h2
    apply Set.Ioo_subset_Ioc_self
    rw [← two_mul, Set.mem_Ioo, ← abs_lt, abs_mul, abs_two, ← lt_div_iff₀' two_pos]
    refine h1.trans_le ?_
    gcongr
    exact le_self_pow₀ one_le_two n.succ_ne_zero
  · simpa [Vn] using Circle.hasBasis_centeredArc_div_two_pow

variable {A B C G}

namespace PontryaginDual

open ContinuousMonoidHom

@[to_additive]
instance : CommGroup (PontryaginDual A) := inferInstanceAs (CommGroup (A →ₜ* Circle))

@[to_additive]
instance : T2Space (PontryaginDual A) := inferInstanceAs (T2Space (A →ₜ* Circle))

@[to_additive]
instance : IsTopologicalGroup (PontryaginDual A) :=
  inferInstanceAs (IsTopologicalGroup (A →ₜ* Circle))

@[to_additive]
instance : Inhabited (PontryaginDual A) := inferInstanceAs (Inhabited (A →ₜ* Circle))

@[to_additive instFunLikeAdditiveCircle]
instance : FunLike (PontryaginDual A) A Circle :=
  inferInstanceAs (FunLike (A →ₜ* Circle) A Circle)

@[to_additive instContinuousMapClassAdditiveCircle]
instance : ContinuousMapClass (PontryaginDual A) A Circle :=
  inferInstanceAs (ContinuousMapClass (A →ₜ* Circle) A Circle)

@[to_additive instAddMonoidHomClassAdditiveCircle]
instance : MonoidHomClass (PontryaginDual A) A Circle :=
  inferInstanceAs (MonoidHomClass (A →ₜ* Circle) A Circle)

@[to_additive instContinuousEvalConstAdditiveCircle]
instance : ContinuousEvalConst (PontryaginDual A) A Circle :=
  inferInstanceAs (ContinuousEvalConst (A →ₜ* Circle) A Circle)

@[to_additive instContinuousEvalAdditiveCircle]
instance [LocallyCompactSpace A] : ContinuousEval (PontryaginDual A) A Circle :=
  inferInstanceAs (ContinuousEval (A →ₜ* Circle) A Circle)

@[to_additive]
instance [DiscreteTopology A] : CompactSpace (PontryaginDual A) :=
  inferInstanceAs (CompactSpace (A →ₜ* Circle))

@[to_additive (attr := ext)]
theorem ext {ψ φ : PontryaginDual A} (h : ∀ a, ψ a = φ a) : ψ = φ := DFunLike.ext _ _ h

@[to_additive (attr := simp)]
theorem one_apply (a : A) : (1 : PontryaginDual A) a = 1 := rfl

@[to_additive (attr := simp)]
theorem mul_apply (ψ φ : PontryaginDual A) (a : A) : (ψ * φ) a = ψ a * φ a := rfl

@[to_additive (attr := simp)]
theorem inv_apply (ψ : PontryaginDual A) (a : A) : ψ⁻¹ a = (ψ a)⁻¹ := rfl

@[to_additive (attr := simp)]
theorem div_apply (ψ φ : PontryaginDual A) (a : A) : (ψ / φ) a = ψ a / φ a := rfl

/-- A discrete monoid has compact Pontryagin dual. -/
add_decl_doc instLocallyCompactSpacePontryaginDual

/-- A compact monoid has discrete Pontryagin dual. -/
instance [CompactSpace A] : DiscreteTopology (PontryaginDual A) := by
  let V : Set (PontryaginDual A) := {ψ | Set.MapsTo ψ Set.univ (Circle.centeredArc (π / 2))}
  have hVopen : IsOpen V := by
    dsimp only [V]
    exact isOpen_induced (ContinuousMap.isOpen_setOfPred_mapsTo isCompact_univ
      (Circle.isOpen_centeredArc (π / 2)))
  have hVeq : V = ({1} : Set (PontryaginDual A)) := by
    ext ψ
    rw [Set.mem_singleton_iff]
    refine ⟨fun hψ ↦ ?_, ?_⟩
    · ext1 a
      refine Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two fun n hn ↦ ?_
      simpa using hψ (Set.mem_univ (a ^ n))
    · rintro rfl _ _
      rw [Circle.mem_centeredArc (by linarith [pi_pos])]
      simp [pi_pos]
  exact discreteTopology_of_isOpen_singleton_one (by simpa [hVeq] using hVopen)

instance [DiscreteTopology A] [CompactSpace A] : Finite (PontryaginDual A) :=
  finite_of_compact_of_discrete

noncomputable instance [DiscreteTopology A] [CompactSpace A] : Fintype (PontryaginDual A) :=
  .ofFinite _

/-- `PontryaginDual` is a contravariant functor. -/
@[to_additive /-- `AddPontryaginDual` is a contravariant functor. -/]
def map (f : A →ₜ* B) :
    (PontryaginDual B) →ₜ* (PontryaginDual A) :=
  f.compLeft Circle

@[to_additive (attr := simp)]
theorem map_apply (f : A →ₜ* B) (x : PontryaginDual B) (y : A) :
    map f x y = x (f y) :=
  rfl

@[to_additive (attr := simp)]
theorem map_one : map (1 : A →ₜ* B) = 1 :=
  ContinuousMonoidHom.ext fun x => PontryaginDual.ext fun _y => OneHomClass.map_one x

@[to_additive (attr := simp)]
theorem map_comp (g : B →ₜ* C) (f : A →ₜ* B) :
    map (comp g f) = ContinuousMonoidHom.comp (map f) (map g) :=
  ContinuousMonoidHom.ext fun _x => PontryaginDual.ext fun _y => rfl

@[to_additive (attr := simp)]
nonrec theorem map_mul (f g : A →ₜ* G) : map (f * g) = map f * map g :=
  ContinuousMonoidHom.ext fun x => PontryaginDual.ext fun y => map_mul x (f y) (g y)

variable (A B C G)

/-- `ContinuousMonoidHom.dual` as a `ContinuousMonoidHom`. -/
@[to_additive /-- `AddPontryaginDual.map` as a `ContinuousAddMonoidHom`. -/]
def mapHom [LocallyCompactSpace G] :
    (A →ₜ* G) →ₜ* ((PontryaginDual G) →ₜ* (PontryaginDual A)) where
  toFun := map
  map_one' := map_one
  map_mul' := map_mul
  continuous_toFun := continuous_of_continuous_uncurry _ continuous_comp

end PontryaginDual

end PontryaginDual

/-! ### The additive Pontryagin dual

The instances whose proofs use the geometry of `Circle` cannot be translated by `to_additive`.
We transfer them along the homeomorphism `AddPontryaginDual A ≃ₜ PontryaginDual (Multiplicative A)`.
-/

section AddPontryaginDual

variable (A H : Type*) [AddMonoid A] [AddGroup H] [TopologicalSpace A] [TopologicalSpace H]
  [IsTopologicalAddGroup H]

namespace AddPontryaginDual

/-- The additive Pontryagin dual of `A` is homeomorphic to the Pontryagin dual of
`Multiplicative A`. -/
def toMultiplicative : AddPontryaginDual A ≃ₜ PontryaginDual (Multiplicative A) where
  toFun φ := ⟨AddMonoidHom.toMultiplicativeLeft φ.toAddMonoidHom, φ.continuous_toFun⟩
  invFun ψ := ⟨MonoidHom.toAdditiveRight ψ.toMonoidHom, ψ.continuous_toFun⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (ContinuousMonoidHom.isInducing_toContinuousMap _ _).continuous_iff.mpr
      (ContinuousAddMonoidHom.isInducing_toContinuousMap A _).continuous
  continuous_invFun :=
    (ContinuousAddMonoidHom.isInducing_toContinuousMap A _).continuous_iff.mpr
      (ContinuousMonoidHom.isInducing_toContinuousMap _ _).continuous

variable {A} in
@[simp]
theorem toMultiplicative_apply (φ : AddPontryaginDual A) (a : Multiplicative A) :
    toMultiplicative A φ a = (φ a.toAdd).toMul := rfl

instance [LocallyCompactSpace H] : LocallyCompactSpace (AddPontryaginDual H) :=
  have : LocallyCompactSpace (Multiplicative H) := ‹LocallyCompactSpace H›
  (toMultiplicative H).isClosedEmbedding.locallyCompactSpace

/-- A compact additive monoid has discrete Pontryagin dual. -/
instance [CompactSpace A] : DiscreteTopology (AddPontryaginDual A) :=
  have : CompactSpace (Multiplicative A) := ‹CompactSpace A›
  (toMultiplicative A).symm.discreteTopology

instance [DiscreteTopology A] [CompactSpace A] : Finite (AddPontryaginDual A) :=
  finite_of_compact_of_discrete

noncomputable instance [DiscreteTopology A] [CompactSpace A] : Fintype (AddPontryaginDual A) :=
  .ofFinite _

/-! ### Elements of the additive Pontryagin dual as additive characters -/

variable {A}

/-- The additive character `A → Circle` associated with an element `χ` of the additive Pontryagin
dual of `A`. It sends `a` to `(χ a).toMul`, turning addition in `A` into multiplication in
`Circle`. -/
def toAddChar (χ : AddPontryaginDual A) : AddChar A Circle :=
  AddChar.toAddMonoidHomEquiv.symm (AddMonoidHom.ofClass χ)

theorem toAddChar_apply (χ : AddPontryaginDual A) (a : A) : χ.toAddChar a = (χ a).toMul := rfl

theorem toAddChar_injective :
    Function.Injective (toAddChar : AddPontryaginDual A → AddChar A Circle) :=
  fun _ _ h ↦ ext fun a ↦ Additive.toMul.injective (DFunLike.congr_fun h a)

@[simp]
theorem toAddChar_inj {χ η : AddPontryaginDual A} : χ.toAddChar = η.toAddChar ↔ χ = η :=
  toAddChar_injective.eq_iff

@[fun_prop]
theorem continuous_toAddChar (χ : AddPontryaginDual A) : Continuous χ.toAddChar :=
  continuous_toMul.comp (map_continuous χ)

/-- The element of the additive Pontryagin dual of `A` associated with a continuous additive
character `A → Circle`. -/
def ofAddChar (ψ : AddChar A Circle) (hψ : Continuous ψ) : AddPontryaginDual A :=
  (⟨AddChar.toAddMonoidHomEquiv ψ, continuous_ofMul.comp hψ⟩ : A →ₜ+ AdditiveCircle)

@[simp]
theorem toAddChar_ofAddChar (ψ : AddChar A Circle) (hψ : Continuous ψ) :
    (ofAddChar ψ hψ).toAddChar = ψ := rfl

@[simp]
theorem ofAddChar_toAddChar (χ : AddPontryaginDual A) :
    ofAddChar χ.toAddChar χ.continuous_toAddChar = χ := rfl

@[simp]
theorem toAddChar_zero_apply (a : A) : (0 : AddPontryaginDual A).toAddChar a = 1 := rfl

@[simp]
theorem toAddChar_add_apply (χ η : AddPontryaginDual A) (a : A) :
    (χ + η).toAddChar a = χ.toAddChar a * η.toAddChar a := rfl

@[simp]
theorem toAddChar_neg_apply (χ : AddPontryaginDual A) (a : A) :
    (-χ).toAddChar a = (χ.toAddChar a)⁻¹ := rfl

@[simp]
theorem toAddChar_sub_apply (χ η : AddPontryaginDual A) (a : A) :
    (χ - η).toAddChar a = χ.toAddChar a / η.toAddChar a := rfl

/-- For every `a : A`, the evaluation `χ ↦ χ.toAddChar a` is continuous. -/
@[fun_prop]
theorem continuous_toAddChar_apply (a : A) :
    Continuous fun χ : AddPontryaginDual A ↦ χ.toAddChar a :=
  continuous_toMul.comp (continuous_eval_const a)

/-- If `A` is locally compact, then the evaluation `(χ, a) ↦ χ.toAddChar a` is jointly
continuous. -/
theorem continuous_toAddChar_uncurry [LocallyCompactSpace A] :
    Continuous fun p : AddPontryaginDual A × A ↦ p.1.toAddChar p.2 :=
  continuous_toMul.comp continuous_eval

/-- A map `f` into the additive Pontryagin dual is continuous if `(x, a) ↦ (f x).toAddChar a` is
jointly continuous. -/
theorem continuous_of_continuous_uncurry {X : Type*} [TopologicalSpace X]
    (f : X → AddPontryaginDual A) (h : Continuous fun p : X × A ↦ (f p.1).toAddChar p.2) :
    Continuous f :=
  ContinuousAddMonoidHom.continuous_of_continuous_uncurry (B := A) (C := AdditiveCircle) f
    (continuous_ofMul.comp h)

end AddPontryaginDual

end AddPontryaginDual
