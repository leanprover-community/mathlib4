/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Andrew Yang
-/
import Mathlib.RingTheory.Derivation.ToSquareZero
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.IsTensorProduct

#align_import ring_theory.kaehler from "leanprover-community/mathlib"@"4b92a463033b5587bb011657e25e4710bfca7364"

/-!
# The module of kaehler differentials

## Main results

- `KaehlerDifferential`: The module of kaehler differentials. For an `R`-algebra `S`, we provide
  the notation `Ω[S⁄R]` for `KaehlerDifferential R S`.
  Note that the slash is `\textfractionsolidus`.
- `KaehlerDifferential.D`: The derivation into the module of kaehler differentials.
- `KaehlerDifferential.span_range_derivation`: The image of `D` spans `Ω[S⁄R]` as an `S`-module.
- `KaehlerDifferential.linearMapEquivDerivation`:
  The isomorphism `Hom_R(Ω[S⁄R], M) ≃ₗ[S] Der_R(S, M)`.
- `KaehlerDifferential.quotKerTotalEquiv`: An alternative description of `Ω[S⁄R]` as `S` copies
  of `S` with kernel (`KaehlerDifferential.kerTotal`) generated by the relations:
  1. `dx + dy = d(x + y)`
  2. `x dy + y dx = d(x * y)`
  3. `dr = 0` for `r ∈ R`
- `KaehlerDifferential.map`: Given a map between the arrows `R → A` and `S → B`, we have an
  `A`-linear map `Ω[A⁄R] → Ω[B⁄S]`.

## Future project

- Define the `IsKaehlerDifferential` predicate.
-/

suppress_compilation

section KaehlerDifferential

open scoped TensorProduct
open Algebra

universe u v

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/-- The kernel of the multiplication map `S ⊗[R] S →ₐ[R] S`. -/
abbrev KaehlerDifferential.ideal : Ideal (S ⊗[R] S) :=
  RingHom.ker (TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S)
#align kaehler_differential.ideal KaehlerDifferential.ideal

variable {S}

theorem KaehlerDifferential.one_smul_sub_smul_one_mem_ideal (a : S) :
    (1 : S) ⊗ₜ[R] a - a ⊗ₜ[R] (1 : S) ∈ KaehlerDifferential.ideal R S := by simp [RingHom.mem_ker]
#align kaehler_differential.one_smul_sub_smul_one_mem_ideal KaehlerDifferential.one_smul_sub_smul_one_mem_ideal

variable {R}

variable {M : Type*} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- For a `R`-derivation `S → M`, this is the map `S ⊗[R] S →ₗ[S] M` sending `s ⊗ₜ t ↦ s • D t`. -/
def Derivation.tensorProductTo (D : Derivation R S M) : S ⊗[R] S →ₗ[S] M :=
  TensorProduct.AlgebraTensorModule.lift ((LinearMap.lsmul S (S →ₗ[R] M)).flip D.toLinearMap)
#align derivation.tensor_product_to Derivation.tensorProductTo

theorem Derivation.tensorProductTo_tmul (D : Derivation R S M) (s t : S) :
    D.tensorProductTo (s ⊗ₜ t) = s • D t := rfl
#align derivation.tensor_product_to_tmul Derivation.tensorProductTo_tmul

theorem Derivation.tensorProductTo_mul (D : Derivation R S M) (x y : S ⊗[R] S) :
    D.tensorProductTo (x * y) =
      TensorProduct.lmul' (S := S) R x • D.tensorProductTo y +
        TensorProduct.lmul' (S := S) R y • D.tensorProductTo x := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · rw [zero_mul, map_zero, map_zero, zero_smul, smul_zero, add_zero]
  swap
  · intro x₁ y₁ h₁ h₂
    rw [add_mul, map_add, map_add, map_add, add_smul, smul_add, h₁, h₂, add_add_add_comm]
  intro x₁ x₂
  refine TensorProduct.induction_on y ?_ ?_ ?_
  · rw [mul_zero, map_zero, map_zero, zero_smul, smul_zero, add_zero]
  swap
  · intro x₁ y₁ h₁ h₂
    rw [mul_add, map_add, map_add, map_add, add_smul, smul_add, h₁, h₂, add_add_add_comm]
  intro x y
  simp only [TensorProduct.tmul_mul_tmul, Derivation.tensorProductTo,
    TensorProduct.AlgebraTensorModule.lift_apply, TensorProduct.lift.tmul',
    TensorProduct.lmul'_apply_tmul]
  dsimp
  rw [D.leibniz]
  simp only [smul_smul, smul_add, mul_comm (x * y) x₁, mul_right_comm x₁ x₂, ← mul_assoc]
#align derivation.tensor_product_to_mul Derivation.tensorProductTo_mul

variable (R S)

/-- The kernel of `S ⊗[R] S →ₐ[R] S` is generated by `1 ⊗ s - s ⊗ 1` as a `S`-module. -/
theorem KaehlerDifferential.submodule_span_range_eq_ideal :
    Submodule.span S (Set.range fun s : S => (1 : S) ⊗ₜ[R] s - s ⊗ₜ[R] (1 : S)) =
      (KaehlerDifferential.ideal R S).restrictScalars S := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    exact KaehlerDifferential.one_smul_sub_smul_one_mem_ideal _ _
  · rintro x (hx : _ = _)
    have : x - TensorProduct.lmul' (S := S) R x ⊗ₜ[R] (1 : S) = x := by
      rw [hx, TensorProduct.zero_tmul, sub_zero]
    rw [← this]
    clear this hx
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · rw [map_zero, TensorProduct.zero_tmul, sub_zero]; exact zero_mem _
    · intro x y
      have : x ⊗ₜ[R] y - (x * y) ⊗ₜ[R] (1 : S) = x • ((1 : S) ⊗ₜ y - y ⊗ₜ (1 : S)) := by
        simp_rw [smul_sub, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [TensorProduct.lmul'_apply_tmul, this]
      refine Submodule.smul_mem _ x ?_
      apply Submodule.subset_span
      exact Set.mem_range_self y
    · intro x y hx hy
      rw [map_add, TensorProduct.add_tmul, ← sub_add_sub_comm]
      exact add_mem hx hy
#align kaehler_differential.submodule_span_range_eq_ideal KaehlerDifferential.submodule_span_range_eq_ideal

theorem KaehlerDifferential.span_range_eq_ideal :
    Ideal.span (Set.range fun s : S => (1 : S) ⊗ₜ[R] s - s ⊗ₜ[R] (1 : S)) =
      KaehlerDifferential.ideal R S := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨s, rfl⟩
    exact KaehlerDifferential.one_smul_sub_smul_one_mem_ideal _ _
  · change (KaehlerDifferential.ideal R S).restrictScalars S ≤ (Ideal.span _).restrictScalars S
    rw [← KaehlerDifferential.submodule_span_range_eq_ideal, Ideal.span]
    conv_rhs => rw [← Submodule.span_span_of_tower S]
    exact Submodule.subset_span
#align kaehler_differential.span_range_eq_ideal KaehlerDifferential.span_range_eq_ideal

/-- The module of Kähler differentials (Kahler differentials, Kaehler differentials).
This is implemented as `I / I ^ 2` with `I` the kernel of the multiplication map `S ⊗[R] S →ₐ[R] S`.
To view elements as a linear combination of the form `s • D s'`, use
`KaehlerDifferential.tensorProductTo_surjective` and `Derivation.tensorProductTo_tmul`.

We also provide the notation `Ω[S⁄R]` for `KaehlerDifferential R S`.
Note that the slash is `\textfractionsolidus`.
-/
def KaehlerDifferential : Type v :=
  (KaehlerDifferential.ideal R S).Cotangent
#align kaehler_differential KaehlerDifferential

instance : AddCommGroup (KaehlerDifferential R S) := by
  unfold KaehlerDifferential
  infer_instance

instance KaehlerDifferential.module : Module (S ⊗[R] S) (KaehlerDifferential R S) :=
  Ideal.Cotangent.moduleOfTower _
#align kaehler_differential.module KaehlerDifferential.module

@[inherit_doc KaehlerDifferential]
notation:100 "Ω[" S "⁄" R "]" => KaehlerDifferential R S

instance : Nonempty (Ω[S⁄R]) := ⟨0⟩

instance KaehlerDifferential.module' {R' : Type*} [CommRing R'] [Algebra R' S]
  [SMulCommClass R R' S] :
    Module R' (Ω[S⁄R]) :=
  Submodule.Quotient.module' _
#align kaehler_differential.module' KaehlerDifferential.module'

instance : IsScalarTower S (S ⊗[R] S) (Ω[S⁄R]) :=
  Ideal.Cotangent.isScalarTower _

instance KaehlerDifferential.isScalarTower_of_tower {R₁ R₂ : Type*} [CommRing R₁] [CommRing R₂]
    [Algebra R₁ S] [Algebra R₂ S] [SMul R₁ R₂]
    [SMulCommClass R R₁ S] [SMulCommClass R R₂ S] [IsScalarTower R₁ R₂ S] :
    IsScalarTower R₁ R₂ (Ω[S⁄R]) :=
  Submodule.Quotient.isScalarTower _ _

#align kaehler_differential.is_scalar_tower_of_tower KaehlerDifferential.isScalarTower_of_tower

instance KaehlerDifferential.isScalarTower' : IsScalarTower R (S ⊗[R] S) (Ω[S⁄R]) :=
  Submodule.Quotient.isScalarTower _ _
#align kaehler_differential.is_scalar_tower' KaehlerDifferential.isScalarTower'

/-- The quotient map `I → Ω[S⁄R]` with `I` being the kernel of `S ⊗[R] S → S`. -/
def KaehlerDifferential.fromIdeal : KaehlerDifferential.ideal R S →ₗ[S ⊗[R] S] Ω[S⁄R] :=
  (KaehlerDifferential.ideal R S).toCotangent
#align kaehler_differential.from_ideal KaehlerDifferential.fromIdeal

/-- (Implementation) The underlying linear map of the derivation into `Ω[S⁄R]`. -/
def KaehlerDifferential.DLinearMap : S →ₗ[R] Ω[S⁄R] :=
  ((KaehlerDifferential.fromIdeal R S).restrictScalars R).comp
    ((TensorProduct.includeRight.toLinearMap - TensorProduct.includeLeft.toLinearMap :
            S →ₗ[R] S ⊗[R] S).codRestrict
        ((KaehlerDifferential.ideal R S).restrictScalars R)
        (KaehlerDifferential.one_smul_sub_smul_one_mem_ideal R) :
      _ →ₗ[R] _)
set_option linter.uppercaseLean3 false in
#align kaehler_differential.D_linear_map KaehlerDifferential.DLinearMap

theorem KaehlerDifferential.DLinearMap_apply (s : S) :
    KaehlerDifferential.DLinearMap R S s =
      (KaehlerDifferential.ideal R S).toCotangent
        ⟨1 ⊗ₜ s - s ⊗ₜ 1, KaehlerDifferential.one_smul_sub_smul_one_mem_ideal R s⟩ := rfl
set_option linter.uppercaseLean3 false in
#align kaehler_differential.D_linear_map_apply KaehlerDifferential.DLinearMap_apply

/-- The universal derivation into `Ω[S⁄R]`. -/
def KaehlerDifferential.D : Derivation R S (Ω[S⁄R]) :=
  { toLinearMap := KaehlerDifferential.DLinearMap R S
    map_one_eq_zero' := by
      dsimp [KaehlerDifferential.DLinearMap_apply]
      congr
      rw [sub_self]
    leibniz' := fun a b => by
      have : LinearMap.CompatibleSMul { x // x ∈ ideal R S } (Ω[S⁄R]) S (S ⊗[R] S) := inferInstance
      dsimp [KaehlerDifferential.DLinearMap_apply, - Ideal.toCotangent_apply]
      -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
      erw [← LinearMap.map_smul_of_tower (M₂ := Ω[S⁄R]),
        ← LinearMap.map_smul_of_tower (M₂ := Ω[S⁄R]), ← map_add, Ideal.toCotangent_eq, pow_two]
      convert Submodule.mul_mem_mul (KaehlerDifferential.one_smul_sub_smul_one_mem_ideal R a : _)
        (KaehlerDifferential.one_smul_sub_smul_one_mem_ideal R b : _) using 1
      simp only [AddSubgroupClass.coe_sub, Submodule.coe_add, Submodule.coe_mk,
        TensorProduct.tmul_mul_tmul, mul_sub, sub_mul, mul_comm b, Submodule.coe_smul_of_tower,
        smul_sub, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      ring_nf }
set_option linter.uppercaseLean3 false in
#align kaehler_differential.D KaehlerDifferential.D

theorem KaehlerDifferential.D_apply (s : S) :
    KaehlerDifferential.D R S s =
      (KaehlerDifferential.ideal R S).toCotangent
        ⟨1 ⊗ₜ s - s ⊗ₜ 1, KaehlerDifferential.one_smul_sub_smul_one_mem_ideal R s⟩ := rfl
set_option linter.uppercaseLean3 false in
#align kaehler_differential.D_apply KaehlerDifferential.D_apply

theorem KaehlerDifferential.span_range_derivation :
    Submodule.span S (Set.range <| KaehlerDifferential.D R S) = ⊤ := by
  rw [_root_.eq_top_iff]
  rintro x -
  obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.toCotangent_surjective _ x
  have : x ∈ (KaehlerDifferential.ideal R S).restrictScalars S := hx
  rw [← KaehlerDifferential.submodule_span_range_eq_ideal] at this
  suffices ∃ hx, (KaehlerDifferential.ideal R S).toCotangent ⟨x, hx⟩ ∈
      Submodule.span S (Set.range <| KaehlerDifferential.D R S) by
    exact this.choose_spec
  refine Submodule.span_induction this ?_ ?_ ?_ ?_
  · rintro _ ⟨x, rfl⟩
    refine ⟨KaehlerDifferential.one_smul_sub_smul_one_mem_ideal R x, ?_⟩
    apply Submodule.subset_span
    exact ⟨x, KaehlerDifferential.DLinearMap_apply R S x⟩
  · exact ⟨zero_mem _, Submodule.zero_mem _⟩
  · rintro x y ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩; exact ⟨add_mem hx₁ hy₁, Submodule.add_mem _ hx₂ hy₂⟩
  · rintro r x ⟨hx₁, hx₂⟩;
    exact ⟨((KaehlerDifferential.ideal R S).restrictScalars S).smul_mem r hx₁,
      Submodule.smul_mem _ r hx₂⟩
#align kaehler_differential.span_range_derivation KaehlerDifferential.span_range_derivation

variable {R S}

/-- The linear map from `Ω[S⁄R]`, associated with a derivation. -/
def Derivation.liftKaehlerDifferential (D : Derivation R S M) : Ω[S⁄R] →ₗ[S] M := by
  refine LinearMap.comp ((((KaehlerDifferential.ideal R S) •
    (⊤ : Submodule (S ⊗[R] S) (KaehlerDifferential.ideal R S))).restrictScalars S).liftQ ?_ ?_)
    (Submodule.Quotient.restrictScalarsEquiv S _).symm.toLinearMap
  · exact D.tensorProductTo.comp ((KaehlerDifferential.ideal R S).subtype.restrictScalars S)
  · intro x hx
    rw [LinearMap.mem_ker]
    refine Submodule.smul_induction_on hx ?_ ?_
    · rintro x hx y -
      rw [RingHom.mem_ker] at hx
      dsimp
      rw [Derivation.tensorProductTo_mul, hx, y.prop, zero_smul, zero_smul, zero_add]
    · intro x y ex ey; rw [map_add, ex, ey, zero_add]
#align derivation.lift_kaehler_differential Derivation.liftKaehlerDifferential

theorem Derivation.liftKaehlerDifferential_apply (D : Derivation R S M) (x) :
    D.liftKaehlerDifferential ((KaehlerDifferential.ideal R S).toCotangent x) =
      D.tensorProductTo x := rfl
#align derivation.lift_kaehler_differential_apply Derivation.liftKaehlerDifferential_apply

theorem Derivation.liftKaehlerDifferential_comp (D : Derivation R S M) :
    D.liftKaehlerDifferential.compDer (KaehlerDifferential.D R S) = D := by
  ext a
  dsimp [KaehlerDifferential.D_apply]
  refine (D.liftKaehlerDifferential_apply _).trans ?_
  rw [Subtype.coe_mk, map_sub, Derivation.tensorProductTo_tmul, Derivation.tensorProductTo_tmul,
    one_smul, D.map_one_eq_zero, smul_zero, sub_zero]
#align derivation.lift_kaehler_differential_comp Derivation.liftKaehlerDifferential_comp

@[simp]
theorem Derivation.liftKaehlerDifferential_comp_D (D' : Derivation R S M) (x : S) :
    D'.liftKaehlerDifferential (KaehlerDifferential.D R S x) = D' x :=
  Derivation.congr_fun D'.liftKaehlerDifferential_comp x
set_option linter.uppercaseLean3 false in
#align derivation.lift_kaehler_differential_comp_D Derivation.liftKaehlerDifferential_comp_D

@[ext]
theorem Derivation.liftKaehlerDifferential_unique (f f' : Ω[S⁄R] →ₗ[S] M)
    (hf : f.compDer (KaehlerDifferential.D R S) = f'.compDer (KaehlerDifferential.D R S)) :
    f = f' := by
  apply LinearMap.ext
  intro x
  have : x ∈ Submodule.span S (Set.range <| KaehlerDifferential.D R S) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  refine Submodule.span_induction this ?_ ?_ ?_ ?_
  · rintro _ ⟨x, rfl⟩; exact congr_arg (fun D : Derivation R S M => D x) hf
  · rw [map_zero, map_zero]
  · intro x y hx hy; rw [map_add, map_add, hx, hy]
  · intro a x e; simp [e]
#align derivation.lift_kaehler_differential_unique Derivation.liftKaehlerDifferential_unique

variable (R S)

theorem Derivation.liftKaehlerDifferential_D :
    (KaehlerDifferential.D R S).liftKaehlerDifferential = LinearMap.id :=
  Derivation.liftKaehlerDifferential_unique _ _
    (KaehlerDifferential.D R S).liftKaehlerDifferential_comp
set_option linter.uppercaseLean3 false in
#align derivation.lift_kaehler_differential_D Derivation.liftKaehlerDifferential_D

variable {R S}

theorem KaehlerDifferential.D_tensorProductTo (x : KaehlerDifferential.ideal R S) :
    (KaehlerDifferential.D R S).tensorProductTo x =
      (KaehlerDifferential.ideal R S).toCotangent x := by
  rw [← Derivation.liftKaehlerDifferential_apply, Derivation.liftKaehlerDifferential_D]
  rfl
set_option linter.uppercaseLean3 false in
#align kaehler_differential.D_tensor_product_to KaehlerDifferential.D_tensorProductTo

variable (R S)

theorem KaehlerDifferential.tensorProductTo_surjective :
    Function.Surjective (KaehlerDifferential.D R S).tensorProductTo := by
  intro x; obtain ⟨x, rfl⟩ := (KaehlerDifferential.ideal R S).toCotangent_surjective x
  exact ⟨x, KaehlerDifferential.D_tensorProductTo x⟩
#align kaehler_differential.tensor_product_to_surjective KaehlerDifferential.tensorProductTo_surjective

/-- The `S`-linear maps from `Ω[S⁄R]` to `M` are (`S`-linearly) equivalent to `R`-derivations
from `S` to `M`.  -/
def KaehlerDifferential.linearMapEquivDerivation : (Ω[S⁄R] →ₗ[S] M) ≃ₗ[S] Derivation R S M :=
  { Derivation.llcomp.flip <| KaehlerDifferential.D R S with
    invFun := Derivation.liftKaehlerDifferential
    left_inv := fun _ =>
      Derivation.liftKaehlerDifferential_unique _ _ (Derivation.liftKaehlerDifferential_comp _)
    right_inv := Derivation.liftKaehlerDifferential_comp }
#align kaehler_differential.linear_map_equiv_derivation KaehlerDifferential.linearMapEquivDerivation

/-- The quotient ring of `S ⊗ S ⧸ J ^ 2` by `Ω[S⁄R]` is isomorphic to `S`. -/
def KaehlerDifferential.quotientCotangentIdealRingEquiv :
    (S ⊗ S ⧸ KaehlerDifferential.ideal R S ^ 2) ⧸ (KaehlerDifferential.ideal R S).cotangentIdeal ≃+*
      S := by
  have : Function.RightInverse (TensorProduct.includeLeft (R := R) (A := S) (B := S))
      (↑(TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S) : S ⊗[R] S →+* S) := by
    intro x; rw [AlgHom.coe_toRingHom, ← AlgHom.comp_apply, TensorProduct.lmul'_comp_includeLeft]
    rfl
  refine (Ideal.quotCotangent _).trans ?_
  refine (Ideal.quotEquivOfEq ?_).trans (RingHom.quotientKerEquivOfRightInverse this)
  ext; rfl
#align kaehler_differential.quotient_cotangent_ideal_ring_equiv KaehlerDifferential.quotientCotangentIdealRingEquiv

/-- The quotient ring of `S ⊗ S ⧸ J ^ 2` by `Ω[S⁄R]` is isomorphic to `S` as an `S`-algebra. -/
def KaehlerDifferential.quotientCotangentIdeal :
    ((S ⊗ S ⧸ KaehlerDifferential.ideal R S ^ 2) ⧸
        (KaehlerDifferential.ideal R S).cotangentIdeal) ≃ₐ[S] S :=
  { KaehlerDifferential.quotientCotangentIdealRingEquiv R S with
    commutes' := (KaehlerDifferential.quotientCotangentIdealRingEquiv R S).apply_symm_apply }
#align kaehler_differential.quotient_cotangent_ideal KaehlerDifferential.quotientCotangentIdeal

theorem KaehlerDifferential.End_equiv_aux (f : S →ₐ[R] S ⊗ S ⧸ KaehlerDifferential.ideal R S ^ 2) :
    (Ideal.Quotient.mkₐ R (KaehlerDifferential.ideal R S).cotangentIdeal).comp f =
        IsScalarTower.toAlgHom R S _ ↔
      (TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S).kerSquareLift.comp f = AlgHom.id R S := by
  rw [AlgHom.ext_iff, AlgHom.ext_iff]
  apply forall_congr'
  intro x
  have e₁ : (TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S).kerSquareLift (f x) =
      KaehlerDifferential.quotientCotangentIdealRingEquiv R S
        (Ideal.Quotient.mk (KaehlerDifferential.ideal R S).cotangentIdeal <| f x) := by
    generalize f x = y; obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y; rfl
  have e₂ :
    x = KaehlerDifferential.quotientCotangentIdealRingEquiv R S (IsScalarTower.toAlgHom R S _ x) :=
    (mul_one x).symm
  constructor
  · intro e
    exact (e₁.trans (@RingEquiv.congr_arg _ _ _ _ _ _
      (KaehlerDifferential.quotientCotangentIdealRingEquiv R S) _ _ e)).trans e₂.symm
  · intro e; apply (KaehlerDifferential.quotientCotangentIdealRingEquiv R S).injective
    exact e₁.symm.trans (e.trans e₂)
#align kaehler_differential.End_equiv_aux KaehlerDifferential.End_equiv_aux

/- Note: Lean is slow to synthesize theses instances (times out).
  Without them the endEquivDerivation' and endEquivAuxEquiv both have significant timeouts.
  In Mathlib 3, it was slow but not this slow. -/
/-- A shortcut instance to prevent timing out. Hopefully to be removed in the future. -/
local instance smul_SSmod_SSmod : SMul (S ⊗[R] S ⧸ KaehlerDifferential.ideal R S ^ 2)
    (S ⊗[R] S ⧸ KaehlerDifferential.ideal R S ^ 2) := Mul.toSMul _

/-- A shortcut instance to prevent timing out. Hopefully to be removed in the future. -/
@[nolint defLemma]
local instance isScalarTower_S_right :
    IsScalarTower S (S ⊗[R] S ⧸ KaehlerDifferential.ideal R S ^ 2)
      (S ⊗[R] S ⧸ KaehlerDifferential.ideal R S ^ 2) := Ideal.Quotient.isScalarTower_right

/-- A shortcut instance to prevent timing out. Hopefully to be removed in the future. -/
@[nolint defLemma]
local instance isScalarTower_R_right :
    IsScalarTower R (S ⊗[R] S ⧸ KaehlerDifferential.ideal R S ^ 2)
      (S ⊗[R] S ⧸ KaehlerDifferential.ideal R S ^ 2) := Ideal.Quotient.isScalarTower_right

/-- A shortcut instance to prevent timing out. Hopefully to be removed in the future. -/
@[nolint defLemma]
local instance isScalarTower_SS_right : IsScalarTower (S ⊗[R] S)
    (S ⊗[R] S ⧸ KaehlerDifferential.ideal R S ^ 2) (S ⊗[R] S ⧸ KaehlerDifferential.ideal R S ^ 2) :=
  Ideal.Quotient.isScalarTower_right

/-- A shortcut instance to prevent timing out. Hopefully to be removed in the future. -/
local instance instS : Module S (KaehlerDifferential.ideal R S).cotangentIdeal :=
  Submodule.module' _

/-- A shortcut instance to prevent timing out. Hopefully to be removed in the future. -/
local instance instR : Module R (KaehlerDifferential.ideal R S).cotangentIdeal :=
  Submodule.module' _

/-- A shortcut instance to prevent timing out. Hopefully to be removed in the future. -/
local instance instSS : Module (S ⊗[R] S) (KaehlerDifferential.ideal R S).cotangentIdeal :=
  Submodule.module' _

/-- Derivations into `Ω[S⁄R]` is equivalent to derivations
into `(KaehlerDifferential.ideal R S).cotangentIdeal`. -/
noncomputable def KaehlerDifferential.endEquivDerivation' :
    Derivation R S (Ω[S⁄R]) ≃ₗ[R] Derivation R S (ideal R S).cotangentIdeal :=
  LinearEquiv.compDer ((KaehlerDifferential.ideal R S).cotangentEquivIdeal.restrictScalars S)
#align kaehler_differential.End_equiv_derivation' KaehlerDifferential.endEquivDerivation'

/-- (Implementation) An `Equiv` version of `KaehlerDifferential.End_equiv_aux`.
Used in `KaehlerDifferential.endEquiv`. -/
def KaehlerDifferential.endEquivAuxEquiv :
    { f //
        (Ideal.Quotient.mkₐ R (KaehlerDifferential.ideal R S).cotangentIdeal).comp f =
          IsScalarTower.toAlgHom R S _ } ≃
      { f // (TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S).kerSquareLift.comp f = AlgHom.id R S } :=
  (Equiv.refl _).subtypeEquiv (KaehlerDifferential.End_equiv_aux R S)
#align kaehler_differential.End_equiv_aux_equiv KaehlerDifferential.endEquivAuxEquiv

/--
The endomorphisms of `Ω[S⁄R]` corresponds to sections of the surjection `S ⊗[R] S ⧸ J ^ 2 →ₐ[R] S`,
with `J` being the kernel of the multiplication map `S ⊗[R] S →ₐ[R] S`.
-/
noncomputable def KaehlerDifferential.endEquiv :
    Module.End S (Ω[S⁄R]) ≃
      { f // (TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S).kerSquareLift.comp f = AlgHom.id R S } :=
  (KaehlerDifferential.linearMapEquivDerivation R S).toEquiv.trans <|
    (KaehlerDifferential.endEquivDerivation' R S).toEquiv.trans <|
      (derivationToSquareZeroEquivLift (KaehlerDifferential.ideal R S).cotangentIdeal
            (KaehlerDifferential.ideal R S).cotangentIdeal_square).trans <|
        KaehlerDifferential.endEquivAuxEquiv R S
#align kaehler_differential.End_equiv KaehlerDifferential.endEquiv

section Presentation

open KaehlerDifferential (D)

open Finsupp (single)

/-- The `S`-submodule of `S →₀ S` (the direct sum of copies of `S` indexed by `S`) generated by
the relations:
1. `dx + dy = d(x + y)`
2. `x dy + y dx = d(x * y)`
3. `dr = 0` for `r ∈ R`
where `db` is the unit in the copy of `S` with index `b`.

This is the kernel of the surjection `Finsupp.total S Ω[S⁄R] S (KaehlerDifferential.D R S)`.
See `KaehlerDifferential.kerTotal_eq` and `KaehlerDifferential.total_surjective`.
-/
noncomputable def KaehlerDifferential.kerTotal : Submodule S (S →₀ S) :=
  Submodule.span S
    (((Set.range fun x : S × S => single x.1 1 + single x.2 1 - single (x.1 + x.2) 1) ∪
        Set.range fun x : S × S => single x.2 x.1 + single x.1 x.2 - single (x.1 * x.2) 1) ∪
      Set.range fun x : R => single (algebraMap R S x) 1)
#align kaehler_differential.ker_total KaehlerDifferential.kerTotal

unsuppress_compilation in
-- Porting note: was `local notation x "𝖣" y => (KaehlerDifferential.kerTotal R S).mkQ (single y x)`
-- but not having `DFunLike.coe` leads to `kerTotal_mkQ_single_smul` failing.
local notation3 x "𝖣" y => DFunLike.coe (KaehlerDifferential.kerTotal R S).mkQ (single y x)

theorem KaehlerDifferential.kerTotal_mkQ_single_add (x y z) : (z𝖣x + y) = (z𝖣x) + z𝖣y := by
  rw [← map_add, eq_comm, ← sub_eq_zero, ← map_sub (Submodule.mkQ (kerTotal R S)),
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  simp_rw [← Finsupp.smul_single_one _ z, ← smul_add, ← smul_sub]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl <| Or.inl <| ⟨⟨_, _⟩, rfl⟩))
#align kaehler_differential.ker_total_mkq_single_add KaehlerDifferential.kerTotal_mkQ_single_add

theorem KaehlerDifferential.kerTotal_mkQ_single_mul (x y z) :
    (z𝖣x * y) = ((z * x)𝖣y) + (z * y)𝖣x := by
  rw [← map_add, eq_comm, ← sub_eq_zero, ← map_sub (Submodule.mkQ (kerTotal R S)),
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  simp_rw [← Finsupp.smul_single_one _ z, ← @smul_eq_mul _ _ z, ← Finsupp.smul_single, ← smul_add,
    ← smul_sub]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl <| Or.inr <| ⟨⟨_, _⟩, rfl⟩))
#align kaehler_differential.ker_total_mkq_single_mul KaehlerDifferential.kerTotal_mkQ_single_mul

theorem KaehlerDifferential.kerTotal_mkQ_single_algebraMap (x y) : (y𝖣algebraMap R S x) = 0 := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, ← Finsupp.smul_single_one _ y]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr <| ⟨_, rfl⟩))
#align kaehler_differential.ker_total_mkq_single_algebra_map KaehlerDifferential.kerTotal_mkQ_single_algebraMap

theorem KaehlerDifferential.kerTotal_mkQ_single_algebraMap_one (x) : (x𝖣1) = 0 := by
  rw [← (algebraMap R S).map_one, KaehlerDifferential.kerTotal_mkQ_single_algebraMap]
#align kaehler_differential.ker_total_mkq_single_algebra_map_one KaehlerDifferential.kerTotal_mkQ_single_algebraMap_one

theorem KaehlerDifferential.kerTotal_mkQ_single_smul (r : R) (x y) : (y𝖣r • x) = r • y𝖣x := by
  letI : SMulZeroClass R S := inferInstance
  rw [Algebra.smul_def, KaehlerDifferential.kerTotal_mkQ_single_mul,
    KaehlerDifferential.kerTotal_mkQ_single_algebraMap, add_zero, ← LinearMap.map_smul_of_tower,
    Finsupp.smul_single, mul_comm, Algebra.smul_def]
#align kaehler_differential.ker_total_mkq_single_smul KaehlerDifferential.kerTotal_mkQ_single_smul

/-- The (universal) derivation into `(S →₀ S) ⧸ KaehlerDifferential.kerTotal R S`. -/
noncomputable def KaehlerDifferential.derivationQuotKerTotal :
    Derivation R S ((S →₀ S) ⧸ KaehlerDifferential.kerTotal R S) where
  toFun x := 1𝖣x
  map_add' x y := KaehlerDifferential.kerTotal_mkQ_single_add _ _ _ _ _
  map_smul' r s := KaehlerDifferential.kerTotal_mkQ_single_smul _ _ _ _ _
  map_one_eq_zero' := KaehlerDifferential.kerTotal_mkQ_single_algebraMap_one _ _ _
  leibniz' a b :=
    (KaehlerDifferential.kerTotal_mkQ_single_mul _ _ _ _ _).trans
      (by simp_rw [← Finsupp.smul_single_one _ (1 * _ : S)]; dsimp; simp)
#align kaehler_differential.derivation_quot_ker_total KaehlerDifferential.derivationQuotKerTotal

theorem KaehlerDifferential.derivationQuotKerTotal_apply (x) :
    KaehlerDifferential.derivationQuotKerTotal R S x = 1𝖣x :=
  rfl
#align kaehler_differential.derivation_quot_ker_total_apply KaehlerDifferential.derivationQuotKerTotal_apply

theorem KaehlerDifferential.derivationQuotKerTotal_lift_comp_total :
    (KaehlerDifferential.derivationQuotKerTotal R S).liftKaehlerDifferential.comp
        (Finsupp.total S (Ω[S⁄R]) S (KaehlerDifferential.D R S)) =
      Submodule.mkQ _ := by
  apply Finsupp.lhom_ext
  intro a b
  conv_rhs => rw [← Finsupp.smul_single_one a b, LinearMap.map_smul]
  simp [KaehlerDifferential.derivationQuotKerTotal_apply]
#align kaehler_differential.derivation_quot_ker_total_lift_comp_total KaehlerDifferential.derivationQuotKerTotal_lift_comp_total

theorem KaehlerDifferential.kerTotal_eq :
    LinearMap.ker (Finsupp.total S (Ω[S⁄R]) S (KaehlerDifferential.D R S)) =
      KaehlerDifferential.kerTotal R S := by
  apply le_antisymm
  · conv_rhs => rw [← (KaehlerDifferential.kerTotal R S).ker_mkQ]
    rw [← KaehlerDifferential.derivationQuotKerTotal_lift_comp_total]
    exact LinearMap.ker_le_ker_comp _ _
  · rw [KaehlerDifferential.kerTotal, Submodule.span_le]
    rintro _ ((⟨⟨x, y⟩, rfl⟩ | ⟨⟨x, y⟩, rfl⟩) | ⟨x, rfl⟩) <;> dsimp <;> simp [LinearMap.mem_ker]
#align kaehler_differential.ker_total_eq KaehlerDifferential.kerTotal_eq

theorem KaehlerDifferential.total_surjective :
    Function.Surjective (Finsupp.total S (Ω[S⁄R]) S (KaehlerDifferential.D R S)) := by
  rw [← LinearMap.range_eq_top, Finsupp.range_total, KaehlerDifferential.span_range_derivation]
#align kaehler_differential.total_surjective KaehlerDifferential.total_surjective

/-- `Ω[S⁄R]` is isomorphic to `S` copies of `S` with kernel `KaehlerDifferential.kerTotal`. -/
@[simps!]
noncomputable def KaehlerDifferential.quotKerTotalEquiv :
    ((S →₀ S) ⧸ KaehlerDifferential.kerTotal R S) ≃ₗ[S] Ω[S⁄R] :=
  { (KaehlerDifferential.kerTotal R S).liftQ
      (Finsupp.total S (Ω[S⁄R]) S (KaehlerDifferential.D R S))
      (KaehlerDifferential.kerTotal_eq R S).ge with
    invFun := (KaehlerDifferential.derivationQuotKerTotal R S).liftKaehlerDifferential
    left_inv := by
      intro x
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
      exact
        LinearMap.congr_fun (KaehlerDifferential.derivationQuotKerTotal_lift_comp_total R S : _) x
    right_inv := by
      intro x
      obtain ⟨x, rfl⟩ := KaehlerDifferential.total_surjective R S x
      have := LinearMap.congr_fun (KaehlerDifferential.derivationQuotKerTotal_lift_comp_total R S) x
      rw [LinearMap.comp_apply] at this
      rw [this]
      rfl }
#align kaehler_differential.quot_ker_total_equiv KaehlerDifferential.quotKerTotalEquiv

theorem KaehlerDifferential.quotKerTotalEquiv_symm_comp_D :
    (KaehlerDifferential.quotKerTotalEquiv R S).symm.toLinearMap.compDer
        (KaehlerDifferential.D R S) =
      KaehlerDifferential.derivationQuotKerTotal R S := by
  convert (KaehlerDifferential.derivationQuotKerTotal R S).liftKaehlerDifferential_comp
set_option linter.uppercaseLean3 false in
#align kaehler_differential.quot_ker_total_equiv_symm_comp_D KaehlerDifferential.quotKerTotalEquiv_symm_comp_D

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra R A] [Algebra S B] [Algebra R B]

variable [Algebra A B] [IsScalarTower R S B] [IsScalarTower R A B]

unsuppress_compilation in
-- The map `(A →₀ A) →ₗ[A] (B →₀ B)`
local macro "finsupp_map" : term =>
  `((Finsupp.mapRange.linearMap (Algebra.linearMap A B)).comp
    (Finsupp.lmapDomain A A (algebraMap A B)))

theorem KaehlerDifferential.kerTotal_map (h : Function.Surjective (algebraMap A B)) :
    (KaehlerDifferential.kerTotal R A).map finsupp_map ⊔
        Submodule.span A (Set.range fun x : S => single (algebraMap S B x) (1 : B)) =
      (KaehlerDifferential.kerTotal S B).restrictScalars _ := by
  rw [KaehlerDifferential.kerTotal, Submodule.map_span, KaehlerDifferential.kerTotal,
    Submodule.restrictScalars_span _ _ h]
  -- Porting note: the proof is diverging from the mathlib3 proof here.
  -- `map_sub` and `map_add` are not firing so we need to use `LinearMap.map_*` instead
  simp_rw [Set.image_union, Submodule.span_union, ← Set.image_univ, Set.image_image, Set.image_univ,
    LinearMap.map_sub, LinearMap.map_add]
  simp only [LinearMap.comp_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, Algebra.linearMap_apply,
    map_one, map_add, map_mul]
  simp_rw [sup_assoc, ← (h.Prod_map h).range_comp]
  congr!
  -- Porting note: new
  simp_rw [← IsScalarTower.algebraMap_apply R A B]
  rw [sup_eq_right]
  apply Submodule.span_mono
  simp_rw [IsScalarTower.algebraMap_apply R S B]
  exact Set.range_comp_subset_range (algebraMap R S) fun x => single (algebraMap S B x) (1 : B)
#align kaehler_differential.ker_total_map KaehlerDifferential.kerTotal_map

end Presentation

section ExactSequence

/- We have the commutative diagram
A --→ B
↑     ↑
|     |
R --→ S -/
variable (A B : Type*) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

variable [Algebra A B] [Algebra S B] [IsScalarTower R A B] [IsScalarTower R S B]

variable [SMulCommClass S A B]

/-- The map `Ω[A⁄R] →ₗ[A] Ω[B⁄R]` given a square
A --→ B
↑     ↑
|     |
R --→ S -/
def KaehlerDifferential.map : Ω[A⁄R] →ₗ[A] Ω[B⁄S] :=
  Derivation.liftKaehlerDifferential
    (((KaehlerDifferential.D S B).restrictScalars R).compAlgebraMap A)
#align kaehler_differential.map KaehlerDifferential.map

theorem KaehlerDifferential.map_compDer :
    (KaehlerDifferential.map R S A B).compDer (KaehlerDifferential.D R A) =
      ((KaehlerDifferential.D S B).restrictScalars R).compAlgebraMap A :=
  Derivation.liftKaehlerDifferential_comp _
#align kaehler_differential.map_comp_der KaehlerDifferential.map_compDer

theorem KaehlerDifferential.map_D (x : A) :
    KaehlerDifferential.map R S A B (KaehlerDifferential.D R A x) =
      KaehlerDifferential.D S B (algebraMap A B x) :=
  Derivation.congr_fun (KaehlerDifferential.map_compDer R S A B) x
set_option linter.uppercaseLean3 false in
#align kaehler_differential.map_D KaehlerDifferential.map_D

open IsScalarTower (toAlgHom)

theorem KaehlerDifferential.map_surjective_of_surjective
    (h : Function.Surjective (algebraMap A B)) :
    Function.Surjective (KaehlerDifferential.map R S A B) := by
  rw [← LinearMap.range_eq_top, _root_.eq_top_iff, ← @Submodule.restrictScalars_top A B,
    ← KaehlerDifferential.span_range_derivation, Submodule.restrictScalars_span _ _ h,
    Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, rfl⟩ := h x
  rw [← KaehlerDifferential.map_D R S A B]
  exact ⟨_, rfl⟩
#align kaehler_differential.map_surjective_of_surjective KaehlerDifferential.map_surjective_of_surjective

/-- The lift of the map `Ω[A⁄R] →ₗ[A] Ω[B⁄R]` to the base change along `A → B`.
This is the first map in the exact sequence `B ⊗[A] Ω[A⁄R] → Ω[B⁄R] → Ω[B⁄A] → 0`. -/
noncomputable def KaehlerDifferential.mapBaseChange : B ⊗[A] Ω[A⁄R] →ₗ[B] Ω[B⁄R] :=
  (TensorProduct.isBaseChange A (Ω[A⁄R]) B).lift (KaehlerDifferential.map R R A B)
#align kaehler_differential.map_base_change KaehlerDifferential.mapBaseChange

@[simp]
theorem KaehlerDifferential.mapBaseChange_tmul (x : B) (y : Ω[A⁄R]) :
    KaehlerDifferential.mapBaseChange R A B (x ⊗ₜ y) = x • KaehlerDifferential.map R R A B y := by
  conv_lhs => rw [← mul_one x, ← smul_eq_mul, ← TensorProduct.smul_tmul', LinearMap.map_smul]
  congr 1
  exact IsBaseChange.lift_eq _ _ _
#align kaehler_differential.map_base_change_tmul KaehlerDifferential.mapBaseChange_tmul

end ExactSequence

end KaehlerDifferential
