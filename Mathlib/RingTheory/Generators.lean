/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Tower
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Extension

/-!

# Generators of algebras

## Main definition

- `Algebra.Generators`: A family of generators of a `R`-algebra `S` consists of
  1. `vars`: The type of variables.
  2. `val : vars → S`: The assignment of each variable to a value.
  3. `σ`: A set-theoretic section of the induced `R`-algebra homomorphism `R[X] → S`, where we
     write `R[X]` for `R[vars]`.

- `Algebra.Generators.Hom`: Given a commuting square
  ```
  R --→ P = R[X] ---→ S
  |                   |
  ↓                   ↓
  R' -→ P' = R'[X'] → S
  ```
  A hom between `P` and `P'` is an assignment `X → P'` such that the arrows commute.

- `Algebra.Generators.Cotangent`: The cotangent space wrt `P = R[X] → S`, i.e. the
  space `I/I²` with `I` being the kernel of the presentation.

-/

universe w u v

open TensorProduct MvPolynomial

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/-- A family of generators of a `R`-algebra `S` consists of
1. `vars`: The type of variables.
2. `val : vars → S`: The assignment of each variable to a value in `S`.
3. `σ`: A section of `R[X] → S`. -/
structure Algebra.Generators where
  /-- The type of variables. -/
  vars : Type w
  /-- The assignment of each variable to a value in `S`. -/
  val : vars → S
  /-- A section of `R[X] → S`. -/
  σ' : S → MvPolynomial vars R
  aeval_val_σ' : ∀ s, aeval val (σ' s) = s

namespace Algebra.Generators

variable {R S}
variable (P : Generators.{w} R S)

/-- The polynomial ring wrt a family of generators. -/
protected
abbrev Ring : Type (max w u) := MvPolynomial P.vars R

/-- The designated section of wrt a family of generators. -/
def σ : S → P.Ring := P.σ'

/-- See Note [custom simps projection] -/
def Simps.σ : S → P.Ring := P.σ

initialize_simps_projections Algebra.Generators (σ' → σ)

@[simp]
lemma aeval_val_σ (s) : aeval P.val (P.σ s) = s := P.aeval_val_σ' s

instance : Algebra P.Ring S := (aeval P.val).toAlgebra

noncomputable instance {R₀} [CommRing R₀] [Algebra R₀ R] [Algebra R₀ S] [IsScalarTower R₀ R S] :
    IsScalarTower R₀ P.Ring S := IsScalarTower.of_algebraMap_eq'
  ((aeval (R := R) P.val).comp_algebraMap_of_tower R₀).symm

lemma algebraMap_eq : algebraMap P.Ring S = ↑(aeval (R := R) P.val) := rfl

@[simp]
lemma algebraMap_apply (x) : algebraMap P.Ring S x = aeval (R := R) P.val x := rfl

@[simp]
lemma σ_smul (x y) : P.σ x • y = x * y := by
  rw [Algebra.smul_def, algebraMap_apply, aeval_val_σ]

lemma σ_injective : P.σ.Injective := by
  intro x y e
  rw [← P.aeval_val_σ x, ← P.aeval_val_σ y, e]

lemma algebraMap_surjective : Function.Surjective (algebraMap P.Ring S) := (⟨_, P.aeval_val_σ ·⟩)

section Construction

/-- Construct `Generators` from an assignment `I → S` such that `R[X] → S` is surjective. -/
@[simps val, simps (config := .lemmasOnly) vars]
noncomputable
def ofSurjective {vars} (val : vars → S) (h : Function.Surjective (aeval (R := R) val)) :
    Generators R S where
  vars := vars
  val := val
  σ' x := (h x).choose
  aeval_val_σ' x := (h x).choose_spec

/-- If `algebraMap R S` is surjective, the empty type generates `S`. -/
noncomputable def ofSurjectiveAlgebraMap (h : Function.Surjective (algebraMap R S)) :
    Generators.{w} R S :=
  ofSurjective PEmpty.elim <| fun s ↦ by
    use C (h s).choose
    simp [(h s).choose_spec]

/-- The canonical generators for `R` as an `R`-algebra. -/
noncomputable def id : Generators.{w} R R := ofSurjectiveAlgebraMap <| by
  rw [id.map_eq_id]
  exact RingHomSurjective.is_surjective

/-- Construct `Generators` from an assignment `I → S` such that `R[X] → S` is surjective. -/
noncomputable
def ofAlgHom {I} (f : MvPolynomial I R →ₐ[R] S) (h : Function.Surjective f) :
    Generators R S :=
  ofSurjective (f ∘ X) (by rwa [show aeval (f ∘ X) = f by ext; simp])

/-- Construct `Generators` from a family of generators of `S`. -/
noncomputable
def ofSet {s : Set S} (hs : Algebra.adjoin R s = ⊤) : Generators R S := by
  refine ofSurjective (Subtype.val : s → S) ?_
  rwa [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval,
    Subtype.range_coe_subtype, Set.setOf_mem_eq]

variable (R S) in
/-- The `Generators` containing the whole algebra, which induces the canonical map  `R[S] → S`. -/
@[simps]
noncomputable
def self : Generators R S where
  vars := S
  val := _root_.id
  σ' := X
  aeval_val_σ' := aeval_X _

/-- The extension `R[X₁,...,Xₙ] → S` given a family of generators. -/
@[simps]
noncomputable
def toExtension : Extension R S where
  Ring := P.Ring
  σ := P.σ
  algebraMap_σ := P.aeval_val_σ

section Localization

variable (r : R) [IsLocalization.Away r S]

/-- If `S` is the localization of `R` away from `r`, we obtain a canonical generator mapping
to the inverse of `r`. -/
@[simps val, simps (config := .lemmasOnly) vars σ]
noncomputable
def localizationAway : Generators R S where
  vars := Unit
  val _ := IsLocalization.Away.invSelf r
  σ' s :=
    letI a : R := (IsLocalization.Away.sec r s).1
    letI n : ℕ := (IsLocalization.Away.sec r s).2
    C a * X () ^ n
  aeval_val_σ' s := by
    rw [map_mul, algHom_C, map_pow, aeval_X]
    simp only [← IsLocalization.Away.sec_spec, map_pow, IsLocalization.Away.invSelf]
    rw [← IsLocalization.mk'_pow, one_pow, ← IsLocalization.mk'_one (M := Submonoid.powers r) S r]
    rw [← IsLocalization.mk'_pow, one_pow, mul_assoc, ← IsLocalization.mk'_mul]
    rw [mul_one, one_mul, IsLocalization.mk'_pow]
    simp

end Localization

variable {T} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- Given two families of generators `S[X] → T` and `R[Y] → S`,
we may construct the family of generators `R[X, Y] → T`. -/
@[simps val, simps (config := .lemmasOnly) vars σ]
noncomputable
def comp (Q : Generators S T) (P : Generators R S) : Generators R T where
  vars := Q.vars ⊕ P.vars
  val := Sum.elim Q.val (algebraMap S T ∘ P.val)
  σ' x := (Q.σ x).sum (fun n r ↦ rename Sum.inr (P.σ r) * monomial (n.mapDomain Sum.inl) 1)
  aeval_val_σ' s := by
    have (x : P.Ring) : aeval (algebraMap S T ∘ P.val) x = algebraMap S T (aeval P.val x) := by
      rw [map_aeval, aeval_def, coe_eval₂Hom, ← IsScalarTower.algebraMap_eq, Function.comp_def]
    conv_rhs => rw [← Q.aeval_val_σ s, ← (Q.σ s).sum_single]
    simp only [map_finsupp_sum, map_mul, aeval_rename, Sum.elim_comp_inr, this, aeval_val_σ,
      aeval_monomial, map_one, Finsupp.prod_mapDomain_index_inj Sum.inl_injective, Sum.elim_inl,
      one_mul, single_eq_monomial]

variable (S) in
/-- If `R → S → T` is a tower of algebras, a family of generators `R[X] → T`
gives a family of generators `S[X] → T`. -/
@[simps val, simps (config := .lemmasOnly) vars]
noncomputable
def extendScalars (P : Generators R T) : Generators S T where
  vars := P.vars
  val := P.val
  σ' x := map (algebraMap R S) (P.σ x)
  aeval_val_σ' s := by simp [@aeval_def S, ← IsScalarTower.algebraMap_eq, ← @aeval_def R]

/-- If `P` is a family of generators of `S` over `R` and `T` is an `R`-algebra, we
obtain a natural family of generators of `T ⊗[R] S` over `T`. -/
@[simps! val, simps! (config := .lemmasOnly) vars]
noncomputable
def baseChange {T} [CommRing T] [Algebra R T] (P : Generators R S) : Generators T (T ⊗[R] S) := by
  apply Generators.ofSurjective (fun x ↦ 1 ⊗ₜ[R] P.val x)
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul a b =>
    let X := P.σ b
    use a • MvPolynomial.map (algebraMap R T) X
    simp only [LinearMapClass.map_smul, X, aeval_map_algebraMap]
    have : ∀ y : P.Ring,
      aeval (fun x ↦ (1 ⊗ₜ[R] P.val x : T ⊗[R] S)) y = 1 ⊗ₜ aeval (fun x ↦ P.val x) y := by
      intro y
      induction y using MvPolynomial.induction_on with
      | h_C a =>
        rw [aeval_C, aeval_C, TensorProduct.algebraMap_apply, algebraMap_eq_smul_one, smul_tmul,
          algebraMap_eq_smul_one]
      | h_add p q hp hq => simp [map_add, tmul_add, hp, hq]
      | h_X p i hp => simp [hp]
    rw [this, P.aeval_val_σ, smul_tmul', smul_eq_mul, mul_one]
  | add x y ex ey =>
    obtain ⟨a, ha⟩ := ex
    obtain ⟨b, hb⟩ := ey
    use (a + b)
    rw [map_add, ha, hb]

end Construction

variable {R' S'} [CommRing R'] [CommRing S'] [Algebra R' S'] (P' : Generators R' S')
variable {R'' S''} [CommRing R''] [CommRing S''] [Algebra R'' S''] (P'' : Generators R'' S'')

section Hom

section

variable [Algebra R R'] [Algebra R' R''] [Algebra R' S'']
variable [Algebra S S'] [Algebra S' S''] [Algebra S S'']

/-- Given a commuting square
R --→ P = R[X] ---→ S
|                   |
↓                   ↓
R' -→ P' = R'[X'] → S
A hom between `P` and `P'` is an assignment `I → P'` such that the arrows commute.
Also see `Algebra.Generators.Hom.equivAlgHom`.
-/
@[ext]
structure Hom where
  /-- The assignment of each variable in `I` to a value in `P' = R'[X']`. -/
  val : P.vars → P'.Ring
  aeval_val : ∀ i, aeval P'.val (val i) = algebraMap S S' (P.val i)

attribute [simp] Hom.aeval_val

variable {P P'}

/-- A hom between two families of generators gives
an algebra homomorphism between the polynomial rings. -/
noncomputable
def Hom.toAlgHom (f : Hom P P') : P.Ring →ₐ[R] P'.Ring := MvPolynomial.aeval f.val

variable [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S'] in
@[simp]
lemma Hom.algebraMap_toAlgHom (f : Hom P P') (x) : MvPolynomial.aeval P'.val (f.toAlgHom x) =
    algebraMap S S' (MvPolynomial.aeval P.val x) := by
  suffices ((MvPolynomial.aeval P'.val).restrictScalars R).comp f.toAlgHom =
      (IsScalarTower.toAlgHom R S S').comp (MvPolynomial.aeval P.val) from
    DFunLike.congr_fun this x
  apply MvPolynomial.algHom_ext
  intro i
  simp [Hom.toAlgHom]

@[simp]
lemma Hom.toAlgHom_X (f : Hom P P') (i) : f.toAlgHom (.X i) = f.val i :=
  MvPolynomial.aeval_X f.val i

lemma Hom.toAlgHom_C (f : Hom P P') (r) : f.toAlgHom (.C r) = .C (algebraMap _ _ r) :=
  MvPolynomial.aeval_C f.val r

lemma Hom.toAlgHom_monomial (f : Generators.Hom P P') (v r) :
    f.toAlgHom (monomial v r) = r • v.prod (f.val · ^ ·) := by
  rw [toAlgHom, aeval_monomial, Algebra.smul_def]

variable [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S'] in
/-- Giving a hom between two families of generators is equivalent to
giving an algebra homomorphism between the polynomial rings. -/
@[simps]
noncomputable
def Hom.equivAlgHom :
    Hom P P' ≃ { f : P.Ring →ₐ[R] P'.Ring //
      ∀ x, aeval P'.val (f x) = algebraMap S S' (aeval P.val x) } where
  toFun f := ⟨f.toAlgHom, f.algebraMap_toAlgHom⟩
  invFun f := ⟨fun i ↦ f.1 (.X i), fun i ↦ by simp [f.2]⟩
  left_inv f := by ext; simp
  right_inv f := by ext; simp

variable (P P')

/-- The hom from `P` to `P'` given by the designated section of `P'`. -/
@[simps]
def defaultHom : Hom P P' := ⟨P'.σ ∘ algebraMap S S' ∘ P.val, fun x ↦ by simp⟩

instance : Inhabited (Hom P P') := ⟨defaultHom P P'⟩

/-- The identity hom. -/
@[simps]
protected noncomputable def Hom.id : Hom P P := ⟨X, by simp⟩

@[simp]
lemma Hom.toAlgHom_id : Hom.toAlgHom (.id P) = AlgHom.id _ _ := by ext1; simp

variable {P P' P''}

/-- The composition of two homs. -/
@[simps]
noncomputable def Hom.comp [IsScalarTower R' R'' S''] [IsScalarTower R' S' S'']
    [IsScalarTower S S' S''] (f : Hom P' P'') (g : Hom P P') : Hom P P'' where
  val x := aeval f.val (g.val x)
  aeval_val x := by
    simp only
    rw [IsScalarTower.algebraMap_apply S S' S'', ← g.aeval_val]
    induction g.val x using MvPolynomial.induction_on with
    | h_C r => simp [← IsScalarTower.algebraMap_apply]
    | h_add x y hx hy => simp only [map_add, hx, hy]
    | h_X p i hp => simp only [map_mul, hp, aeval_X, aeval_val]

@[simp]
lemma Hom.comp_id [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S'] (f : Hom P P') :
    f.comp (Hom.id P) = f := by ext; simp

end

@[simp]
lemma Hom.id_comp [Algebra S S'] (f : Hom P P') : (Hom.id P').comp f = f := by
  ext; simp [Hom.id, aeval_X_left]

variable [Algebra R R'] [Algebra R' R''] [Algebra R' S'']
variable [Algebra S S'] [Algebra S' S''] [Algebra S S'']

@[simp]
lemma Hom.toAlgHom_comp_apply
    [Algebra R R''] [IsScalarTower R R' R''] [IsScalarTower R' R'' S'']
    [IsScalarTower R' S' S''] [IsScalarTower S S' S'']
    (f : Hom P P') (g : Hom P' P'') (x) :
    (g.comp f).toAlgHom x = g.toAlgHom (f.toAlgHom x) := by
  induction x using MvPolynomial.induction_on with
  | h_C r => simp only [← MvPolynomial.algebraMap_eq, AlgHom.map_algebraMap]
  | h_add x y hx hy => simp only [map_add, hx, hy]
  | h_X p i hp => simp only [map_mul, hp, toAlgHom_X, comp_val]; rfl

variable {T} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- Given families of generators `X ⊆ T` over `S` and `Y ⊆ S` over `R`,
there is a map of generators `R[Y] → R[X, Y]`. -/
@[simps]
noncomputable
def toComp (Q : Generators S T) (P : Generators R S) : Hom P (Q.comp P) where
  val i := X (.inr i)
  aeval_val i := by simp

/-- Given families of generators `X ⊆ T` over `S` and `Y ⊆ S` over `R`,
there is a map of generators `R[X, Y] → S[X]`. -/
@[simps]
noncomputable
def ofComp (Q : Generators S T) (P : Generators R S) : Hom (Q.comp P) Q where
  val i := i.elim X (C ∘ P.val)
  aeval_val i := by cases i <;> simp

/-- Given families of generators `X ⊆ T`, there is a map `R[X] → S[X]`. -/
@[simps]
noncomputable
def toExtendScalars (P : Generators R T) : Hom P (P.extendScalars S) where
  val := X
  aeval_val i := by simp

variable {P P'} in
/-- Reinterpret a hom between generators as a hom between extensions. -/
@[simps]
noncomputable
def Hom.toExtensionHom [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S']
    (f : P.Hom P') : P.toExtension.Hom P'.toExtension where
  toRingHom := f.toAlgHom.toRingHom
  toRingHom_algebraMap x := by simp
  algebraMap_toRingHom x := by simp

@[simp]
lemma Hom.toExtensionHom_id : Hom.toExtensionHom (.id P) = .id _ := by ext; simp

@[simp]
lemma Hom.toExtensionHom_comp [Algebra R S'] [IsScalarTower R S S']
    [Algebra R R''] [Algebra R S''] [IsScalarTower R R'' S'']
    [IsScalarTower R S S''] [IsScalarTower R' R'' S''] [IsScalarTower R' S' S'']
    [IsScalarTower S S' S''] [IsScalarTower R R' R''] [IsScalarTower R R' S']
    (f : P'.Hom P'') (g : P.Hom P') :
    toExtensionHom (f.comp g) = f.toExtensionHom.comp g.toExtensionHom := by ext; simp

end Hom

/-- The kernel of a presentation. -/
noncomputable abbrev ker : Ideal P.Ring := P.toExtension.ker

lemma ker_eq_ker_aeval_val : P.ker = RingHom.ker (aeval P.val) :=
  rfl

end Algebra.Generators
