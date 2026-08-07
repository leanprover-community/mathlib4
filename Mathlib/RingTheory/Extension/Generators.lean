/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.MvPolynomial.Tower
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.Extension.Basic

/-!

# Generators of algebras

## Main definition

- `Algebra.Generators`: A family of generators of an `R`-algebra `S` consists of
  1. `ι`: The type of variables.
  2. `val : ι → S`: The assignment of each variable to a value.
  3. `σ`: A set-theoretic section of the induced `R`-algebra homomorphism `R[X] → S`, where we
     write `R[X]` for `R[ι]`.

- `Algebra.Generators.Hom`: Given a commuting square
  ```
  R --→ P = R[X] ---→ S
  |                   |
  ↓                   ↓
  R' -→ P' = R'[X'] → S
  ```
  A hom between `P` and `P'` is an assignment `X → P'` such that the arrows commute.

- `Algebra.Generators.Cotangent`: The cotangent space w.r.t. `P = R[X] → S`, i.e. the
  space `I/I²` with `I` being the kernel of the presentation.

- `Algebra.Generators.mvPolynomial`: The canonical `R`-generators of the polynomial algebra
  `MvPolynomial ι R`, indexed by `ι` via the variables `X`.

## TODOs

Currently, Lean does not see through the `ι` field of terms of `Generators R S` obtained
from constructions, e.g. composition. This causes fragile and cumbersome proofs, because
`simp` and `rw` often don't work properly. `Generators R S` (and `Presentation R S`, etc.) should
be refactored in a way that makes these equalities reducibly def-eq, for example
by unbundling the `ι` field or making the field globally reducible in constructions using
unification hints.

-/

@[expose] public section

universe w u v

open TensorProduct MvPolynomial

variable (R : Type u) (S : Type v) (ι : Type w) [CommRing R] [CommRing S] [Algebra R S]

/-- A family of generators of an `R`-algebra `S` consists of
1. `ι`: The type of variables.
2. `val : ι → S`: The assignment of each variable to a value in `S`.
3. `σ`: A section of `R[X] → S`. -/
structure Algebra.Generators where
  /-- The assignment of each variable to a value in `S`. -/
  val : ι → S
  /-- A section of `R[X] → S`. -/
  σ' : S → MvPolynomial ι R
  aeval_val_σ' : ∀ s, aeval val (σ' s) = s
  /-- An `R[X]`-algebra instance on `S`. The default is the one induced by the map `R[X] → S`,
  but this causes a diamond if there is an existing instance. -/
  algebra : Algebra (MvPolynomial ι R) S := (aeval val).toAlgebra
  algebraMap_eq :
    algebraMap (MvPolynomial ι R) S = aeval (R := R) val := by rfl

namespace Algebra.Generators

variable {R S ι}
variable (P : Generators R S ι)

set_option linter.unusedVariables false in
/-- The polynomial ring w.r.t. a family of generators. -/
@[nolint unusedArguments]
protected
abbrev Ring (P : Generators R S ι) : Type (max w u) := MvPolynomial ι R

instance : Algebra P.Ring S := P.algebra

/-- The designated section w.r.t. a family of generators. -/
def σ : S → P.Ring := P.σ'

/-- See Note [custom simps projection] -/
def Simps.σ : S → P.Ring := P.σ

initialize_simps_projections Algebra.Generators (σ' → σ)

@[simp]
lemma aeval_val_σ (s) : aeval P.val (P.σ s) = s := P.aeval_val_σ' s

noncomputable instance {R₀} [CommRing R₀] [Algebra R₀ R] [Algebra R₀ S] [IsScalarTower R₀ R S] :
    IsScalarTower R₀ P.Ring S := IsScalarTower.of_algebraMap_eq' <|
  P.algebraMap_eq ▸ ((aeval (R := R) P.val).comp_algebraMap_of_tower R₀).symm

@[simp]
lemma algebraMap_apply (x) : algebraMap P.Ring S x = aeval (R := R) P.val x := by
  simp [algebraMap_eq]

@[simp]
lemma σ_smul (x y) : P.σ x • y = x * y := by
  rw [Algebra.smul_def, algebraMap_apply, aeval_val_σ]

lemma σ_injective : P.σ.Injective := by
  intro x y e
  rw [← P.aeval_val_σ x, ← P.aeval_val_σ y, e]

lemma aeval_val_surjective : Function.Surjective (aeval (R := R) P.val) :=
  fun x ↦ ⟨P.σ x, by simp⟩

lemma algebraMap_surjective : Function.Surjective (algebraMap P.Ring S) :=
  (⟨_, P.algebraMap_apply _ ▸ P.aeval_val_σ ·⟩)

section Construction

/-- Construct `Generators` from an assignment `I → S` such that `R[X] → S` is surjective. -/
@[simps val]
noncomputable
def ofSurjective (val : ι → S) (h : Function.Surjective (aeval (R := R) val)) :
    Generators R S ι where
  val := val
  σ' x := (h x).choose
  aeval_val_σ' x := (h x).choose_spec

/-- If `algebraMap R S` is surjective, the empty type generates `S`. -/
noncomputable def ofSurjectiveAlgebraMap (h : Function.Surjective (algebraMap R S)) :
    Generators R S PEmpty.{w + 1} :=
  ofSurjective PEmpty.elim <| fun s ↦ by
    use C (h s).choose
    simp [(h s).choose_spec]

/-- The canonical generators for `R` as an `R`-algebra. -/
noncomputable def id : Generators R R PEmpty.{w + 1} := ofSurjectiveAlgebraMap <| by
  rw [algebraMap_self]
  exact RingHomSurjective.is_surjective

variable (R ι) in
/-- The canonical `R`-generators of the polynomial algebra `MvPolynomial ι R`,
indexed by `ι` via the variables `X`. -/
@[simps σ, simps -fullyApplied val]
noncomputable def mvPolynomial : Generators R (MvPolynomial ι R) ι where
  val := X
  σ' f := f
  aeval_val_σ' := aeval_X_left_apply

/-- Construct `Generators` from an assignment `I → S` such that `R[X] → S` is surjective. -/
noncomputable
def ofAlgHom {I : Type*} (f : MvPolynomial I R →ₐ[R] S) (h : Function.Surjective f) :
    Generators R S I :=
  ofSurjective (f ∘ X) (by rwa [show aeval (f ∘ X) = f by ext; simp])

/-- Construct `Generators` from a family of generators of `S`. -/
noncomputable
def ofSet {s : Set S} (hs : Algebra.adjoin R s = ⊤) : Generators R S s := by
  refine ofSurjective (Subtype.val : s → S) ?_
  rwa [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval,
    Subtype.range_coe_subtype, Set.ofPred_mem_eq]

variable (R S) in
/-- The `Generators` containing the whole algebra, which induces the canonical map  `R[S] → S`. -/
@[simps]
noncomputable
def self : Generators R S S where
  val := _root_.id
  σ' := X
  aeval_val_σ' := aeval_X _

/-- The extension `R[X₁,...,Xₙ] → S` given a family of generators. -/
@[simps]
noncomputable
def toExtension : Extension R S where
  Ring := P.Ring
  σ := P.σ
  algebraMap_σ := by simp

/-- Transport generators along an algebra isomorphism. -/
noncomputable def ofAlgEquiv
    (P : Generators R S ι) {T : Type*} [CommRing T] [Algebra R T] (e : S ≃ₐ[R] T) :
    Generators R T ι where
  val := e ∘ P.val
  σ' := P.σ ∘ e.symm
  aeval_val_σ' t := by
    rw [Function.comp_def, ← AlgHom.coe_coe e, ← MvPolynomial.comp_aeval_apply]
    simp

@[simp]
lemma ofAlgEquiv_val (P : Generators R S ι) {T : Type*} [CommRing T] [Algebra R T] (e : S ≃ₐ[R] T) :
    (P.ofAlgEquiv e).val = e ∘ P.val :=
  rfl

section Localization

variable (r : R) [IsLocalization.Away r S]

variable (S) in
/-- If `S` is the localization of `R` away from `r`, we obtain a canonical generator mapping
to the inverse of `r`. -/
@[simps val, simps -isSimp σ]
noncomputable
def localizationAway : Generators R S Unit where
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

variable {ι' : Type*} {T} [CommRing T] [Algebra R T]

set_option backward.isDefEq.respectTransparency.types false in
/-- Given two families of generators `S[X] → T` and `R[Y] → S`,
we may construct the family of generators `R[X, Y] → T`. -/
@[simps val, simps -isSimp σ]
noncomputable
def comp [Algebra S T] [IsScalarTower R S T]
    (Q : Generators S T ι') (P : Generators R S ι) : Generators R T (ι' ⊕ ι) where
  val := Sum.elim Q.val (algebraMap S T ∘ P.val)
  σ' x := (AddMonoidAlgebra.coeff <| Q.σ x).sum fun n r ↦
    rename .inr (P.σ r) * monomial (n.mapDomain .inl) 1
  aeval_val_σ' s := by
    have (x : P.Ring) : aeval (algebraMap S T ∘ P.val) x = algebraMap S T (aeval P.val x) := by
      rw [map_aeval, aeval_def, coe_eval₂Hom, ← IsScalarTower.algebraMap_eq, Function.comp_def]
    have hfold (p : MvPolynomial ι' S) :
        (∑ x ∈ support p, (algebraMap S T) (p.coeff x) * x.prod fun a b ↦ Q.val a ^ b) =
          aeval Q.val p :=
      ((aeval_def (f := Q.val) p).trans (eval₂_eq (algebraMap S T) Q.val p)).symm
    conv_rhs => rw [← Q.aeval_val_σ s, (Q.σ s).as_sum]
    simp [aeval_rename, this, aeval_monomial, Finsupp.prod_mapDomain_index_inj Sum.inl_injective,
      Finsupp.sum, MvPolynomial.finsupp_support_eq_support, hfold]

variable (S) in
/-- If `R → S → T` is a tower of algebras, a family of generators `R[X] → T`
gives a family of generators `S[X] → T`. -/
@[simps val]
noncomputable
def extendScalars [Algebra S T] [IsScalarTower R S T] (P : Generators R T ι) :
    Generators S T ι where
  val := P.val
  σ' x := map (algebraMap R S) (P.σ x)
  aeval_val_σ' s := by simp [@aeval_def S, ← IsScalarTower.algebraMap_eq, ← @aeval_def R]

/-- If `P` is a family of generators of `S` over `R` and `T` is an `R`-algebra, we
obtain a natural family of generators of `T ⊗[R] S` over `T`. -/
@[simps! val]
noncomputable
def baseChange (T) [CommRing T] [Algebra R T] (P : Generators R S ι) :
    Generators T (T ⊗[R] S) ι := by
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
      | C a =>
        rw [aeval_C, aeval_C, TensorProduct.algebraMap_apply, algebraMap_eq_smul_one, smul_tmul,
          algebraMap_eq_smul_one]
      | add p q hp hq => simp [map_add, tmul_add, hp, hq]
      | mul_X p i hp => simp [hp]
    rw [this, P.aeval_val_σ, smul_tmul', smul_eq_mul, mul_one]
  | add x y ex ey =>
    obtain ⟨a, ha⟩ := ex
    obtain ⟨b, hb⟩ := ey
    use (a + b)
    rw [map_add, ha, hb]

set_option backward.defeqAttrib.useBackward true in
variable (T) in
set_option backward.isDefEq.respectTransparency false in
/-- The forwards direction of the canonical isomorphism `T ⊗[R] R[Xᵢ] ≃ₐ[T] T[Xᵢ]` as
a map of extensions. -/
noncomputable def baseChangeFromBaseChange :
    (P.toExtension.baseChange (T := T)).Hom (P.baseChange (T := T)).toExtension :=
  .ofAlgHom (MvPolynomial.algebraTensorAlgEquiv R T).toAlgHom <| by
    dsimp [Extension.baseChange]
    ext
    simp [RingHom.algebraMap_toAlgebra]

set_option backward.defeqAttrib.useBackward true in
@[simp]
lemma baseChangeFromBaseChange_apply (x : P.toExtension.baseChange.Ring) :
    dsimp% (P.baseChangeFromBaseChange T).toRingHom x = MvPolynomial.algebraTensorAlgEquiv R T x :=
  rfl

set_option backward.defeqAttrib.useBackward true in
variable (T) in
set_option backward.isDefEq.respectTransparency false in
/-- The backwards direction of the canonical isomorphism `T ⊗[R] R[Xᵢ] ≃ₐ[T] T[Xᵢ]` as
a map of extensions. -/
noncomputable def baseChangeToBaseChange :
    (P.baseChange (T := T)).toExtension.Hom (P.toExtension.baseChange (T := T)) :=
  .ofAlgHom (MvPolynomial.algebraTensorAlgEquiv R T).symm.toAlgHom <| by
    dsimp [Extension.baseChange]
    ext
    simp [RingHom.algebraMap_toAlgebra]

set_option backward.defeqAttrib.useBackward true in
@[simp]
lemma baseChangeToBaseChange_apply (x : (baseChange T P).toExtension.Ring) :
    dsimp% (P.baseChangeToBaseChange T).toRingHom x =
      (MvPolynomial.algebraTensorAlgEquiv R T).symm x :=
  rfl

/-- Extend generators by more variables. -/
noncomputable def extend (P : Generators R S ι) (b : ι' → S) : Generators R S (ι ⊕ ι') :=
  .ofSurjective (Sum.elim P.val b) fun s ↦ by
    use rename Sum.inl (P.σ s)
    simp [aeval_rename]

@[simp]
lemma extend_val_inl (P : Generators R S ι) (b : ι' → S) (i : ι) :
    (P.extend b).val (.inl i) = P.val i := rfl

@[simp]
lemma extend_val_inr (P : Generators R S ι) (b : ι' → S) (i : ι') :
    (P.extend b).val (.inr i) = b i := rfl

/-- Given generators `P` with variable type `ι'` and an equivalence `ι ≃ ι'`, these
are the induced generators indexed by `ι`. -/
noncomputable def reindex (P : Generators R S ι') (e : ι ≃ ι') :
    Generators R S ι where
  val := P.val ∘ e
  σ' := rename e.symm ∘ P.σ
  aeval_val_σ' s := by
    conv_rhs => rw [← P.aeval_val_σ s]
    rw [← MvPolynomial.aeval_rename]
    simp

lemma reindex_val (P : Generators R S ι') (e : ι ≃ ι') :
    (P.reindex e).val = P.val ∘ e :=
  rfl

section

variable {σ : Type*} {I : Ideal (MvPolynomial σ R)}
  (s : MvPolynomial σ R ⧸ I → MvPolynomial σ R)
  (hs : ∀ x, Ideal.Quotient.mk _ (s x) = x)

/--
The naive generators for a quotient `R[Xᵢ] ⧸ I`.
If the definitional equality of the section matters, it can be explicitly provided.
-/
@[simps val]
noncomputable
def naive (s : MvPolynomial σ R ⧸ I → MvPolynomial σ R :=
      Function.surjInv Ideal.Quotient.mk_surjective)
    (hs : ∀ x, Ideal.Quotient.mk _ (s x) = x := by apply Function.surjInv_eq) :
    Generators R (MvPolynomial σ R ⧸ I) σ where
  val i := Ideal.Quotient.mk _ (X i)
  σ' := s
  aeval_val_σ' x := by
    conv_rhs => rw [← hs x, ← Ideal.Quotient.mkₐ_eq_mk R, aeval_unique (Ideal.Quotient.mkₐ _ I)]
    simp [Function.comp_def]
  algebra := inferInstance
  algebraMap_eq := by ext x <;> simp [IsScalarTower.algebraMap_apply R (MvPolynomial σ R)]

@[simp] lemma naive_σ : (Generators.naive s hs).σ = s := rfl

end

lemma finiteType {α : Type*} [Finite α] (P : Generators R S α) : FiniteType R S :=
  .of_surjective (IsScalarTower.toAlgHom R P.Ring S) P.algebraMap_surjective

lemma _root_.Algebra.FiniteType.iff_exists_generators :
    FiniteType R S ↔ ∃ (n : ℕ), Nonempty (Generators R S (Fin n)) := by
  refine ⟨fun h ↦ ?_, fun ⟨n, ⟨P⟩⟩ ↦ P.finiteType⟩
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp h
  exact ⟨n, ⟨.ofSurjective (fun i ↦ f (X i)) <| by rwa [aeval_unique f] at hf⟩⟩

end Construction

variable {R' S' ι' : Type*} [CommRing R'] [CommRing S'] [Algebra R' S'] (P' : Generators R' S' ι')
variable {R'' S'' ι'' : Type*} [CommRing R''] [CommRing S''] [Algebra R'' S'']
  (P'' : Generators R'' S'' ι'')

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
  val : ι → P'.Ring
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

/-- Version of `Hom.algebraMap_toAlgHom` where `S = S'`, sometimes useful for rewriting. -/
lemma Hom.algebraMap_toAlgHom' [Algebra R' S] [IsScalarTower R R' S]
    {P' : Generators R' S ι'} (f : Hom P P') (x : P.Ring) :
    MvPolynomial.aeval P'.val (f.toAlgHom x) = MvPolynomial.aeval P.val x :=
  f.algebraMap_toAlgHom _

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
    rw [IsScalarTower.algebraMap_apply S S' S'', ← g.aeval_val]
    induction g.val x using MvPolynomial.induction_on with
    | C r => simp [← IsScalarTower.algebraMap_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
    | mul_X p i hp => simp only [map_mul, hp, aeval_X, aeval_val]

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
  | C r => simp only [← MvPolynomial.algebraMap_eq, AlgHom.map_algebraMap]
  | add x y hx hy => simp only [map_add, hx, hy]
  | mul_X p i hp => simp only [map_mul, hp, toAlgHom_X, comp_val]; rfl

variable {T : Type*} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- Given families of generators `X ⊆ T` over `S` and `Y ⊆ S` over `R`,
there is a map of generators `R[Y] → R[X, Y]`. -/
@[simps]
noncomputable
def toComp (Q : Generators S T ι') (P : Generators R S ι) : Hom P (Q.comp P) where
  val i := X (.inr i)
  aeval_val i := by simp

lemma toComp_toAlgHom (Q : Generators S T ι') (P : Generators R S ι) :
    (Q.toComp P).toAlgHom = rename Sum.inr := by rw [rename_eq_aeval]; rfl

/-- Given families of generators `X ⊆ T` over `S` and `Y ⊆ S` over `R`,
there is a map of generators `R[X, Y] → S[X]`. -/
@[simps]
noncomputable
def ofComp (Q : Generators S T ι') (P : Generators R S ι) : Hom (Q.comp P) Q where
  val i := i.elim X (C ∘ P.val)
  aeval_val i := by cases i <;> simp

lemma ofComp_toAlgHom_monomial_sumElim (Q : Generators S T ι') (P : Generators R S ι) (v₁ v₂ a) :
    (Q.ofComp P).toAlgHom (monomial (Finsupp.sumElim v₁ v₂) a) =
      monomial v₁ (aeval P.val (monomial v₂ a)) := by
  rw [Hom.toAlgHom_monomial, monomial_eq]
  simp only [ofComp_val, aeval_monomial]
  rw [Finsupp.prod_sumElim]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, ← map_pow, ← map_finsuppProd,
    C_mul, Algebra.smul_def, MvPolynomial.algebraMap_apply, mul_assoc]
  nth_rw 2 [mul_comm]

lemma toComp_toAlgHom_monomial (Q : Generators S T ι') (P : Generators R S ι) (j a) :
    (Q.toComp P).toAlgHom (monomial j a) =
      monomial (Finsupp.sumElim 0 j) a := by
  convert! rename_monomial _ _ _
  · ext f (i₁ | i₂)
    simp [rename_eq_aeval]
    rfl
  · ext f (i₁ | i₂) <;>
      simp [Finsupp.mapDomain_of_notMem_range, Finsupp.mapDomain_apply Sum.inr_injective]

@[simp]
lemma toAlgHom_ofComp_rename (Q : Generators S T ι') (P : Generators R S ι) (p : P.Ring) :
    (Q.ofComp P).toAlgHom ((rename Sum.inr) p) = C (algebraMap _ _ p) :=
  have : (Q.ofComp P).toAlgHom.comp (rename Sum.inr) =
    (IsScalarTower.toAlgHom R S Q.Ring).comp (IsScalarTower.toAlgHom R P.Ring S) := by ext; simp
  DFunLike.congr_fun this p

set_option backward.isDefEq.respectTransparency.types false in
lemma toAlgHom_ofComp_surjective (Q : Generators S T ι') (P : Generators R S ι) :
    Function.Surjective (Q.ofComp P).toAlgHom := by
  intro p
  induction p using MvPolynomial.induction_on with
  | C a =>
      use MvPolynomial.rename Sum.inr (P.σ a)
      simp only [Hom.toAlgHom, ofComp, Generators.comp, MvPolynomial.aeval_rename,
        Sum.elim_comp_inr]
      simp_rw [Function.comp_def, ← MvPolynomial.algebraMap_eq, ← IsScalarTower.toAlgHom_apply R,
        ← MvPolynomial.comp_aeval]
      simp
  | add p q hp hq =>
      obtain ⟨p, rfl⟩ := hp
      obtain ⟨q, rfl⟩ := hq
      use p + q
      simp
  | mul_X p i hp =>
      obtain ⟨(p : MvPolynomial (ι' ⊕ ι) R), rfl⟩ := hp
      use p * MvPolynomial.X (R := R) (Sum.inl i)
      simp [Algebra.Generators.ofComp, Algebra.Generators.Hom.toAlgHom]

/-- Given families of generators `X ⊆ T`, there is a map `R[X] → S[X]`. -/
@[simps]
noncomputable
def toExtendScalars (P : Generators R T ι) : Hom P (P.extendScalars S) where
  val := X
  aeval_val i := by simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {P P'} in
/-- Reinterpret a hom between generators as a hom between extensions. -/
@[simps]
noncomputable
def Hom.toExtensionHom [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S']
    (f : P.Hom P') : P.toExtension.Hom P'.toExtension where
  toRingHom := f.toAlgHom.toRingHom
  toRingHom_algebraMap x := by simp
  algebraMap_toRingHom x := by simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma Hom.toExtensionHom_id : Hom.toExtensionHom (.id P) = .id _ := by ext; simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma Hom.toExtensionHom_comp [Algebra R S'] [IsScalarTower R S S']
    [Algebra R R''] [Algebra R S''] [IsScalarTower R R'' S'']
    [IsScalarTower R S S''] [IsScalarTower R' R'' S''] [IsScalarTower R' S' S'']
    [IsScalarTower S S' S''] [IsScalarTower R R' R''] [IsScalarTower R R' S']
    (f : P'.Hom P'') (g : P.Hom P') :
    toExtensionHom (f.comp g) = f.toExtensionHom.comp g.toExtensionHom := by ext; simp

lemma Hom.toExtensionHom_toAlgHom_apply [Algebra R S'] [IsScalarTower R R' S']
    [IsScalarTower R S S'] (f : P.Hom P') (x) :
    f.toExtensionHom.toAlgHom x = f.toAlgHom x := rfl

/-- The kernel of a presentation. -/
noncomputable abbrev ker : Ideal P.Ring := P.toExtension.ker

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma ker_eq_ker_aeval_val : P.ker = RingHom.ker (aeval P.val) := by
  simp only [ker, Extension.ker, toExtension_Ring, algebraMap_eq]
  rfl

lemma ker_mvPolynomial : (mvPolynomial R ι).ker = ⊥ := by
  simp [ker_eq_ker_aeval_val, SetLike.ext_iff, aeval_X_left]

variable {P} in
lemma aeval_val_eq_zero {x} (hx : x ∈ P.ker) : aeval P.val x = 0 := by rwa [← algebraMap_apply]

lemma ker_naive {σ : Type*} {I : Ideal (MvPolynomial σ R)}
    (s : MvPolynomial σ R ⧸ I → MvPolynomial σ R) (hs : ∀ x, Ideal.Quotient.mk _ (s x) = x) :
    (Generators.naive s hs).ker = I :=
  I.mk_ker

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma ker_ofAlgHom {I : Type*} (f : MvPolynomial I R →ₐ[R] S) (h : Function.Surjective ⇑f) :
    (ofAlgHom f h).ker = RingHom.ker f.toRingHom := by
  change RingHom.ker _ = _
  congr
  exact MvPolynomial.ringHom_ext (by simp) (by simp [ofAlgHom])

@[simp]
lemma ker_ofAlgEquiv (P : Generators R S ι) {T : Type*} [CommRing T] [Algebra R T] (e : S ≃ₐ[R] T) :
    (P.ofAlgEquiv e).ker = P.ker := by
  rw [ker_eq_ker_aeval_val, ofAlgEquiv_val, Function.comp_def, ← AlgHom.coe_coe,
    ← MvPolynomial.comp_aeval, ← AlgHom.comap_ker, ← RingHom.ker_coe_toRingHom,
    AlgHomClass.toRingHom_toAlgHom, AlgHom.ker_coe_equiv, ← RingHom.ker_eq_comap_bot,
    ← ker_eq_ker_aeval_val]

set_option backward.isDefEq.respectTransparency.types false in
lemma map_toComp_ker (Q : Generators S T ι') (P : Generators R S ι) :
    P.ker.map (Q.toComp P).toAlgHom = RingHom.ker (Q.ofComp P).toAlgHom := by
  let : DecidableEq (ι' →₀ ℕ) := Classical.decEq _
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    rintro x (hx : algebraMap P.Ring S x = 0)
    have : (Q.ofComp P).toAlgHom.comp (Q.toComp P).toAlgHom = IsScalarTower.toAlgHom R _ _ := by
      ext1; simp
    simp only [Ideal.mem_comap,
      RingHom.mem_ker, ← AlgHom.comp_apply, this, IsScalarTower.toAlgHom_apply]
    rw [IsScalarTower.algebraMap_apply P.Ring S, hx, map_zero]
  · rintro x (h₂ : (Q.ofComp P).toAlgHom x = 0)
    let e : (ι' ⊕ ι →₀ ℕ) ≃+ (ι' →₀ ℕ) × (ι →₀ ℕ) :=
      Finsupp.sumFinsuppAddEquivProdFinsupp
    suffices ∑ v ∈ (support x).map e, (monomial (e.symm v)) (x.coeff (e.symm v)) ∈
        Ideal.map (Q.toComp P).toAlgHom.toRingHom P.ker by
      simpa only [AlgHom.toRingHom_eq_coe, Finset.sum_map, Equiv.coe_toEmbedding,
        EquivLike.coe_coe, AddEquiv.symm_apply_apply, support_sum_monomial_coeff] using! this
    rw [← Finset.sum_fiberwise_of_maps_to (fun i ↦ Finset.mem_image_of_mem Prod.fst)]
    refine sum_mem fun i hi ↦ ?_
    convert_to monomial (e.symm (i, 0)) 1 * (Q.toComp P).toAlgHom.toRingHom
      (∑ j ∈ (support x).map e.toEmbedding with j.1 = i, monomial j.2 (x.coeff (e.symm j))) ∈ _
    · rw [map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj ↦ ?_
      obtain rfl := (Finset.mem_filter.mp hj).2
      obtain ⟨i, j⟩ := j
      clear hj hi
      have : (Q.toComp P).toAlgHom (monomial j (x.coeff (e.symm (i, j)))) =
          monomial (e.symm (0, j)) (x.coeff (e.symm (i, j))) :=
        toComp_toAlgHom_monomial ..
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          this]
      rw [monomial_mul, ← map_add, Prod.mk_add_mk, add_zero, zero_add, one_mul]
    · apply Ideal.mul_mem_left
      refine Ideal.mem_map_of_mem _ ?_
      simp only [ker_eq_ker_aeval_val, AddEquiv.toEquiv_eq_coe, RingHom.mem_ker, map_sum]
      rw [show (0 : S) = ((Q.ofComp P).toAlgHom x).coeff i by rw [h₂]; simp]
      clear h₂ hi
      have (x : (Q.comp P).Ring) : (Function.support fun a ↦ if a.1 = i then aeval P.val
          (monomial a.2 (x.coeff (e.symm a))) else 0) ⊆ SetLike.coe ((support x).map e) := by
        rw [← Set.compl_subset_compl]
        intro j
        obtain ⟨j, rfl⟩ := e.surjective j
        simp_all
      rw [Finset.sum_filter, ← finsum_eq_sum_of_support_subset _ (this x)]
      induction x using MvPolynomial.induction_on' with
      | monomial v a =>
        rw [finsum_eq_sum_of_support_subset _ (this _), ← Finset.sum_filter]
        obtain ⟨v, rfl⟩ := e.symm.surjective v
        -- Rewrite `e` in the right-hand side only.
        conv_rhs => simp only [e, Finsupp.sumFinsuppAddEquivProdFinsupp,
          Finsupp.sumFinsuppEquivProdFinsupp, AddEquiv.symm_mk, AddEquiv.coe_mk,
          Equiv.coe_fn_symm_mk, ofComp_toAlgHom_monomial_sumElim]
        classical
        simp only [coeff_monomial, ← e.injective.eq_iff,
          map_zero, AddEquiv.apply_symm_apply, apply_ite]
        rw [← apply_ite, Finset.sum_ite_eq]
        simp only [Finset.mem_filter, Finset.mem_map_equiv, AddEquiv.coe_toEquiv_symm,
          mem_support_iff, coeff_monomial, ↓reduceIte, ne_eq, ite_and, ite_not]
        split
        · simp only [*, map_zero, ite_self]
        · congr
      | add p q hp hq =>
        simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, map_add, ite_add_zero]
        rw [finsum_add_distrib, hp, hq]
        · refine (((support p).map e).finite_toSet.subset ?_)
          convert! this p
        · refine (((support q).map e).finite_toSet.subset ?_)
          convert! this q

/--
Given `R[X] → S` and `S[Y] → T`, this is the lift of an element in `ker(S[Y] → T)`
to `ker(R[X][Y] → S[Y] → T)` constructed from `P.σ`.
-/
noncomputable
def kerCompPreimage (Q : Generators S T ι') (P : Generators R S ι) (x : Q.ker) :
    (Q.comp P).ker := by
  refine ⟨(AddMonoidAlgebra.coeff x.1).sum fun n r ↦ ?_, ?_⟩
  · -- The use of `refine` is intentional to control the elaboration order
    -- so that the term has type `(Q.comp P).Ring` and not `MvPolynomial (Q.ι ⊕ P.ι) R`
    refine rename ?_ (P.σ r) * monomial ?_ 1
    exacts [Sum.inr, n.mapDomain Sum.inl]
  · simp only [ker_eq_ker_aeval_val, RingHom.mem_ker]
    conv_rhs => rw [← aeval_val_eq_zero x.2, ← x.1.support_sum_monomial_coeff]
    simp only [Finsupp.sum, map_sum, map_mul, aeval_rename, Function.comp_def, comp_val,
      Sum.elim_inr, aeval_monomial, map_one, Finsupp.prod_mapDomain_index_inj Sum.inl_injective,
      Sum.elim_inl, one_mul]
    congr! with v i
    simp_rw [← IsScalarTower.toAlgHom_apply R, ← comp_aeval, AlgHom.comp_apply, P.aeval_val_σ]

set_option backward.isDefEq.respectTransparency.types false in
lemma ofComp_kerCompPreimage (Q : Generators S T ι') (P : Generators R S ι) (x : Q.ker) :
    (Q.ofComp P).toAlgHom (kerCompPreimage Q P x) = x := by
  conv_rhs => rw [← x.1.support_sum_monomial_coeff]
  rw [kerCompPreimage, map_finsuppSum, Finsupp.sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [map_mul, Hom.toAlgHom_monomial]
  rw [one_smul, Finsupp.prod_mapDomain_index_inj Sum.inl_injective]
  rw [rename_eq_aeval, ← AlgHom.comp_apply, comp_aeval]
  simp only [ofComp_val, Sum.elim_inr, Function.comp_apply,
    Sum.elim_inl, monomial_eq, Hom.toAlgHom_X]
  congr 1
  rw [aeval_def, IsScalarTower.algebraMap_eq R S, ← MvPolynomial.algebraMap_eq,
    ← coe_eval₂Hom, ← map_aeval, P.aeval_val_σ]

lemma map_ofComp_ker (Q : Generators S T ι') (P : Generators R S ι) :
    Ideal.map (Q.ofComp P).toAlgHom (Q.comp P).ker = Q.ker := by
  ext x
  rw [Ideal.mem_map_iff_of_surjective _ (toAlgHom_ofComp_surjective Q P)]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [ker_eq_ker_aeval_val,
      RingHom.mem_ker] at hx ⊢
    rw [← hx, Hom.algebraMap_toAlgHom, algebraMap_self_apply]
  · intro hx
    exact ⟨_, (kerCompPreimage Q P ⟨x, hx⟩).2, ofComp_kerCompPreimage Q P ⟨x, hx⟩⟩

lemma ker_comp_eq_sup (Q : Generators S T ι') (P : Generators R S ι) :
    (Q.comp P).ker =
      Ideal.map (Q.toComp P).toAlgHom P.ker ⊔ Ideal.comap (Q.ofComp P).toAlgHom Q.ker := by
  rw [← map_ofComp_ker Q P,
    Ideal.comap_map_of_surjective _ (toAlgHom_ofComp_surjective Q P)]
  rw [← sup_assoc, Algebra.Generators.map_toComp_ker, ← RingHom.ker_eq_comap_bot]
  apply le_antisymm (le_trans le_sup_right le_sup_left)
  simp only [le_sup_left, sup_of_le_left, sup_le_iff, le_refl, and_true]
  intro x hx
  simp only [RingHom.mem_ker] at hx
  rw [Generators.ker_eq_ker_aeval_val, RingHom.mem_ker,
    ← algebraMap_self_apply (MvPolynomial.aeval _ x)]
  rw [← Generators.Hom.algebraMap_toAlgHom (Q.ofComp P), hx, map_zero]

lemma toAlgHom_ofComp_localizationAway (g : S) [IsLocalization.Away g T] :
    ((localizationAway T g).ofComp P).toAlgHom
      (rename Sum.inr (P.σ g) * X (Sum.inl ()) - 1) = C g * X () - 1 := by
  simp [Generators.Hom.toAlgHom, Generators.ofComp, aeval_rename]

end Hom

end Algebra.Generators

namespace Algebra.Extension

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical homomorphism of extensions from the universal extension `R[S] → S`
(given by `Generators.self R S`) to any extension `P` defined via the designated section `P.σ`. -/
@[simps!]
noncomputable
def defaultHom (P : Extension.{w} R S) : (Generators.self R S).toExtension.Hom P :=
  .ofAlgHom (MvPolynomial.aeval P.σ) (by dsimp; ext; simp)

end Algebra.Extension
