/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.Ideal.Cotangent

/-!

# Generators of algebras

## Main definition
- `Algebra.Generators`: A family of generators of a `R`-algebra `S` consists of
  1. `vars`: The type of variables.
  2. `val : vars → S`: The assignment of each variable to a value.
  3. `σ`: A section of `R[X] → S`.
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

## TODO
* Define `Algebra.Presentation` that extends `Generators` and contains the data of a family of
  relations that spans the kernel of the presentation.

-/

universe w u v

open TensorProduct MvPolynomial

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/-- A family of generators of a `R`-algebra `S` consists of
1. `vars`: The type of variables.
2. `val : vars → S`: The assignment of each variable to a value in `S`.
3. `σ`: A section of `R[X] → S`. -/
structure Algebra.Generators where
  /-- The type of variables.  -/
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
@[simps vars val]
noncomputable
def ofSurjective {vars} (val : vars → S) (h : Function.Surjective (aeval (R := R) val)) :
    Generators R S where
  vars := vars
  val := val
  σ' x := (h x).choose
  aeval_val_σ' x := (h x).choose_spec

/-- Construct `Generators` from an assignment `I → S` such that `R[X] → S` is surjective. -/
noncomputable
def ofAlgHom {I} (f : MvPolynomial I R →ₐ[R] S) (h : Function.Surjective f) :
    Generators R S :=
  ofSurjective (f ∘ X) (by rwa [show aeval (f ∘ X) = f by ext; simp])

/-- Construct `Generators` from a family of generators of `S`. -/
noncomputable
def ofSet {s : Set S} (hs : Algebra.adjoin R s = ⊤) : Generators R S := by
  refine ofSurjective (Subtype.val : s → S) ?_
  rwa [← Algebra.range_top_iff_surjective, ← Algebra.adjoin_range_eq_range_aeval,
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

variable {T} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- Given two families of generators `S[X] → T` and `R[Y] → S`,
we may constuct the family of generators `R[X, Y] → T`. -/
@[simps vars val, simps (config := .lemmasOnly) σ]
noncomputable
def comp (Q : Generators S T) (P : Generators R S) : Generators R T where
  vars := Q.vars ⊕ P.vars
  val := Sum.elim Q.val (algebraMap S T ∘ P.val)
  σ' x := (Q.σ x).sum (fun n r ↦ rename Sum.inr (P.σ r) * monomial (n.mapDomain Sum.inl) 1)
  aeval_val_σ' s := by
    have (x : P.Ring) : aeval (algebraMap S T ∘ P.val) x = algebraMap S T (aeval P.val x) := by
      rw [map_aeval, aeval_def, coe_eval₂Hom, ← IsScalarTower.algebraMap_eq, Function.comp]
    conv_rhs => rw [← Q.aeval_val_σ s, ← (Q.σ s).sum_single]
    simp only [map_finsupp_sum, _root_.map_mul, aeval_rename, Sum.elim_comp_inr, this, aeval_val_σ,
      aeval_monomial, _root_.map_one, Finsupp.prod_mapDomain_index_inj Sum.inl_injective,
      Sum.elim_inl, one_mul, single_eq_monomial]

variable (S) in
/-- If `R → S → T` is a tower of algebras, a family of generators `R[X] → T`
gives a family of generators `S[X] → T`. -/
@[simps vars val]
noncomputable
def extendScalars (P : Generators R T) : Generators S T where
  vars := P.vars
  val := P.val
  σ' x := map (algebraMap R S) (P.σ x)
  aeval_val_σ' s := by simp [@aeval_def S, ← IsScalarTower.algebraMap_eq, ← @aeval_def R]

end Construction

variable {R' S'} [CommRing R'] [CommRing S'] [Algebra R' S'] (P' : Generators R' S')
variable [Algebra R R'] [Algebra S S'] [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S']

variable {R'' S''} [CommRing R''] [CommRing S''] [Algebra R'' S''] (P'' : Generators R'' S'')
variable [Algebra R R''] [Algebra S S''] [Algebra R S'']
  [IsScalarTower R R'' S''] [IsScalarTower R S S'']
variable [Algebra R' R''] [Algebra S' S''] [Algebra R' S'']
  [IsScalarTower R' R'' S''] [IsScalarTower R' S' S'']
variable [IsScalarTower R' R'' R''] [IsScalarTower S S' S'']

section Hom

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

@[simp]
lemma Hom.toAlgHom_C (f : Hom P P') (r) : f.toAlgHom (.C r) = .C (algebraMap _ _ r) :=
  MvPolynomial.aeval_C f.val r

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

variable {P P' P''}

/-- The composition of two homs. -/
@[simps]
noncomputable def Hom.comp (f : Hom P' P'') (g : Hom P P') : Hom P P'' where
  val x := aeval f.val (g.val x)
  aeval_val x := by
    simp only
    rw [IsScalarTower.algebraMap_apply S S' S'', ← g.aeval_val]
    induction g.val x using MvPolynomial.induction_on with
    | h_C r => simp [← IsScalarTower.algebraMap_apply]
    | h_add x y hx hy => simp only [map_add, hx, hy]
    | h_X p i hp => simp only [_root_.map_mul, hp, aeval_X, aeval_val]

@[simp]
lemma Hom.comp_id (f : Hom P P') : f.comp (Hom.id P) = f := by ext; simp

@[simp]
lemma Hom.id_comp (f : Hom P P') : (Hom.id P').comp f = f := by ext; simp [Hom.id, aeval_X_left]

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

end Hom

section Cotangent

/-- The kernel of a presentation. -/
abbrev ker : Ideal P.Ring := RingHom.ker (algebraMap P.Ring S)

/-- The cotangent space of a presentation.
This is a type synonym so that `P = R[X]` can act on it through the action of `S` without creating
a diamond. -/
def Cotangent : Type _ := P.ker.Cotangent

noncomputable
instance : AddCommGroup P.Cotangent := inferInstanceAs (AddCommGroup P.ker.Cotangent)

variable {P}

/-- The identity map `P.ker.Cotangent → P.Cotangent` into the type synonym.  -/
def Cotangent.of (x : P.ker.Cotangent) : P.Cotangent := x

/-- The identity map `P.Cotangent → P.ker.Cotangent` from the type synonym.  -/
def Cotangent.val (x : P.Cotangent) : P.ker.Cotangent := x

@[ext]
lemma Cotangent.ext {x y : P.Cotangent} (e : x.val = y.val) : x = y := e

namespace Cotangent

variable (x y : P.Cotangent) (w z : P.ker.Cotangent)

@[simp] lemma val_add : (x + y).val = x.val + y.val := rfl
@[simp] lemma val_zero : (0 : P.Cotangent).val = 0 := rfl
@[simp] lemma of_add : of (w + z) = of w + of z := rfl
@[simp] lemma of_zero : (of 0 : P.Cotangent) = 0 := rfl
@[simp] lemma of_val : of x.val = x := rfl
@[simp] lemma val_of : (of w).val = w := rfl

end Cotangent

lemma Cotangent.smul_eq_zero_of_mem (p : P.Ring) (hp : p ∈ P.ker) (m : P.ker.Cotangent) :
    p • m = 0 := by
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ m
  rw [← map_smul, Ideal.toCotangent_eq_zero, Submodule.coe_smul, smul_eq_mul, pow_two]
  exact Ideal.mul_mem_mul hp x.2

attribute [local simp] RingHom.mem_ker

noncomputable
instance Cotangent.module : Module S P.Cotangent where
  smul := fun r s ↦ .of (P.σ r • s.val)
  smul_zero := fun r ↦ ext (smul_zero (P.σ r))
  smul_add := fun r x y ↦ ext (smul_add (P.σ r) x.val y.val)
  add_smul := fun r s x ↦ by
    have := smul_eq_zero_of_mem (P.σ (r + s) - (P.σ r + P.σ s) : P.Ring) (by simp ) x
    simp only [sub_smul, add_smul, sub_eq_zero] at this
    exact this
  zero_smul := fun x ↦ smul_eq_zero_of_mem (P.σ 0 : P.Ring) (by simp) x
  one_smul := fun x ↦ by
    have := smul_eq_zero_of_mem (P.σ 1 - 1 : P.Ring) (by simp) x
    simp [sub_eq_zero, sub_smul] at this
    exact this
  mul_smul := fun r s x ↦ by
    have := smul_eq_zero_of_mem (P.σ (r * s) - (P.σ r * P.σ s) : P.Ring) (by simp) x
    simpa only [sub_smul, mul_smul, sub_eq_zero] using this

noncomputable
instance Cotangent.module' {R₀} [CommRing R₀] [Algebra R₀ S] : Module R₀ P.Cotangent :=
  Module.compHom P.Cotangent (algebraMap R₀ S)

instance {R₁ R₂} [CommRing R₁] [CommRing R₂] [Algebra R₁ S] [Algebra R₂ S] [Algebra R₁ R₂]
    [IsScalarTower R₁ R₂ S] :
  IsScalarTower R₁ R₂ P.Cotangent := by
  constructor
  intros r s m
  show algebraMap R₂ S (r • s) • m = (algebraMap _ S r) • (algebraMap _ S s) • m
  rw [Algebra.smul_def, _root_.map_mul, mul_smul, ← IsScalarTower.algebraMap_apply]

lemma Cotangent.val_smul''' {R₀} [CommRing R₀] [Algebra R₀ S] (r : R₀) (x : P.Cotangent) :
    (r • x).val = P.σ (algebraMap R₀ S r) • x.val := rfl

@[simp]
lemma Cotangent.val_smul (r : S) (x : P.Cotangent) : (r • x).val = P.σ r • x.val := rfl

@[simp]
lemma Cotangent.val_smul' (r : P.Ring) (x : P.Cotangent) : (r • x).val = r • x.val := by
  rw [val_smul''', ← sub_eq_zero, ← sub_smul]
  exact Cotangent.smul_eq_zero_of_mem _ (by simp) _

@[simp]
lemma Cotangent.val_smul'' (r : R) (x : P.Cotangent) : (r • x).val = r • x.val := by
  rw [← algebraMap_smul P.Ring, val_smul', algebraMap_smul]

/-- The quotient map from the kernel of `P = R[X] → S` onto the cotangent space. -/
def Cotangent.mk : P.ker →ₗ[P.Ring] P.Cotangent where
  toFun x := .of (Ideal.toCotangent _ x)
  map_add' x y := by simp
  map_smul' x y := ext <| by simp

@[simp]
lemma Cotangent.val_mk (x : P.ker) : (mk x).val = Ideal.toCotangent _ x := rfl

lemma Cotangent.mk_surjective : Function.Surjective (mk (P := P)) :=
  fun x ↦ Ideal.toCotangent_surjective P.ker x.val

variable {P'}

/-- A hom between families of generators induce a map between cotangent spaces. -/
noncomputable
def Cotangent.map (f : Hom P P') : P.Cotangent →ₗ[S] P'.Cotangent where
  toFun x := .of (Ideal.mapCotangent (R := R) _ _ f.toAlgHom
    (fun x hx ↦ by simpa using RingHom.congr_arg (algebraMap S S') hx) x.val)
  map_add' x y := ext (map_add _ x.val y.val)
  map_smul' r x := by
    ext
    obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
    obtain ⟨r, rfl⟩ := P.algebraMap_surjective r
    simp only [algebraMap_smul, val_smul', val_mk, val_of, Ideal.mapCotangent_toCotangent,
      RingHomCompTriple.comp_apply, ← (Ideal.toCotangent _).map_smul]
    conv_rhs => rw [algebraMap_apply, ← algebraMap_smul S', ← f.algebraMap_toAlgHom,
      ← algebraMap_apply, algebraMap_smul, val_smul', val_of, ← (Ideal.toCotangent _).map_smul]
    congr 1
    ext1
    simp only [SetLike.val_smul, smul_eq_mul, _root_.map_mul]

@[simp]
lemma Cotangent.map_mk (f : Hom P P') (x) :
    Cotangent.map f (.mk x) =
      .mk ⟨f.toAlgHom x, by simpa [-map_aeval] using RingHom.congr_arg (algebraMap S S') x.2⟩ :=
  rfl

end Cotangent

end Algebra.Generators
