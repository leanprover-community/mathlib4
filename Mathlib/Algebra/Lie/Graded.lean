/-
Copyright (c) 2026 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.Lie.Derivation.Basic

/-!
# Internally-graded Lie algebras

This file defines the typeclass `GradedLieAlgebra ℒ`, for working with an Lie algebra `L` that is
internally graded by a collection of submodules `ℒ : ι → Submodule R L`.
See the docstring of that typeclass for more information.

## Main definitions

* `GradedLieRing ℒ`: the typeclass, which is a combination of `SetLike.GradedBracket`, and
  `DirectSum.Decomposition ℒ`.
* `GradedLieAlgebra ℒ`: A convenience alias for `GradedLieRing` when `ℒ` is a family of submodules.
* `DirectSum.decomposeLieAlgEquiv ℒ : L ≃⁅R⁆ ⨁ i, ℒ i`, a more bundled version of
  `DirectSum.decompose ℒ`.
* `GradedLieAlgebra.proj ℒ i` is the linear map from `L` to its degree `i : ι` component, such that
  `proj ℒ i x = decompose ℒ x i`.

## Tags

graded Lie algebra, decomposition
-/

@[expose] public section


open DirectSum

variable {ι R L σ : Type*}

section GradedLieRing

variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [SetLike σ L] [AddSubmonoidClass σ L] (ℒ : ι → σ)

open DirectSum

variable (A : ι → Type*)
/-- A graded version of `Bracket`. Grades are combined additively, like
`AddMonoidAlgebra`. -/
class GBracket [Add ι] where
  /-- The homogeneous multiplication map `bracket`. We do not use `A i → A j → A (i + j)` because
    the `leibniz_lie` rule for graded Lie algebras would then require a cast. -/
  bracket {i j k} (h : i + j = k) : A i → A j → A k

namespace DirectSum

/-- A graded version of `LieRing`. -/
class GLieRing [AddCommMonoid ι] [∀ i, AddCommGroup (A i)] extends GBracket A where
  /-- A Lie ring bracket is additive in its first component. -/
  protected add_lie : ∀ {i j k} (h : i + j = k) (x y : A i) (z : A j),
    bracket h (x + y) z = bracket h x z + bracket h y z
  /-- A Lie ring bracket is additive in its second component. -/
  protected lie_add : ∀ {i j k} (h : i + j = k) (x : A i) (y z : A j),
    bracket h x (y + z) = bracket h x y + bracket h x z
  /-- A Lie ring bracket vanishes on the diagonal in L × L. -/
  protected lie_self : ∀ {i j} (h : i + i = j) (x : A i), bracket h x x = 0
  protected lie_antisymm : ∀ {i j k} (hij : i + j = k) (hji : j + i = k) (x : A i) (y : A j),
    bracket hij x y + bracket hji y x = 0
  /-- A Lie ring bracket satisfies a Leibniz / Jacobi identity. -/
  protected leibniz_lie : ∀ {i j k ij ik jk ijk} (hij : i + j = ij) (hik : i + k = ik)
      (hjk : j + k = jk) (hi : i + jk = ijk) (hk : ij + k = ijk) (hj : j + ik = ijk) (x : A i)
      (y : A j) (z : A k),
    bracket hi x (bracket hjk y z) = bracket hk (bracket hij x y) z + bracket hj y (bracket hik x z)

/-- The piecewise multiplication from the `Mul` instance, as a bundled homomorphism. -/
@[simps]
def gBracketHom [AddCommMonoid ι] [∀ i, AddCommGroup (A i)] [GLieRing A] {i j k} (h : i + j = k) :
    A i →+ A j →+ A k where
  toFun a :=
    { toFun := fun b => GBracket.bracket h a b
      map_zero' := by
        have : GBracket.bracket h a (0 : A j) = GBracket.bracket h a 0 := rfl
        nth_rw 1 [← add_zero 0] at this
        rwa [GLieRing.lie_add, add_eq_left] at this
      map_add' x y := by rw [GLieRing.lie_add] }
  map_zero' := by
    ext b
    have : GBracket.bracket h (0 : A i) b = GBracket.bracket h 0 b := rfl
    nth_rw 1 [← add_zero 0] at this
    rwa [GLieRing.add_lie, add_eq_left] at this
  map_add' _ _ := by
    ext b
    simp [GLieRing.add_lie]

/-- The multiplication from the `Mul` instance, as a bundled homomorphism. -/
-- See note [non-reducible instance]
@[reducible]
def bracketHom [DecidableEq ι] [AddCommMonoid ι] [∀ i, AddCommGroup (A i)] [GLieRing A] :
    (⨁ i, A i) →+ (⨁ i, A i) →+ ⨁ i, A i :=
  DirectSum.toAddMonoid fun _ =>
    AddMonoidHom.flip <|
      DirectSum.toAddMonoid fun _ =>
        AddMonoidHom.flip <| (DirectSum.of A _).compHom.comp <| gBracketHom A rfl

instance [DecidableEq ι] [AddCommMonoid ι] [∀ i, AddCommGroup (A i)] [GLieRing A] :
    Bracket (⨁ i, A i)  (⨁ i, A i) where
  bracket a b := bracketHom A a b

lemma bracketHom_apply [DecidableEq ι] [AddCommMonoid ι] [∀ i, AddCommGroup (A i)] [GLieRing A]
    (a b : ⨁ i, A i) :
    bracketHom A a b = ⁅a, b⁆ := rfl

--omit?
lemma bracketHom_of_of [DecidableEq ι] [AddCommMonoid ι] [∀ i, AddCommGroup (A i)] [GLieRing A]
    {i j} (a : A i) (b : A j) :
    bracketHom A (of A i a) (of A j b) = of A (i + j) (GBracket.bracket rfl a b) := by
  simp

lemma of_bracket_of [DecidableEq ι] [AddCommMonoid ι] [∀ i, AddCommGroup (A i)] [GLieRing A]
    {i j} (a : A i) (b : A j) :
    ⁅of A i a, of A j b⁆ = of _ (i + j) (GBracket.bracket rfl a b) :=
  bracketHom_of_of A a b

lemma rec_bracket [AddCommMonoid ι] [∀ i, AddCommGroup (A i)] [GLieRing A]
    {i j k l} (a : A i) (b : A j) (hk : i + j = k) (hl : i + j = l) (hkl : k = l) :
    Eq.rec (GBracket.bracket hk a b) hkl = GBracket.bracket hl a b := by
  grind

lemma bracketHom_single_apply [DecidableEq ι] [AddCommMonoid ι] [∀ i, AddCommGroup (A i)]
    [GLieRing A] (i j : ι) (a : A i) (b : A j) :
    bracketHom A (DFinsupp.single i a) (DFinsupp.single j b) =
      DirectSum.of A (i + j) (GBracket.bracket rfl a b) := by
    have (k : ι) (c : A k) : DFinsupp.single k c = of A k c := DFinsupp.ext (congrFun rfl)
    simp [this]

instance instBracket [DecidableEq ι] [AddCommMonoid ι] [∀ i, AddCommGroup (A i)] [GLieRing A] :
    Bracket (⨁ i, A i) (⨁ i, A i) where
  bracket := fun a b => bracketHom A a b

/-- `GLieRing` implies a Lie ring structure. -/
instance GLieRing.toLieRing [DecidableEq ι] [AddCommMonoid ι] [∀ i, AddCommGroup (A i)]
    [GLieRing A] :
    LieRing (⨁ i, A i) :=
  { (inferInstance : AddCommGroup _) with
    bracket x y := bracketHom A x y
    add_lie _ _ _ := by simp
    lie_add _ _ _ := by simp
    lie_self x := by
      have hof (k : ι) (c : A k) : DFinsupp.single k c = of A k c := DFinsupp.ext (congrFun rfl)
      have hsum (i : ι) (a : A i) (f : (⨁ i, A i)) :
          bracketHom A (of A i a) f + bracketHom A f (of A i a) = 0 := by
        induction f using DFinsupp.induction with
        | h0 => simp
        | ha j b f hj _ h =>
          simp only [hof, map_add, AddMonoidHom.add_apply]
          rw [add_rotate, add_left_comm, h, add_zero]
          ext k
          by_cases h : i + j = k
          · simp [of_apply, h, add_comm i j ▸ h, rec_bracket, GLieRing.lie_antisymm]
          · simp [of_apply, h, add_comm i j ▸ h]
      induction x using DFinsupp.induction with
      | h0 => simp
      | ha j b f hj _ h =>
        simp only [hof, map_add, AddMonoidHom.add_apply, h, add_zero]
        rw [bracketHom_of_of, GLieRing.lie_self, map_zero, zero_add, add_comm]
        exact hsum j b f
    leibniz_lie x y z := by
      have hof (k : ι) (c : A k) : DFinsupp.single k c = of A k c := DFinsupp.ext (congrFun rfl)
      have hbss (i j : ι) (a : A i) (b : A j) :
          ((bracketHom A) (of A i a)) (((bracketHom A) (of A j b)) z) =
          ((bracketHom A) (of A j b)) (((bracketHom A) (of A i a)) z) +
          ((bracketHom A) (((bracketHom A) (of A i a)) (of A j b))) z := by
        induction z using DFinsupp.induction with
        | h0 => simp
        | ha k c f _ _ ih =>
          simp only [map_add, ih, ← add_assoc, add_left_inj]
          rw [add_right_comm, add_right_cancel_iff]
          simp only [hof, toAddMonoid_of, AddMonoidHom.flip_apply, AddMonoidHom.coe_comp,
            Function.comp_apply, AddMonoidHom.compHom_apply_apply, gBracketHom_apply_apply]
          ext l
          by_cases h : i + j + k = l
          · simp [of_apply, h, add_assoc i j k ▸ h, add_assoc j i k ▸ add_comm i j ▸ h, rec_bracket,
            GLieRing.leibniz_lie, add_comm (GBracket.bracket _ (GBracket.bracket _ a b) c)]
          · simp [of_apply, h, add_assoc i j k ▸ h, add_assoc j i k ▸ add_comm i j ▸ h]
      have hbs (i : ι) (a : A i) : ((bracketHom A) (of A i a)) (((bracketHom A) y) z) =
          ((bracketHom A) y) (((bracketHom A) (of A i a)) z) +
          ((bracketHom A) (((bracketHom A) (of A i a)) y)) z := by
        induction y using DFinsupp.induction with
        | h0 => simp
        | ha j b f _ _ ih =>
          simp only [map_add, AddMonoidHom.add_apply, ih, ← add_assoc]
          rw [add_right_cancel_iff, add_right_comm, add_right_cancel_iff]
          exact hbss i j a b
      induction x using DFinsupp.induction with
      | h0 => simp
      | ha i a f _ _ ih =>
        simp only [hof, map_add, AddMonoidHom.add_apply, ih, ← add_assoc]
        rw [add_right_cancel_iff, ← add_rotate, add_right_cancel_iff]
        exact hbs i a }

/-- A Lie algebra is a module with compatible product, known as the bracket, satisfying the Jacobi
identity. Forgetting the scalar multiplication, every Lie algebra is a Lie ring. -/
@[ext] class GLieAlgebra (R : Type*) (A : ι → Type*) [CommRing R] [AddCommMonoid ι]
    [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)] extends GLieRing A where
  /-- A Lie algebra bracket is compatible with scalar multiplication in its second argument.

  The compatibility in the first argument is not a class property, but follows since every
  Lie algebra has a natural Lie module action on itself, see `LieModule`. -/
  protected lie_smul : ∀ (t : R) {i j k} (h : i + j = k) (x : A i) (y : A j),
    bracket h x (t • y) = t • bracket h x y

/-- `GLieAlgebra` implies a Lie algebra structure. -/
instance GLieAlgebra.toLieAlgebra [DecidableEq ι] [AddCommMonoid ι] [∀ i, AddCommGroup (A i)]
    [∀ i, Module R (A i)] [GLieAlgebra R A] : LieAlgebra R (⨁ i, A i) where
  lie_smul r x y := by
    have (i : ι) (a : A i) : ⁅of A i a, r • y⁆ = r • ⁅of A i a, y⁆ := by
      induction y using DFinsupp.induction with
        | h0 => simp
        | ha j b f _ _ ih =>
          have (k : ι) (c : A k) : DFinsupp.single k c = of A k c := DFinsupp.ext (congrFun rfl)
          simp only [this, smul_add, lie_add, ih, add_left_inj]
          rw [of_bracket_of, ← of_smul, of_bracket_of, ← of_smul]
          refine DFunLike.congr rfl <| GLieAlgebra.lie_smul r rfl a b
    induction x using DFinsupp.induction with
    | h0 => simp
    | ha i b f _ _ ih =>
      simp only [add_lie, ih, smul_add, add_left_inj]
      exact this i b

-- Internal grading?
/-
/-- A type alias of sigma types for graded monoids. -/
def GradedBracket :=
  Sigma A

namespace GradedBracket

/-- Construct an element of a graded monoid. -/
def mk {A : ι → Type*} : ∀ i, A i → GradedBracket A :=
  Sigma.mk

/-- `GBracket` implies `Bracket (GradedMonoid A)`. -/
instance GBracket.toBracket [Add ι] [GBracket A] : Bracket (GradedBracket A) (GradedBracket A) :=
  ⟨fun x y : GradedBracket A => ⟨_, GBracket.bracket rfl x.snd y.snd⟩⟩

@[simp] theorem fst_bracket [Add ι] [GBracket A] (x y : GradedBracket A) :
    ⁅x, y⁆.fst = x.fst + y.fst := rfl

@[simp] theorem snd_bracket [Add ι] [GBracket A] (x y : GradedBracket A) :
    ⁅x, y⁆.snd = GBracket.bracket rfl x.snd y.snd := rfl

theorem mk_bracket_mk [Add ι] [GBracket A] {i j} (a : A i) (b : A j) :
    ⁅mk i a, mk j b⁆ = mk (i + j) (GBracket.bracket rfl a b) :=
  rfl

/-- A version of `GradedMonoid.ghas_one` for internally graded objects. -/
class SetLike.GradedBracket {L} {S : Type*} [SetLike S L] [Bracket L L] [Add ι] (A : ι → S) :
    Prop where
  /-- Bracket is homogeneous -/
  mul_mem : ∀ ⦃i j⦄ {gi gj}, gi ∈ A i → gj ∈ A j → ⁅gi, gj⁆ ∈ A (i + j)
-/

end DirectSum

namespace LieDerivation

@[simp]
lemma lof_comp_DistribSMul_apply [DecidableEq ι] [CommSemiring ι] [∀ i, AddCommGroup (A i)]
    [∀ i, Module ι (A i)] [∀ i, Module R (A i)] [∀ i, SMulCommClass ι R (A i)] (i : ι) (x : A i) :
    (lof R ι A i ∘ₗ DistribSMul.toLinearMap R (A i) i) x = of A i (i • x) := by
  rfl

@[simp]
lemma toModule_lof_smul_of [DecidableEq ι] [CommSemiring ι] [∀ i, AddCommGroup (A i)]
    [∀ i, Module ι (A i)] [∀ i, Module R (A i)] [∀ i, SMulCommClass ι R (A i)] (k : ι) (b : A k) :
    (toModule R ι (⨁ (i : ι), A i)
      fun i ↦ lof R ι A i ∘ₗ DistribSMul.toLinearMap R (A i) i) (of A k b) = k • (of A k b) := by
  rw [coe_toModule_eq_coe_toAddMonoid, toAddMonoid_of, LinearMap.toAddMonoidHom_coe,
      lof_comp_DistribSMul_apply, of_smul]

/-- The Lie derivation on a graded Lie algebra that scalar multiplies by the degree. -/
def ofGrading [DecidableEq ι] [CommSemiring ι] [Algebra ι R] [∀ i, AddCommGroup (A i)]
    [∀ i, Module ι (A i)] [∀ i, Module R (A i)] [GLieAlgebra R A] [∀ i, SMulCommClass ι R (A i)]
    [IsScalarTower ι R (⨁ i, A i)] :
    LieDerivation R (⨁ i, A i) (⨁ i, A i) :=
  { __ := (DirectSum.toModule R ι (⨁ i, A i)
      fun i ↦ (DirectSum.lof R ι A i).comp (DistribSMul.toLinearMap R _ i))
    leibniz' x y := by
      have hof (k : ι) (c : A k) : DFinsupp.single k c = of A k c := DFinsupp.ext (congrFun rfl)
      have (i j : ι) (a : A i) (f : (⨁ i, A i)) :
          ((toModule R ι (⨁ (i : ι), A i) fun i ↦
            lof R ι A i ∘ₗ DistribSMul.toLinearMap R (A i) i) ⁅of A i a, y⁆) j =
          (⁅of A i a, (toModule R ι (⨁ (i : ι), A i) fun i ↦
            lof R ι A i ∘ₗ DistribSMul.toLinearMap R (A i) i) y⁆ -
          ⁅y, (toModule R ι (⨁ (i : ι), A i) fun i ↦
            lof R ι A i ∘ₗ DistribSMul.toLinearMap R (A i) i) (of A i a)⁆) j := by
        induction y using DFinsupp.induction with
        | h0 => simp
        | ha k b f _ _ ih =>
          simp only [DirectSum.sub_apply] at ih
          simp only [hof, lie_add, map_add, DirectSum.add_apply, ih, add_lie, DirectSum.sub_apply]
          rw [add_sub_add_comm, add_right_cancel_iff]
          simp only [of_bracket_of, toModule_lof_smul_of A k b (R := R), toModule_lof_smul_of A i a,
            toModule_lof_smul_of A (i + k)]
          rw [← smul_one_smul R i, lie_smul, smul_one_smul, ← lie_skew (of A k b), smul_neg,
            DFinsupp.neg_apply, sub_neg_eq_add, ← smul_one_smul R k, lie_smul, smul_one_smul,
            of_bracket_of, add_smul, add_comm, DirectSum.add_apply]
      ext j
      induction x using DFinsupp.induction with
      | h0 => simp
      | ha i a f _ _ ih =>
        simp only [DirectSum.sub_apply] at ih
        simp only [add_lie, map_add, DirectSum.add_apply, ih, lie_add, DirectSum.sub_apply, hof]
        rw [add_sub_add_comm, add_right_cancel_iff, ← DirectSum.sub_apply]
        exact this i j a f }

@[simp]
lemma ofGrading_of [DecidableEq ι] [CommSemiring ι] [Algebra ι R] [∀ i, AddCommGroup (A i)]
    [∀ i, Module ι (A i)] [∀ i, Module R (A i)] [GLieAlgebra R A] [∀ i, SMulCommClass ι R (A i)]
    [IsScalarTower ι R (⨁ i, A i)] (i : ι) (a : A i) :
    ofGrading A (of A i a) (R := R) = i • (of A i a) := by
  ext j
  simp [ofGrading]

end LieDerivation
