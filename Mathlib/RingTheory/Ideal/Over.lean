/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Yongle Hu
-/
import Mathlib.Algebra.Group.Subgroup.Actions
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.Pointwise

/-!
# Ideals over/under ideals

This file concerns ideals lying over other ideals.
Let `f : R →+* S` be a ring homomorphism (typically a ring extension), `I` an ideal of `R` and
`J` an ideal of `S`. We say `J` lies over `I` (and `I` under `J`) if `I` is the `f`-preimage of `J`.
This is expressed here by writing `I = J.comap f`.
-/

-- for going-up results about integral extensions, see `Mathlib.RingTheory.Ideal.GoingUp`
assert_not_exists Algebra.IsIntegral

variable {R : Type*} [CommRing R]

namespace Ideal

open Polynomial Submodule

open scoped Pointwise

section CommRing

variable {S : Type*} [CommRing S] {f : R →+* S} {I J : Ideal S}

variable {p : Ideal R} {P : Ideal S}

/-- If there is an injective map `R/p → S/P` such that following diagram commutes:
```
R   → S
↓     ↓
R/p → S/P
```
then `P` lies over `p`.
-/
theorem comap_eq_of_scalar_tower_quotient [Algebra R S] [Algebra (R ⧸ p) (S ⧸ P)]
    [IsScalarTower R (R ⧸ p) (S ⧸ P)] (h : Function.Injective (algebraMap (R ⧸ p) (S ⧸ P))) :
    comap (algebraMap R S) P = p := by
  ext x
  rw [mem_comap, ← Quotient.eq_zero_iff_mem, ← Quotient.eq_zero_iff_mem, Quotient.mk_algebraMap,
    IsScalarTower.algebraMap_apply R (R ⧸ p) (S ⧸ P), Quotient.algebraMap_eq]
  constructor
  · intro hx
    exact (injective_iff_map_eq_zero (algebraMap (R ⧸ p) (S ⧸ P))).mp h _ hx
  · intro hx
    rw [hx, RingHom.map_zero]

variable [Algebra R S]

/-- `R / p` has a canonical map to `S / pS`. -/
instance Quotient.algebraQuotientMapQuotient : Algebra (R ⧸ p) (S ⧸ map (algebraMap R S) p) :=
  Ideal.Quotient.algebraQuotientOfLEComap le_comap_map

@[simp]
theorem Quotient.algebraMap_quotient_map_quotient (x : R) :
    letI f := algebraMap R S
    algebraMap (R ⧸ p) (S ⧸ map f p) (Ideal.Quotient.mk p x) =
    Ideal.Quotient.mk (map f p) (f x) :=
  rfl

@[simp]
theorem Quotient.mk_smul_mk_quotient_map_quotient (x : R) (y : S) :
    letI f := algebraMap R S
    Quotient.mk p x • Quotient.mk (map f p) y = Quotient.mk (map f p) (f x * y) :=
  Algebra.smul_def _ _

instance Quotient.tower_quotient_map_quotient [Algebra R S] :
    IsScalarTower R (R ⧸ p) (S ⧸ map (algebraMap R S) p) :=
  IsScalarTower.of_algebraMap_eq fun x => by
    rw [Quotient.algebraMap_eq, Quotient.algebraMap_quotient_map_quotient,
      Quotient.mk_algebraMap]

instance QuotientMapQuotient.isNoetherian [Algebra R S] [IsNoetherian R S] (I : Ideal R) :
    IsNoetherian (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
  isNoetherian_of_tower R <|
    isNoetherian_of_surjective S (Ideal.Quotient.mkₐ R _).toLinearMap <|
      LinearMap.range_eq_top.mpr Ideal.Quotient.mk_surjective

end CommRing

section ideal_liesOver

section Semiring

variable (A : Type*) [CommSemiring A] {B C : Type*} [Semiring B] [Semiring C] [Algebra A B]
  [Algebra A C] (P : Ideal B) {Q : Ideal C} (p : Ideal A)

/-- The ideal obtained by pulling back the ideal `P` from `B` to `A`. -/
abbrev under : Ideal A := Ideal.comap (algebraMap A B) P

theorem under_def : P.under A = Ideal.comap (algebraMap A B) P := rfl

instance IsPrime.under [hP : P.IsPrime] : (P.under A).IsPrime :=
  hP.comap (algebraMap A B)

@[simp]
lemma under_smul {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B] (g : G) :
    (g • P : Ideal B).under A = P.under A := by
  ext a
  rw [mem_comap, mem_comap, mem_pointwise_smul_iff_inv_smul_mem, smul_algebraMap]

variable (B) in
theorem under_top : under A (⊤ : Ideal B) = ⊤ := comap_top

variable {A}

/-- `P` lies over `p` if `p` is the preimage of `P` of the `algebraMap`. -/
class LiesOver : Prop where
  over : p = P.under A

instance over_under : P.LiesOver (P.under A) where over := rfl

theorem over_def [P.LiesOver p] : p = P.under A := LiesOver.over

theorem mem_of_liesOver [P.LiesOver p] (x : A) : x ∈ p ↔ algebraMap A B x ∈ P := by
  rw [P.over_def p]
  rfl

variable (A B) in
instance top_liesOver_top : (⊤ : Ideal B).LiesOver (⊤ : Ideal A) where
  over := (under_top A B).symm

theorem eq_top_iff_of_liesOver [P.LiesOver p] : P = ⊤ ↔ p = ⊤ := by
  rw [P.over_def p]
  exact comap_eq_top_iff.symm

variable {P}

theorem LiesOver.of_eq_comap [Q.LiesOver p] {F : Type*} [FunLike F B C]
    [AlgHomClass F A B C] (f : F) (h : P = Q.comap f) : P.LiesOver p where
  over := by
    rw [h]
    exact (over_def Q p).trans <|
      congrFun (congrFun (congrArg comap ((f : B →ₐ[A] C).comp_algebraMap.symm)) _) Q

theorem LiesOver.of_eq_map_equiv [P.LiesOver p] {E : Type*} [EquivLike E B C]
    [AlgEquivClass E A B C] (σ : E) (h : Q = P.map σ) : Q.LiesOver p := by
  rw [← show _ = P.map σ from comap_symm (σ : B ≃+* C)] at h
  exact of_eq_comap p (σ : B ≃ₐ[A] C).symm h

variable (P) (Q)

instance comap_liesOver [Q.LiesOver p] {F : Type*} [FunLike F B C] [AlgHomClass F A B C]
    (f : F) : (Q.comap f).LiesOver p :=
  LiesOver.of_eq_comap p f rfl

instance map_equiv_liesOver [P.LiesOver p] {E : Type*} [EquivLike E B C] [AlgEquivClass E A B C]
    (σ : E) : (P.map σ).LiesOver p :=
  LiesOver.of_eq_map_equiv p σ rfl

end Semiring

section CommSemiring

variable {A : Type*} [CommSemiring A] {B : Type*} [CommSemiring B] {C : Type*} [Semiring C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  (𝔓 : Ideal C) (P : Ideal B) (p : Ideal A)

@[simp]
theorem under_under : (𝔓.under B).under A  = 𝔓.under A := by
  simp_rw [comap_comap, ← IsScalarTower.algebraMap_eq]

theorem LiesOver.trans [𝔓.LiesOver P] [P.LiesOver p] : 𝔓.LiesOver p where
  over := by rw [P.over_def p, 𝔓.over_def P, under_under]

theorem LiesOver.tower_bot [hp : 𝔓.LiesOver p] [hP : 𝔓.LiesOver P] : P.LiesOver p where
  over := by rw [𝔓.over_def p, 𝔓.over_def P, under_under]

variable (B)

instance under_liesOver_of_liesOver [𝔓.LiesOver p] : (𝔓.under B).LiesOver p :=
  LiesOver.tower_bot 𝔓 (𝔓.under B) p

end CommSemiring

section CommRing

variable (A : Type*) [CommRing A] (B : Type*) [Ring B] [Nontrivial B]
  [Algebra A B] [NoZeroSMulDivisors A B] {p : Ideal A}

@[simp]
theorem under_bot : under A (⊥ : Ideal B) = ⊥ :=
  comap_bot_of_injective (algebraMap A B) (FaithfulSMul.algebraMap_injective A B)

instance bot_liesOver_bot : (⊥ : Ideal B).LiesOver (⊥ : Ideal A) where
  over := (under_bot A B).symm

variable {A B} in
theorem ne_bot_of_liesOver_of_ne_bot (hp : p ≠ ⊥) (P : Ideal B) [P.LiesOver p] : P ≠ ⊥ := by
  contrapose! hp
  rw [over_def P p, hp, under_bot]

end CommRing

namespace Quotient

variable (R : Type*) [CommSemiring R] {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C] [Algebra R A] [Algebra R B] [IsScalarTower R A B]
  (P : Ideal B) {Q : Ideal C} (p : Ideal A) [Q.LiesOver p] [P.LiesOver p]
  (G : Type*) [Group G] [MulSemiringAction G B] [SMulCommClass G A B]

/-- If `P` lies over `p`, then canonically `B ⧸ P` is a `A ⧸ p`-algebra. -/
instance algebraOfLiesOver : Algebra (A ⧸ p) (B ⧸ P) :=
  algebraQuotientOfLEComap (le_of_eq (P.over_def p))

instance isScalarTower_of_liesOver : IsScalarTower R (A ⧸ p) (B ⧸ P) :=
  IsScalarTower.of_algebraMap_eq' <|
    congrArg (algebraMap B (B ⧸ P)).comp (IsScalarTower.algebraMap_eq R A B)

/-- `B ⧸ P` is a finite `A ⧸ p`-module if `B` is a finite `A`-module. -/
instance module_finite_of_liesOver [Module.Finite A B] : Module.Finite (A ⧸ p) (B ⧸ P) :=
  Module.Finite.of_restrictScalars_finite A (A ⧸ p) (B ⧸ P)

example [Module.Finite A B] : Module.Finite (A ⧸ P.under A) (B ⧸ P) := inferInstance

/-- `B ⧸ P` is a finitely generated `A ⧸ p`-algebra if `B` is a finitely generated `A`-algebra. -/
instance algebra_finiteType_of_liesOver [Algebra.FiniteType A B] :
    Algebra.FiniteType (A ⧸ p) (B ⧸ P) :=
  Algebra.FiniteType.of_restrictScalars_finiteType A (A ⧸ p) (B ⧸ P)

/-- `B ⧸ P` is a Noetherian `A ⧸ p`-module if `B` is a Noetherian `A`-module. -/
instance isNoetherian_of_liesOver [IsNoetherian A B] : IsNoetherian (A ⧸ p) (B ⧸ P) :=
  isNoetherian_of_tower A inferInstance

instance instFaithfulSMul : FaithfulSMul (A ⧸ p) (B ⧸ P) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  rintro ⟨a⟩ ⟨b⟩ hab
  apply Quotient.eq.mpr ((mem_of_liesOver P p (a - b)).mpr _)
  rw [RingHom.map_sub]
  exact Quotient.eq.mp hab

@[deprecated (since := "2025-01-31")]
alias algebraMap_injective_of_liesOver := instFaithfulSMul

variable {p} in
theorem nontrivial_of_liesOver_of_ne_top (hp : p ≠ ⊤) : Nontrivial (B ⧸ P) :=
  Quotient.nontrivial ((eq_top_iff_of_liesOver P p).mp.mt hp)

theorem nontrivial_of_liesOver_of_isPrime [hp : p.IsPrime] : Nontrivial (B ⧸ P) :=
  nontrivial_of_liesOver_of_ne_top P hp.ne_top

section algEquiv

variable {P} {E : Type*} [EquivLike E B C] [AlgEquivClass E A B C] (σ : E)

/-- An `A ⧸ p`-algebra isomorphism between `B ⧸ P` and `C ⧸ Q` induced by an `A`-algebra
  isomorphism between `B` and `C`, where `Q = σ P`. -/
def algEquivOfEqMap (h : Q = P.map σ) : (B ⧸ P) ≃ₐ[A ⧸ p] (C ⧸ Q) where
  __ := quotientEquiv P Q σ h
  commutes' := by
    rintro ⟨x⟩
    exact congrArg (Ideal.Quotient.mk Q) (AlgHomClass.commutes σ x)

@[simp]
theorem algEquivOfEqMap_apply (h : Q = P.map σ) (x : B) : algEquivOfEqMap p σ h x = σ x :=
  rfl

/-- An `A ⧸ p`-algebra isomorphism between `B ⧸ P` and `C ⧸ Q` induced by an `A`-algebra
  isomorphism between `B` and `C`, where `P = σ⁻¹ Q`. -/
def algEquivOfEqComap (h : P = Q.comap σ) : (B ⧸ P) ≃ₐ[A ⧸ p] (C ⧸ Q) :=
  algEquivOfEqMap p σ ((congrArg (map σ) h).trans (Q.map_comap_eq_self_of_equiv σ)).symm

@[simp]
theorem algEquivOfEqComap_apply (h : P = Q.comap σ) (x : B) : algEquivOfEqComap p σ h x = σ x :=
  rfl

end algEquiv

/-- If `P` lies over `p`, then the stabilizer of `P` acts on the extension `(B ⧸ P) / (A ⧸ p)`. -/
def stabilizerHom : MulAction.stabilizer G P →* ((B ⧸ P) ≃ₐ[A ⧸ p] (B ⧸ P)) where
  toFun g := algEquivOfEqMap p (MulSemiringAction.toAlgEquiv A B g) g.2.symm
  map_one' := by
    ext ⟨x⟩
    exact congrArg (Ideal.Quotient.mk P) (one_smul G x)
  map_mul' g h := by
    ext ⟨x⟩
    exact congrArg (Ideal.Quotient.mk P) (mul_smul g h x)

@[simp] theorem stabilizerHom_apply (g : MulAction.stabilizer G P) (b : B) :
    stabilizerHom P p G g b = ↑(g • b) :=
  rfl

end Quotient

end ideal_liesOver

section primesOver

variable {A : Type*} [CommSemiring A] (p : Ideal A) (B : Type*) [Semiring B] [Algebra A B]

/-- The set of all prime ideals in `B` that lie over an ideal `p` of `A`. -/
def primesOver : Set (Ideal B) :=
  { P : Ideal B | P.IsPrime ∧ P.LiesOver p }

variable {B}

instance primesOver.isPrime (Q : primesOver p B) : Q.1.IsPrime :=
  Q.2.1

instance primesOver.liesOver (Q : primesOver p B) : Q.1.LiesOver p :=
  Q.2.2

/-- If an ideal `P` of `B` is prime and lying over `p`, then it is in `primesOver p B`. -/
abbrev primesOver.mk (P : Ideal B) [hPp : P.IsPrime] [hp : P.LiesOver p] : primesOver p B :=
  ⟨P, ⟨hPp, hp⟩⟩

end primesOver

end Ideal
