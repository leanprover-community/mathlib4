/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Yongle Hu
-/
module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Ideals over/under ideals

This file concerns ideals lying over other ideals.
Let `f : R →+* S` be a ring homomorphism (typically a ring extension), `I` an ideal of `R` and
`J` an ideal of `S`. We say `J` lies over `I` (and `I` under `J`) if `I` is the `f`-preimage of `J`.
This is expressed here by writing `I = J.comap f`.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

-- for going-up results about integral extensions, see `Mathlib/RingTheory/Ideal/GoingUp.lean`
assert_not_exists Algebra.IsIntegral

-- for results about finiteness, see `Mathlib/RingTheory/Finiteness/Quotient.lean`
assert_not_exists Module.Finite

variable {R : Type*} [CommRing R]

namespace Ideal

open Submodule

open scoped Pointwise

section CommRing

variable {S : Type*} [CommRing S] {f : R →+* S} {I J : Ideal S}

variable {p : Ideal R} {P : Ideal S}

/-- If there is an injective map `R/p → S/P` such that the following diagram commutes:
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
  exact map_eq_zero_iff _ h

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

instance Quotient.tower_quotient_map_quotient :
    IsScalarTower R (R ⧸ p) (S ⧸ map (algebraMap R S) p) :=
  IsScalarTower.of_algebraMap_eq fun x => by
    rw [Quotient.algebraMap_eq, Quotient.algebraMap_quotient_map_quotient,
      Quotient.mk_algebraMap]

end CommRing

section ideal_liesOver

section Semiring

variable (A : Type*) [CommSemiring A] {B C : Type*} [Semiring B] [Semiring C] [Algebra A B]
  [Algebra A C] (P : Ideal B) {Q : Ideal C} (p : Ideal A)
  {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B] (g : G)

/-- The ideal obtained by pulling back the ideal `P` from `B` to `A`. -/
abbrev under : Ideal A := Ideal.comap (algebraMap A B) P

theorem under_def : P.under A = Ideal.comap (algebraMap A B) P := rfl

instance IsPrime.under [hP : P.IsPrime] : (P.under A).IsPrime :=
  hP.comap (algebraMap A B)

@[simp]
lemma under_smul : (g • P : Ideal B).under A = P.under A := by
  ext a
  rw [mem_comap, mem_comap, mem_pointwise_smul_iff_inv_smul_mem, smul_algebraMap]

variable (B) in
theorem under_top : under A (⊤ : Ideal B) = ⊤ := comap_top

variable {A}

/-- `P` lies over `p` if `p` is the preimage of `P` by the `algebraMap`. -/
@[mk_iff] class LiesOver : Prop where
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

lemma ne_top_iff_of_liesOver [P.LiesOver p] : P ≠ ⊤ ↔ p ≠ ⊤ := (eq_top_iff_of_liesOver ..).ne

lemma isPrime_of_liesOver [P.LiesOver p] [P.IsPrime] : p.IsPrime := by
  rw [over_def P p]
  exact IsPrime.under A P

variable {P}

theorem LiesOver.of_eq_comap [Q.LiesOver p] {F : Type*} [FunLike F B C]
    [AlgHomClass F A B C] (f : F) (h : P = Q.comap f) : P.LiesOver p where
  over := by
    rw [h]
    exact (over_def Q p).trans <|
      congrFun (congrFun (congrArg comap ((f : B →ₐ[A] C).comp_algebraMap.symm)) _) Q

theorem LiesOver.of_eq_map_equiv [P.LiesOver p] {E : Type*} [EquivLike E B C]
    [AlgEquivClass E A B C] (σ : E) (h : Q = P.map σ) : Q.LiesOver p := by
  rw [← show _ = P.map σ from comap_symm (RingEquivClass.toRingEquiv σ)] at h
  exact of_eq_comap p (AlgEquivClass.toAlgEquiv σ : B ≃ₐ[A] C).symm h

variable {p} in
instance LiesOver.smul [h : P.LiesOver p] : (g • P).LiesOver p :=
  ⟨h.over.trans (under_smul A P g).symm⟩

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
theorem under_under : (𝔓.under B).under A = 𝔓.under A := by
  simp_rw [comap_comap, ← IsScalarTower.algebraMap_eq]

theorem LiesOver.trans [𝔓.LiesOver P] [P.LiesOver p] : 𝔓.LiesOver p where
  over := by rw [P.over_def p, 𝔓.over_def P, under_under]

theorem LiesOver.tower_bot [hp : 𝔓.LiesOver p] [hP : 𝔓.LiesOver P] : P.LiesOver p where
  over := by rw [𝔓.over_def p, 𝔓.over_def P, under_under]

/--
Consider the following commutative diagram of ring maps
```
A → B
↓   ↓
C → D
```
and let `P` be an ideal of `B`. The image in `C` of the ideal of `A` under `P` is included
in the ideal of `C` under the image of `P` in `D`.
-/
theorem map_under_le_under_map {C D : Type*} [CommSemiring C] [Semiring D] [Algebra A C]
    [Algebra C D] [Algebra A D] [Algebra B D] [IsScalarTower A C D] [IsScalarTower A B D] :
    map (algebraMap A C) (under A P) ≤ under C (map (algebraMap B D) P) := by
  apply le_comap_of_map_le
  rw [map_map, ← IsScalarTower.algebraMap_eq, map_le_iff_le_comap,
    IsScalarTower.algebraMap_eq A B D, ← comap_comap]
  exact comap_mono <| le_comap_map

/--
Consider the following commutative diagram of ring maps
```
A → B
↓   ↓
C → D
```
and let `P` be an ideal of `B`. Assume that the image in `C` of the ideal of `A` under `P`
is maximal and that the image of `P` in `D` is not equal to `D`, then the image in `C` of the
ideal of `A` under `P` is equal to the ideal of `C` under the image of `P` in `D`.
-/
theorem under_map_eq_map_under {C D : Type*} [CommSemiring C] [Semiring D] [Algebra A C]
    [Algebra C D] [Algebra A D] [Algebra B D] [IsScalarTower A C D] [IsScalarTower A B D]
    (h₁ : (map (algebraMap A C) (under A P)).IsMaximal) (h₂ : map (algebraMap B D) P ≠ ⊤) :
    under C (map (algebraMap B D) P) = map (algebraMap A C) (under A P) :=
  (IsCoatom.le_iff_eq (isMaximal_def.mp h₁) (comap_ne_top (algebraMap C D) h₂)).mp <|
    map_under_le_under_map P

theorem disjoint_primeCompl_of_liesOver [p.IsPrime] [hPp : 𝔓.LiesOver p] :
  Disjoint ((Algebra.algebraMapSubmonoid C p.primeCompl) : Set C) (𝔓 : Set C) := by
  rw [liesOver_iff, under_def, SetLike.ext'_iff, coe_comap] at hPp
  simpa only [Algebra.algebraMapSubmonoid, primeCompl, hPp, ← le_compl_iff_disjoint_left]
    using Set.subset_compl_comm.mp (by simp)

variable (B)

instance under_liesOver_of_liesOver [𝔓.LiesOver p] : (𝔓.under B).LiesOver p :=
  LiesOver.tower_bot 𝔓 (𝔓.under B) p

end CommSemiring

section CommRing

variable (A B : Type*) [CommRing A] [IsDomain A] [Ring B] [Nontrivial B]
  [Algebra A B] [Module.IsTorsionFree A B] {p : Ideal A}

@[simp]
theorem under_bot : under A (⊥ : Ideal B) = ⊥ :=
  comap_bot_of_injective (algebraMap A B) (FaithfulSMul.algebraMap_injective A B)

instance bot_liesOver_bot : (⊥ : Ideal B).LiesOver (⊥ : Ideal A) where
  over := (under_bot A B).symm

variable {A B} in
theorem ne_bot_of_liesOver_of_ne_bot (hp : p ≠ ⊥) (P : Ideal B) [P.LiesOver p] : P ≠ ⊥ := by
  contrapose hp
  rw [over_def P p, hp, under_bot]

end CommRing

instance {K A : Type*} [Field K] [Semiring A] [Algebra K A] (P : Ideal A) [P.IsPrime] :
    P.LiesOver (⊥ : Ideal K) :=
  ⟨((IsSimpleOrder.eq_bot_or_eq_top _).resolve_right Ideal.IsPrime.ne_top').symm⟩
namespace Quotient

variable (R : Type*) [CommSemiring R] {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C] [Algebra R A] [Algebra R B] [IsScalarTower R A B]
  (P : Ideal B) {Q : Ideal C} (p : Ideal A) [Q.LiesOver p] [P.LiesOver p]
  (G : Type*) [Group G] [MulSemiringAction G B] [SMulCommClass G A B]

/-- If `P` lies over `p`, then canonically `B ⧸ P` is a `A ⧸ p`-algebra. -/
instance algebraOfLiesOver : Algebra (A ⧸ p) (B ⧸ P) :=
  algebraQuotientOfLEComap (le_of_eq (P.over_def p))

@[simp]
lemma algebraMap_mk_of_liesOver (x : A) :
    algebraMap (A ⧸ p) (B ⧸ P) (Ideal.Quotient.mk p x) = Ideal.Quotient.mk P (algebraMap _ _ x) :=
  rfl

instance isScalarTower_of_liesOver : IsScalarTower R (A ⧸ p) (B ⧸ P) :=
  IsScalarTower.of_algebraMap_eq' <|
    congrArg (algebraMap B (B ⧸ P)).comp (IsScalarTower.algebraMap_eq R A B)

instance instFaithfulSMul : FaithfulSMul (A ⧸ p) (B ⧸ P) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  rintro ⟨a⟩ ⟨b⟩ hab
  apply Quotient.eq.mpr ((mem_of_liesOver P p (a - b)).mpr _)
  rw [map_sub]
  exact Quotient.eq.mp hab

variable {p} in
theorem nontrivial_of_liesOver_of_ne_top (hp : p ≠ ⊤) : Nontrivial (B ⧸ P) := by
  rwa [Quotient.nontrivial_iff, ne_top_iff_of_liesOver _ p]

theorem nontrivial_of_liesOver_of_isPrime [hp : p.IsPrime] : Nontrivial (B ⧸ P) :=
  nontrivial_of_liesOver_of_ne_top P hp.ne_top

section algEquiv

variable {P} {E : Type*} [EquivLike E B C] [AlgEquivClass E A B C] (σ : E)

/-- An `A ⧸ p`-algebra isomorphism between `B ⧸ P` and `C ⧸ Q` induced by an `A`-algebra
  isomorphism between `B` and `C`, where `Q = σ P`. -/
def algEquivOfEqMap (h : Q = P.map σ) : (B ⧸ P) ≃ₐ[A ⧸ p] (C ⧸ Q) where
  __ := quotientEquiv P Q (RingEquivClass.toRingEquiv σ) h
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

lemma ker_stabilizerHom :
    (stabilizerHom P p G).ker = (P.inertia G).subgroupOf _ := by
  ext σ
  simp [DFunLike.ext_iff, mk_surjective.forall, Quotient.eq]

theorem map_ker_stabilizer_subtype :
    (stabilizerHom P p G).ker.map (Subgroup.subtype _) = P.inertia G := by
  simp [ker_stabilizerHom, Ideal.inertia_le_stabilizer]

instance (p : Ideal R) (P : Ideal A) [P.IsPrime] [P.LiesOver p] :
    (P.map (Ideal.Quotient.mk <| p.map (algebraMap R A))).IsPrime := by
  apply Ideal.isPrime_map_quotientMk_of_isPrime
  rw [Ideal.map_le_iff_le_comap, Ideal.LiesOver.over (p := p) (P := P)]

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

variable {p} in
theorem ne_bot_of_mem_primesOver [IsDomain R] {S : Type*} [Ring S] [Algebra R S] [Nontrivial S]
    [Module.IsTorsionFree R S] {p : Ideal R} (hp : p ≠ ⊥) {P : Ideal S} (hP : P ∈ p.primesOver S) :
    P ≠ ⊥ := by have : P.LiesOver p := hP.2; exact ne_bot_of_liesOver_of_ne_bot hp P

end primesOver

end Ideal
