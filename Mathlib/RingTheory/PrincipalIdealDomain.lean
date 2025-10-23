/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Morenikeji Neri
-/
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.RingTheory.Ideal.Prod
import Mathlib.RingTheory.Ideal.Nonunits
import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain

/-!
# Principal ideal rings, principal ideal domains, and Bézout rings

A principal ideal ring (PIR) is a ring in which all left ideals are principal. A
principal ideal domain (PID) is an integral domain which is a principal ideal ring.

The definition of `IsPrincipalIdealRing` can be found in `Mathlib/RingTheory/Ideal/Span.lean`.

## Main definitions

Note that for principal ideal domains, one should use
`[IsDomain R] [IsPrincipalIdealRing R]`. There is no explicit definition of a PID.
Theorems about PID's are in the `PrincipalIdealRing` namespace.

- `IsBezout`: the predicate saying that every finitely generated left ideal is principal.
- `generator`: a generator of a principal ideal (or more generally submodule)
- `to_uniqueFactorizationMonoid`: a PID is a unique factorization domain

## Main results

- `Ideal.IsPrime.to_maximal_ideal`: a non-zero prime ideal in a PID is maximal.
- `EuclideanDomain.to_principal_ideal_domain` : a Euclidean domain is a PID.
- `IsBezout.nonemptyGCDMonoid`: Every Bézout domain is a GCD domain.

-/


universe u v

variable {R : Type u} {M : Type v}

open Set Function

open Submodule

section

variable [Semiring R] [AddCommMonoid M] [Module R M]

instance bot_isPrincipal : (⊥ : Submodule R M).IsPrincipal :=
  ⟨⟨0, by simp⟩⟩

instance top_isPrincipal : (⊤ : Submodule R R).IsPrincipal :=
  ⟨⟨1, Ideal.span_singleton_one.symm⟩⟩

variable (R)

/-- A Bézout ring is a ring whose finitely generated ideals are principal. -/
class IsBezout : Prop where
  /-- Any finitely generated ideal is principal. -/
  isPrincipal_of_FG : ∀ I : Ideal R, I.FG → I.IsPrincipal

instance (priority := 100) IsBezout.of_isPrincipalIdealRing [IsPrincipalIdealRing R] : IsBezout R :=
  ⟨fun I _ => IsPrincipalIdealRing.principal I⟩

instance (priority := 100) DivisionSemiring.isPrincipalIdealRing (K : Type u) [DivisionSemiring K] :
    IsPrincipalIdealRing K where
  principal S := by
    rcases Ideal.eq_bot_or_top S with (rfl | rfl)
    · apply bot_isPrincipal
    · apply top_isPrincipal

end

namespace Submodule.IsPrincipal

variable [AddCommMonoid M]

section Semiring

variable [Semiring R] [Module R M]

@[simp]
theorem _root_.Ideal.span_singleton_generator (I : Ideal R) [I.IsPrincipal] :
    Ideal.span ({generator I} : Set R) = I :=
  Eq.symm (Classical.choose_spec (principal I))

@[simp]
theorem generator_mem (S : Submodule R M) [S.IsPrincipal] : generator S ∈ S := by
  have : generator S ∈ span R {generator S} := subset_span (mem_singleton _)
  convert this
  exact span_singleton_generator S |>.symm

theorem mem_iff_eq_smul_generator (S : Submodule R M) [S.IsPrincipal] {x : M} :
    x ∈ S ↔ ∃ s : R, x = s • generator S := by
  simp_rw [@eq_comm _ x, ← mem_span_singleton, span_singleton_generator]

theorem eq_bot_iff_generator_eq_zero (S : Submodule R M) [S.IsPrincipal] :
    S = ⊥ ↔ generator S = 0 := by rw [← @span_singleton_eq_bot R M, span_singleton_generator]

protected lemma fg {S : Submodule R M} (h : S.IsPrincipal) : S.FG :=
  ⟨{h.generator}, by simp only [Finset.coe_singleton, span_singleton_generator]⟩

-- See note [lower instance priority]
instance (priority := 100) _root_.PrincipalIdealRing.isNoetherianRing [IsPrincipalIdealRing R] :
    IsNoetherianRing R where
  noetherian S := (IsPrincipalIdealRing.principal S).fg

-- See note [lower instance priority]
instance (priority := 100) _root_.IsPrincipalIdealRing.of_isNoetherianRing_of_isBezout
    [IsNoetherianRing R] [IsBezout R] : IsPrincipalIdealRing R where
  principal S := IsBezout.isPrincipal_of_FG S (IsNoetherian.noetherian S)

end Semiring

section CommSemiring

variable [CommSemiring R] [Module R M]

theorem associated_generator_span_self [IsDomain R] (r : R) :
    Associated (generator <| Ideal.span {r}) r := by
  rw [← Ideal.span_singleton_eq_span_singleton]
  exact Ideal.span_singleton_generator _

theorem mem_iff_generator_dvd (S : Ideal R) [S.IsPrincipal] {x : R} : x ∈ S ↔ generator S ∣ x :=
  (mem_iff_eq_smul_generator S).trans (exists_congr fun a => by simp only [mul_comm, smul_eq_mul])

theorem prime_generator_of_isPrime (S : Ideal R) [S.IsPrincipal] [is_prime : S.IsPrime]
    (ne_bot : S ≠ ⊥) : Prime (generator S) :=
  ⟨fun h => ne_bot ((eq_bot_iff_generator_eq_zero S).2 h), fun h =>
    is_prime.ne_top (S.eq_top_of_isUnit_mem (generator_mem S) h), fun _ _ => by
    simpa only [← mem_iff_generator_dvd S] using is_prime.2⟩

-- Note that the converse may not hold if `ϕ` is not injective.
theorem generator_map_dvd_of_mem {N : Submodule R M} (ϕ : M →ₗ[R] R) [(N.map ϕ).IsPrincipal] {x : M}
    (hx : x ∈ N) : generator (N.map ϕ) ∣ ϕ x := by
  rw [← mem_iff_generator_dvd, Submodule.mem_map]
  exact ⟨x, hx, rfl⟩

-- Note that the converse may not hold if `ϕ` is not injective.
theorem generator_submoduleImage_dvd_of_mem {N O : Submodule R M} (hNO : N ≤ O) (ϕ : O →ₗ[R] R)
    [(ϕ.submoduleImage N).IsPrincipal] {x : M} (hx : x ∈ N) :
    generator (ϕ.submoduleImage N) ∣ ϕ ⟨x, hNO hx⟩ := by
  rw [← mem_iff_generator_dvd, LinearMap.mem_submoduleImage_of_le hNO]
  exact ⟨x, hx, rfl⟩

theorem dvd_generator_span_iff {r : R} {s : Set R} [(Ideal.span s).IsPrincipal] :
    r ∣ generator (Ideal.span s) ↔ ∀ x ∈ s, r ∣ x where
  mp h x hx := h.trans <| (mem_iff_generator_dvd _).mp (Ideal.subset_span hx)
  mpr h := have : (span R s).IsPrincipal := ‹_›
    span_induction h (dvd_zero _) (fun _ _ _ _ ↦ dvd_add) (fun _ _ _ ↦ (·.mul_left _))
      (generator_mem _)

end CommSemiring

end Submodule.IsPrincipal

namespace IsBezout

section

variable [Ring R]

instance span_pair_isPrincipal [IsBezout R] (x y : R) : (Ideal.span {x, y}).IsPrincipal := by
  classical exact isPrincipal_of_FG (Ideal.span {x, y}) ⟨{x, y}, by simp⟩

variable (x y : R) [(Ideal.span {x, y}).IsPrincipal]

/-- A choice of gcd of two elements in a Bézout domain.

Note that the choice is usually not unique. -/
noncomputable def gcd : R := Submodule.IsPrincipal.generator (Ideal.span {x, y})

theorem span_gcd : Ideal.span {gcd x y} = Ideal.span {x, y} :=
  Ideal.span_singleton_generator _

end

variable [CommRing R] (x y z : R) [(Ideal.span {x, y}).IsPrincipal]

theorem gcd_dvd_left : gcd x y ∣ x :=
  (Submodule.IsPrincipal.mem_iff_generator_dvd _).mp (Ideal.subset_span (by simp))

theorem gcd_dvd_right : gcd x y ∣ y :=
  (Submodule.IsPrincipal.mem_iff_generator_dvd _).mp (Ideal.subset_span (by simp))

variable {x y z} in
theorem dvd_gcd (hx : z ∣ x) (hy : z ∣ y) : z ∣ gcd x y := by
  rw [← Ideal.span_singleton_le_span_singleton] at hx hy ⊢
  rw [span_gcd, Ideal.span_insert, sup_le_iff]
  exact ⟨hx, hy⟩

theorem gcd_eq_sum : ∃ a b : R, a * x + b * y = gcd x y :=
  Ideal.mem_span_pair.mp (by rw [← span_gcd]; apply Ideal.subset_span; simp)

variable {x y}

theorem _root_.IsRelPrime.isCoprime (h : IsRelPrime x y) : IsCoprime x y := by
  rw [← Ideal.isCoprime_span_singleton_iff, Ideal.isCoprime_iff_sup_eq, ← Ideal.span_union,
    Set.singleton_union, ← span_gcd, Ideal.span_singleton_eq_top]
  exact h (gcd_dvd_left x y) (gcd_dvd_right x y)

theorem _root_.isRelPrime_iff_isCoprime : IsRelPrime x y ↔ IsCoprime x y :=
  ⟨IsRelPrime.isCoprime, IsCoprime.isRelPrime⟩

variable (R)

/-- Any Bézout domain is a GCD domain. This is not an instance since `GCDMonoid` contains data,
and this might not be how we would like to construct it. -/
noncomputable def toGCDDomain [IsBezout R] [IsDomain R] [DecidableEq R] : GCDMonoid R :=
  gcdMonoidOfGCD (gcd · ·) (gcd_dvd_left · ·) (gcd_dvd_right · ·) dvd_gcd

instance nonemptyGCDMonoid [IsBezout R] [IsDomain R] : Nonempty (GCDMonoid R) := by
  classical exact ⟨toGCDDomain R⟩

theorem associated_gcd_gcd [IsDomain R] [GCDMonoid R] :
    Associated (IsBezout.gcd x y) (GCDMonoid.gcd x y) :=
  gcd_greatest_associated (gcd_dvd_left _ _) (gcd_dvd_right _ _) (fun _ => dvd_gcd)

end IsBezout

namespace IsPrime

open Submodule.IsPrincipal Ideal

-- TODO -- for a non-ID one could perhaps prove that if p < q are prime then q maximal;
-- 0 isn't prime in a non-ID PIR but the Krull dimension is still <= 1.
-- The below result follows from this, but we could also use the below result to
-- prove this (quotient out by p).
theorem to_maximal_ideal [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] {S : Ideal R}
    [hpi : IsPrime S] (hS : S ≠ ⊥) : IsMaximal S :=
  isMaximal_iff.2
    ⟨(ne_top_iff_one S).1 hpi.1, by
      intro T x hST hxS hxT
      obtain ⟨z, hz⟩ := (mem_iff_generator_dvd _).1 (hST <| generator_mem S)
      cases hpi.mem_or_mem (show generator T * z ∈ S from hz ▸ generator_mem S) with
      | inl h =>
        have hTS : T ≤ S := by
          rwa [← T.span_singleton_generator, Ideal.span_le, singleton_subset_iff]
        exact (hxS <| hTS hxT).elim
      | inr h =>
        obtain ⟨y, hy⟩ := (mem_iff_generator_dvd _).1 h
        have : generator S ≠ 0 := mt (eq_bot_iff_generator_eq_zero _).2 hS
        rw [← mul_one (generator S), hy, mul_left_comm, mul_right_inj' this] at hz
        exact hz.symm ▸ T.mul_mem_right _ (generator_mem T)⟩

end IsPrime

section

open EuclideanDomain

variable [EuclideanDomain R]

theorem mod_mem_iff {S : Ideal R} {x y : R} (hy : y ∈ S) : x % y ∈ S ↔ x ∈ S :=
  ⟨fun hxy => div_add_mod x y ▸ S.add_mem (S.mul_mem_right _ hy) hxy, fun hx =>
    (mod_eq_sub_mul_div x y).symm ▸ S.sub_mem hx (S.mul_mem_right _ hy)⟩

-- see Note [lower instance priority]
instance (priority := 100) EuclideanDomain.to_principal_ideal_domain : IsPrincipalIdealRing R where
  principal S := by classical exact
    ⟨if h : { x : R | x ∈ S ∧ x ≠ 0 }.Nonempty then
        have wf : WellFounded (EuclideanDomain.r : R → R → Prop) := EuclideanDomain.r_wellFounded
        have hmin : WellFounded.min wf { x : R | x ∈ S ∧ x ≠ 0 } h ∈ S ∧
            WellFounded.min wf { x : R | x ∈ S ∧ x ≠ 0 } h ≠ 0 :=
          WellFounded.min_mem wf { x : R | x ∈ S ∧ x ≠ 0 } h
        ⟨WellFounded.min wf { x : R | x ∈ S ∧ x ≠ 0 } h,
          Submodule.ext fun x => ⟨fun hx =>
            div_add_mod x (WellFounded.min wf { x : R | x ∈ S ∧ x ≠ 0 } h) ▸
              (Ideal.mem_span_singleton.2 <| dvd_add (dvd_mul_right _ _) <| by
                have : x % WellFounded.min wf { x : R | x ∈ S ∧ x ≠ 0 } h ∉
                    { x : R | x ∈ S ∧ x ≠ 0 } :=
                  fun h₁ => WellFounded.not_lt_min wf _ h h₁ (mod_lt x hmin.2)
                have : x % WellFounded.min wf { x : R | x ∈ S ∧ x ≠ 0 } h = 0 := by
                  simp only [not_and_or, Set.mem_setOf_eq, not_ne_iff] at this
                  exact this.neg_resolve_left <| (mod_mem_iff hmin.1).2 hx
                simp [*]),
              fun hx =>
                let ⟨y, hy⟩ := Ideal.mem_span_singleton.1 hx
                hy.symm ▸ S.mul_mem_right _ hmin.1⟩⟩
      else ⟨0, Submodule.ext fun a => by
            rw [← @Submodule.bot_coe R R _ _ _, span_eq, Submodule.mem_bot]
            exact ⟨fun haS => by_contra fun ha0 => h ⟨a, ⟨haS, ha0⟩⟩,
              fun h₁ => h₁.symm ▸ S.zero_mem⟩⟩⟩

end

theorem IsField.isPrincipalIdealRing {R : Type*} [Ring R] (h : IsField R) :
    IsPrincipalIdealRing R :=
  @EuclideanDomain.to_principal_ideal_domain R (@Field.toEuclideanDomain R h.toField)

namespace PrincipalIdealRing

open IsPrincipalIdealRing

theorem isMaximal_of_irreducible [CommSemiring R] [IsPrincipalIdealRing R] {p : R}
    (hp : Irreducible p) : Ideal.IsMaximal (span R ({p} : Set R)) :=
  ⟨⟨mt Ideal.span_singleton_eq_top.1 hp.1, fun I hI => by
      rcases principal I with ⟨a, rfl⟩
      rw [Ideal.submodule_span_eq, Ideal.span_singleton_eq_top]
      rcases Ideal.span_singleton_le_span_singleton.1 (le_of_lt hI) with ⟨b, rfl⟩
      refine (of_irreducible_mul hp).resolve_right (mt (fun hb => ?_) (not_le_of_gt hI))
      rw [Ideal.submodule_span_eq, Ideal.submodule_span_eq,
        Ideal.span_singleton_le_span_singleton, IsUnit.mul_right_dvd hb]⟩⟩

variable [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

section

open scoped Classical in
/-- `factors a` is a multiset of irreducible elements whose product is `a`, up to units -/
noncomputable def factors (a : R) : Multiset R :=
  if h : a = 0 then ∅ else Classical.choose (WfDvdMonoid.exists_factors a h)

theorem factors_spec (a : R) (h : a ≠ 0) :
    (∀ b ∈ factors a, Irreducible b) ∧ Associated (factors a).prod a := by
  unfold factors; rw [dif_neg h]
  exact Classical.choose_spec (WfDvdMonoid.exists_factors a h)

theorem ne_zero_of_mem_factors {R : Type v} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {a b : R} (ha : a ≠ 0) (hb : b ∈ factors a) : b ≠ 0 :=
  Irreducible.ne_zero ((factors_spec a ha).1 b hb)

theorem mem_submonoid_of_factors_subset_of_units_subset (s : Submonoid R) {a : R} (ha : a ≠ 0)
    (hfac : ∀ b ∈ factors a, b ∈ s) (hunit : ∀ c : Rˣ, (c : R) ∈ s) : a ∈ s := by
  rcases (factors_spec a ha).2 with ⟨c, hc⟩
  rw [← hc]
  exact mul_mem (multiset_prod_mem _ hfac) (hunit _)

/-- If a `RingHom` maps all units and all factors of an element `a` into a submonoid `s`, then it
also maps `a` into that submonoid. -/
theorem ringHom_mem_submonoid_of_factors_subset_of_units_subset {R S : Type*} [CommRing R]
    [IsDomain R] [IsPrincipalIdealRing R] [NonAssocSemiring S] (f : R →+* S) (s : Submonoid S)
    (a : R) (ha : a ≠ 0) (h : ∀ b ∈ factors a, f b ∈ s) (hf : ∀ c : Rˣ, f c ∈ s) : f a ∈ s :=
  mem_submonoid_of_factors_subset_of_units_subset (s.comap f.toMonoidHom) ha h hf

-- see Note [lower instance priority]
/-- A principal ideal domain has unique factorization -/
instance (priority := 100) to_uniqueFactorizationMonoid : UniqueFactorizationMonoid R :=
  { (IsNoetherianRing.wfDvdMonoid : WfDvdMonoid R) with
    irreducible_iff_prime := irreducible_iff_prime }

end

end PrincipalIdealRing

section Surjective

open Submodule

variable {S N F : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Semiring S]
variable [Module R M] [Module R N] [FunLike F R S] [RingHomClass F R S]

theorem Submodule.IsPrincipal.map (f : M →ₗ[R] N) {S : Submodule R M}
    (hI : IsPrincipal S) : IsPrincipal (map f S) :=
  ⟨⟨f (IsPrincipal.generator S), by
      rw [← Set.image_singleton, ← map_span, span_singleton_generator]⟩⟩

theorem Submodule.IsPrincipal.of_comap (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (S : Submodule R N) [hI : IsPrincipal (S.comap f)] : IsPrincipal S := by
  rw [← Submodule.map_comap_eq_of_surjective hf S]
  exact hI.map f

theorem Submodule.IsPrincipal.map_ringHom (f : F) {I : Ideal R}
    (hI : IsPrincipal I) : IsPrincipal (Ideal.map f I) :=
  ⟨⟨f (IsPrincipal.generator I), by
      rw [Ideal.submodule_span_eq, ← Set.image_singleton, ← Ideal.map_span,
      Ideal.span_singleton_generator]⟩⟩

theorem Ideal.IsPrincipal.of_comap (f : F) (hf : Function.Surjective f) (I : Ideal S)
    [hI : IsPrincipal (I.comap f)] : IsPrincipal I := by
  rw [← map_comap_of_surjective f hf I]
  exact hI.map_ringHom f

/-- The surjective image of a principal ideal ring is again a principal ideal ring. -/
theorem IsPrincipalIdealRing.of_surjective [IsPrincipalIdealRing R] (f : F)
    (hf : Function.Surjective f) : IsPrincipalIdealRing S :=
  ⟨fun I => Ideal.IsPrincipal.of_comap f hf I⟩

theorem isPrincipalIdealRing_prod_iff :
    IsPrincipalIdealRing (R × S) ↔ IsPrincipalIdealRing R ∧ IsPrincipalIdealRing S where
  mp h := ⟨h.of_surjective (RingHom.fst R S) Prod.fst_surjective,
    h.of_surjective (RingHom.snd R S) Prod.snd_surjective⟩
  mpr := fun ⟨_, _⟩ ↦ inferInstance

theorem isPrincipalIdealRing_pi_iff {ι} [Finite ι] {R : ι → Type*} [∀ i, Semiring (R i)] :
    IsPrincipalIdealRing (Π i, R i) ↔ ∀ i, IsPrincipalIdealRing (R i) where
  mp h i := h.of_surjective (Pi.evalRingHom R i) (Function.surjective_eval _)
  mpr _ := inferInstance

end Surjective

section

open Ideal

variable [CommRing R]

section Bezout
variable [IsBezout R]

theorem isCoprime_of_dvd (x y : R) (nonzero : ¬(x = 0 ∧ y = 0))
    (H : ∀ z ∈ nonunits R, z ≠ 0 → z ∣ x → ¬z ∣ y) : IsCoprime x y :=
  (isRelPrime_of_no_nonunits_factors nonzero H).isCoprime

theorem dvd_or_isCoprime (x y : R) (h : Irreducible x) : x ∣ y ∨ IsCoprime x y :=
  h.dvd_or_isRelPrime.imp_right IsRelPrime.isCoprime

/-- See also `Irreducible.isRelPrime_iff_not_dvd`. -/
theorem Irreducible.coprime_iff_not_dvd {p n : R} (hp : Irreducible p) :
    IsCoprime p n ↔ ¬p ∣ n := by rw [← isRelPrime_iff_isCoprime, hp.isRelPrime_iff_not_dvd]

/-- See also `Irreducible.coprime_iff_not_dvd'`. -/
theorem Irreducible.dvd_iff_not_isCoprime {p n : R} (hp : Irreducible p) : p ∣ n ↔ ¬IsCoprime p n :=
  iff_not_comm.2 hp.coprime_iff_not_dvd

theorem Irreducible.coprime_pow_of_not_dvd {p a : R} (m : ℕ) (hp : Irreducible p) (h : ¬p ∣ a) :
    IsCoprime a (p ^ m) :=
  (hp.coprime_iff_not_dvd.2 h).symm.pow_right

theorem Irreducible.isCoprime_or_dvd {p : R} (hp : Irreducible p) (i : R) : IsCoprime p i ∨ p ∣ i :=
  (_root_.em _).imp_right hp.dvd_iff_not_isCoprime.2

variable [IsDomain R]

section GCD
variable [GCDMonoid R]

theorem IsBezout.span_gcd_eq_span_gcd (x y : R) :
    span {GCDMonoid.gcd x y} = span {IsBezout.gcd x y} := by
  rw [Ideal.span_singleton_eq_span_singleton]
  exact associated_of_dvd_dvd
    (IsBezout.dvd_gcd (GCDMonoid.gcd_dvd_left _ _) <| GCDMonoid.gcd_dvd_right _ _)
    (GCDMonoid.dvd_gcd (IsBezout.gcd_dvd_left _ _) <| IsBezout.gcd_dvd_right _ _)

theorem span_gcd (x y : R) : span {gcd x y} = span {x, y} := by
  rw [← IsBezout.span_gcd, IsBezout.span_gcd_eq_span_gcd]

theorem gcd_dvd_iff_exists (a b : R) {z} : gcd a b ∣ z ↔ ∃ x y, z = a * x + b * y := by
  simp_rw [mul_comm a, mul_comm b, @eq_comm _ z, ← Ideal.mem_span_pair, ← span_gcd,
    Ideal.mem_span_singleton]

/-- **Bézout's lemma** -/
theorem exists_gcd_eq_mul_add_mul (a b : R) : ∃ x y, gcd a b = a * x + b * y := by
  rw [← gcd_dvd_iff_exists]

theorem gcd_isUnit_iff (x y : R) : IsUnit (gcd x y) ↔ IsCoprime x y := by
  rw [IsCoprime, ← Ideal.mem_span_pair, ← span_gcd, ← span_singleton_eq_top, eq_top_iff_one]

end GCD

theorem Prime.coprime_iff_not_dvd {p n : R} (hp : Prime p) : IsCoprime p n ↔ ¬p ∣ n :=
  hp.irreducible.coprime_iff_not_dvd

theorem exists_associated_pow_of_mul_eq_pow' {a b c : R} (hab : IsCoprime a b) {k : ℕ}
    (h : a * b = c ^ k) : ∃ d : R, Associated (d ^ k) a := by
  classical
  letI := IsBezout.toGCDDomain R
  exact exists_associated_pow_of_mul_eq_pow ((gcd_isUnit_iff _ _).mpr hab) h

theorem exists_associated_pow_of_associated_pow_mul {a b c : R} (hab : IsCoprime a b) {k : ℕ}
    (h : Associated (c ^ k) (a * b)) : ∃ d : R, Associated (d ^ k) a := by
  obtain ⟨u, hu⟩ := h.symm
  exact exists_associated_pow_of_mul_eq_pow'
    ((isCoprime_mul_unit_right_right u.isUnit a b).mpr hab) <| mul_assoc a _ _ ▸ hu

end Bezout

variable [IsDomain R] [IsPrincipalIdealRing R]

theorem isCoprime_of_irreducible_dvd {x y : R} (nonzero : ¬(x = 0 ∧ y = 0))
    (H : ∀ z : R, Irreducible z → z ∣ x → ¬z ∣ y) : IsCoprime x y :=
  (WfDvdMonoid.isRelPrime_of_no_irreducible_factors nonzero H).isCoprime

theorem isCoprime_of_prime_dvd {x y : R} (nonzero : ¬(x = 0 ∧ y = 0))
    (H : ∀ z : R, Prime z → z ∣ x → ¬z ∣ y) : IsCoprime x y :=
  isCoprime_of_irreducible_dvd nonzero fun z zi ↦ H z zi.prime

end

section PrincipalOfPrime

namespace Ideal

variable (R) [Semiring R]

/-- `nonPrincipals R` is the set of all ideals of `R` that are not principal ideals. -/
abbrev nonPrincipals := { I : Ideal R | ¬I.IsPrincipal }

variable {R}

theorem nonPrincipals_eq_empty_iff : nonPrincipals R = ∅ ↔ IsPrincipalIdealRing R := by
  simp [Set.eq_empty_iff_forall_notMem, isPrincipalIdealRing_iff]

/-- Any chain in the set of non-principal ideals has an upper bound which is non-principal.
(Namely, the union of the chain is such an upper bound.)

If you want the existence of a maximal non-principal ideal see
`Ideal.exists_maximal_not_isPrincipal`. -/
theorem nonPrincipals_zorn (hR : ¬IsPrincipalIdealRing R) (c : Set (Ideal R))
    (hs : c ⊆ nonPrincipals R) (hchain : IsChain (· ≤ ·) c) :
    ∃ I ∈ nonPrincipals R, ∀ J ∈ c, J ≤ I := by
  by_cases H : c.Nonempty
  · obtain ⟨K, hKmem⟩ := Set.nonempty_def.1 H
    refine ⟨sSup c, fun ⟨x, hx⟩ ↦ ?_, fun _ ↦ le_sSup⟩
    have hxmem : x ∈ sSup c := hx.symm ▸ Submodule.mem_span_singleton_self x
    obtain ⟨J, hJc, hxJ⟩ := (Submodule.mem_sSup_of_directed ⟨K, hKmem⟩ hchain.directedOn).1 hxmem
    have hsSupJ : sSup c = J := le_antisymm (by simp [hx, Ideal.span_le, hxJ]) (le_sSup hJc)
    exact hs hJc ⟨hsSupJ ▸ ⟨x, hx⟩⟩
  · simpa [Set.not_nonempty_iff_eq_empty.1 H, isPrincipalIdealRing_iff] using hR

theorem exists_maximal_not_isPrincipal (hR : ¬IsPrincipalIdealRing R) :
    ∃ I : Ideal R, Maximal (¬·.IsPrincipal) I :=
  zorn_le₀ _ (nonPrincipals_zorn hR)

end Ideal

end PrincipalOfPrime

section PrincipalOfPrime_old

variable (R) [CommRing R]

/-- `nonPrincipals R` is the set of all ideals of `R` that are not principal ideals. -/
@[deprecated Ideal.nonPrincipals (since := "2025-09-30")]
def nonPrincipals :=
  { I : Ideal R | ¬I.IsPrincipal }

@[deprecated "Not necessary anymore since Ideal.nonPrincipals is an abrev." (since := "2025-09-30")]
theorem nonPrincipals_def {I : Ideal R} : I ∈ { I : Ideal R | ¬I.IsPrincipal } ↔ ¬I.IsPrincipal :=
  Iff.rfl

variable {R}

@[deprecated Ideal.nonPrincipals_eq_empty_iff (since := "2025-09-30")]
theorem nonPrincipals_eq_empty_iff :
    { I : Ideal R | ¬I.IsPrincipal } = ∅ ↔ IsPrincipalIdealRing R := by
  simp [Set.eq_empty_iff_forall_notMem, isPrincipalIdealRing_iff]

/-- Any chain in the set of non-principal ideals has an upper bound which is non-principal.
(Namely, the union of the chain is such an upper bound.)
-/
@[deprecated Ideal.nonPrincipals_zorn (since := "2025-09-30")]
theorem nonPrincipals_zorn (c : Set (Ideal R)) (hs : c ⊆ { I : Ideal R | ¬I.IsPrincipal })
    (hchain : IsChain (· ≤ ·) c) {K : Ideal R} (hKmem : K ∈ c) :
    ∃ I ∈ { I : Ideal R | ¬I.IsPrincipal }, ∀ J ∈ c, J ≤ I := by
  refine ⟨sSup c, ?_, fun J hJ => le_sSup hJ⟩
  rintro ⟨x, hx⟩
  have hxmem : x ∈ sSup c := hx.symm ▸ Submodule.mem_span_singleton_self x
  obtain ⟨J, hJc, hxJ⟩ := (Submodule.mem_sSup_of_directed ⟨K, hKmem⟩ hchain.directedOn).1 hxmem
  have hsSupJ : sSup c = J := le_antisymm (by simp [hx, Ideal.span_le, hxJ]) (le_sSup hJc)
  specialize hs hJc
  rw [← hsSupJ, hx] at hs
  exact hs ⟨⟨x, rfl⟩⟩

end PrincipalOfPrime_old
