/-
Copyright (c) 2018 Mario Carneiro, Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Buzzard
-/
import Mathlib.Algebra.Order.PartialSups
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.Ideal.Prod

/-!
# Noetherian rings and modules

The following are equivalent for a module M over a ring R:
1. Every increasing chain of submodules M₁ ⊆ M₂ ⊆ M₃ ⊆ ⋯ eventually stabilises.
2. Every submodule is finitely generated.

A module satisfying these equivalent conditions is said to be a *Noetherian* R-module.
A ring is a *Noetherian ring* if it is Noetherian as a module over itself.

(Note that we do not assume yet that our rings are commutative,
so perhaps this should be called "left Noetherian".
To avoid cumbersome names once we specialize to the commutative case,
we don't make this explicit in the declaration names.)

## Main definitions

Let `R` be a ring and let `M` and `P` be `R`-modules. Let `N` be an `R`-submodule of `M`.

* `IsNoetherian R M` is the proposition that `M` is a Noetherian `R`-module. It is a class,
  implemented as the predicate that all `R`-submodules of `M` are finitely generated.

## Main statements

* `isNoetherian_iff` is the theorem that an R-module M is Noetherian iff `>` is well-founded on
  `Submodule R M`.

Note that the Hilbert basis theorem, that if a commutative ring R is Noetherian then so is R[X],
is proved in `RingTheory.Polynomial`.

## References

* [M. F. Atiyah and I. G. Macdonald, *Introduction to commutative algebra*][atiyah-macdonald]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1967]

## Tags

Noetherian, noetherian, Noetherian ring, Noetherian module, noetherian ring, noetherian module

-/

assert_not_exists Matrix

open Set Pointwise

section

variable {R M P : Type*}
variable [Semiring R] [AddCommMonoid M] [AddCommMonoid P]
variable [Module R M] [Module R P]

open IsNoetherian

variable (M) in
theorem isNoetherian_of_surjective (f : M →ₗ[R] P) (hf : LinearMap.range f = ⊤) [IsNoetherian R M] :
    IsNoetherian R P :=
  ⟨fun s =>
    have : (s.comap f).map f = s := Submodule.map_comap_eq_self <| hf.symm ▸ le_top
    this ▸ (noetherian _).map _⟩

instance isNoetherian_range (f : M →ₗ[R] P) [IsNoetherian R M] :
    IsNoetherian R (LinearMap.range f) :=
  isNoetherian_of_surjective _ _ f.range_rangeRestrict

instance isNoetherian_quotient {A M : Type*} [Ring A] [AddCommGroup M] [SMul R A] [Module R M]
    [Module A M] [IsScalarTower R A M] (N : Submodule A M) [IsNoetherian R M] :
    IsNoetherian R (M ⧸ N) :=
  isNoetherian_of_surjective M ((Submodule.mkQ N).restrictScalars R) <|
    LinearMap.range_eq_top.mpr N.mkQ_surjective

theorem isNoetherian_of_linearEquiv (f : M ≃ₗ[R] P) [IsNoetherian R M] : IsNoetherian R P :=
  isNoetherian_of_surjective _ f.toLinearMap f.range

theorem LinearEquiv.isNoetherian_iff (f : M ≃ₗ[R] P) : IsNoetherian R M ↔ IsNoetherian R P :=
  ⟨fun _ ↦ isNoetherian_of_linearEquiv f, fun _ ↦ isNoetherian_of_linearEquiv f.symm⟩

theorem isNoetherian_top_iff : IsNoetherian R (⊤ : Submodule R M) ↔ IsNoetherian R M :=
  Submodule.topEquiv.isNoetherian_iff

theorem isNoetherian_of_injective [IsNoetherian R P] (f : M →ₗ[R] P) (hf : Function.Injective f) :
    IsNoetherian R M :=
  isNoetherian_of_linearEquiv (LinearEquiv.ofInjective f hf).symm

theorem fg_of_injective [IsNoetherian R P] {N : Submodule R M} (f : M →ₗ[R] P)
    (hf : Function.Injective f) : N.FG :=
  haveI := isNoetherian_of_injective f hf
  IsNoetherian.noetherian N

end

namespace Module

variable {R M N : Type*}
variable [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
variable (R M)

-- see Note [lower instance priority]
instance (priority := 80) _root_.isNoetherian_of_finite [Finite M] : IsNoetherian R M :=
  ⟨fun s => ⟨(s : Set M).toFinite.toFinset, by rw [Set.Finite.coe_toFinset, Submodule.span_eq]⟩⟩

-- see Note [lower instance priority]
instance (priority := 100) IsNoetherian.finite [IsNoetherian R M] : Module.Finite R M :=
  ⟨IsNoetherian.noetherian ⊤⟩

instance {R₁ S : Type*} [CommSemiring R₁] [Semiring S] [Algebra R₁ S]
    [IsNoetherian R₁ S] (I : Ideal S) : Module.Finite R₁ I :=
  IsNoetherian.finite R₁ ((I : Submodule S S).restrictScalars R₁)

variable {R M}

theorem Finite.of_injective [IsNoetherian R N] (f : M →ₗ[R] N) (hf : Function.Injective f) :
    Module.Finite R M :=
  ⟨fg_of_injective f hf⟩

end Module

section

variable {R M N P : Type*}
variable [Ring R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
variable [Module R M] [Module R N] [Module R P]

open IsNoetherian

theorem isNoetherian_of_ker_bot [IsNoetherian R P] (f : M →ₗ[R] P) (hf : LinearMap.ker f = ⊥) :
    IsNoetherian R M :=
  isNoetherian_of_linearEquiv (LinearEquiv.ofInjective f <| LinearMap.ker_eq_bot.mp hf).symm

theorem fg_of_ker_bot [IsNoetherian R P] {N : Submodule R M} (f : M →ₗ[R] P)
    (hf : LinearMap.ker f = ⊥) : N.FG :=
  haveI := isNoetherian_of_ker_bot f hf
  IsNoetherian.noetherian N

-- False over a semiring: ℕ is a Noetherian ℕ-module but ℕ × ℕ is not.
instance isNoetherian_prod [IsNoetherian R M] [IsNoetherian R P] : IsNoetherian R (M × P) :=
  ⟨fun s =>
    Submodule.fg_of_fg_map_of_fg_inf_ker (LinearMap.snd R M P) (noetherian _) <|
      have : s ⊓ LinearMap.ker (LinearMap.snd R M P) ≤ LinearMap.range (LinearMap.inl R M P) :=
        fun x ⟨_, hx2⟩ => ⟨x.1, Prod.ext rfl <| Eq.symm <| LinearMap.mem_ker.1 hx2⟩
      Submodule.map_comap_eq_self this ▸ (noetherian _).map _⟩

instance isNoetherian_sup (M₁ M₂ : Submodule R P) [IsNoetherian R M₁] [IsNoetherian R M₂] :
    IsNoetherian R ↥(M₁ ⊔ M₂) := by
  have := isNoetherian_range (M₁.subtype.coprod M₂.subtype)
  rwa [LinearMap.range_coprod, Submodule.range_subtype, Submodule.range_subtype] at this

variable {ι : Type*} [Finite ι]

instance isNoetherian_pi :
    ∀ {M : ι → Type*} [∀ i, AddCommGroup (M i)]
      [∀ i, Module R (M i)] [∀ i, IsNoetherian R (M i)], IsNoetherian R (Π i, M i) := by
  apply Finite.induction_empty_option _ _ _ ι
  · exact fun e h ↦ isNoetherian_of_linearEquiv (LinearEquiv.piCongrLeft R _ e)
  · infer_instance
  · exact fun ih ↦ isNoetherian_of_linearEquiv (LinearEquiv.piOptionEquivProd R).symm

/-- A version of `isNoetherian_pi` for non-dependent functions. We need this instance because
sometimes Lean fails to apply the dependent version in non-dependent settings (e.g., it fails to
prove that `ι → ℝ` is finite dimensional over `ℝ`). -/
instance isNoetherian_pi' [IsNoetherian R M] : IsNoetherian R (ι → M) :=
  isNoetherian_pi

instance isNoetherian_iSup :
    ∀ {M : ι → Submodule R P} [∀ i, IsNoetherian R (M i)], IsNoetherian R ↥(⨆ i, M i) := by
  apply Finite.induction_empty_option _ _ _ ι
  · intro _ _ e h _ _; rw [← e.iSup_comp]; apply h
  · intros; rw [iSup_of_empty]; infer_instance
  · intro _ _ ih _ _; rw [iSup_option]; infer_instance

/-- If the first and final modules in an exact sequence are Noetherian,
  then the middle module is also Noetherian. -/
theorem isNoetherian_of_range_eq_ker [IsNoetherian R M] [IsNoetherian R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (h : LinearMap.range f = LinearMap.ker g) :
    IsNoetherian R N :=
  isNoetherian_mk <|
    wellFounded_gt_exact_sequence
      (LinearMap.range f)
      (Submodule.map ((LinearMap.ker f).liftQ f le_rfl))
      (Submodule.comap ((LinearMap.ker f).liftQ f le_rfl))
      (Submodule.comap g.rangeRestrict) (Submodule.map g.rangeRestrict)
      (Submodule.gciMapComap <| LinearMap.ker_eq_bot.mp <| Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)
      (Submodule.giMapComap g.surjective_rangeRestrict)
      (by simp [Submodule.map_comap_eq, inf_comm, Submodule.range_liftQ])
      (by simp [Submodule.comap_map_eq, h])

theorem isNoetherian_iff_submodule_quotient (S : Submodule R P) :
    IsNoetherian R P ↔ IsNoetherian R S ∧ IsNoetherian R (P ⧸ S) := by
  refine ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ ↦ ?_⟩
  apply isNoetherian_of_range_eq_ker S.subtype S.mkQ
  rw [Submodule.ker_mkQ, Submodule.range_subtype]

end

section CommRing

variable (R M N : Type*) [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
  [IsNoetherian R M] [Module.Finite R N]

instance isNoetherian_linearMap_pi {ι : Type*} [Finite ι] : IsNoetherian R ((ι → R) →ₗ[R] M) :=
  let _i : Fintype ι := Fintype.ofFinite ι; isNoetherian_of_linearEquiv (Module.piEquiv ι R M)

instance isNoetherian_linearMap : IsNoetherian R (N →ₗ[R] M) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R N
  let g : (N →ₗ[R] M) →ₗ[R] (Fin n → R) →ₗ[R] M := (LinearMap.llcomp R (Fin n → R) N M).flip f
  exact isNoetherian_of_injective g hf.injective_linearMapComp_right

end CommRing

open IsNoetherian Submodule Function

section

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- If `∀ I > J, P I` implies `P J`, then `P` holds for all submodules. -/
theorem IsNoetherian.induction [IsNoetherian R M] {P : Submodule R M → Prop}
    (hgt : ∀ I, (∀ J > I, P J) → P I) (I : Submodule R M) : P I :=
  IsWellFounded.induction _ I hgt

theorem LinearMap.isNoetherian_iff_of_bijective {S P} [Semiring S] [AddCommMonoid P] [Module S P]
    {σ : R →+* S} [RingHomSurjective σ] (l : M →ₛₗ[σ] P) (hl : Function.Bijective l) :
    IsNoetherian R M ↔ IsNoetherian S P := by
  simp_rw [isNoetherian_iff']
  let e := Submodule.orderIsoMapComapOfBijective l hl
  exact ⟨fun _ ↦ e.symm.strictMono.wellFoundedGT, fun _ ↦ e.strictMono.wellFoundedGT⟩

end

section

variable {R M N P : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [IsNoetherian R M]

lemma Submodule.finite_ne_bot_of_iSupIndep {ι : Type*} {N : ι → Submodule R M}
    (h : iSupIndep N) :
    Set.Finite {i | N i ≠ ⊥} :=
  WellFoundedGT.finite_ne_bot_of_iSupIndep h

/-- A linearly-independent family of vectors in a module over a non-trivial ring must be finite if
the module is Noetherian. -/
theorem LinearIndependent.finite_of_isNoetherian [Nontrivial R] {ι} {v : ι → M}
    (hv : LinearIndependent R v) : Finite ι := by
  refine WellFoundedGT.finite_of_iSupIndep
    hv.iSupIndep_span_singleton
    fun i contra => ?_
  apply hv.ne_zero i
  have : v i ∈ R ∙ v i := Submodule.mem_span_singleton_self (v i)
  rwa [contra, Submodule.mem_bot] at this

theorem LinearIndependent.set_finite_of_isNoetherian [Nontrivial R] {s : Set M}
    (hi : LinearIndependent R ((↑) : s → M)) : s.Finite :=
  @Set.toFinite _ _ hi.finite_of_isNoetherian

/-- A sequence `f` of submodules of a noetherian module,
with `f (n+1)` disjoint from the supremum of `f 0`, ..., `f n`,
is eventually zero. -/
theorem IsNoetherian.disjoint_partialSups_eventually_bot
    (f : ℕ → Submodule R M) (h : ∀ n, Disjoint (partialSups f n) (f (n + 1))) :
    ∃ n : ℕ, ∀ m, n ≤ m → f m = ⊥ := by
  -- A little off-by-one cleanup first:
  suffices t : ∃ n : ℕ, ∀ m, n ≤ m → f (m + 1) = ⊥ by
    obtain ⟨n, w⟩ := t
    use n + 1
    rintro (_ | m) p
    · cases p
    · apply w
      exact Nat.succ_le_succ_iff.mp p
  obtain ⟨n, w⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance (partialSups f)
  refine ⟨n, fun m p ↦ (h m).eq_bot_of_ge <| sup_eq_left.mp ?_⟩
  simpa only [partialSups_add_one] using (w (m + 1) <| le_add_right p).symm.trans <| w m p

end

-- see Note [lower instance priority]
/-- Modules over the trivial ring are Noetherian. -/
instance (priority := 100) isNoetherian_of_subsingleton (R M) [Subsingleton R] [Semiring R]
    [AddCommMonoid M] [Module R M] : IsNoetherian R M :=
  haveI := Module.subsingleton R M
  isNoetherian_of_finite R M

theorem isNoetherian_of_submodule_of_noetherian (R M) [Semiring R] [AddCommMonoid M] [Module R M]
    (N : Submodule R M) (h : IsNoetherian R M) : IsNoetherian R N :=
  isNoetherian_mk ⟨OrderEmbedding.wellFounded (Submodule.MapSubtype.orderEmbedding N).dual h.wf⟩

/-- If `M / S / R` is a scalar tower, and `M / R` is Noetherian, then `M / S` is
also noetherian. -/
theorem isNoetherian_of_tower (R) {S M} [Semiring R] [Semiring S] [AddCommMonoid M] [SMul R S]
    [Module S M] [Module R M] [IsScalarTower R S M] (h : IsNoetherian R M) : IsNoetherian S M :=
  isNoetherian_mk ⟨(Submodule.restrictScalarsEmbedding R S M).dual.wellFounded h.wf⟩

instance isNoetherian_of_isNoetherianRing_of_finite (R M : Type*)
    [Ring R] [AddCommGroup M] [Module R M] [IsNoetherianRing R] [Module.Finite R M] :
    IsNoetherian R M :=
  have ⟨_, _, h⟩ := Module.Finite.exists_fin' R M
  isNoetherian_of_surjective _ _ (LinearMap.range_eq_top.mpr h)

theorem isNoetherian_of_fg_of_noetherian {R M} [Ring R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) [I : IsNoetherianRing R] (hN : N.FG) : IsNoetherian R N := by
  rw [← Module.Finite.iff_fg] at hN; infer_instance

/-- In a module over a Noetherian ring, the submodule generated by finitely many vectors is
Noetherian. -/
theorem isNoetherian_span_of_finite (R) {M} [Ring R] [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] {A : Set M} (hA : A.Finite) : IsNoetherian R (Submodule.span R A) :=
  isNoetherian_of_fg_of_noetherian _ (Submodule.fg_def.mpr ⟨A, hA, rfl⟩)

theorem IsNoetherianRing.of_finite (R S) [Ring R] [Ring S] [Module R S] [IsScalarTower R S S]
    [IsNoetherianRing R] [Module.Finite R S] : IsNoetherianRing S :=
  isNoetherian_of_tower R inferInstance

theorem isNoetherianRing_of_surjective (R) [Semiring R] (S) [Semiring S] (f : R →+* S)
    (hf : Function.Surjective f) [H : IsNoetherianRing R] : IsNoetherianRing S :=
  isNoetherian_mk ⟨OrderEmbedding.wellFounded (Ideal.orderEmbeddingOfSurjective f hf).dual H.wf⟩

instance isNoetherianRing_rangeS {R} [Semiring R] {S} [Semiring S] (f : R →+* S)
    [IsNoetherianRing R] : IsNoetherianRing f.rangeS :=
  isNoetherianRing_of_surjective R f.rangeS f.rangeSRestrict f.rangeSRestrict_surjective

instance isNoetherianRing_range {R} [Ring R] {S} [Ring S] (f : R →+* S)
    [IsNoetherianRing R] : IsNoetherianRing f.range :=
  isNoetherianRing_rangeS f

theorem isNoetherianRing_of_ringEquiv (R) [Semiring R] {S} [Semiring S] (f : R ≃+* S)
    [IsNoetherianRing R] : IsNoetherianRing S :=
  isNoetherianRing_of_surjective R S f.toRingHom f.toEquiv.surjective

instance {R S} [Semiring R] [Semiring S] [IsNoetherianRing R] [IsNoetherianRing S] :
    IsNoetherianRing (R × S) := by
  rw [IsNoetherianRing, isNoetherian_iff'] at *
  exact Ideal.idealProdEquiv.toOrderEmbedding.wellFoundedGT

instance {ι} [Finite ι] : ∀ {R : ι → Type*} [Π i, Semiring (R i)] [∀ i, IsNoetherianRing (R i)],
    IsNoetherianRing (Π i, R i) := by
  apply Finite.induction_empty_option _ _ _ ι
  · exact fun e h ↦ isNoetherianRing_of_ringEquiv _ (.piCongrLeft _ e)
  · infer_instance
  · exact fun ih ↦ isNoetherianRing_of_ringEquiv _ (.symm .piOptionEquivProd)
