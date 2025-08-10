/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Data.SetLike.Fintype
import Mathlib.Order.Filter.EventuallyConst
import Mathlib.RingTheory.Ideal.Prod
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Jacobson.Semiprimary
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Spectrum.Maximal.Basic
import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# Artinian rings and modules

A module satisfying these equivalent conditions is said to be an *Artinian* R-module
if every decreasing chain of submodules is eventually constant, or equivalently,
if the relation `<` on submodules is well founded.

A ring is said to be left (or right) Artinian if it is Artinian as a left (or right) module over
itself, or simply Artinian if it is both left and right Artinian.

## Main definitions

Let `R` be a ring and let `M` and `P` be `R`-modules. Let `N` be an `R`-submodule of `M`.

* `IsArtinian R M` is the proposition that `M` is an Artinian `R`-module. It is a class,
  implemented as the predicate that the `<` relation on submodules is well founded.
* `IsArtinianRing R` is the proposition that `R` is a left Artinian ring.

## Main results

* `IsArtinianRing.primeSpectrum_finite`, `IsArtinianRing.isMaximal_of_isPrime`: there are only
  finitely prime ideals in a commutative artinian ring, and each of them is maximal.

* `IsArtinianRing.equivPi`: a reduced commutative artinian ring `R` is isomorphic to a finite
  product of fields (and therefore is a semisimple ring and a decomposition monoid; moreover
  `R[X]` is also a decomposition monoid).

* `IsArtinian.isSemisimpleModule_iff_jacobson`: an Artinian module is semisimple
  iff its Jacobson radical is zero.

* `instIsSemiprimaryRingOfIsArtinianRing`: an Artinian ring `R` is semiprimary, in particular
  the Jacobson radical of `R` is a nilpotent ideal (`IsArtinianRing.isNilpotent_jacobson_bot`).

## References

* [M. F. Atiyah and I. G. Macdonald, *Introduction to commutative algebra*][atiyah-macdonald]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1967]

## Tags

Artinian, artinian, Artinian ring, Artinian module, artinian ring, artinian module

-/

open Set Filter Pointwise

/-- `IsArtinian R M` is the proposition that `M` is an Artinian `R`-module,
implemented as the well-foundedness of submodule inclusion. -/
abbrev IsArtinian (R M) [Semiring R] [AddCommMonoid M] [Module R M] : Prop :=
  WellFoundedLT (Submodule R M)

theorem isArtinian_iff (R M) [Semiring R] [AddCommMonoid M] [Module R M] : IsArtinian R M ↔
    WellFounded (· < · : Submodule R M → Submodule R M → Prop) :=
  isWellFounded_iff _ _

section Semiring

variable {R M P N : Type*}
variable [Semiring R] [AddCommMonoid M] [AddCommMonoid P] [AddCommMonoid N]
variable [Module R M] [Module R P] [Module R N]

theorem LinearMap.isArtinian_iff_of_bijective {S P} [Semiring S] [AddCommMonoid P] [Module S P]
    {σ : R →+* S} [RingHomSurjective σ] (l : M →ₛₗ[σ] P) (hl : Function.Bijective l) :
    IsArtinian R M ↔ IsArtinian S P :=
  let e := Submodule.orderIsoMapComapOfBijective l hl
  ⟨fun _ ↦ e.symm.strictMono.wellFoundedLT, fun _ ↦ e.strictMono.wellFoundedLT⟩

theorem isArtinian_of_injective (f : M →ₗ[R] P) (h : Function.Injective f) [IsArtinian R P] :
    IsArtinian R M :=
  ⟨Subrelation.wf
    (fun {A B} hAB => show A.map f < B.map f from Submodule.map_strictMono_of_injective h hAB)
    (InvImage.wf (Submodule.map f) IsWellFounded.wf)⟩

instance isArtinian_submodule' [IsArtinian R M] (N : Submodule R M) : IsArtinian R N :=
  isArtinian_of_injective N.subtype Subtype.val_injective

theorem isArtinian_of_le {s t : Submodule R M} [IsArtinian R t] (h : s ≤ t) : IsArtinian R s :=
  isArtinian_of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)

variable (M) in
theorem isArtinian_of_surjective (f : M →ₗ[R] P) (hf : Function.Surjective f) [IsArtinian R M] :
    IsArtinian R P :=
  ⟨Subrelation.wf
    (fun {A B} hAB =>
      show A.comap f < B.comap f from Submodule.comap_strictMono_of_surjective hf hAB)
    (InvImage.wf (Submodule.comap f) IsWellFounded.wf)⟩

/--
If `M` is an Artinian `R` module, and `S` is an `R`-algebra with a surjective
algebra map, then `M` is an Artinian `S` module.
-/
theorem isArtinian_of_surjective_algebraMap {S : Type*} [CommSemiring S] [Algebra S R]
    [Module S M] [IsArtinian R M] [IsScalarTower S R M]
    (H : Function.Surjective (algebraMap S R)) : IsArtinian S M := by
  apply (OrderEmbedding.wellFoundedLT (β := Submodule R M))
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro N
    refine {toAddSubmonoid := N.toAddSubmonoid, smul_mem' := ?_}
    intro c x hx
    obtain ⟨r, rfl⟩ := H c
    suffices r • x ∈ N by simpa [Algebra.algebraMap_eq_smul_one, smul_assoc]
    apply N.smul_mem _ hx
  · intro N1 N2 h
    rwa [Submodule.ext_iff] at h ⊢
  · intro N1 N2
    rfl

instance isArtinian_range (f : M →ₗ[R] P) [IsArtinian R M] : IsArtinian R (LinearMap.range f) :=
  isArtinian_of_surjective _ _ f.surjective_rangeRestrict

theorem isArtinian_of_linearEquiv (f : M ≃ₗ[R] P) [IsArtinian R M] : IsArtinian R P :=
  isArtinian_of_surjective _ f.toLinearMap f.toEquiv.surjective

theorem LinearEquiv.isArtinian_iff (f : M ≃ₗ[R] P) : IsArtinian R M ↔ IsArtinian R P :=
  ⟨fun _ ↦ isArtinian_of_linearEquiv f, fun _ ↦ isArtinian_of_linearEquiv f.symm⟩

-- This was previously a global instance,
-- but it doesn't appear to be used and has been implicated in slow typeclass resolutions.
lemma isArtinian_of_finite [Finite M] : IsArtinian R M :=
  ⟨Finite.wellFounded_of_trans_of_irrefl _⟩

-- Porting note: elab_as_elim can only be global and cannot be changed on an imported decl
-- attribute [local elab_as_elim] Finite.induction_empty_option

open Submodule

theorem IsArtinian.finite_of_linearIndependent [Nontrivial R] [h : IsArtinian R M] {s : Set M}
    (hs : LinearIndependent R ((↑) : s → M)) : s.Finite := by
  refine by_contradiction fun hf ↦ (RelEmbedding.wellFounded_iff_no_descending_seq.1 h.wf).elim' ?_
  have f : ℕ ↪ s := Set.Infinite.natEmbedding s hf
  have : ∀ n, (↑) ∘ f '' { m | n ≤ m } ⊆ s := by
    rintro n x ⟨y, _, rfl⟩
    exact (f y).2
  have : ∀ a b : ℕ, a ≤ b ↔
      span R (Subtype.val ∘ f '' { m | b ≤ m }) ≤ span R (Subtype.val ∘ f '' { m | a ≤ m }) := by
    intro a b
    rw [span_le_span_iff hs (this b) (this a),
      Set.image_subset_image_iff (Subtype.coe_injective.comp f.injective), Set.subset_def]
    simp only [Set.mem_setOf_eq]
    exact ⟨fun hab x ↦ hab.trans, (· _ le_rfl)⟩
  exact ⟨⟨fun n ↦ span R (Subtype.val ∘ f '' { m | n ≤ m }), fun x y ↦ by
    rw [le_antisymm_iff, ← this y x, ← this x y]
    exact fun ⟨h₁, h₂⟩ ↦ le_antisymm_iff.2 ⟨h₂, h₁⟩⟩, by
    intro a b
    conv_rhs => rw [GT.gt, lt_iff_le_not_ge, this, this, ← lt_iff_le_not_ge]
    rfl⟩

/-- A module is Artinian iff every nonempty set of submodules has a minimal submodule among them. -/
theorem set_has_minimal_iff_artinian :
    (∀ a : Set <| Submodule R M, a.Nonempty → ∃ M' ∈ a, ∀ I ∈ a, ¬I < M') ↔ IsArtinian R M := by
  rw [isArtinian_iff, WellFounded.wellFounded_iff_has_min]

theorem IsArtinian.set_has_minimal [IsArtinian R M] (a : Set <| Submodule R M) (ha : a.Nonempty) :
    ∃ M' ∈ a, ∀ I ∈ a, ¬I < M' :=
  set_has_minimal_iff_artinian.mpr ‹_› a ha

/-- A module is Artinian iff every decreasing chain of submodules stabilizes. -/
theorem monotone_stabilizes_iff_artinian :
    (∀ f : ℕ →o (Submodule R M)ᵒᵈ, ∃ n, ∀ m, n ≤ m → f n = f m) ↔ IsArtinian R M :=
  wellFoundedGT_iff_monotone_chain_condition.symm

namespace IsArtinian

variable [IsArtinian R M]

theorem monotone_stabilizes (f : ℕ →o (Submodule R M)ᵒᵈ) : ∃ n, ∀ m, n ≤ m → f n = f m :=
  monotone_stabilizes_iff_artinian.mpr ‹_› f

theorem eventuallyConst_of_isArtinian (f : ℕ →o (Submodule R M)ᵒᵈ) :
    atTop.EventuallyConst f := by
  simp_rw [eventuallyConst_atTop, eq_comm]
  exact monotone_stabilizes f

/-- If `∀ I > J, P I` implies `P J`, then `P` holds for all submodules. -/
theorem induction {P : Submodule R M → Prop} (hgt : ∀ I, (∀ J < I, P J) → P I) (I : Submodule R M) :
    P I :=
  WellFoundedLT.induction I hgt

open Function

/-- Any injective endomorphism of an Artinian module is surjective. -/
theorem surjective_of_injective_endomorphism (f : M →ₗ[R] M) (s : Injective f) : Surjective f := by
  have h := ‹IsArtinian R M›; contrapose! h
  rw [IsArtinian, WellFoundedLT, isWellFounded_iff]
  refine (RelEmbedding.natGT (LinearMap.range <| f ^ ·) ?_).not_wellFounded_of_decreasing_seq
  intro n
  simp_rw [pow_succ, Module.End.mul_eq_comp, LinearMap.range_comp, ← Submodule.map_top (f ^ n)]
  refine Submodule.map_strictMono_of_injective (Module.End.iterate_injective s n) (Ne.lt_top ?_)
  rwa [Ne, LinearMap.range_eq_top]

/-- Any injective endomorphism of an Artinian module is bijective. -/
theorem bijective_of_injective_endomorphism (f : M →ₗ[R] M) (s : Injective f) : Bijective f :=
  ⟨s, surjective_of_injective_endomorphism f s⟩

/-- A sequence `f` of submodules of an artinian module,
with the supremum `f (n+1)` and the infimum of `f 0`, ..., `f n` being ⊤,
is eventually ⊤. -/
theorem disjoint_partial_infs_eventually_top (f : ℕ → Submodule R M)
    (h : ∀ n, Disjoint (partialSups (OrderDual.toDual ∘ f) n) (OrderDual.toDual (f (n + 1)))) :
    ∃ n : ℕ, ∀ m, n ≤ m → f m = ⊤ := by
  -- A little off-by-one cleanup first:
  rsuffices ⟨n, w⟩ : ∃ n : ℕ, ∀ m, n ≤ m → OrderDual.toDual f (m + 1) = ⊤
  · use n + 1
    rintro (_ | m) p
    · cases p
    · apply w
      exact Nat.succ_le_succ_iff.mp p
  obtain ⟨n, w⟩ := monotone_stabilizes (partialSups (OrderDual.toDual ∘ f))
  refine ⟨n, fun m p ↦ (h m).eq_bot_of_ge <| sup_eq_left.mp ?_⟩
  simpa only [partialSups_add_one] using (w (m + 1) <| le_add_right p).symm.trans <| w m p

end IsArtinian

namespace LinearMap

variable [IsArtinian R M]

lemma eventually_iInf_range_pow_eq (f : Module.End R M) :
    ∀ᶠ n in atTop, ⨅ m, LinearMap.range (f ^ m) = LinearMap.range (f ^ n) := by
  obtain ⟨n, hn : ∀ m, n ≤ m → LinearMap.range (f ^ n) = LinearMap.range (f ^ m)⟩ :=
    IsArtinian.monotone_stabilizes f.iterateRange
  refine eventually_atTop.mpr ⟨n, fun l hl ↦ le_antisymm (iInf_le _ _) (le_iInf fun m ↦ ?_)⟩
  rcases le_or_gt l m with h | h
  · rw [← hn _ (hl.trans h), hn _ hl]
  · exact f.iterateRange.monotone h.le

end LinearMap

end Semiring

section Ring

variable {R M P N : Type*}
variable [Ring R] [AddCommGroup M] [AddCommGroup P] [AddCommGroup N]
variable [Module R M] [Module R P] [Module R N]

instance isArtinian_of_quotient_of_artinian
    (N : Submodule R M) [IsArtinian R M] : IsArtinian R (M ⧸ N) :=
  isArtinian_of_surjective M (Submodule.mkQ N) (Submodule.Quotient.mk_surjective N)

theorem isArtinian_of_range_eq_ker [IsArtinian R M] [IsArtinian R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (h : LinearMap.range f = LinearMap.ker g) : IsArtinian R N :=
  wellFounded_lt_exact_sequence (LinearMap.range f)
    (Submodule.map ((LinearMap.ker f).liftQ f le_rfl))
    (Submodule.comap ((LinearMap.ker f).liftQ f le_rfl))
    (Submodule.comap g.rangeRestrict) (Submodule.map g.rangeRestrict)
    (Submodule.gciMapComap <| LinearMap.ker_eq_bot.mp <| Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)
    (Submodule.giMapComap g.surjective_rangeRestrict)
    (by simp [Submodule.map_comap_eq, inf_comm, Submodule.range_liftQ])
    (by simp [Submodule.comap_map_eq, h])

theorem isArtinian_iff_submodule_quotient (S : Submodule R P) :
    IsArtinian R P ↔ IsArtinian R S ∧ IsArtinian R (P ⧸ S) := by
  refine ⟨fun h ↦ ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ ↦ ?_⟩
  apply isArtinian_of_range_eq_ker S.subtype S.mkQ
  rw [Submodule.ker_mkQ, Submodule.range_subtype]

instance isArtinian_prod [IsArtinian R M] [IsArtinian R P] : IsArtinian R (M × P) :=
  isArtinian_of_range_eq_ker (LinearMap.inl R M P) (LinearMap.snd R M P) (LinearMap.range_inl R M P)

instance isArtinian_sup (M₁ M₂ : Submodule R P) [IsArtinian R M₁] [IsArtinian R M₂] :
    IsArtinian R ↥(M₁ ⊔ M₂) := by
  have := isArtinian_range (M₁.subtype.coprod M₂.subtype)
  rwa [LinearMap.range_coprod, Submodule.range_subtype, Submodule.range_subtype] at this

variable {ι : Type*} [Finite ι]

instance isArtinian_pi :
    ∀ {M : ι → Type*} [Π i, AddCommGroup (M i)]
      [Π i, Module R (M i)] [∀ i, IsArtinian R (M i)], IsArtinian R (Π i, M i) := by
  apply Finite.induction_empty_option _ _ _ ι
  · exact fun e h ↦ isArtinian_of_linearEquiv (LinearEquiv.piCongrLeft R _ e)
  · infer_instance
  · exact fun ih ↦ isArtinian_of_linearEquiv (LinearEquiv.piOptionEquivProd R).symm

/-- A version of `isArtinian_pi` for non-dependent functions. We need this instance because
sometimes Lean fails to apply the dependent version in non-dependent settings (e.g., it fails to
prove that `ι → ℝ` is finite dimensional over `ℝ`). -/
instance isArtinian_pi' [IsArtinian R M] : IsArtinian R (ι → M) :=
  isArtinian_pi

--Porting note (https://github.com/leanprover-community/mathlib4/issues/10754): new instance
instance isArtinian_finsupp [IsArtinian R M] : IsArtinian R (ι →₀ M) :=
  isArtinian_of_linearEquiv (Finsupp.linearEquivFunOnFinite _ _ _).symm

instance isArtinian_iSup :
    ∀ {M : ι → Submodule R P} [∀ i, IsArtinian R (M i)], IsArtinian R ↥(⨆ i, M i) := by
  apply Finite.induction_empty_option _ _ _ ι
  · intro _ _ e h _ _; rw [← e.iSup_comp]; apply h
  · intros; rw [iSup_of_empty]; infer_instance
  · intro _ _ ih _ _; rw [iSup_option]; infer_instance

variable (R M) in
theorem IsArtinian.isSemisimpleModule_iff_jacobson [IsArtinian R M] :
    IsSemisimpleModule R M ↔ Module.jacobson R M = ⊥ :=
  ⟨fun _ ↦ IsSemisimpleModule.jacobson_eq_bot R M, fun h ↦
    have ⟨s, hs⟩ := Finset.exists_inf_le (Subtype.val (p := fun m : Submodule R M ↦ IsCoatom m))
    have _ (m : s) : IsSimpleModule R (M ⧸ m.1.1) := isSimpleModule_iff_isCoatom.mpr m.1.2
    let f : M →ₗ[R] ∀ m : s, M ⧸ m.1.1 := LinearMap.pi fun m ↦ m.1.1.mkQ
    .of_injective f <| LinearMap.ker_eq_bot.mp <| le_bot_iff.mp fun x hx ↦ by
      rw [← h, Module.jacobson, Submodule.mem_sInf]
      exact fun m hm ↦ hs ⟨m, hm⟩ <| Submodule.mem_finset_inf.mpr fun i hi ↦
        (Submodule.Quotient.mk_eq_zero i.1).mp <| congr_fun hx ⟨i, hi⟩⟩

open Submodule Function

namespace LinearMap

variable [IsArtinian R M]

/-- For any endomorphism of an Artinian module, any sufficiently high iterate has codisjoint kernel
and range. -/
theorem eventually_codisjoint_ker_pow_range_pow (f : Module.End R M) :
    ∀ᶠ n in atTop, Codisjoint (LinearMap.ker (f ^ n)) (LinearMap.range (f ^ n)) := by
  obtain ⟨n, hn : ∀ m, n ≤ m → LinearMap.range (f ^ n) = LinearMap.range (f ^ m)⟩ :=
    IsArtinian.monotone_stabilizes f.iterateRange
  refine eventually_atTop.mpr ⟨n, fun m hm ↦ codisjoint_iff.mpr ?_⟩
  simp_rw [← hn _ hm, Submodule.eq_top_iff', Submodule.mem_sup]
  intro x
  rsuffices ⟨y, hy⟩ : ∃ y, (f ^ m) ((f ^ n) y) = (f ^ m) x
  · exact ⟨x - (f ^ n) y, by simp [hy], (f ^ n) y, by simp⟩
  -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to change `mem_range` into `mem_range (f := _)`
  simp_rw [f.pow_apply n, f.pow_apply m, ← iterate_add_apply, ← f.pow_apply (m + n),
    ← f.pow_apply m, ← mem_range (f := _), ← hn _ (n.le_add_left m), hn _ hm]
  exact LinearMap.mem_range_self (f ^ m) x

/-- This is the Fitting decomposition of the module `M` with respect to the endomorphism `f`.

See also `LinearMap.isCompl_iSup_ker_pow_iInf_range_pow` for an alternative spelling. -/
theorem eventually_isCompl_ker_pow_range_pow [IsNoetherian R M] (f : Module.End R M) :
    ∀ᶠ n in atTop, IsCompl (LinearMap.ker (f ^ n)) (LinearMap.range (f ^ n)) := by
  filter_upwards [f.eventually_disjoint_ker_pow_range_pow.and
    f.eventually_codisjoint_ker_pow_range_pow] with n hn
  simpa only [isCompl_iff]

/-- This is the Fitting decomposition of the module `M` with respect to the endomorphism `f`.

See also `LinearMap.eventually_isCompl_ker_pow_range_pow` for an alternative spelling. -/
theorem isCompl_iSup_ker_pow_iInf_range_pow [IsNoetherian R M] (f : M →ₗ[R] M) :
    IsCompl (⨆ n, LinearMap.ker (f ^ n)) (⨅ n, LinearMap.range (f ^ n)) := by
  obtain ⟨k, hk⟩ := eventually_atTop.mp <| f.eventually_isCompl_ker_pow_range_pow.and <|
    f.eventually_iInf_range_pow_eq.and f.eventually_iSup_ker_pow_eq
  obtain ⟨h₁, h₂, h₃⟩ := hk k (le_refl k)
  rwa [h₂, h₃]

end LinearMap

end Ring

section CommSemiring

variable {R : Type*} (M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M] [IsArtinian R M]

namespace IsArtinian

theorem range_smul_pow_stabilizes (r : R) :
    ∃ n : ℕ, ∀ m, n ≤ m →
      LinearMap.range (r ^ n • LinearMap.id : M →ₗ[R] M) =
      LinearMap.range (r ^ m • LinearMap.id : M →ₗ[R] M) :=
  monotone_stabilizes
    ⟨fun n => LinearMap.range (r ^ n • LinearMap.id : M →ₗ[R] M), fun n m h x ⟨y, hy⟩ =>
      ⟨r ^ (m - n) • y, by
        dsimp at hy ⊢
        rw [← smul_assoc, smul_eq_mul, ← pow_add, ← hy, add_tsub_cancel_of_le h]⟩⟩

variable {M}

theorem exists_pow_succ_smul_dvd (r : R) (x : M) :
    ∃ (n : ℕ) (y : M), r ^ n.succ • y = r ^ n • x := by
  obtain ⟨n, hn⟩ := IsArtinian.range_smul_pow_stabilizes M r
  simp_rw [SetLike.ext_iff] at hn
  exact ⟨n, by simpa using hn n.succ n.le_succ (r ^ n • x)⟩

end IsArtinian

end CommSemiring

theorem isArtinian_of_submodule_of_artinian (R M) [Semiring R] [AddCommMonoid M] [Module R M]
    (N : Submodule R M) (_ : IsArtinian R M) : IsArtinian R N := inferInstance

/-- If `M / S / R` is a scalar tower, and `M / R` is Artinian, then `M / S` is also Artinian. -/
theorem isArtinian_of_tower (R) {S M} [Semiring R] [Semiring S] [AddCommMonoid M] [SMul R S]
    [Module S M] [Module R M] [IsScalarTower R S M] (h : IsArtinian R M) : IsArtinian S M :=
  ⟨(Submodule.restrictScalarsEmbedding R S M).wellFounded h.wf⟩

-- See `Mathlib/RingTheory/Artinian/Ring.lean`
assert_not_exists IsLocalization IsLocalRing

/-- A ring is Artinian if it is Artinian as a module over itself.

Strictly speaking, this should be called `IsLeftArtinianRing` but we omit the `Left` for
convenience in the commutative case. For a right Artinian ring, use `IsArtinian Rᵐᵒᵖ R`.

For equivalent definitions, see `Mathlib/RingTheory/Artinian/Ring.lean`.
-/
@[stacks 00J5]
abbrev IsArtinianRing (R) [Semiring R] :=
  IsArtinian R R

theorem isArtinianRing_iff {R} [Semiring R] : IsArtinianRing R ↔ IsArtinian R R := Iff.rfl

instance DivisionSemiring.instIsArtinianRing {K : Type*} [DivisionSemiring K] : IsArtinianRing K :=
  ⟨Finite.wellFounded_of_trans_of_irrefl _⟩

instance DivisionRing.instIsArtinianRing {K : Type*} [DivisionRing K] : IsArtinianRing K :=
  inferInstance

theorem Ring.isArtinian_of_zero_eq_one {R} [Semiring R] (h01 : (0 : R) = 1) : IsArtinianRing R :=
  have := subsingleton_of_zero_eq_one h01
  inferInstance

instance (R) [Ring R] [IsArtinianRing R] (I : Ideal R) [I.IsTwoSided] : IsArtinianRing (R ⧸ I) :=
  isArtinian_of_tower R inferInstance

open Submodule Function

instance isArtinian_of_fg_of_artinian' {R M} [Ring R] [AddCommGroup M] [Module R M]
    [IsArtinianRing R] [Module.Finite R M] : IsArtinian R M :=
  have ⟨_, _, h⟩ := Module.Finite.exists_fin' R M
  isArtinian_of_surjective _ _ h

theorem isArtinian_of_fg_of_artinian {R M} [Ring R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) [IsArtinianRing R] (hN : N.FG) : IsArtinian R N := by
  rw [← Module.Finite.iff_fg] at hN; infer_instance

theorem IsArtinianRing.of_finite (R S) [Ring R] [Ring S] [Module R S] [IsScalarTower R S S]
    [IsArtinianRing R] [Module.Finite R S] : IsArtinianRing S :=
  isArtinian_of_tower R isArtinian_of_fg_of_artinian'

/-- In a module over an artinian ring, the submodule generated by finitely many vectors is
artinian. -/
theorem isArtinian_span_of_finite (R) {M} [Ring R] [AddCommGroup M] [Module R M] [IsArtinianRing R]
    {A : Set M} (hA : A.Finite) : IsArtinian R (Submodule.span R A) :=
  isArtinian_of_fg_of_artinian _ (Submodule.fg_def.mpr ⟨A, hA, rfl⟩)

theorem Function.Surjective.isArtinianRing {R} [Semiring R] {S} [Semiring S] {F}
    [FunLike F R S] [RingHomClass F R S]
    {f : F} (hf : Function.Surjective f) [H : IsArtinianRing R] : IsArtinianRing S := by
  rw [isArtinianRing_iff] at H ⊢
  exact ⟨(Ideal.orderEmbeddingOfSurjective f hf).wellFounded H.wf⟩

instance isArtinianRing_rangeS {R} [Semiring R] {S} [Semiring S] (f : R →+* S) [IsArtinianRing R] :
    IsArtinianRing f.rangeS :=
  f.rangeSRestrict_surjective.isArtinianRing

instance isArtinianRing_range {R} [Ring R] {S} [Ring S] (f : R →+* S) [IsArtinianRing R] :
    IsArtinianRing f.range :=
  isArtinianRing_rangeS f

theorem RingEquiv.isArtinianRing {R S} [Semiring R] [Semiring S] (f : R ≃+* S)
    [IsArtinianRing R] : IsArtinianRing S :=
  f.surjective.isArtinianRing

instance {R S} [Semiring R] [Semiring S] [IsArtinianRing R] [IsArtinianRing S] :
    IsArtinianRing (R × S) :=
  Ideal.idealProdEquiv.toOrderEmbedding.wellFoundedLT

instance {ι} [Finite ι] : ∀ {R : ι → Type*} [Π i, Semiring (R i)] [∀ i, IsArtinianRing (R i)],
    IsArtinianRing (Π i, R i) := by
  apply Finite.induction_empty_option _ _ _ ι
  · exact fun e h ↦ RingEquiv.isArtinianRing (.piCongrLeft _ e)
  · infer_instance
  · exact fun ih ↦ RingEquiv.isArtinianRing (.symm .piOptionEquivProd)

namespace IsArtinianRing

section CommSemiring

variable (R : Type*) [CommSemiring R] [IsArtinianRing R]

@[stacks 00J7]
lemma setOf_isMaximal_finite : {I : Ideal R | I.IsMaximal}.Finite := by
  have ⟨s, H⟩ := Finset.exists_inf_le (Subtype.val (p := fun I : Ideal R ↦ I.IsMaximal))
  refine Set.finite_def.2 ⟨s, fun p ↦ ?_⟩
  have ⟨q, hq1, hq2⟩ := p.2.isPrime.inf_le'.mp (H p)
  rwa [← Subtype.ext <| q.2.eq_of_le p.2.ne_top hq2]

instance : Finite (MaximalSpectrum R) :=
  haveI : Finite {I : Ideal R // I.IsMaximal} := (setOf_isMaximal_finite R).to_subtype
  .of_equiv _ (MaximalSpectrum.equivSubtype _).symm

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] [IsArtinianRing R]

variable (R) in
lemma isField_of_isDomain [IsDomain R] : IsField R := by
  refine ⟨Nontrivial.exists_pair_ne, mul_comm, fun {x} hx ↦ ?_⟩
  obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd x (1 : R)
  replace hy : x ^ n * (x * y - 1) = 0 := by
    rw [mul_sub, sub_eq_zero]
    convert hy using 1
    simp [Nat.succ_eq_add_one, pow_add, mul_assoc]
  rw [mul_eq_zero, sub_eq_zero] at hy
  exact ⟨_, hy.resolve_left <| pow_ne_zero _ hx⟩

/- Does not hold in a commutative semiring:
consider {0, 0.5, 1} with ⊔ as + and ⊓ as *, then both {0} and {0, 0.5} are prime ideals. -/
-- Note: type class synthesis should try to synthesize `p.IsPrime` before `IsArtinianRing R`,
-- hence the argument order.
instance isMaximal_of_isPrime {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime]
    [IsArtinianRing R] : p.IsMaximal :=
  Ideal.Quotient.maximal_of_isField _ (isField_of_isDomain _)

lemma isPrime_iff_isMaximal (p : Ideal R) : p.IsPrime ↔ p.IsMaximal :=
  ⟨fun _ ↦ isMaximal_of_isPrime p, fun h ↦ h.isPrime⟩

/-- The prime spectrum is in bijection with the maximal spectrum. -/
@[simps]
def primeSpectrumEquivMaximalSpectrum : PrimeSpectrum R ≃ MaximalSpectrum R where
  toFun I := ⟨I.asIdeal, isPrime_iff_isMaximal I.asIdeal |>.mp I.isPrime⟩
  invFun I := ⟨I.asIdeal, isPrime_iff_isMaximal I.asIdeal |>.mpr I.isMaximal⟩

lemma primeSpectrumEquivMaximalSpectrum_comp_asIdeal :
    MaximalSpectrum.asIdeal ∘ primeSpectrumEquivMaximalSpectrum =
      PrimeSpectrum.asIdeal (R := R) := rfl

lemma primeSpectrumEquivMaximalSpectrum_symm_comp_asIdeal :
    PrimeSpectrum.asIdeal ∘ primeSpectrumEquivMaximalSpectrum.symm =
      MaximalSpectrum.asIdeal (R := R) := rfl

lemma primeSpectrum_asIdeal_range_eq :
    range PrimeSpectrum.asIdeal = (range <| MaximalSpectrum.asIdeal (R := R)) := by
  simp only [PrimeSpectrum.range_asIdeal, MaximalSpectrum.range_asIdeal,
    isPrime_iff_isMaximal]

variable (R)

lemma setOf_isPrime_finite : {I : Ideal R | I.IsPrime}.Finite := by
  simpa only [isPrime_iff_isMaximal] using setOf_isMaximal_finite R

instance : Finite (PrimeSpectrum R) :=
  haveI : Finite {I : Ideal R // I.IsPrime} := (setOf_isPrime_finite R).to_subtype
  .of_equiv _ (PrimeSpectrum.equivSubtype _).symm.toEquiv

/-- A temporary field instance on the quotients by maximal ideals. -/
@[local instance] noncomputable def fieldOfSubtypeIsMaximal
    (I : MaximalSpectrum R) : Field (R ⧸ I.asIdeal) :=
  Ideal.Quotient.field I.asIdeal

/-- The quotient of a commutative artinian ring by its nilradical is isomorphic to
a finite product of fields, namely the quotients by the maximal ideals. -/
noncomputable def quotNilradicalEquivPi :
    R ⧸ nilradical R ≃+* ∀ I : MaximalSpectrum R, R ⧸ I.asIdeal :=
  let f := MaximalSpectrum.asIdeal (R := R)
  .trans
    (Ideal.quotEquivOfEq <| ext fun x ↦ by
      rw [PrimeSpectrum.nilradical_eq_iInf, iInf, primeSpectrum_asIdeal_range_eq]; rfl)
    (Ideal.quotientInfRingEquivPiQuotient f <| fun I J h ↦
      Ideal.isCoprime_iff_sup_eq.mpr <| I.2.coprime_of_ne J.2 <|
      fun hIJ ↦ h <| MaximalSpectrum.ext hIJ)

/-- A reduced commutative artinian ring is isomorphic to a finite product of fields,
namely the quotients by the maximal ideals. -/
noncomputable def equivPi [IsReduced R] : R ≃+* ∀ I : MaximalSpectrum R, R ⧸ I.asIdeal :=
  .trans (.symm <| .quotientBot R) <| .trans
    (Ideal.quotEquivOfEq (nilradical_eq_zero R).symm) (quotNilradicalEquivPi R)

theorem isSemisimpleRing_of_isReduced [IsReduced R] : IsSemisimpleRing R :=
  (equivPi R).symm.isSemisimpleRing

end CommRing

section Ring

variable {R : Type*} [Ring R] [IsArtinianRing R]

theorem isSemisimpleRing_iff_jacobson : IsSemisimpleRing R ↔ Ring.jacobson R = ⊥ :=
  IsArtinian.isSemisimpleModule_iff_jacobson R R

instance : IsSemiprimaryRing R where
  isSemisimpleRing :=
    IsArtinianRing.isSemisimpleRing_iff_jacobson.mpr (Ring.jacobson_quotient_jacobson R)
  isNilpotent := by
    let Jac := Ring.jacobson R
    have ⟨n, hn⟩ := IsArtinian.monotone_stabilizes ⟨(Jac ^ ·), @Ideal.pow_le_pow_right _ _ _⟩
    have hn : Jac * Jac ^ n = Jac ^ n := by
      rw [← Ideal.IsTwoSided.pow_succ]; exact (hn _ n.le_succ).symm
    use n; by_contra ne
    have ⟨N, ⟨eq, ne⟩, min⟩ := wellFounded_lt.has_min {N | Jac * N = N ∧ N ≠ ⊥} ⟨_, hn, ne⟩
    have : Jac ^ n * N = N := n.rec (by rw [Jac.pow_zero, N.one_mul])
      fun n hn ↦ by rwa [Jac.pow_succ, mul_assoc, eq]
    let I x := Submodule.map (LinearMap.toSpanSingleton R R x) (Jac ^ n)
    have hI x : I x ≤ Ideal.span {x} := by
      rw [Ideal.span, LinearMap.span_singleton_eq_range]; exact LinearMap.map_le_range
    have ⟨x, hx⟩ : ∃ x ∈ N, I x ≠ ⊥ := by
      contrapose! ne
      rw [← this, ← le_bot_iff, Ideal.mul_le]
      refine fun ri hi rn hn ↦ ?_
      rw [← ne rn hn]
      exact ⟨ri, hi, rfl⟩
    rw [← Ideal.span_singleton_le_iff_mem] at hx
    have : I x = N := by
      refine ((hI x).trans hx.1).eq_of_not_lt (min _ ⟨?_, hx.2⟩)
      rw [← smul_eq_mul, ← Submodule.map_smul'', smul_eq_mul, hn]
    have : Ideal.span {x} = N := le_antisymm hx.1 (this.symm.trans_le <| hI x)
    refine (this ▸ ne) ((Submodule.fg_span <| Set.finite_singleton x).eq_bot_of_le_jacobson_smul ?_)
    rw [← Ideal.span, this, smul_eq_mul, eq]

end Ring

end IsArtinianRing
