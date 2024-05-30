/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Data.SetLike.Fintype
import Mathlib.Algebra.Divisibility.Prod
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.SimpleModule
import Mathlib.Tactic.RSuffices

#align_import ring_theory.artinian from "leanprover-community/mathlib"@"210657c4ea4a4a7b234392f70a3a2a83346dfa90"

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

* `IsArtinianRing.localization_surjective`: the canonical homomorphism from a commutative artinian
  ring to any localization of itself is surjective.

* `IsArtinianRing.isNilpotent_jacobson_bot`: the Jacobson radical of a commutative artinian ring
  is a nilpotent ideal. (TODO: generalize to noncommutative rings.)

* `IsArtinianRing.primeSpectrum_finite`, `IsArtinianRing.isMaximal_of_isPrime`: there are only
  finitely prime ideals in a commutative artinian ring, and each of them is maximal.

* `IsArtinianRing.equivPi`: a reduced commutative artinian ring `R` is isomorphic to a finite
  product of fields (and therefore is a semisimple ring and a decomposition monoid; moreover
  `R[X]` is also a decomposition monoid).

## References

* [M. F. Atiyah and I. G. Macdonald, *Introduction to commutative algebra*][atiyah-macdonald]
* [samuel]

## Tags

Artinian, artinian, Artinian ring, Artinian module, artinian ring, artinian module

-/

open Set Filter Pointwise

/-- `IsArtinian R M` is the proposition that `M` is an Artinian `R`-module,
implemented as the well-foundedness of submodule inclusion. -/
class IsArtinian (R M) [Semiring R] [AddCommMonoid M] [Module R M] : Prop where
  wellFounded_submodule_lt' : WellFounded ((· < ·) : Submodule R M → Submodule R M → Prop)
#align is_artinian IsArtinian

section

variable {R M P N : Type*}
variable [Ring R] [AddCommGroup M] [AddCommGroup P] [AddCommGroup N]
variable [Module R M] [Module R P] [Module R N]

open IsArtinian

/- Porting note: added this version with `R` and `M` explicit because infer kinds are unsupported in
Lean 4-/
theorem IsArtinian.wellFounded_submodule_lt (R M) [Semiring R] [AddCommMonoid M] [Module R M]
    [IsArtinian R M] : WellFounded ((· < ·) : Submodule R M → Submodule R M → Prop) :=
  IsArtinian.wellFounded_submodule_lt'
#align is_artinian.well_founded_submodule_lt IsArtinian.wellFounded_submodule_lt

theorem isArtinian_of_injective (f : M →ₗ[R] P) (h : Function.Injective f) [IsArtinian R P] :
    IsArtinian R M :=
  ⟨Subrelation.wf
    (fun {A B} hAB => show A.map f < B.map f from Submodule.map_strictMono_of_injective h hAB)
    (InvImage.wf (Submodule.map f) (IsArtinian.wellFounded_submodule_lt R P))⟩
#align is_artinian_of_injective isArtinian_of_injective

instance isArtinian_submodule' [IsArtinian R M] (N : Submodule R M) : IsArtinian R N :=
  isArtinian_of_injective N.subtype Subtype.val_injective
#align is_artinian_submodule' isArtinian_submodule'

theorem isArtinian_of_le {s t : Submodule R M} [IsArtinian R t] (h : s ≤ t) : IsArtinian R s :=
  isArtinian_of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)
#align is_artinian_of_le isArtinian_of_le

variable (M)

theorem isArtinian_of_surjective (f : M →ₗ[R] P) (hf : Function.Surjective f) [IsArtinian R M] :
    IsArtinian R P :=
  ⟨Subrelation.wf
    (fun {A B} hAB =>
      show A.comap f < B.comap f from Submodule.comap_strictMono_of_surjective hf hAB)
    (InvImage.wf (Submodule.comap f) (IsArtinian.wellFounded_submodule_lt R M))⟩
#align is_artinian_of_surjective isArtinian_of_surjective

variable {M}

theorem isArtinian_of_linearEquiv (f : M ≃ₗ[R] P) [IsArtinian R M] : IsArtinian R P :=
  isArtinian_of_surjective _ f.toLinearMap f.toEquiv.surjective
#align is_artinian_of_linear_equiv isArtinian_of_linearEquiv

theorem isArtinian_of_range_eq_ker [IsArtinian R M] [IsArtinian R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (h : LinearMap.range f = LinearMap.ker g) : IsArtinian R N :=
  ⟨wellFounded_lt_exact_sequence (IsArtinian.wellFounded_submodule_lt R M)
    (IsArtinian.wellFounded_submodule_lt R P) (LinearMap.range f) (Submodule.map f)
    (Submodule.comap f) (Submodule.comap g) (Submodule.map g) (Submodule.gciMapComap hf)
    (Submodule.giMapComap hg)
    (by simp [Submodule.map_comap_eq, inf_comm]) (by simp [Submodule.comap_map_eq, h])⟩
#align is_artinian_of_range_eq_ker isArtinian_of_range_eq_ker

instance isArtinian_prod [IsArtinian R M] [IsArtinian R P] : IsArtinian R (M × P) :=
  isArtinian_of_range_eq_ker (LinearMap.inl R M P) (LinearMap.snd R M P) LinearMap.inl_injective
    LinearMap.snd_surjective (LinearMap.range_inl R M P)
#align is_artinian_prod isArtinian_prod

instance (priority := 100) isArtinian_of_finite [Finite M] : IsArtinian R M :=
  ⟨Finite.wellFounded_of_trans_of_irrefl _⟩
#align is_artinian_of_finite isArtinian_of_finite

-- Porting note: elab_as_elim can only be global and cannot be changed on an imported decl
-- attribute [local elab_as_elim] Finite.induction_empty_option

instance isArtinian_pi {R ι : Type*} [Finite ι] :
    ∀ {M : ι → Type*} [Ring R] [∀ i, AddCommGroup (M i)],
      ∀ [∀ i, Module R (M i)], ∀ [∀ i, IsArtinian R (M i)], IsArtinian R (∀ i, M i) := by
  apply Finite.induction_empty_option _ _ _ ι
  · intro α β e hα M _ _ _ _
    have := @hα
    exact isArtinian_of_linearEquiv (LinearEquiv.piCongrLeft R M e)
  · intro M _ _ _ _
    infer_instance
  · intro α _ ih M _ _ _ _
    have := @ih
    exact isArtinian_of_linearEquiv (LinearEquiv.piOptionEquivProd R).symm
#align is_artinian_pi isArtinian_pi

/-- A version of `isArtinian_pi` for non-dependent functions. We need this instance because
sometimes Lean fails to apply the dependent version in non-dependent settings (e.g., it fails to
prove that `ι → ℝ` is finite dimensional over `ℝ`). -/
instance isArtinian_pi' {R ι M : Type*} [Ring R] [AddCommGroup M] [Module R M] [Finite ι]
    [IsArtinian R M] : IsArtinian R (ι → M) :=
  isArtinian_pi
#align is_artinian_pi' isArtinian_pi'

--porting note (#10754): new instance
instance isArtinian_finsupp {R ι M : Type*} [Ring R] [AddCommGroup M] [Module R M] [Finite ι]
    [IsArtinian R M] : IsArtinian R (ι →₀ M) :=
  isArtinian_of_linearEquiv (Finsupp.linearEquivFunOnFinite _ _ _).symm

end

open IsArtinian Submodule Function

section Ring

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

theorem isArtinian_iff_wellFounded :
    IsArtinian R M ↔ WellFounded ((· < ·) : Submodule R M → Submodule R M → Prop) :=
  ⟨fun h => h.1, IsArtinian.mk⟩
#align is_artinian_iff_well_founded isArtinian_iff_wellFounded

theorem IsArtinian.finite_of_linearIndependent [Nontrivial R] [IsArtinian R M] {s : Set M}
    (hs : LinearIndependent R ((↑) : s → M)) : s.Finite := by
  refine by_contradiction fun hf => (RelEmbedding.wellFounded_iff_no_descending_seq.1
    (wellFounded_submodule_lt (R := R) (M := M))).elim' ?_
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
    exact ⟨fun hab x => le_trans hab, fun h => h _ le_rfl⟩
  exact ⟨⟨fun n => span R (Subtype.val ∘ f '' { m | n ≤ m }), fun x y => by
    rw [le_antisymm_iff, ← this y x, ← this x y]
    exact fun ⟨h₁, h₂⟩ => le_antisymm_iff.2 ⟨h₂, h₁⟩⟩, by
    intro a b
    conv_rhs => rw [GT.gt, lt_iff_le_not_le, this, this, ← lt_iff_le_not_le]
    rfl⟩
#align is_artinian.finite_of_linear_independent IsArtinian.finite_of_linearIndependent

/-- A module is Artinian iff every nonempty set of submodules has a minimal submodule among them. -/
theorem set_has_minimal_iff_artinian :
    (∀ a : Set <| Submodule R M, a.Nonempty → ∃ M' ∈ a, ∀ I ∈ a, ¬I < M') ↔ IsArtinian R M := by
  rw [isArtinian_iff_wellFounded, WellFounded.wellFounded_iff_has_min]
#align set_has_minimal_iff_artinian set_has_minimal_iff_artinian

theorem IsArtinian.set_has_minimal [IsArtinian R M] (a : Set <| Submodule R M) (ha : a.Nonempty) :
    ∃ M' ∈ a, ∀ I ∈ a, ¬I < M' :=
  set_has_minimal_iff_artinian.mpr ‹_› a ha
#align is_artinian.set_has_minimal IsArtinian.set_has_minimal

/-- A module is Artinian iff every decreasing chain of submodules stabilizes. -/
theorem monotone_stabilizes_iff_artinian :
    (∀ f : ℕ →o (Submodule R M)ᵒᵈ, ∃ n, ∀ m, n ≤ m → f n = f m) ↔ IsArtinian R M := by
  rw [isArtinian_iff_wellFounded]
  exact WellFounded.monotone_chain_condition.symm
#align monotone_stabilizes_iff_artinian monotone_stabilizes_iff_artinian

namespace IsArtinian

variable [IsArtinian R M]

theorem monotone_stabilizes (f : ℕ →o (Submodule R M)ᵒᵈ) : ∃ n, ∀ m, n ≤ m → f n = f m :=
  monotone_stabilizes_iff_artinian.mpr ‹_› f
#align is_artinian.monotone_stabilizes IsArtinian.monotone_stabilizes

theorem eventuallyConst_of_isArtinian (f : ℕ →o (Submodule R M)ᵒᵈ) :
    atTop.EventuallyConst f := by
  simp_rw [eventuallyConst_atTop, eq_comm]
  exact monotone_stabilizes f

/-- If `∀ I > J, P I` implies `P J`, then `P` holds for all submodules. -/
theorem induction {P : Submodule R M → Prop} (hgt : ∀ I, (∀ J < I, P J) → P I) (I : Submodule R M) :
    P I :=
  (wellFounded_submodule_lt R M).recursion I hgt
#align is_artinian.induction IsArtinian.induction

end IsArtinian

namespace LinearMap

variable [IsArtinian R M]

/-- For any endomorphism of an Artinian module, any sufficiently high iterate has codisjoint kernel
and range. -/
theorem eventually_codisjoint_ker_pow_range_pow (f : M →ₗ[R] M) :
    ∀ᶠ n in atTop, Codisjoint (LinearMap.ker (f ^ n)) (LinearMap.range (f ^ n)) := by
  obtain ⟨n, hn : ∀ m, n ≤ m → LinearMap.range (f ^ n) = LinearMap.range (f ^ m)⟩ :=
    monotone_stabilizes f.iterateRange
  refine eventually_atTop.mpr ⟨n, fun m hm ↦ codisjoint_iff.mpr ?_⟩
  simp_rw [← hn _ hm, Submodule.eq_top_iff', Submodule.mem_sup]
  intro x
  rsuffices ⟨y, hy⟩ : ∃ y, (f ^ m) ((f ^ n) y) = (f ^ m) x
  · exact ⟨x - (f ^ n) y, by simp [hy], (f ^ n) y, by simp⟩
  -- Note: #8386 had to change `mem_range` into `mem_range (f := _)`
  simp_rw [f.pow_apply n, f.pow_apply m, ← iterate_add_apply, ← f.pow_apply (m + n),
    ← f.pow_apply m, ← mem_range (f := _), ← hn _ (n.le_add_left m), hn _ hm]
  exact LinearMap.mem_range_self (f ^ m) x
#align is_artinian.exists_endomorphism_iterate_ker_sup_range_eq_top LinearMap.eventually_codisjoint_ker_pow_range_pow

lemma eventually_iInf_range_pow_eq (f : Module.End R M) :
    ∀ᶠ n in atTop, ⨅ m, LinearMap.range (f ^ m) = LinearMap.range (f ^ n) := by
  obtain ⟨n, hn : ∀ m, n ≤ m → LinearMap.range (f ^ n) = LinearMap.range (f ^ m)⟩ :=
    monotone_stabilizes f.iterateRange
  refine eventually_atTop.mpr ⟨n, fun l hl ↦ le_antisymm (iInf_le _ _) (le_iInf fun m ↦ ?_)⟩
  rcases le_or_lt l m with h | h
  · rw [← hn _ (hl.trans h), hn _ hl]
  · exact f.iterateRange.monotone h.le

/-- This is the Fitting decomposition of the module `M` with respect to the endomorphism `f`.

See also `LinearMap.isCompl_iSup_ker_pow_iInf_range_pow` for an alternative spelling. -/
theorem eventually_isCompl_ker_pow_range_pow [IsNoetherian R M] (f : M →ₗ[R] M) :
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

namespace IsArtinian

variable [IsArtinian R M]

/-- Any injective endomorphism of an Artinian module is surjective. -/
theorem surjective_of_injective_endomorphism (f : M →ₗ[R] M) (s : Injective f) : Surjective f := by
  obtain ⟨n, hn⟩ := eventually_atTop.mp f.eventually_codisjoint_ker_pow_range_pow
  specialize hn (n + 1) (n.le_add_right 1)
  rw [codisjoint_iff, LinearMap.ker_eq_bot.mpr (LinearMap.iterate_injective s _), bot_sup_eq,
    LinearMap.range_eq_top] at hn
  exact LinearMap.surjective_of_iterate_surjective n.succ_ne_zero hn
#align is_artinian.surjective_of_injective_endomorphism IsArtinian.surjective_of_injective_endomorphism

/-- Any injective endomorphism of an Artinian module is bijective. -/
theorem bijective_of_injective_endomorphism (f : M →ₗ[R] M) (s : Injective f) : Bijective f :=
  ⟨s, surjective_of_injective_endomorphism f s⟩
#align is_artinian.bijective_of_injective_endomorphism IsArtinian.bijective_of_injective_endomorphism

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
  refine ⟨n, fun m p => ?_⟩
  exact (h m).eq_bot_of_ge (sup_eq_left.1 <| (w (m + 1) <| le_add_right p).symm.trans <| w m p)
#align is_artinian.disjoint_partial_infs_eventually_top IsArtinian.disjoint_partial_infs_eventually_top

end IsArtinian

end Ring

section CommRing

variable {R : Type*} (M : Type*) [CommRing R] [AddCommGroup M] [Module R M] [IsArtinian R M]

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
#align is_artinian.range_smul_pow_stabilizes IsArtinian.range_smul_pow_stabilizes

variable {M}

theorem exists_pow_succ_smul_dvd (r : R) (x : M) :
    ∃ (n : ℕ) (y : M), r ^ n.succ • y = r ^ n • x := by
  obtain ⟨n, hn⟩ := IsArtinian.range_smul_pow_stabilizes M r
  simp_rw [SetLike.ext_iff] at hn
  exact ⟨n, by simpa using hn n.succ n.le_succ (r ^ n • x)⟩
#align is_artinian.exists_pow_succ_smul_dvd IsArtinian.exists_pow_succ_smul_dvd

end IsArtinian

end CommRing

/-- A ring is Artinian if it is Artinian as a module over itself.

Strictly speaking, this should be called `IsLeftArtinianRing` but we omit the `Left` for
convenience in the commutative case. For a right Artinian ring, use `IsArtinian Rᵐᵒᵖ R`. -/
abbrev IsArtinianRing (R) [Ring R] :=
  IsArtinian R R
#align is_artinian_ring IsArtinianRing

theorem isArtinianRing_iff {R} [Ring R] : IsArtinianRing R ↔ IsArtinian R R := Iff.rfl
#align is_artinian_ring_iff isArtinianRing_iff

instance DivisionRing.instIsArtinianRing {K : Type*} [DivisionRing K] : IsArtinianRing K :=
  ⟨Finite.wellFounded_of_trans_of_irrefl _⟩

theorem Ring.isArtinian_of_zero_eq_one {R} [Ring R] (h01 : (0 : R) = 1) : IsArtinianRing R :=
  have := subsingleton_of_zero_eq_one h01
  inferInstance
#align ring.is_artinian_of_zero_eq_one Ring.isArtinian_of_zero_eq_one

theorem isArtinian_of_submodule_of_artinian (R M) [Ring R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) (_ : IsArtinian R M) : IsArtinian R N := inferInstance
#align is_artinian_of_submodule_of_artinian isArtinian_of_submodule_of_artinian

instance isArtinian_of_quotient_of_artinian (R) [Ring R] (M) [AddCommGroup M] [Module R M]
    (N : Submodule R M) [IsArtinian R M] : IsArtinian R (M ⧸ N) :=
  isArtinian_of_surjective M (Submodule.mkQ N) (Submodule.Quotient.mk_surjective N)
#align is_artinian_of_quotient_of_artinian isArtinian_of_quotient_of_artinian

/-- If `M / S / R` is a scalar tower, and `M / R` is Artinian, then `M / S` is also Artinian. -/
theorem isArtinian_of_tower (R) {S M} [CommRing R] [Ring S] [AddCommGroup M] [Algebra R S]
    [Module S M] [Module R M] [IsScalarTower R S M] (h : IsArtinian R M) : IsArtinian S M := by
  rw [isArtinian_iff_wellFounded] at h ⊢
  exact (Submodule.restrictScalarsEmbedding R S M).wellFounded h
#align is_artinian_of_tower isArtinian_of_tower

instance (R) [CommRing R] [IsArtinianRing R] (I : Ideal R) : IsArtinianRing (R ⧸ I) :=
  isArtinian_of_tower R inferInstance

theorem isArtinian_of_fg_of_artinian {R M} [Ring R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) [IsArtinianRing R] (hN : N.FG) : IsArtinian R N := by
  let ⟨s, hs⟩ := hN
  haveI := Classical.decEq M
  haveI := Classical.decEq R
  have : ∀ x ∈ s, x ∈ N := fun x hx => hs ▸ Submodule.subset_span hx
  refine @isArtinian_of_surjective _ ((↑s : Set M) →₀ R) N _ _ _ _ _ ?_ ?_ isArtinian_finsupp
  · exact Finsupp.total (↑s : Set M) N R (fun i => ⟨i, hs ▸ subset_span i.2⟩)
  · rw [← LinearMap.range_eq_top, eq_top_iff,
       ← map_le_map_iff_of_injective (show Injective (Submodule.subtype N)
         from Subtype.val_injective), Submodule.map_top, range_subtype,
         ← Submodule.map_top, ← Submodule.map_comp, Submodule.map_top]
    subst N
    refine span_le.2 (fun i hi => ?_)
    use Finsupp.single ⟨i, hi⟩ 1
    simp
#align is_artinian_of_fg_of_artinian isArtinian_of_fg_of_artinian

instance isArtinian_of_fg_of_artinian' {R M} [Ring R] [AddCommGroup M] [Module R M]
    [IsArtinianRing R] [Module.Finite R M] : IsArtinian R M :=
  have : IsArtinian R (⊤ : Submodule R M) := isArtinian_of_fg_of_artinian _ Module.Finite.out
  isArtinian_of_linearEquiv (LinearEquiv.ofTop (⊤ : Submodule R M) rfl)
#align is_artinian_of_fg_of_artinian' isArtinian_of_fg_of_artinian'

theorem IsArtinianRing.of_finite (R S) [CommRing R] [Ring S] [Algebra R S]
    [IsArtinianRing R] [Module.Finite R S] : IsArtinianRing S :=
  isArtinian_of_tower R isArtinian_of_fg_of_artinian'

/-- In a module over an artinian ring, the submodule generated by finitely many vectors is
artinian. -/
theorem isArtinian_span_of_finite (R) {M} [Ring R] [AddCommGroup M] [Module R M] [IsArtinianRing R]
    {A : Set M} (hA : A.Finite) : IsArtinian R (Submodule.span R A) :=
  isArtinian_of_fg_of_artinian _ (Submodule.fg_def.mpr ⟨A, hA, rfl⟩)
#align is_artinian_span_of_finite isArtinian_span_of_finite

theorem Function.Surjective.isArtinianRing {R} [Ring R] {S} [Ring S] {F}
    [FunLike F R S] [RingHomClass F R S]
    {f : F} (hf : Function.Surjective f) [H : IsArtinianRing R] : IsArtinianRing S := by
  rw [isArtinianRing_iff, isArtinian_iff_wellFounded] at H ⊢
  exact (Ideal.orderEmbeddingOfSurjective f hf).wellFounded H
#align function.surjective.is_artinian_ring Function.Surjective.isArtinianRing

instance isArtinianRing_range {R} [Ring R] {S} [Ring S] (f : R →+* S) [IsArtinianRing R] :
    IsArtinianRing f.range :=
  f.rangeRestrict_surjective.isArtinianRing
#align is_artinian_ring_range isArtinianRing_range

namespace IsArtinianRing

open IsArtinian

variable {R : Type*} [CommRing R] [IsArtinianRing R]

theorem isNilpotent_jacobson_bot : IsNilpotent (Ideal.jacobson (⊥ : Ideal R)) := by
  let Jac := Ideal.jacobson (⊥ : Ideal R)
  let f : ℕ →o (Ideal R)ᵒᵈ := ⟨fun n => Jac ^ n, fun _ _ h => Ideal.pow_le_pow_right h⟩
  obtain ⟨n, hn⟩ : ∃ n, ∀ m, n ≤ m → Jac ^ n = Jac ^ m := IsArtinian.monotone_stabilizes f
  refine ⟨n, ?_⟩
  let J : Ideal R := annihilator (Jac ^ n)
  suffices J = ⊤ by
    have hJ : J • Jac ^ n = ⊥ := annihilator_smul (Jac ^ n)
    simpa only [this, top_smul, Ideal.zero_eq_bot] using hJ
  by_contra hJ
  change J ≠ ⊤ at hJ
  rcases IsArtinian.set_has_minimal { J' : Ideal R | J < J' } ⟨⊤, hJ.lt_top⟩ with
    ⟨J', hJJ' : J < J', hJ' : ∀ I, J < I → ¬I < J'⟩
  rcases SetLike.exists_of_lt hJJ' with ⟨x, hxJ', hxJ⟩
  obtain rfl : J ⊔ Ideal.span {x} = J' := by
    apply eq_of_le_of_not_lt _ (hJ' (J ⊔ Ideal.span {x}) _)
    · exact sup_le hJJ'.le (span_le.2 (singleton_subset_iff.2 hxJ'))
    · rw [SetLike.lt_iff_le_and_exists]
      exact ⟨le_sup_left, ⟨x, mem_sup_right (mem_span_singleton_self x), hxJ⟩⟩
  have : J ⊔ Jac • Ideal.span {x} ≤ J ⊔ Ideal.span {x} :=
    sup_le_sup_left (smul_le.2 fun _ _ _ => Submodule.smul_mem _ _) _
  have : Jac * Ideal.span {x} ≤ J := by -- Need version 4 of Nakayama's lemma on Stacks
    by_contra H
    refine H (Ideal.mul_le_left.trans (le_of_le_smul_of_le_jacobson_bot (fg_span_singleton _) le_rfl
      (le_sup_right.trans_eq (this.eq_of_not_lt (hJ' _ ?_)).symm)))
    exact lt_of_le_of_ne le_sup_left fun h => H <| h.symm ▸ le_sup_right
  have : Ideal.span {x} * Jac ^ (n + 1) ≤ ⊥ := calc
    Ideal.span {x} * Jac ^ (n + 1) = Ideal.span {x} * Jac * Jac ^ n := by
      rw [pow_succ', ← mul_assoc]
    _ ≤ J * Jac ^ n := mul_le_mul (by rwa [mul_comm]) le_rfl
    _ = ⊥ := by simp [J]
  refine hxJ (mem_annihilator.2 fun y hy => (mem_bot R).1 ?_)
  refine this (mul_mem_mul (mem_span_singleton_self x) ?_)
  rwa [← hn (n + 1) (Nat.le_succ _)]
#align is_artinian_ring.is_nilpotent_jacobson_bot IsArtinianRing.isNilpotent_jacobson_bot

section Localization

variable (S : Submonoid R) (L : Type*) [CommRing L] [Algebra R L] [IsLocalization S L]

/-- Localizing an artinian ring can only reduce the amount of elements. -/
theorem localization_surjective : Function.Surjective (algebraMap R L) := by
  intro r'
  obtain ⟨r₁, s, rfl⟩ := IsLocalization.mk'_surjective S r'
  -- TODO: can `rsuffices` be used to move the `exact` below before the proof of this `obtain`?
  obtain ⟨r₂, h⟩ : ∃ r : R, IsLocalization.mk' L 1 s = algebraMap R L r := by
    obtain ⟨n, r, hr⟩ := IsArtinian.exists_pow_succ_smul_dvd (s : R) (1 : R)
    use r
    rw [smul_eq_mul, smul_eq_mul, pow_succ, mul_assoc] at hr
    apply_fun algebraMap R L at hr
    simp only [map_mul] at hr
    rw [← IsLocalization.mk'_one (M := S) L, IsLocalization.mk'_eq_iff_eq, mul_one,
      Submonoid.coe_one, ← (IsLocalization.map_units L (s ^ n)).mul_left_cancel hr, map_mul]
  exact ⟨r₁ * r₂, by rw [IsLocalization.mk'_eq_mul_mk'_one, map_mul, h]⟩
#align is_artinian_ring.localization_surjective IsArtinianRing.localization_surjective

theorem localization_artinian : IsArtinianRing L :=
  (localization_surjective S L).isArtinianRing
#align is_artinian_ring.localization_artinian IsArtinianRing.localization_artinian

/-- `IsArtinianRing.localization_artinian` can't be made an instance, as it would make `S` + `R`
into metavariables. However, this is safe. -/
instance : IsArtinianRing (Localization S) :=
  localization_artinian S _

end Localization

instance isMaximal_of_isPrime (p : Ideal R) [p.IsPrime] : p.IsMaximal :=
  Ideal.Quotient.maximal_of_isField _ <|
    (MulEquiv.ofBijective _ ⟨IsFractionRing.injective (R ⧸ p) (FractionRing (R ⧸ p)),
      localization_surjective (nonZeroDivisors (R ⧸ p)) (FractionRing (R ⧸ p))⟩).isField _
    <| Field.toIsField <| FractionRing (R ⧸ p)

lemma isPrime_iff_isMaximal (p : Ideal R) : p.IsPrime ↔ p.IsMaximal :=
  ⟨fun _ ↦ isMaximal_of_isPrime p, fun h ↦ h.isPrime⟩

variable (R) in
lemma primeSpectrum_finite : {I : Ideal R | I.IsPrime}.Finite := by
  set Spec := {I : Ideal R | I.IsPrime}
  obtain ⟨_, ⟨s, rfl⟩, H⟩ := set_has_minimal
    (range (Finset.inf · Subtype.val : Finset Spec → Ideal R)) ⟨⊤, ∅, by simp⟩
  refine Set.finite_def.2 ⟨s, fun p ↦ ?_⟩
  classical
  obtain ⟨q, hq1, hq2⟩ := p.2.inf_le'.mp <| inf_eq_right.mp <|
    inf_le_right.eq_of_not_lt (H (p ⊓ s.inf Subtype.val) ⟨insert p s, by simp⟩)
  rwa [← Subtype.ext <| (@isMaximal_of_isPrime _ _ _ _ q.2).eq_of_le p.2.1 hq2]

variable (R)
/--
[Stacks Lemma 00J7](https://stacks.math.columbia.edu/tag/00J7)
-/
lemma maximal_ideals_finite : {I : Ideal R | I.IsMaximal}.Finite := by
  simp_rw [← isPrime_iff_isMaximal]
  apply primeSpectrum_finite R

@[local instance] lemma subtype_isMaximal_finite : Finite {I : Ideal R | I.IsMaximal} :=
  (maximal_ideals_finite R).to_subtype

/-- A temporary field instance on the quotients by maximal ideals. -/
@[local instance] noncomputable def fieldOfSubtypeIsMaximal
    (I : {I : Ideal R | I.IsMaximal}) : Field (R ⧸ I.1) :=
  have := mem_setOf.mp I.2; Ideal.Quotient.field I.1

/-- The quotient of a commutative artinian ring by its nilradical is isomorphic to
a finite product of fields, namely the quotients by the maximal ideals. -/
noncomputable def quotNilradicalEquivPi :
    R ⧸ nilradical R ≃+* ∀ I : {I : Ideal R | I.IsMaximal}, R ⧸ I.1 :=
  .trans (Ideal.quotEquivOfEq <| ext fun x ↦ by simp_rw [mem_nilradical,
    nilpotent_iff_mem_prime, Submodule.mem_iInf, Subtype.forall, isPrime_iff_isMaximal, mem_setOf])
  (Ideal.quotientInfRingEquivPiQuotient _ fun I J h ↦
    Ideal.isCoprime_iff_sup_eq.mpr <| I.2.coprime_of_ne J.2 <| by rwa [Ne, Subtype.coe_inj])

/-- A reduced commutative artinian ring is isomorphic to a finite product of fields,
namely the quotients by the maximal ideals. -/
noncomputable def equivPi [IsReduced R] : R ≃+* ∀ I : {I : Ideal R | I.IsMaximal}, R ⧸ I.1 :=
  .trans (.symm <| .quotientBot R) <| .trans
    (Ideal.quotEquivOfEq (nilradical_eq_zero R).symm) (quotNilradicalEquivPi R)

instance [IsReduced R] : DecompositionMonoid R := MulEquiv.decompositionMonoid (equivPi R)

instance [IsReduced R] : DecompositionMonoid (Polynomial R) :=
  MulEquiv.decompositionMonoid <| (Polynomial.mapEquiv <| equivPi R).trans (Polynomial.piEquiv _)

theorem isSemisimpleRing_of_isReduced [IsReduced R] : IsSemisimpleRing R :=
  (equivPi R).symm.isSemisimpleRing

proof_wanted IsSemisimpleRing.isArtinianRing [IsSemisimpleRing R] : IsArtinianRing R

end IsArtinianRing
