/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes

! This file was ported from Lean 3 source module ring_theory.artinian
! leanprover-community/mathlib commit 210657c4ea4a4a7b234392f70a3a2a83346dfa90
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.Nakayama
import Mathbin.Data.SetLike.Fintype

/-!
# Artinian rings and modules


A module satisfying these equivalent conditions is said to be an *Artinian* R-module
if every decreasing chain of submodules is eventually constant, or equivalently,
if the relation `<` on submodules is well founded.

A ring is said to be left (or right) Artinian if it is Artinian as a left (or right) module over
itself, or simply Artinian if it is both left and right Artinian.

## Main definitions

Let `R` be a ring and let `M` and `P` be `R`-modules. Let `N` be an `R`-submodule of `M`.

* `is_artinian R M` is the proposition that `M` is a Artinian `R`-module. It is a class,
  implemented as the predicate that the `<` relation on submodules is well founded.
* `is_artinian_ring R` is the proposition that `R` is a left Artinian ring.

## References

* [M. F. Atiyah and I. G. Macdonald, *Introduction to commutative algebra*][atiyah-macdonald]
* [samuel]

## Tags

Artinian, artinian, Artinian ring, Artinian module, artinian ring, artinian module

-/


open Set

open BigOperators Pointwise

/- ./././Mathport/Syntax/Translate/Command.lean:393:30: infer kinds are unsupported in Lean 4: #[`wellFounded_submodule_lt] [] -/
/-- `is_artinian R M` is the proposition that `M` is an Artinian `R`-module,
implemented as the well-foundedness of submodule inclusion.
-/
class IsArtinian (R M) [Semiring R] [AddCommMonoid M] [Module R M] : Prop where
  wellFounded_submodule_lt : WellFounded ((· < ·) : Submodule R M → Submodule R M → Prop)
#align is_artinian IsArtinian

section

variable {R M P N : Type _}

variable [Ring R] [AddCommGroup M] [AddCommGroup P] [AddCommGroup N]

variable [Module R M] [Module R P] [Module R N]

open IsArtinian

include R

theorem isArtinian_of_injective (f : M →ₗ[R] P) (h : Function.Injective f) [IsArtinian R P] :
    IsArtinian R M :=
  ⟨Subrelation.wf
      (fun A B hAB => show A.map f < B.map f from Submodule.map_strictMono_of_injective h hAB)
      (InvImage.wf (Submodule.map f) (IsArtinian.wellFounded_submodule_lt R P))⟩
#align is_artinian_of_injective isArtinian_of_injective

instance isArtinian_submodule' [IsArtinian R M] (N : Submodule R M) : IsArtinian R N :=
  isArtinian_of_injective N.Subtype Subtype.val_injective
#align is_artinian_submodule' isArtinian_submodule'

theorem isArtinian_of_le {s t : Submodule R M} [ht : IsArtinian R t] (h : s ≤ t) : IsArtinian R s :=
  isArtinian_of_injective (Submodule.ofLe h) (Submodule.ofLe_injective h)
#align is_artinian_of_le isArtinian_of_le

variable (M)

theorem isArtinian_of_surjective (f : M →ₗ[R] P) (hf : Function.Surjective f) [IsArtinian R M] :
    IsArtinian R P :=
  ⟨Subrelation.wf
      (fun A B hAB =>
        show A.comap f < B.comap f from Submodule.comap_strictMono_of_surjective hf hAB)
      (InvImage.wf (Submodule.comap f) (IsArtinian.wellFounded_submodule_lt _ _))⟩
#align is_artinian_of_surjective isArtinian_of_surjective

variable {M}

theorem isArtinian_of_linearEquiv (f : M ≃ₗ[R] P) [IsArtinian R M] : IsArtinian R P :=
  isArtinian_of_surjective _ f.toLinearMap f.toEquiv.Surjective
#align is_artinian_of_linear_equiv isArtinian_of_linearEquiv

theorem isArtinian_of_range_eq_ker [IsArtinian R M] [IsArtinian R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : Function.Injective f) (hg : Function.Surjective g) (h : f.range = g.ker) :
    IsArtinian R N :=
  ⟨wellFounded_lt_exact_sequence (IsArtinian.wellFounded_submodule_lt _ _)
      (IsArtinian.wellFounded_submodule_lt _ _) f.range (Submodule.map f) (Submodule.comap f)
      (Submodule.comap g) (Submodule.map g) (Submodule.gciMapComap hf) (Submodule.giMapComap hg)
      (by simp [Submodule.map_comap_eq, inf_comm]) (by simp [Submodule.comap_map_eq, h])⟩
#align is_artinian_of_range_eq_ker isArtinian_of_range_eq_ker

instance isArtinian_prod [IsArtinian R M] [IsArtinian R P] : IsArtinian R (M × P) :=
  isArtinian_of_range_eq_ker (LinearMap.inl R M P) (LinearMap.snd R M P) LinearMap.inl_injective
    LinearMap.snd_surjective (LinearMap.range_inl R M P)
#align is_artinian_prod isArtinian_prod

instance (priority := 100) isArtinian_of_finite [Finite M] : IsArtinian R M :=
  ⟨Finite.wellFounded_of_trans_of_irrefl _⟩
#align is_artinian_of_finite isArtinian_of_finite

attribute [local elab_as_elim] Finite.induction_empty_option

instance isArtinian_pi {R ι : Type _} [Finite ι] :
    ∀ {M : ι → Type _} [Ring R] [∀ i, AddCommGroup (M i)],
      ∀ [∀ i, Module R (M i)], ∀ [∀ i, IsArtinian R (M i)], IsArtinian R (∀ i, M i) :=
  Finite.induction_empty_option
    (by
      intro α β e hα M _ _ _ _
      exact isArtinian_of_linearEquiv (LinearEquiv.piCongrLeft R M e))
    (by
      intro M _ _ _ _
      infer_instance)
    (by
      intro α _ ih M _ _ _ _
      exact isArtinian_of_linearEquiv (LinearEquiv.piOptionEquivProd R).symm)
    ι
#align is_artinian_pi isArtinian_pi

/-- A version of `is_artinian_pi` for non-dependent functions. We need this instance because
sometimes Lean fails to apply the dependent version in non-dependent settings (e.g., it fails to
prove that `ι → ℝ` is finite dimensional over `ℝ`). -/
instance isArtinian_pi' {R ι M : Type _} [Ring R] [AddCommGroup M] [Module R M] [Finite ι]
    [IsArtinian R M] : IsArtinian R (ι → M) :=
  isArtinian_pi
#align is_artinian_pi' isArtinian_pi'

end

open IsArtinian Submodule Function

section Ring

variable {R M : Type _} [Ring R] [AddCommGroup M] [Module R M]

theorem isArtinian_iff_wellFounded :
    IsArtinian R M ↔ WellFounded ((· < ·) : Submodule R M → Submodule R M → Prop) :=
  ⟨fun h => h.1, IsArtinian.mk⟩
#align is_artinian_iff_well_founded isArtinian_iff_wellFounded

variable {R M}

theorem IsArtinian.finite_of_linearIndependent [Nontrivial R] [IsArtinian R M] {s : Set M}
    (hs : LinearIndependent R (coe : s → M)) : s.Finite :=
  by
  refine'
    by_contradiction fun hf =>
      (RelEmbedding.wellFounded_iff_no_descending_seq.1 (well_founded_submodule_lt R M)).elim' _
  have f : ℕ ↪ s := Set.Infinite.natEmbedding s hf
  have : ∀ n, coe ∘ f '' { m | n ≤ m } ⊆ s :=
    by
    rintro n x ⟨y, hy₁, rfl⟩
    exact (f y).2
  have : ∀ a b : ℕ, a ≤ b ↔ span R (coe ∘ f '' { m | b ≤ m }) ≤ span R (coe ∘ f '' { m | a ≤ m }) :=
    by
    intro a b
    rw [span_le_span_iff hs (this b) (this a),
      Set.image_subset_image_iff (subtype.coe_injective.comp f.injective), Set.subset_def]
    simp only [Set.mem_setOf_eq]
    exact ⟨fun hab x => le_trans hab, fun h => h _ le_rfl⟩
  exact
    ⟨⟨fun n => span R (coe ∘ f '' { m | n ≤ m }), fun x y => by
        simp (config := { contextual := true }) [le_antisymm_iff, (this _ _).symm]⟩,
      by
      intro a b
      conv_rhs => rw [GT.gt, lt_iff_le_not_le, this, this, ← lt_iff_le_not_le]
      simp⟩
#align is_artinian.finite_of_linear_independent IsArtinian.finite_of_linearIndependent

/-- A module is Artinian iff every nonempty set of submodules has a minimal submodule among them.
-/
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
    (∀ f : ℕ →o (Submodule R M)ᵒᵈ, ∃ n, ∀ m, n ≤ m → f n = f m) ↔ IsArtinian R M :=
  by
  rw [isArtinian_iff_wellFounded]
  exact well_founded.monotone_chain_condition.symm
#align monotone_stabilizes_iff_artinian monotone_stabilizes_iff_artinian

namespace IsArtinian

variable [IsArtinian R M]

theorem monotone_stabilizes (f : ℕ →o (Submodule R M)ᵒᵈ) : ∃ n, ∀ m, n ≤ m → f n = f m :=
  monotone_stabilizes_iff_artinian.mpr ‹_› f
#align is_artinian.monotone_stabilizes IsArtinian.monotone_stabilizes

/-- If `∀ I > J, P I` implies `P J`, then `P` holds for all submodules. -/
theorem induction {P : Submodule R M → Prop} (hgt : ∀ I, (∀ J < I, P J) → P I) (I : Submodule R M) :
    P I :=
  (wellFounded_submodule_lt R M).recursion I hgt
#align is_artinian.induction IsArtinian.induction

/-- For any endomorphism of a Artinian module, there is some nontrivial iterate
with disjoint kernel and range.
-/
theorem exists_endomorphism_iterate_ker_sup_range_eq_top (f : M →ₗ[R] M) :
    ∃ n : ℕ, n ≠ 0 ∧ (f ^ n).ker ⊔ (f ^ n).range = ⊤ :=
  by
  obtain ⟨n, w⟩ :=
    monotone_stabilizes (f.iterate_range.comp ⟨fun n => n + 1, fun n m w => by linarith⟩)
  specialize w (n + 1 + n) (by linarith)
  dsimp at w
  refine' ⟨n + 1, Nat.succ_ne_zero _, _⟩
  simp_rw [eq_top_iff', mem_sup]
  intro x
  have : (f ^ (n + 1)) x ∈ (f ^ (n + 1 + n + 1)).range :=
    by
    rw [← w]
    exact mem_range_self _
  rcases this with ⟨y, hy⟩
  use x - (f ^ (n + 1)) y
  constructor
  · rw [LinearMap.mem_ker, LinearMap.map_sub, ← hy, sub_eq_zero, pow_add]
    simp [iterate_add_apply]
  · use (f ^ (n + 1)) y
    simp
#align is_artinian.exists_endomorphism_iterate_ker_sup_range_eq_top IsArtinian.exists_endomorphism_iterate_ker_sup_range_eq_top

/-- Any injective endomorphism of an Artinian module is surjective. -/
theorem surjective_of_injective_endomorphism (f : M →ₗ[R] M) (s : Injective f) : Surjective f :=
  by
  obtain ⟨n, ne, w⟩ := exists_endomorphism_iterate_ker_sup_range_eq_top f
  rw [linear_map.ker_eq_bot.mpr (LinearMap.iterate_injective s n), bot_sup_eq,
    LinearMap.range_eq_top] at w
  exact LinearMap.surjective_of_iterate_surjective Ne w
#align is_artinian.surjective_of_injective_endomorphism IsArtinian.surjective_of_injective_endomorphism

/-- Any injective endomorphism of an Artinian module is bijective. -/
theorem bijective_of_injective_endomorphism (f : M →ₗ[R] M) (s : Injective f) : Bijective f :=
  ⟨s, surjective_of_injective_endomorphism f s⟩
#align is_artinian.bijective_of_injective_endomorphism IsArtinian.bijective_of_injective_endomorphism

/-- A sequence `f` of submodules of a artinian module,
with the supremum `f (n+1)` and the infinum of `f 0`, ..., `f n` being ⊤,
is eventually ⊤.
-/
theorem disjoint_partial_infs_eventually_top (f : ℕ → Submodule R M)
    (h : ∀ n, Disjoint (partialSups (OrderDual.toDual ∘ f) n) (OrderDual.toDual (f (n + 1)))) :
    ∃ n : ℕ, ∀ m, n ≤ m → f m = ⊤ :=
  by
  -- A little off-by-one cleanup first:
  rsuffices ⟨n, w⟩ : ∃ n : ℕ, ∀ m, n ≤ m → OrderDual.toDual f (m + 1) = ⊤
  · use n + 1
    rintro (_ | m) p
    · cases p
    · apply w
      exact nat.succ_le_succ_iff.mp p
  obtain ⟨n, w⟩ := monotone_stabilizes (partialSups (OrderDual.toDual ∘ f))
  refine' ⟨n, fun m p => _⟩
  exact (h m).eq_bot_of_ge (sup_eq_left.1 <| (w (m + 1) <| le_add_right p).symm.trans <| w m p)
#align is_artinian.disjoint_partial_infs_eventually_top IsArtinian.disjoint_partial_infs_eventually_top

end IsArtinian

end Ring

section CommRing

variable {R : Type _} (M : Type _) [CommRing R] [AddCommGroup M] [Module R M] [IsArtinian R M]

namespace IsArtinian

theorem range_smul_pow_stabilizes (r : R) :
    ∃ n : ℕ,
      ∀ m,
        n ≤ m →
          (r ^ n • LinearMap.id : M →ₗ[R] M).range = (r ^ m • LinearMap.id : M →ₗ[R] M).range :=
  monotone_stabilizes
    ⟨fun n => (r ^ n • LinearMap.id : M →ₗ[R] M).range, fun n m h x ⟨y, hy⟩ =>
      ⟨r ^ (m - n) • y, by
        dsimp at hy⊢
        rw [← smul_assoc, smul_eq_mul, ← pow_add, ← hy, add_tsub_cancel_of_le h]⟩⟩
#align is_artinian.range_smul_pow_stabilizes IsArtinian.range_smul_pow_stabilizes

variable {M}

theorem exists_pow_succ_smul_dvd (r : R) (x : M) : ∃ (n : ℕ)(y : M), r ^ n.succ • y = r ^ n • x :=
  by
  obtain ⟨n, hn⟩ := IsArtinian.range_smul_pow_stabilizes M r
  simp_rw [SetLike.ext_iff] at hn
  exact ⟨n, by simpa using hn n.succ n.le_succ (r ^ n • x)⟩
#align is_artinian.exists_pow_succ_smul_dvd IsArtinian.exists_pow_succ_smul_dvd

end IsArtinian

end CommRing

-- TODO: Prove this for artinian modules
-- /--
-- If `M ⊕ N` embeds into `M`, for `M` noetherian over `R`, then `N` is trivial.
-- -/
-- universe w
-- variables {N : Type w} [add_comm_group N] [module R N]
-- noncomputable def is_noetherian.equiv_punit_of_prod_injective [is_noetherian R M]
--   (f : M × N →ₗ[R] M) (i : injective f) : N ≃ₗ[R] punit.{w+1} :=
-- begin
--   apply nonempty.some,
--   obtain ⟨n, w⟩ := is_noetherian.disjoint_partial_sups_eventually_bot (f.tailing i)
--     (f.tailings_disjoint_tailing i),
--   specialize w n (le_refl n),
--   apply nonempty.intro,
--   refine (f.tailing_linear_equiv i n).symm.trans _,
--   rw w,
--   exact submodule.bot_equiv_punit,
-- end
/-- A ring is Artinian if it is Artinian as a module over itself.

Strictly speaking, this should be called `is_left_artinian_ring` but we omit the `left_` for
convenience in the commutative case. For a right Artinian ring, use `is_artinian Rᵐᵒᵖ R`. -/
@[reducible]
def IsArtinianRing (R) [Ring R] :=
  IsArtinian R R
#align is_artinian_ring IsArtinianRing

theorem isArtinianRing_iff {R} [Ring R] : IsArtinianRing R ↔ IsArtinian R R :=
  Iff.rfl
#align is_artinian_ring_iff isArtinianRing_iff

theorem Ring.is_artinian_of_zero_eq_one {R} [Ring R] (h01 : (0 : R) = 1) : IsArtinianRing R :=
  have := subsingleton_of_zero_eq_one h01
  inferInstance
#align ring.is_artinian_of_zero_eq_one Ring.is_artinian_of_zero_eq_one

theorem isArtinian_of_submodule_of_artinian (R M) [Ring R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) (h : IsArtinian R M) : IsArtinian R N := by infer_instance
#align is_artinian_of_submodule_of_artinian isArtinian_of_submodule_of_artinian

theorem isArtinian_of_quotient_of_artinian (R) [Ring R] (M) [AddCommGroup M] [Module R M]
    (N : Submodule R M) (h : IsArtinian R M) : IsArtinian R (M ⧸ N) :=
  isArtinian_of_surjective M (Submodule.mkQ N) (Submodule.Quotient.mk_surjective N)
#align is_artinian_of_quotient_of_artinian isArtinian_of_quotient_of_artinian

/-- If `M / S / R` is a scalar tower, and `M / R` is Artinian, then `M / S` is
also Artinian. -/
theorem isArtinian_of_tower (R) {S M} [CommRing R] [Ring S] [AddCommGroup M] [Algebra R S]
    [Module S M] [Module R M] [IsScalarTower R S M] (h : IsArtinian R M) : IsArtinian S M :=
  by
  rw [isArtinian_iff_wellFounded] at h⊢
  refine' (Submodule.restrictScalarsEmbedding R S M).WellFounded h
#align is_artinian_of_tower isArtinian_of_tower

theorem isArtinian_of_fG_of_artinian {R M} [Ring R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) [IsArtinianRing R] (hN : N.FG) : IsArtinian R N :=
  by
  let ⟨s, hs⟩ := hN
  haveI := Classical.decEq M
  haveI := Classical.decEq R
  have : ∀ x ∈ s, x ∈ N := fun x hx => hs ▸ Submodule.subset_span hx
  refine' @isArtinian_of_surjective ((↑s : Set M) → R) _ _ _ (Pi.module _ _ _) _ _ _ isArtinian_pi
  · fapply LinearMap.mk
    · exact fun f => ⟨∑ i in s.attach, f i • i.1, N.sum_mem fun c _ => N.smul_mem _ <| this _ c.2⟩
    · intro f g
      apply Subtype.eq
      change (∑ i in s.attach, (f i + g i) • _) = _
      simp only [add_smul, Finset.sum_add_distrib]
      rfl
    · intro c f
      apply Subtype.eq
      change (∑ i in s.attach, (c • f i) • _) = _
      simp only [smul_eq_mul, mul_smul]
      exact finset.smul_sum.symm
  rintro ⟨n, hn⟩
  change n ∈ N at hn
  rw [← hs, ← Set.image_id ↑s, Finsupp.mem_span_image_iff_total] at hn
  rcases hn with ⟨l, hl1, hl2⟩
  refine' ⟨fun x => l x, Subtype.ext _⟩
  change (∑ i in s.attach, l i • (i : M)) = n
  rw [@Finset.sum_attach M M s _ fun i => l i • i, ← hl2, Finsupp.total_apply, Finsupp.sum, eq_comm]
  refine' Finset.sum_subset hl1 fun x _ hx => _
  rw [Finsupp.not_mem_support_iff.1 hx, zero_smul]
#align is_artinian_of_fg_of_artinian isArtinian_of_fG_of_artinian

theorem isArtinian_of_fG_of_artinian' {R M} [Ring R] [AddCommGroup M] [Module R M]
    [IsArtinianRing R] (h : (⊤ : Submodule R M).FG) : IsArtinian R M :=
  have : IsArtinian R (⊤ : Submodule R M) := isArtinian_of_fG_of_artinian _ h
  isArtinian_of_linearEquiv (LinearEquiv.ofTop (⊤ : Submodule R M) rfl)
#align is_artinian_of_fg_of_artinian' isArtinian_of_fG_of_artinian'

/-- In a module over a artinian ring, the submodule generated by finitely many vectors is
artinian. -/
theorem isArtinian_span_of_finite (R) {M} [Ring R] [AddCommGroup M] [Module R M] [IsArtinianRing R]
    {A : Set M} (hA : A.Finite) : IsArtinian R (Submodule.span R A) :=
  isArtinian_of_fG_of_artinian _ (Submodule.fg_def.mpr ⟨A, hA, rfl⟩)
#align is_artinian_span_of_finite isArtinian_span_of_finite

theorem Function.Surjective.isArtinianRing {R} [Ring R] {S} [Ring S] {F} [RingHomClass F R S]
    {f : F} (hf : Function.Surjective f) [H : IsArtinianRing R] : IsArtinianRing S :=
  by
  rw [isArtinianRing_iff, isArtinian_iff_wellFounded] at H⊢
  exact (Ideal.orderEmbeddingOfSurjective f hf).WellFounded H
#align function.surjective.is_artinian_ring Function.Surjective.isArtinianRing

instance isArtinianRing_range {R} [Ring R] {S} [Ring S] (f : R →+* S) [IsArtinianRing R] :
    IsArtinianRing f.range :=
  f.rangeRestrict_surjective.IsArtinianRing
#align is_artinian_ring_range isArtinianRing_range

namespace IsArtinianRing

open IsArtinian

variable {R : Type _} [CommRing R] [IsArtinianRing R]

theorem isNilpotent_jacobson_bot : IsNilpotent (Ideal.jacobson (⊥ : Ideal R)) :=
  by
  let Jac := Ideal.jacobson (⊥ : Ideal R)
  let f : ℕ →o (Ideal R)ᵒᵈ := ⟨fun n => Jac ^ n, fun _ _ h => Ideal.pow_le_pow h⟩
  obtain ⟨n, hn⟩ : ∃ n, ∀ m, n ≤ m → Jac ^ n = Jac ^ m := IsArtinian.monotone_stabilizes f
  refine' ⟨n, _⟩
  let J : Ideal R := annihilator (Jac ^ n)
  suffices J = ⊤ by
    have hJ : J • Jac ^ n = ⊥ := annihilator_smul (Jac ^ n)
    simpa only [this, top_smul, Ideal.zero_eq_bot] using hJ
  by_contra hJ
  change J ≠ ⊤ at hJ
  rcases IsArtinian.set_has_minimal { J' : Ideal R | J < J' } ⟨⊤, hJ.lt_top⟩ with
    ⟨J', hJJ' : J < J', hJ' : ∀ I, J < I → ¬I < J'⟩
  rcases SetLike.exists_of_lt hJJ' with ⟨x, hxJ', hxJ⟩
  obtain rfl : J ⊔ Ideal.span {x} = J' :=
    by
    apply eq_of_le_of_not_lt _ (hJ' (J ⊔ Ideal.span {x}) _)
    · exact sup_le hJJ'.le (span_le.2 (singleton_subset_iff.2 hxJ'))
    · rw [SetLike.lt_iff_le_and_exists]
      exact ⟨le_sup_left, ⟨x, mem_sup_right (mem_span_singleton_self x), hxJ⟩⟩
  have : J ⊔ Jac • Ideal.span {x} ≤ J ⊔ Ideal.span {x} :=
    sup_le_sup_left (smul_le.2 fun _ _ _ => Submodule.smul_mem _ _) _
  have : Jac * Ideal.span {x} ≤ J := by
    classical
      --Need version 4 of Nakayamas lemma on Stacks
      by_contra H
      refine'
        H
          (smul_sup_le_of_le_smul_of_le_jacobson_bot (fg_span_singleton _) le_rfl
            (this.eq_of_not_lt (hJ' _ _)).ge)
      exact lt_of_le_of_ne le_sup_left fun h => H <| h.symm ▸ le_sup_right
  have : Ideal.span {x} * Jac ^ (n + 1) ≤ ⊥
  calc
    Ideal.span {x} * Jac ^ (n + 1) = Ideal.span {x} * Jac * Jac ^ n := by rw [pow_succ, ← mul_assoc]
    _ ≤ J * Jac ^ n := (mul_le_mul (by rwa [mul_comm]) le_rfl)
    _ = ⊥ := by simp [J]
    
  refine' hxJ (mem_annihilator.2 fun y hy => (mem_bot R).1 _)
  refine' this (mul_mem_mul (mem_span_singleton_self x) _)
  rwa [← hn (n + 1) (Nat.le_succ _)]
#align is_artinian_ring.is_nilpotent_jacobson_bot IsArtinianRing.isNilpotent_jacobson_bot

section Localization

variable (S : Submonoid R) (L : Type _) [CommRing L] [Algebra R L] [IsLocalization S L]

include S

/-- Localizing an artinian ring can only reduce the amount of elements. -/
theorem localization_surjective : Function.Surjective (algebraMap R L) :=
  by
  intro r'
  obtain ⟨r₁, s, rfl⟩ := IsLocalization.mk'_surjective S r'
  obtain ⟨r₂, h⟩ : ∃ r : R, IsLocalization.mk' L 1 s = algebraMap R L r
  swap; · exact ⟨r₁ * r₂, by rw [IsLocalization.mk'_eq_mul_mk'_one, map_mul, h]⟩
  obtain ⟨n, r, hr⟩ := IsArtinian.exists_pow_succ_smul_dvd (s : R) (1 : R)
  use r
  rw [smul_eq_mul, smul_eq_mul, pow_succ', mul_assoc] at hr
  apply_fun algebraMap R L  at hr
  simp only [map_mul, ← [anonymous]] at hr
  rw [← IsLocalization.mk'_one L, IsLocalization.mk'_eq_iff_eq, mul_one, Submonoid.coe_one, ←
    (IsLocalization.map_units L (s ^ n)).mul_left_cancel hr, map_mul]
#align is_artinian_ring.localization_surjective IsArtinianRing.localization_surjective

theorem localization_artinian : IsArtinianRing L :=
  (localization_surjective S L).IsArtinianRing
#align is_artinian_ring.localization_artinian IsArtinianRing.localization_artinian

/-- `is_artinian_ring.localization_artinian` can't be made an instance, as it would make `S` + `R`
into metavariables. However, this is safe. -/
instance : IsArtinianRing (Localization S) :=
  localization_artinian S _

end Localization

end IsArtinianRing

