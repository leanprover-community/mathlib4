/-
Copyright (c) 2018 Mario Carneiro, Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Buzzard
-/
import Mathlib.Order.Filter.EventuallyConst
import Mathlib.Order.PartialSups
import Mathlib.Algebra.Module.Submodule.IterateMapComap
import Mathlib.RingTheory.OrzechProperty
import Mathlib.RingTheory.Nilpotent.Lemmas

#align_import ring_theory.noetherian from "leanprover-community/mathlib"@"210657c4ea4a4a7b234392f70a3a2a83346dfa90"

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

* `isNoetherian_iff_wellFounded` is the theorem that an R-module M is Noetherian iff
  `>` is well-founded on `Submodule R M`.

Note that the Hilbert basis theorem, that if a commutative ring R is Noetherian then so is R[X],
is proved in `RingTheory.Polynomial`.

## References

* [M. F. Atiyah and I. G. Macdonald, *Introduction to commutative algebra*][atiyah-macdonald]
* [samuel1967]

## Tags

Noetherian, noetherian, Noetherian ring, Noetherian module, noetherian ring, noetherian module

-/


open Set Filter Pointwise

/-- `IsNoetherian R M` is the proposition that `M` is a Noetherian `R`-module,
implemented as the predicate that all `R`-submodules of `M` are finitely generated.
-/
-- Porting note: should this be renamed to `Noetherian`?
class IsNoetherian (R M) [Semiring R] [AddCommMonoid M] [Module R M] : Prop where
  noetherian : ∀ s : Submodule R M, s.FG
#align is_noetherian IsNoetherian

attribute [inherit_doc IsNoetherian] IsNoetherian.noetherian

section

variable {R : Type*} {M : Type*} {P : Type*}
variable [Semiring R] [AddCommMonoid M] [AddCommMonoid P]
variable [Module R M] [Module R P]

open IsNoetherian

/-- An R-module is Noetherian iff all its submodules are finitely-generated. -/
theorem isNoetherian_def : IsNoetherian R M ↔ ∀ s : Submodule R M, s.FG :=
  ⟨fun h => h.noetherian, IsNoetherian.mk⟩
#align is_noetherian_def isNoetherian_def

theorem isNoetherian_submodule {N : Submodule R M} :
    IsNoetherian R N ↔ ∀ s : Submodule R M, s ≤ N → s.FG := by
  refine ⟨fun ⟨hn⟩ => fun s hs =>
    have : s ≤ LinearMap.range N.subtype := N.range_subtype.symm ▸ hs
    Submodule.map_comap_eq_self this ▸ (hn _).map _,
    fun h => ⟨fun s => ?_⟩⟩
  have f := (Submodule.equivMapOfInjective N.subtype Subtype.val_injective s).symm
  have h₁ := h (s.map N.subtype) (Submodule.map_subtype_le N s)
  have h₂ : (⊤ : Submodule R (s.map N.subtype)).map f = ⊤ := by simp
  have h₃ := ((Submodule.fg_top _).2 h₁).map (↑f : _ →ₗ[R] s)
  exact (Submodule.fg_top _).1 (h₂ ▸ h₃)
#align is_noetherian_submodule isNoetherian_submodule

theorem isNoetherian_submodule_left {N : Submodule R M} :
    IsNoetherian R N ↔ ∀ s : Submodule R M, (N ⊓ s).FG :=
  isNoetherian_submodule.trans ⟨fun H _ => H _ inf_le_left, fun H _ hs => inf_of_le_right hs ▸ H _⟩
#align is_noetherian_submodule_left isNoetherian_submodule_left

theorem isNoetherian_submodule_right {N : Submodule R M} :
    IsNoetherian R N ↔ ∀ s : Submodule R M, (s ⊓ N).FG :=
  isNoetherian_submodule.trans ⟨fun H _ => H _ inf_le_right, fun H _ hs => inf_of_le_left hs ▸ H _⟩
#align is_noetherian_submodule_right isNoetherian_submodule_right

instance isNoetherian_submodule' [IsNoetherian R M] (N : Submodule R M) : IsNoetherian R N :=
  isNoetherian_submodule.2 fun _ _ => IsNoetherian.noetherian _
#align is_noetherian_submodule' isNoetherian_submodule'

theorem isNoetherian_of_le {s t : Submodule R M} [ht : IsNoetherian R t] (h : s ≤ t) :
    IsNoetherian R s :=
  isNoetherian_submodule.mpr fun _ hs' => isNoetherian_submodule.mp ht _ (le_trans hs' h)
#align is_noetherian_of_le isNoetherian_of_le

variable (M)

theorem isNoetherian_of_surjective (f : M →ₗ[R] P) (hf : LinearMap.range f = ⊤) [IsNoetherian R M] :
    IsNoetherian R P :=
  ⟨fun s =>
    have : (s.comap f).map f = s := Submodule.map_comap_eq_self <| hf.symm ▸ le_top
    this ▸ (noetherian _).map _⟩
#align is_noetherian_of_surjective isNoetherian_of_surjective

variable {M}

instance isNoetherian_quotient {R} [Ring R] {M} [AddCommGroup M] [Module R M]
    (N : Submodule R M) [IsNoetherian R M] : IsNoetherian R (M ⧸ N) :=
  isNoetherian_of_surjective _ _ (LinearMap.range_eq_top.mpr N.mkQ_surjective)
#align submodule.quotient.is_noetherian isNoetherian_quotient

@[deprecated (since := "2024-04-27"), nolint defLemma]
alias Submodule.Quotient.isNoetherian := isNoetherian_quotient

theorem isNoetherian_of_linearEquiv (f : M ≃ₗ[R] P) [IsNoetherian R M] : IsNoetherian R P :=
  isNoetherian_of_surjective _ f.toLinearMap f.range
#align is_noetherian_of_linear_equiv isNoetherian_of_linearEquiv

theorem isNoetherian_top_iff : IsNoetherian R (⊤ : Submodule R M) ↔ IsNoetherian R M := by
  constructor <;> intro h
  · exact isNoetherian_of_linearEquiv (LinearEquiv.ofTop (⊤ : Submodule R M) rfl)
  · exact isNoetherian_of_linearEquiv (LinearEquiv.ofTop (⊤ : Submodule R M) rfl).symm
#align is_noetherian_top_iff isNoetherian_top_iff

theorem isNoetherian_of_injective [IsNoetherian R P] (f : M →ₗ[R] P) (hf : Function.Injective f) :
    IsNoetherian R M :=
  isNoetherian_of_linearEquiv (LinearEquiv.ofInjective f hf).symm
#align is_noetherian_of_injective isNoetherian_of_injective

theorem fg_of_injective [IsNoetherian R P] {N : Submodule R M} (f : M →ₗ[R] P)
    (hf : Function.Injective f) : N.FG :=
  haveI := isNoetherian_of_injective f hf
  IsNoetherian.noetherian N
#align fg_of_injective fg_of_injective

end

namespace Module

variable {R M N : Type*}
variable [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
variable (R M)

-- see Note [lower instance priority]
instance (priority := 100) IsNoetherian.finite [IsNoetherian R M] : Finite R M :=
  ⟨IsNoetherian.noetherian ⊤⟩
#align module.is_noetherian.finite Module.IsNoetherian.finite

instance {R₁ S : Type*} [CommSemiring R₁] [Semiring S] [Algebra R₁ S]
    [IsNoetherian R₁ S] (I : Ideal S) : Finite R₁ I :=
  IsNoetherian.finite R₁ ((I : Submodule S S).restrictScalars R₁)

variable {R M}

theorem Finite.of_injective [IsNoetherian R N] (f : M →ₗ[R] N) (hf : Function.Injective f) :
    Finite R M :=
  ⟨fg_of_injective f hf⟩
#align module.finite.of_injective Module.Finite.of_injective

end Module

section

variable {R : Type*} {M : Type*} {P : Type*}
variable [Ring R] [AddCommGroup M] [AddCommGroup P]
variable [Module R M] [Module R P]

open IsNoetherian

theorem isNoetherian_of_ker_bot [IsNoetherian R P] (f : M →ₗ[R] P) (hf : LinearMap.ker f = ⊥) :
    IsNoetherian R M :=
  isNoetherian_of_linearEquiv (LinearEquiv.ofInjective f <| LinearMap.ker_eq_bot.mp hf).symm
#align is_noetherian_of_ker_bot isNoetherian_of_ker_bot

theorem fg_of_ker_bot [IsNoetherian R P] {N : Submodule R M} (f : M →ₗ[R] P)
    (hf : LinearMap.ker f = ⊥) : N.FG :=
  haveI := isNoetherian_of_ker_bot f hf
  IsNoetherian.noetherian N
#align fg_of_ker_bot fg_of_ker_bot

instance isNoetherian_prod [IsNoetherian R M] [IsNoetherian R P] : IsNoetherian R (M × P) :=
  ⟨fun s =>
    Submodule.fg_of_fg_map_of_fg_inf_ker (LinearMap.snd R M P) (noetherian _) <|
      have : s ⊓ LinearMap.ker (LinearMap.snd R M P) ≤ LinearMap.range (LinearMap.inl R M P) :=
        fun x ⟨_, hx2⟩ => ⟨x.1, Prod.ext rfl <| Eq.symm <| LinearMap.mem_ker.1 hx2⟩
      Submodule.map_comap_eq_self this ▸ (noetherian _).map _⟩
#align is_noetherian_prod isNoetherian_prod

instance isNoetherian_pi {R ι : Type*} {M : ι → Type*}
    [Ring R] [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [Finite ι]
    [∀ i, IsNoetherian R (M i)] : IsNoetherian R (∀ i, M i) := by
  cases nonempty_fintype ι
  haveI := Classical.decEq ι
  suffices on_finset : ∀ s : Finset ι, IsNoetherian R (∀ i : s, M i) by
    let coe_e := Equiv.subtypeUnivEquiv <| @Finset.mem_univ ι _
    letI : IsNoetherian R (∀ i : Finset.univ, M (coe_e i)) := on_finset Finset.univ
    exact isNoetherian_of_linearEquiv (LinearEquiv.piCongrLeft R M coe_e)
  intro s
  induction' s using Finset.induction with a s has ih
  · exact ⟨fun s => by
      have : s = ⊥ := by simp only [eq_iff_true_of_subsingleton]
      rw [this]
      apply Submodule.fg_bot⟩
  refine
    @isNoetherian_of_linearEquiv R (M a × ((i : s) → M i)) _ _ _ _ _ _ ?_ <|
      @isNoetherian_prod R (M a) _ _ _ _ _ _ _ ih
  refine
  { toFun := fun f i =>
      (Finset.mem_insert.1 i.2).by_cases
        (fun h : i.1 = a => show M i.1 from Eq.recOn h.symm f.1)
        (fun h : i.1 ∈ s => show M i.1 from f.2 ⟨i.1, h⟩),
    invFun := fun f =>
      (f ⟨a, Finset.mem_insert_self _ _⟩, fun i => f ⟨i.1, Finset.mem_insert_of_mem i.2⟩),
    map_add' := ?_,
    map_smul' := ?_
    left_inv := ?_,
    right_inv := ?_ }
  · intro f g
    ext i
    unfold Or.by_cases
    cases' i with i hi
    rcases Finset.mem_insert.1 hi with (rfl | h)
    · change _ = _ + _
      simp only [dif_pos]
      rfl
    · change _ = _ + _
      have : ¬i = a := by
        rintro rfl
        exact has h
      simp only [dif_neg this, dif_pos h]
      rfl
  · intro c f
    ext i
    unfold Or.by_cases
    cases' i with i hi
    rcases Finset.mem_insert.1 hi with (rfl | h)
    · dsimp
      simp only [dif_pos]
    · dsimp
      have : ¬i = a := by
        rintro rfl
        exact has h
      simp only [dif_neg this, dif_pos h]
  · intro f
    apply Prod.ext
    · simp only [Or.by_cases, dif_pos]
    · ext ⟨i, his⟩
      have : ¬i = a := by
        rintro rfl
        exact has his
      simp only [Or.by_cases, this, not_false_iff, dif_neg]
  · intro f
    ext ⟨i, hi⟩
    rcases Finset.mem_insert.1 hi with (rfl | h)
    · simp only [Or.by_cases, dif_pos]
    · have : ¬i = a := by
        rintro rfl
        exact has h
      simp only [Or.by_cases, dif_neg this, dif_pos h]
#align is_noetherian_pi isNoetherian_pi

/-- A version of `isNoetherian_pi` for non-dependent functions. We need this instance because
sometimes Lean fails to apply the dependent version in non-dependent settings (e.g., it fails to
prove that `ι → ℝ` is finite dimensional over `ℝ`). -/
instance isNoetherian_pi' {R ι M : Type*} [Ring R] [AddCommGroup M] [Module R M] [Finite ι]
    [IsNoetherian R M] : IsNoetherian R (ι → M) :=
  isNoetherian_pi
#align is_noetherian_pi' isNoetherian_pi'

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

universe w

variable {R M P : Type*} {N : Type w} [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N] [AddCommMonoid P] [Module R P]

theorem isNoetherian_iff_wellFounded :
    IsNoetherian R M ↔ WellFounded ((· > ·) : Submodule R M → Submodule R M → Prop) := by
  have := (CompleteLattice.wellFounded_characterisations <| Submodule R M).out 0 3
  -- Porting note: inlining this makes rw complain about it being a metavariable
  rw [this]
  exact
    ⟨fun ⟨h⟩ => fun k => (fg_iff_compact k).mp (h k), fun h =>
      ⟨fun k => (fg_iff_compact k).mpr (h k)⟩⟩
#align is_noetherian_iff_well_founded isNoetherian_iff_wellFounded

theorem isNoetherian_iff_fg_wellFounded :
    IsNoetherian R M ↔
      WellFounded
        ((· > ·) : { N : Submodule R M // N.FG } → { N : Submodule R M // N.FG } → Prop) := by
  let α := { N : Submodule R M // N.FG }
  constructor
  · intro H
    let f : α ↪o Submodule R M := OrderEmbedding.subtype _
    exact OrderEmbedding.wellFounded f.dual (isNoetherian_iff_wellFounded.mp H)
  · intro H
    constructor
    intro N
    obtain ⟨⟨N₀, h₁⟩, e : N₀ ≤ N, h₂⟩ :=
      WellFounded.has_min H { N' : α | N'.1 ≤ N } ⟨⟨⊥, Submodule.fg_bot⟩, @bot_le _ _ _ N⟩
    convert h₁
    refine (e.antisymm ?_).symm
    by_contra h₃
    obtain ⟨x, hx₁ : x ∈ N, hx₂ : x ∉ N₀⟩ := Set.not_subset.mp h₃
    apply hx₂
    rw [eq_of_le_of_not_lt (le_sup_right : N₀ ≤ _) (h₂
      ⟨_, Submodule.FG.sup ⟨{x}, by rw [Finset.coe_singleton]⟩ h₁⟩ <|
      sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hx₁) e)]
    exact (le_sup_left : (R ∙ x) ≤ _) (Submodule.mem_span_singleton_self _)
#align is_noetherian_iff_fg_well_founded isNoetherian_iff_fg_wellFounded

variable (R M)

theorem wellFounded_submodule_gt (R M) [Semiring R] [AddCommMonoid M] [Module R M] :
    ∀ [IsNoetherian R M], WellFounded ((· > ·) : Submodule R M → Submodule R M → Prop) :=
  isNoetherian_iff_wellFounded.mp ‹_›
#align well_founded_submodule_gt wellFounded_submodule_gt

variable {R M}

/-- A module is Noetherian iff every nonempty set of submodules has a maximal submodule among them.
-/
theorem set_has_maximal_iff_noetherian :
    (∀ a : Set <| Submodule R M, a.Nonempty → ∃ M' ∈ a, ∀ I ∈ a, ¬M' < I) ↔ IsNoetherian R M := by
  rw [isNoetherian_iff_wellFounded, WellFounded.wellFounded_iff_has_min]
#align set_has_maximal_iff_noetherian set_has_maximal_iff_noetherian

/-- A module is Noetherian iff every increasing chain of submodules stabilizes. -/
theorem monotone_stabilizes_iff_noetherian :
    (∀ f : ℕ →o Submodule R M, ∃ n, ∀ m, n ≤ m → f n = f m) ↔ IsNoetherian R M := by
  rw [isNoetherian_iff_wellFounded, WellFounded.monotone_chain_condition]
#align monotone_stabilizes_iff_noetherian monotone_stabilizes_iff_noetherian

theorem eventuallyConst_of_isNoetherian [IsNoetherian R M] (f : ℕ →o Submodule R M) :
    atTop.EventuallyConst f := by
  simp_rw [eventuallyConst_atTop, eq_comm]
  exact (monotone_stabilizes_iff_noetherian.mpr inferInstance) f

/-- If `∀ I > J, P I` implies `P J`, then `P` holds for all submodules. -/
theorem IsNoetherian.induction [IsNoetherian R M] {P : Submodule R M → Prop}
    (hgt : ∀ I, (∀ J > I, P J) → P I) (I : Submodule R M) : P I :=
  WellFounded.recursion (wellFounded_submodule_gt R M) I hgt
#align is_noetherian.induction IsNoetherian.induction

end

section

universe w

variable {R M P : Type*} {N : Type w} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] [AddCommGroup P] [Module R P] [IsNoetherian R M]

lemma Submodule.finite_ne_bot_of_independent {ι : Type*} {N : ι → Submodule R M}
    (h : CompleteLattice.Independent N) :
    Set.Finite {i | N i ≠ ⊥} :=
  CompleteLattice.WellFounded.finite_ne_bot_of_independent
    (isNoetherian_iff_wellFounded.mp inferInstance) h

/-- A linearly-independent family of vectors in a module over a non-trivial ring must be finite if
the module is Noetherian. -/
theorem LinearIndependent.finite_of_isNoetherian [Nontrivial R] {ι} {v : ι → M}
    (hv : LinearIndependent R v) : Finite ι := by
  have hwf := isNoetherian_iff_wellFounded.mp (by infer_instance : IsNoetherian R M)
  refine CompleteLattice.WellFounded.finite_of_independent hwf hv.independent_span_singleton
    fun i contra => ?_
  apply hv.ne_zero i
  have : v i ∈ R ∙ v i := Submodule.mem_span_singleton_self (v i)
  rwa [contra, Submodule.mem_bot] at this
#align linear_independent.finite_of_is_noetherian LinearIndependent.finite_of_isNoetherian

theorem LinearIndependent.set_finite_of_isNoetherian [Nontrivial R] {s : Set M}
    (hi : LinearIndependent R ((↑) : s → M)) : s.Finite :=
  @Set.toFinite _ _ hi.finite_of_isNoetherian
#align linear_independent.set_finite_of_is_noetherian LinearIndependent.set_finite_of_isNoetherian

@[deprecated]
alias finite_of_linearIndependent := LinearIndependent.set_finite_of_isNoetherian
#align finite_of_linear_independent LinearIndependent.set_finite_of_isNoetherian

/-- If the first and final modules in an exact sequence are Noetherian,
  then the middle module is also Noetherian. -/
theorem isNoetherian_of_range_eq_ker [IsNoetherian R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (h : LinearMap.range f = LinearMap.ker g) :
    IsNoetherian R N :=
  isNoetherian_iff_wellFounded.2 <|
    wellFounded_gt_exact_sequence
      (wellFounded_submodule_gt R _) (wellFounded_submodule_gt R _)
      (LinearMap.range f)
      (Submodule.map (f.ker.liftQ f <| le_rfl))
      (Submodule.comap (f.ker.liftQ f <| le_rfl))
      (Submodule.comap g.rangeRestrict) (Submodule.map g.rangeRestrict)
      (Submodule.gciMapComap <| LinearMap.ker_eq_bot.mp <|
        Submodule.ker_liftQ_eq_bot _ _ _ (le_refl _))
      (Submodule.giMapComap g.surjective_rangeRestrict)
      (by simp [Submodule.map_comap_eq, inf_comm, Submodule.range_liftQ])
      (by simp [Submodule.comap_map_eq, h])
#align is_noetherian_of_range_eq_ker isNoetherian_of_range_eq_ker

/-- For an endomorphism of a Noetherian module, any sufficiently large iterate has disjoint kernel
and range. -/
theorem LinearMap.eventually_disjoint_ker_pow_range_pow (f : M →ₗ[R] M) :
    ∀ᶠ n in atTop, Disjoint (LinearMap.ker (f ^ n)) (LinearMap.range (f ^ n)) := by
  obtain ⟨n, hn : ∀ m, n ≤ m → LinearMap.ker (f ^ n) = LinearMap.ker (f ^ m)⟩ :=
    monotone_stabilizes_iff_noetherian.mpr inferInstance f.iterateKer
  refine eventually_atTop.mpr ⟨n, fun m hm ↦ disjoint_iff.mpr ?_⟩
  rw [← hn _ hm, Submodule.eq_bot_iff]
  rintro - ⟨hx, ⟨x, rfl⟩⟩
  apply LinearMap.pow_map_zero_of_le hm
  replace hx : x ∈ LinearMap.ker (f ^ (n + m)) := by
    simpa [f.pow_apply n, f.pow_apply m, ← f.pow_apply (n + m), ← iterate_add_apply] using hx
  rwa [← hn _ (n.le_add_right m)] at hx
#align is_noetherian.exists_endomorphism_iterate_ker_inf_range_eq_bot LinearMap.eventually_disjoint_ker_pow_range_pow

lemma LinearMap.eventually_iSup_ker_pow_eq (f : M →ₗ[R] M) :
    ∀ᶠ n in atTop, ⨆ m, LinearMap.ker (f ^ m) = LinearMap.ker (f ^ n) := by
  obtain ⟨n, hn : ∀ m, n ≤ m → ker (f ^ n) = ker (f ^ m)⟩ :=
    monotone_stabilizes_iff_noetherian.mpr inferInstance f.iterateKer
  refine eventually_atTop.mpr ⟨n, fun m hm ↦ ?_⟩
  refine le_antisymm (iSup_le fun l ↦ ?_) (le_iSup (fun i ↦ LinearMap.ker (f ^ i)) m)
  rcases le_or_lt m l with h | h
  · rw [← hn _ (hm.trans h), hn _ hm]
  · exact f.iterateKer.monotone h.le

/-- **Orzech's theorem** for Noetherian module: if `R` is a ring (not necessarily commutative),
`M` and `N` are `R`-modules, `M` is Noetherian, `i : N →ₗ[R] M` is injective,
`f : N →ₗ[R] M` is surjective, then `f` is also injective. The proof here is adapted from
Djoković's paper *Epimorphisms of modules which must be isomorphisms* [djokovic1973],
utilizing `LinearMap.iterateMapComap`.
See also Orzech's original paper: *Onto endomorphisms are isomorphisms* [orzech1971]. -/
theorem IsNoetherian.injective_of_surjective_of_injective (i f : N →ₗ[R] M)
    (hi : Injective i) (hf : Surjective f) : Injective f := by
  haveI := isNoetherian_of_injective i hi
  obtain ⟨n, H⟩ := monotone_stabilizes_iff_noetherian.2 ‹_›
    ⟨_, monotone_nat_of_le_succ <| f.iterateMapComap_le_succ i ⊥ (by simp)⟩
  exact LinearMap.ker_eq_bot.1 <| bot_unique <|
    f.ker_le_of_iterateMapComap_eq_succ i ⊥ n (H _ (Nat.le_succ _)) hf hi

/-- **Orzech's theorem** for Noetherian module: if `R` is a ring (not necessarily commutative),
`M` is a Noetherian `R`-module, `N` is a submodule, `f : N →ₗ[R] M` is surjective, then `f` is also
injective. -/
theorem IsNoetherian.injective_of_surjective_of_submodule
    {N : Submodule R M} (f : N →ₗ[R] M) (hf : Surjective f) : Injective f :=
  IsNoetherian.injective_of_surjective_of_injective N.subtype f N.injective_subtype hf

/-- Any surjective endomorphism of a Noetherian module is injective. -/
theorem IsNoetherian.injective_of_surjective_endomorphism (f : M →ₗ[R] M)
    (s : Surjective f) : Injective f :=
  IsNoetherian.injective_of_surjective_of_injective _ f (LinearEquiv.refl _ _).injective s
#align is_noetherian.injective_of_surjective_endomorphism IsNoetherian.injective_of_surjective_endomorphism

/-- Any surjective endomorphism of a Noetherian module is bijective. -/
theorem IsNoetherian.bijective_of_surjective_endomorphism (f : M →ₗ[R] M)
    (s : Surjective f) : Bijective f :=
  ⟨IsNoetherian.injective_of_surjective_endomorphism f s, s⟩
#align is_noetherian.bijective_of_surjective_endomorphism IsNoetherian.bijective_of_surjective_endomorphism

/-- A sequence `f` of submodules of a noetherian module,
with `f (n+1)` disjoint from the supremum of `f 0`, ..., `f n`,
is eventually zero.
-/
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
  exact
    ⟨n, fun m p =>
      (h m).eq_bot_of_ge <| sup_eq_left.1 <| (w (m + 1) <| le_add_right p).symm.trans <| w m p⟩
#align is_noetherian.disjoint_partial_sups_eventually_bot IsNoetherian.disjoint_partialSups_eventually_bot

/-- If `M ⊕ N` embeds into `M`, for `M` noetherian over `R`, then `N` is trivial. -/
theorem IsNoetherian.subsingleton_of_prod_injective (f : M × N →ₗ[R] M)
    (i : Injective f) : Subsingleton N := .intro fun x y ↦ by
  have h := IsNoetherian.injective_of_surjective_of_injective f _ i LinearMap.fst_surjective
  simpa using h (show LinearMap.fst R M N (0, x) = LinearMap.fst R M N (0, y) from rfl)

/-- If `M ⊕ N` embeds into `M`, for `M` noetherian over `R`, then `N` is trivial. -/
@[simps!]
def IsNoetherian.equivPUnitOfProdInjective (f : M × N →ₗ[R] M)
    (i : Injective f) : N ≃ₗ[R] PUnit.{w + 1} :=
  haveI := IsNoetherian.subsingleton_of_prod_injective f i
  .ofSubsingleton _ _
#align is_noetherian.equiv_punit_of_prod_injective IsNoetherian.equivPUnitOfProdInjective

end

/-- A (semi)ring is Noetherian if it is Noetherian as a module over itself,
i.e. all its ideals are finitely generated.
-/
abbrev IsNoetherianRing (R) [Semiring R] :=
  IsNoetherian R R
#align is_noetherian_ring IsNoetherianRing

theorem isNoetherianRing_iff {R} [Semiring R] : IsNoetherianRing R ↔ IsNoetherian R R :=
  Iff.rfl
#align is_noetherian_ring_iff isNoetherianRing_iff

/-- A ring is Noetherian if and only if all its ideals are finitely-generated. -/
theorem isNoetherianRing_iff_ideal_fg (R : Type*) [Semiring R] :
    IsNoetherianRing R ↔ ∀ I : Ideal R, I.FG :=
  isNoetherianRing_iff.trans isNoetherian_def
#align is_noetherian_ring_iff_ideal_fg isNoetherianRing_iff_ideal_fg

-- see Note [lower instance priority]
instance (priority := 80) isNoetherian_of_finite (R M) [Finite M] [Semiring R] [AddCommMonoid M]
    [Module R M] : IsNoetherian R M :=
  ⟨fun s => ⟨(s : Set M).toFinite.toFinset, by rw [Set.Finite.coe_toFinset, Submodule.span_eq]⟩⟩
#align is_noetherian_of_finite isNoetherian_of_finite

-- see Note [lower instance priority]
/-- Modules over the trivial ring are Noetherian. -/
instance (priority := 100) isNoetherian_of_subsingleton (R M) [Subsingleton R] [Semiring R]
    [AddCommMonoid M] [Module R M] : IsNoetherian R M :=
  haveI := Module.subsingleton R M
  isNoetherian_of_finite R M
#align is_noetherian_of_subsingleton isNoetherian_of_subsingleton

theorem isNoetherian_of_submodule_of_noetherian (R M) [Semiring R] [AddCommMonoid M] [Module R M]
    (N : Submodule R M) (h : IsNoetherian R M) : IsNoetherian R N := by
  rw [isNoetherian_iff_wellFounded] at h ⊢
  exact OrderEmbedding.wellFounded (Submodule.MapSubtype.orderEmbedding N).dual h
#align is_noetherian_of_submodule_of_noetherian isNoetherian_of_submodule_of_noetherian

/-- If `M / S / R` is a scalar tower, and `M / R` is Noetherian, then `M / S` is
also noetherian. -/
theorem isNoetherian_of_tower (R) {S M} [Semiring R] [Semiring S] [AddCommMonoid M] [SMul R S]
    [Module S M] [Module R M] [IsScalarTower R S M] (h : IsNoetherian R M) : IsNoetherian S M := by
  rw [isNoetherian_iff_wellFounded] at h ⊢
  exact (Submodule.restrictScalarsEmbedding R S M).dual.wellFounded h
#align is_noetherian_of_tower isNoetherian_of_tower

theorem isNoetherian_of_fg_of_noetherian {R M} [Ring R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) [I : IsNoetherianRing R] (hN : N.FG) : IsNoetherian R N := by
  let ⟨s, hs⟩ := hN
  haveI := Classical.decEq M
  haveI := Classical.decEq R
  have : ∀ x ∈ s, x ∈ N := fun x hx => hs ▸ Submodule.subset_span hx
  refine
    @isNoetherian_of_surjective
      R ((↑s : Set M) → R) N _ _ _ (Pi.module _ _ _) _ ?_ ?_ isNoetherian_pi
  · fapply LinearMap.mk
    · fapply AddHom.mk
      · exact fun f => ⟨∑ i ∈ s.attach, f i • i.1, N.sum_mem fun c _ => N.smul_mem _ <| this _ c.2⟩
      · intro f g
        apply Subtype.eq
        change (∑ i ∈ s.attach, (f i + g i) • _) = _
        simp only [add_smul, Finset.sum_add_distrib]
        rfl
    · intro c f
      apply Subtype.eq
      change (∑ i ∈ s.attach, (c • f i) • _) = _
      simp only [smul_eq_mul, mul_smul]
      exact Finset.smul_sum.symm
  · rw [LinearMap.range_eq_top]
    rintro ⟨n, hn⟩
    change n ∈ N at hn
    rw [← hs, ← Set.image_id (s : Set M), Finsupp.mem_span_image_iff_total] at hn
    rcases hn with ⟨l, hl1, hl2⟩
    refine ⟨fun x => l x, Subtype.ext ?_⟩
    change (∑ i ∈ s.attach, l i • (i : M)) = n
    rw [s.sum_attach fun i ↦ l i • i, ← hl2,
      Finsupp.total_apply, Finsupp.sum, eq_comm]
    refine Finset.sum_subset hl1 fun x _ hx => ?_
    rw [Finsupp.not_mem_support_iff.1 hx, zero_smul]
#align is_noetherian_of_fg_of_noetherian isNoetherian_of_fg_of_noetherian

instance isNoetherian_of_isNoetherianRing_of_finite (R M : Type*)
    [Ring R] [AddCommGroup M] [Module R M] [IsNoetherianRing R] [Module.Finite R M] :
    IsNoetherian R M :=
  have : IsNoetherian R (⊤ : Submodule R M) :=
    isNoetherian_of_fg_of_noetherian _ <| Module.finite_def.mp inferInstance
  isNoetherian_of_linearEquiv (LinearEquiv.ofTop (⊤ : Submodule R M) rfl)
#align is_noetherian_of_fg_of_noetherian' isNoetherian_of_isNoetherianRing_of_finite

/-- In a module over a Noetherian ring, the submodule generated by finitely many vectors is
Noetherian. -/
theorem isNoetherian_span_of_finite (R) {M} [Ring R] [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] {A : Set M} (hA : A.Finite) : IsNoetherian R (Submodule.span R A) :=
  isNoetherian_of_fg_of_noetherian _ (Submodule.fg_def.mpr ⟨A, hA, rfl⟩)
#align is_noetherian_span_of_finite isNoetherian_span_of_finite

theorem isNoetherianRing_of_surjective (R) [Ring R] (S) [Ring S] (f : R →+* S)
    (hf : Function.Surjective f) [H : IsNoetherianRing R] : IsNoetherianRing S := by
  rw [isNoetherianRing_iff, isNoetherian_iff_wellFounded] at H ⊢
  exact OrderEmbedding.wellFounded (Ideal.orderEmbeddingOfSurjective f hf).dual H
#align is_noetherian_ring_of_surjective isNoetherianRing_of_surjective

instance isNoetherianRing_range {R} [Ring R] {S} [Ring S] (f : R →+* S) [IsNoetherianRing R] :
    IsNoetherianRing f.range :=
  isNoetherianRing_of_surjective R f.range f.rangeRestrict f.rangeRestrict_surjective
#align is_noetherian_ring_range isNoetherianRing_range

theorem isNoetherianRing_of_ringEquiv (R) [Ring R] {S} [Ring S] (f : R ≃+* S) [IsNoetherianRing R] :
    IsNoetherianRing S :=
  isNoetherianRing_of_surjective R S f.toRingHom f.toEquiv.surjective
#align is_noetherian_ring_of_ring_equiv isNoetherianRing_of_ringEquiv

theorem IsNoetherianRing.isNilpotent_nilradical (R : Type*) [CommRing R] [IsNoetherianRing R] :
    IsNilpotent (nilradical R) := by
  obtain ⟨n, hn⟩ := Ideal.exists_radical_pow_le_of_fg (⊥ : Ideal R) (IsNoetherian.noetherian _)
  exact ⟨n, eq_bot_iff.mpr hn⟩
#align is_noetherian_ring.is_nilpotent_nilradical IsNoetherianRing.isNilpotent_nilradical

/-- Any Noetherian ring satisfies Orzech property.
See also `IsNoetherian.injective_of_surjective_of_submodule` and
`IsNoetherian.injective_of_surjective_of_injective`. -/
instance (priority := 100) IsNoetherianRing.orzechProperty
    (R) [Ring R] [IsNoetherianRing R] : OrzechProperty R where
  injective_of_surjective_of_submodule' {M} :=
    letI := Module.addCommMonoidToAddCommGroup R (M := M)
    IsNoetherian.injective_of_surjective_of_submodule
