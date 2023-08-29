/-
Copyright (c) 2018 Mario Carneiro, Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Buzzard
-/
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Ring.Idempotents
import Mathlib.GroupTheory.Finiteness
import Mathlib.LinearAlgebra.LinearIndependent
import Mathlib.Order.CompactlyGenerated
import Mathlib.Order.OrderIsoNat
import Mathlib.RingTheory.Finiteness
import Mathlib.RingTheory.Nilpotent

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


open Set

open BigOperators Pointwise

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
  -- ⊢ Submodule.FG s
  have h₁ := h (s.map N.subtype) (Submodule.map_subtype_le N s)
  -- ⊢ Submodule.FG s
  have h₂ : (⊤ : Submodule R (s.map N.subtype)).map f = ⊤ := by simp
  -- ⊢ Submodule.FG s
  have h₃ := ((Submodule.fg_top _).2 h₁).map (↑f : _ →ₗ[R] s)
  -- ⊢ Submodule.FG s
  exact (Submodule.fg_top _).1 (h₂ ▸ h₃)
  -- 🎉 no goals
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

theorem isNoetherian_of_linearEquiv (f : M ≃ₗ[R] P) [IsNoetherian R M] : IsNoetherian R P :=
  isNoetherian_of_surjective _ f.toLinearMap f.range
#align is_noetherian_of_linear_equiv isNoetherian_of_linearEquiv

theorem isNoetherian_top_iff : IsNoetherian R (⊤ : Submodule R M) ↔ IsNoetherian R M := by
  constructor <;> intro h
  -- ⊢ IsNoetherian R { x // x ∈ ⊤ } → IsNoetherian R M
                  -- ⊢ IsNoetherian R M
                  -- ⊢ IsNoetherian R { x // x ∈ ⊤ }
  · exact isNoetherian_of_linearEquiv (LinearEquiv.ofTop (⊤ : Submodule R M) rfl)
    -- 🎉 no goals
  · exact isNoetherian_of_linearEquiv (LinearEquiv.ofTop (⊤ : Submodule R M) rfl).symm
    -- 🎉 no goals
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
  -- ⊢ IsNoetherian R ((i : ι) → M i)
  haveI := Classical.decEq ι
  -- ⊢ IsNoetherian R ((i : ι) → M i)
  suffices on_finset : ∀ s : Finset ι, IsNoetherian R (∀ i : s, M i)
  -- ⊢ IsNoetherian R ((i : ι) → M i)
  · let coe_e := Equiv.subtypeUnivEquiv <| @Finset.mem_univ ι _
    -- ⊢ IsNoetherian R ((i : ι) → M i)
    letI : IsNoetherian R (∀ i : Finset.univ, M (coe_e i)) := on_finset Finset.univ
    -- ⊢ IsNoetherian R ((i : ι) → M i)
    exact isNoetherian_of_linearEquiv (LinearEquiv.piCongrLeft R M coe_e)
    -- 🎉 no goals
  intro s
  -- ⊢ IsNoetherian R ((i : { x // x ∈ s }) → M ↑i)
  induction' s using Finset.induction with a s has ih
  -- ⊢ IsNoetherian R ((i : { x // x ∈ ∅ }) → M ↑i)
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
    -- ⊢ (fun f i =>
    ext i
    -- ⊢ (fun f i =>
    unfold Or.by_cases
    -- ⊢ (fun f i =>
    cases' i with i hi
    -- ⊢ (fun f i =>
    rcases Finset.mem_insert.1 hi with (rfl | h)
    · change _ = _ + _
      -- ⊢ (fun f i_1 =>
      simp only [dif_pos]
      -- ⊢ (f + g).fst = f.fst + g.fst
      rfl
      -- 🎉 no goals
    · change _ = _ + _
      -- ⊢ (fun f i =>
      have : ¬i = a := by
        rintro rfl
        exact has h
      simp only [dif_neg this, dif_pos h]
      -- ⊢ Prod.snd (f + g) { val := i, property := (_ : i ∈ s) } = Prod.snd f { val := …
      rfl
      -- 🎉 no goals
  · intro c f
    -- ⊢ AddHom.toFun
    ext i
    -- ⊢ AddHom.toFun
    unfold Or.by_cases
    -- ⊢ AddHom.toFun
    cases' i with i hi
    -- ⊢ AddHom.toFun
    rcases Finset.mem_insert.1 hi with (rfl | h)
    · dsimp
      -- ⊢ (if hp : i = i then c • f.fst else c • Prod.snd f { val := i, property := (_ …
      simp only [dif_pos]
      -- 🎉 no goals
    · dsimp
      -- ⊢ (if hp : i = a then (_ : a = i) ▸ (c • f.fst) else c • Prod.snd f { val := i …
      have : ¬i = a := by
        rintro rfl
        exact has h
      simp only [dif_neg this, dif_pos h]
      -- 🎉 no goals
  · intro f
    -- ⊢ (fun f => (f { val := a, property := (_ : a ∈ insert a s) }, fun i => f { va …
    apply Prod.ext
    · simp only [Or.by_cases, dif_pos]
      -- 🎉 no goals
    · ext ⟨i, his⟩
      -- ⊢ Prod.snd
      have : ¬i = a := by
        rintro rfl
        exact has his
      simp only [Or.by_cases, this, not_false_iff, dif_neg]
      -- 🎉 no goals
  · intro f
    -- ⊢ AddHom.toFun
    ext ⟨i, hi⟩
    -- ⊢ AddHom.toFun
    rcases Finset.mem_insert.1 hi with (rfl | h)
    · simp only [Or.by_cases, dif_pos]
      -- 🎉 no goals
    · have : ¬i = a := by
        rintro rfl
        exact has h
      simp only [Or.by_cases, dif_neg this, dif_pos h]
      -- 🎉 no goals
#align is_noetherian_pi isNoetherian_pi

/-- A version of `isNoetherian_pi` for non-dependent functions. We need this instance because
sometimes Lean fails to apply the dependent version in non-dependent settings (e.g., it fails to
prove that `ι → ℝ` is finite dimensional over `ℝ`). -/
instance isNoetherian_pi' {R ι M : Type*} [Ring R] [AddCommGroup M] [Module R M] [Finite ι]
    [IsNoetherian R M] : IsNoetherian R (ι → M) :=
  isNoetherian_pi
#align is_noetherian_pi' isNoetherian_pi'

end

open IsNoetherian Submodule Function

section

universe w

variable {R M P : Type*} {N : Type w} [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N] [AddCommMonoid P] [Module R P]

theorem isNoetherian_iff_wellFounded :
    IsNoetherian R M ↔ WellFounded ((· > ·) : Submodule R M → Submodule R M → Prop) := by
  have := (CompleteLattice.wellFounded_characterisations <| Submodule R M).out 0 3
  -- ⊢ IsNoetherian R M ↔ WellFounded fun x x_1 => x > x_1
  -- Porting note: inlining this makes rw complain about it being a metavariable
  rw [this]
  -- ⊢ IsNoetherian R M ↔ ∀ (k : Submodule R M), CompleteLattice.IsCompactElement k
  exact
    ⟨fun ⟨h⟩ => fun k => (fg_iff_compact k).mp (h k), fun h =>
      ⟨fun k => (fg_iff_compact k).mpr (h k)⟩⟩
#align is_noetherian_iff_well_founded isNoetherian_iff_wellFounded

theorem isNoetherian_iff_fg_wellFounded :
    IsNoetherian R M ↔
      WellFounded
        ((· > ·) : { N : Submodule R M // N.FG } → { N : Submodule R M // N.FG } → Prop) := by
  let α := { N : Submodule R M // N.FG }
  -- ⊢ IsNoetherian R M ↔ WellFounded fun x x_1 => x > x_1
  constructor
  -- ⊢ IsNoetherian R M → WellFounded fun x x_1 => x > x_1
  · intro H
    -- ⊢ WellFounded fun x x_1 => x > x_1
    let f : α ↪o Submodule R M := OrderEmbedding.subtype _
    -- ⊢ WellFounded fun x x_1 => x > x_1
    exact OrderEmbedding.wellFounded f.dual (isNoetherian_iff_wellFounded.mp H)
    -- 🎉 no goals
  · intro H
    -- ⊢ IsNoetherian R M
    constructor
    -- ⊢ ∀ (s : Submodule R M), FG s
    intro N
    -- ⊢ FG N
    obtain ⟨⟨N₀, h₁⟩, e : N₀ ≤ N, h₂⟩ :=
      WellFounded.has_min H { N' : α | N'.1 ≤ N } ⟨⟨⊥, Submodule.fg_bot⟩, @bot_le _ _ _ N⟩
    convert h₁
    -- ⊢ N = N₀
    refine' (e.antisymm _).symm
    -- ⊢ N ≤ N₀
    by_contra h₃
    -- ⊢ False
    obtain ⟨x, hx₁ : x ∈ N, hx₂ : x ∉ N₀⟩ := Set.not_subset.mp h₃
    -- ⊢ False
    apply hx₂
    -- ⊢ x ∈ N₀
    rw [eq_of_le_of_not_lt (le_sup_right : N₀ ≤ _) (h₂
      ⟨_, Submodule.FG.sup ⟨{x}, by rw [Finset.coe_singleton]⟩ h₁⟩ <|
      sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hx₁) e)]
    exact (le_sup_left : (R ∙ x) ≤ _) (Submodule.mem_span_singleton_self _)
    -- 🎉 no goals
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
  -- 🎉 no goals
#align set_has_maximal_iff_noetherian set_has_maximal_iff_noetherian

/-- A module is Noetherian iff every increasing chain of submodules stabilizes. -/
theorem monotone_stabilizes_iff_noetherian :
    (∀ f : ℕ →o Submodule R M, ∃ n, ∀ m, n ≤ m → f n = f m) ↔ IsNoetherian R M := by
  rw [isNoetherian_iff_wellFounded, WellFounded.monotone_chain_condition]
  -- 🎉 no goals
#align monotone_stabilizes_iff_noetherian monotone_stabilizes_iff_noetherian

/-- If `∀ I > J, P I` implies `P J`, then `P` holds for all submodules. -/
theorem IsNoetherian.induction [IsNoetherian R M] {P : Submodule R M → Prop}
    (hgt : ∀ I, (∀ J > I, P J) → P I) (I : Submodule R M) : P I :=
  WellFounded.recursion (wellFounded_submodule_gt R M) I hgt
#align is_noetherian.induction IsNoetherian.induction

end

section

universe w

variable {R M P : Type*} {N : Type w} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] [AddCommGroup P] [Module R P]

theorem finite_of_linearIndependent [Nontrivial R] [IsNoetherian R M] {s : Set M}
    (hs : LinearIndependent R ((↑) : s → M)) : s.Finite := by
  refine'
    by_contradiction fun hf =>
      (RelEmbedding.wellFounded_iff_no_descending_seq.1 (wellFounded_submodule_gt R M)).elim' _
  have f : ℕ ↪ s := Set.Infinite.natEmbedding s hf
  -- ⊢ (fun x x_1 => x > x_1) ↪r fun x x_1 => x > x_1
  have : ∀ n, (↑) ∘ f '' { m | m ≤ n } ⊆ s := by
    rintro n x ⟨y, _, rfl⟩
    exact (f y).2
  let coe' : s → M := (↑)
  -- ⊢ (fun x x_1 => x > x_1) ↪r fun x x_1 => x > x_1
  have : ∀ a b : ℕ, a ≤ b ↔
    span R (coe' ∘ f '' { m | m ≤ a }) ≤ span R ((↑) ∘ f '' { m | m ≤ b }) := by
    intro a b
    rw [span_le_span_iff hs (this a) (this b),
      Set.image_subset_image_iff (Subtype.coe_injective.comp f.injective), Set.subset_def]
    exact ⟨fun hab x (hxa : x ≤ a) => le_trans hxa hab, fun hx => hx a (le_refl a)⟩
  exact
    ⟨⟨fun n => span R (coe' ∘ f '' { m | m ≤ n }), fun x y => by
        rw [le_antisymm_iff, (this x y).symm, (this y x).symm, ←le_antisymm_iff, imp_self]
        trivial⟩,
      by dsimp [GT.gt]; simp only [lt_iff_le_not_le, (this _ _).symm]; tauto⟩
#align finite_of_linear_independent finite_of_linearIndependent

/-- If the first and final modules in a short exact sequence are Noetherian,
  then the middle module is also Noetherian. -/
theorem isNoetherian_of_range_eq_ker [IsNoetherian R M] [IsNoetherian R P] (f : M →ₗ[R] N)
    (g : N →ₗ[R] P) (hf : Function.Injective f) (hg : Function.Surjective g)
    (h : LinearMap.range f = LinearMap.ker g) :
    IsNoetherian R N :=
  isNoetherian_iff_wellFounded.2 <|
    wellFounded_gt_exact_sequence (wellFounded_submodule_gt R M) (wellFounded_submodule_gt R P)
      (LinearMap.range f) (Submodule.map f) (Submodule.comap f) (Submodule.comap g)
      (Submodule.map g) (Submodule.gciMapComap hf) (Submodule.giMapComap hg)
      (by simp [Submodule.map_comap_eq, inf_comm]) (by simp [Submodule.comap_map_eq, h])
          -- 🎉 no goals
                                                       -- 🎉 no goals
#align is_noetherian_of_range_eq_ker isNoetherian_of_range_eq_ker

/-- For any endomorphism of a Noetherian module, there is some nontrivial iterate
with disjoint kernel and range.
-/
theorem IsNoetherian.exists_endomorphism_iterate_ker_inf_range_eq_bot [I : IsNoetherian R M]
    (f : M →ₗ[R] M) :
    ∃ n : ℕ, n ≠ 0 ∧ LinearMap.ker (f ^ n) ⊓ LinearMap.range (f ^ n) = ⊥ := by
  obtain ⟨n, w⟩ :=
    monotone_stabilizes_iff_noetherian.mpr I
      (f.iterateKer.comp ⟨fun n => n + 1, fun n m w => by linarith⟩)
  specialize w (2 * n + 1) (by linarith only)
  -- ⊢ ∃ n, n ≠ 0 ∧ LinearMap.ker (f ^ n) ⊓ LinearMap.range (f ^ n) = ⊥
  dsimp at w
  -- ⊢ ∃ n, n ≠ 0 ∧ LinearMap.ker (f ^ n) ⊓ LinearMap.range (f ^ n) = ⊥
  refine' ⟨n + 1, Nat.succ_ne_zero _, _⟩
  -- ⊢ LinearMap.ker (f ^ (n + 1)) ⊓ LinearMap.range (f ^ (n + 1)) = ⊥
  rw [eq_bot_iff]
  -- ⊢ LinearMap.ker (f ^ (n + 1)) ⊓ LinearMap.range (f ^ (n + 1)) ≤ ⊥
  rintro - ⟨h, ⟨y, rfl⟩⟩
  -- ⊢ ↑(f ^ (n + 1)) y ∈ ⊥
  rw [mem_bot, ← LinearMap.mem_ker, w]
  -- ⊢ y ∈ LinearMap.ker (f ^ (2 * n + 1 + 1))
  erw [LinearMap.mem_ker] at h ⊢
  -- ⊢ ↑(f ^ (2 * n + 1 + 1)) y = 0
  change (f ^ (n + 1) * f ^ (n + 1)) y = 0 at h
  -- ⊢ ↑(f ^ (2 * n + 1 + 1)) y = 0
  rw [← pow_add] at h
  -- ⊢ ↑(f ^ (2 * n + 1 + 1)) y = 0
  convert h using 3
  -- ⊢ 2 * n + 1 + 1 = n + 1 + (n + 1)
  ring
  -- 🎉 no goals
#align is_noetherian.exists_endomorphism_iterate_ker_inf_range_eq_bot IsNoetherian.exists_endomorphism_iterate_ker_inf_range_eq_bot

/-- Any surjective endomorphism of a Noetherian module is injective. -/
theorem IsNoetherian.injective_of_surjective_endomorphism [IsNoetherian R M] (f : M →ₗ[R] M)
    (s : Surjective f) : Injective f := by
  obtain ⟨n, ne, w⟩ := IsNoetherian.exists_endomorphism_iterate_ker_inf_range_eq_bot f
  -- ⊢ Injective ↑f
  rw [LinearMap.range_eq_top.mpr (LinearMap.iterate_surjective s n), inf_top_eq,
    LinearMap.ker_eq_bot] at w
  exact LinearMap.injective_of_iterate_injective ne w
  -- 🎉 no goals
#align is_noetherian.injective_of_surjective_endomorphism IsNoetherian.injective_of_surjective_endomorphism

/-- Any surjective endomorphism of a Noetherian module is bijective. -/
theorem IsNoetherian.bijective_of_surjective_endomorphism [IsNoetherian R M] (f : M →ₗ[R] M)
    (s : Surjective f) : Bijective f :=
  ⟨IsNoetherian.injective_of_surjective_endomorphism f s, s⟩
#align is_noetherian.bijective_of_surjective_endomorphism IsNoetherian.bijective_of_surjective_endomorphism

/-- A sequence `f` of submodules of a noetherian module,
with `f (n+1)` disjoint from the supremum of `f 0`, ..., `f n`,
is eventually zero.
-/
theorem IsNoetherian.disjoint_partialSups_eventually_bot [I : IsNoetherian R M]
    (f : ℕ → Submodule R M) (h : ∀ n, Disjoint (partialSups f n) (f (n + 1))) :
    ∃ n : ℕ, ∀ m, n ≤ m → f m = ⊥ := by
  -- A little off-by-one cleanup first:
  suffices t : ∃ n : ℕ, ∀ m, n ≤ m → f (m + 1) = ⊥
  -- ⊢ ∃ n, ∀ (m : ℕ), n ≤ m → f m = ⊥
  · obtain ⟨n, w⟩ := t
    -- ⊢ ∃ n, ∀ (m : ℕ), n ≤ m → f m = ⊥
    use n + 1
    -- ⊢ ∀ (m : ℕ), n + 1 ≤ m → f m = ⊥
    rintro (_ | m) p
    -- ⊢ f Nat.zero = ⊥
    · cases p
      -- 🎉 no goals
    · apply w
      -- ⊢ n ≤ m
      exact Nat.succ_le_succ_iff.mp p
      -- 🎉 no goals
  obtain ⟨n, w⟩ := monotone_stabilizes_iff_noetherian.mpr I (partialSups f)
  -- ⊢ ∃ n, ∀ (m : ℕ), n ≤ m → f (m + 1) = ⊥
  exact
    ⟨n, fun m p =>
      (h m).eq_bot_of_ge <| sup_eq_left.1 <| (w (m + 1) <| le_add_right p).symm.trans <| w m p⟩
#align is_noetherian.disjoint_partial_sups_eventually_bot IsNoetherian.disjoint_partialSups_eventually_bot

/-- If `M ⊕ N` embeds into `M`, for `M` noetherian over `R`, then `N` is trivial.
-/
noncomputable def IsNoetherian.equivPUnitOfProdInjective [IsNoetherian R M] (f : M × N →ₗ[R] M)
    (i : Injective f) : N ≃ₗ[R] PUnit.{w + 1} := by
  apply Nonempty.some
  -- ⊢ Nonempty (N ≃ₗ[R] PUnit)
  obtain ⟨n, w⟩ :=
    IsNoetherian.disjoint_partialSups_eventually_bot (f.tailing i) (f.tailings_disjoint_tailing i)
  specialize w n (le_refl n)
  -- ⊢ Nonempty (N ≃ₗ[R] PUnit)
  apply Nonempty.intro
  -- ⊢ N ≃ₗ[R] PUnit
  -- Porting note: refine' makes this line time out at elaborator
  refine (LinearMap.tailingLinearEquiv f i n).symm ≪≫ₗ ?_
  -- ⊢ { x // x ∈ LinearMap.tailing f i n } ≃ₗ[R] PUnit
  rw [w]
  -- ⊢ { x // x ∈ ⊥ } ≃ₗ[R] PUnit
  apply Submodule.botEquivPUnit
  -- 🎉 no goals
#align is_noetherian.equiv_punit_of_prod_injective IsNoetherian.equivPUnitOfProdInjective

end

/-- A (semi)ring is Noetherian if it is Noetherian as a module over itself,
i.e. all its ideals are finitely generated.
-/
@[reducible]
def IsNoetherianRing (R) [Semiring R] :=
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
                                               -- 🎉 no goals
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
  -- ⊢ WellFounded fun x x_1 => x > x_1
  exact OrderEmbedding.wellFounded (Submodule.MapSubtype.orderEmbedding N).dual h
  -- 🎉 no goals
#align is_noetherian_of_submodule_of_noetherian isNoetherian_of_submodule_of_noetherian

instance Submodule.Quotient.isNoetherian {R} [Ring R] {M} [AddCommGroup M] [Module R M]
    (N : Submodule R M) [h : IsNoetherian R M] : IsNoetherian R (M ⧸ N) := by
  rw [isNoetherian_iff_wellFounded] at h ⊢
  -- ⊢ WellFounded fun x x_1 => x > x_1
  exact OrderEmbedding.wellFounded (Submodule.comapMkQOrderEmbedding N).dual h
  -- 🎉 no goals
#align submodule.quotient.is_noetherian Submodule.Quotient.isNoetherian

/-- If `M / S / R` is a scalar tower, and `M / R` is Noetherian, then `M / S` is
also noetherian. -/
theorem isNoetherian_of_tower (R) {S M} [Semiring R] [Semiring S] [AddCommMonoid M] [SMul R S]
    [Module S M] [Module R M] [IsScalarTower R S M] (h : IsNoetherian R M) : IsNoetherian S M := by
  rw [isNoetherian_iff_wellFounded] at h ⊢
  -- ⊢ WellFounded fun x x_1 => x > x_1
  refine' (Submodule.restrictScalarsEmbedding R S M).dual.wellFounded h
  -- 🎉 no goals
#align is_noetherian_of_tower isNoetherian_of_tower

theorem isNoetherian_of_fg_of_noetherian {R M} [Ring R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) [I : IsNoetherianRing R] (hN : N.FG) : IsNoetherian R N := by
  let ⟨s, hs⟩ := hN
  -- ⊢ IsNoetherian R { x // x ∈ N }
  haveI := Classical.decEq M
  -- ⊢ IsNoetherian R { x // x ∈ N }
  haveI := Classical.decEq R
  -- ⊢ IsNoetherian R { x // x ∈ N }
  have : ∀ x ∈ s, x ∈ N := fun x hx => hs ▸ Submodule.subset_span hx
  -- ⊢ IsNoetherian R { x // x ∈ N }
  refine
    @isNoetherian_of_surjective
      R ((↑s : Set M) → R) N _ _ _ (Pi.module _ _ _) _ ?_ ?_ isNoetherian_pi
  · fapply LinearMap.mk
    -- ⊢ AddHom (↑↑s → R) { x // x ∈ N }
    · fapply AddHom.mk
      -- ⊢ (↑↑s → R) → { x // x ∈ N }
      · exact fun f => ⟨∑ i in s.attach, f i • i.1, N.sum_mem fun c _ => N.smul_mem _ <| this _ c.2⟩
        -- 🎉 no goals
      · intro f g
        -- ⊢ { val := ∑ i in Finset.attach s, (f + g) i • ↑i, property := (_ : ∑ i in Fin …
        apply Subtype.eq
        -- ⊢ ↑{ val := ∑ i in Finset.attach s, (f + g) i • ↑i, property := (_ : ∑ i in Fi …
        change (∑ i in s.attach, (f i + g i) • _) = _
        -- ⊢ ∑ i in Finset.attach s, (f i + g i) • ↑i = ↑({ val := ∑ i in Finset.attach s …
        simp only [add_smul, Finset.sum_add_distrib]
        -- ⊢ ∑ x in Finset.attach s, f x • ↑x + ∑ x in Finset.attach s, g x • ↑x = ↑({ va …
        rfl
        -- 🎉 no goals
    · intro c f
      -- ⊢ AddHom.toFun { toFun := fun f => { val := ∑ i in Finset.attach s, f i • ↑i,  …
      apply Subtype.eq
      -- ⊢ ↑(AddHom.toFun { toFun := fun f => { val := ∑ i in Finset.attach s, f i • ↑i …
      change (∑ i in s.attach, (c • f i) • _) = _
      -- ⊢ ∑ i in Finset.attach s, (c • f i) • ↑i = ↑(↑(RingHom.id R) c • AddHom.toFun  …
      simp only [smul_eq_mul, mul_smul]
      -- ⊢ ∑ x in Finset.attach s, c • f x • ↑x = ↑(↑(RingHom.id R) c • { val := ∑ i in …
      exact Finset.smul_sum.symm
      -- 🎉 no goals
  · rw [LinearMap.range_eq_top]
    -- ⊢ Surjective ↑{ toAddHom := { toFun := fun f => { val := ∑ i in Finset.attach  …
    rintro ⟨n, hn⟩
    -- ⊢ ∃ a, ↑{ toAddHom := { toFun := fun f => { val := ∑ i in Finset.attach s, f i …
    change n ∈ N at hn
    -- ⊢ ∃ a, ↑{ toAddHom := { toFun := fun f => { val := ∑ i in Finset.attach s, f i …
    rw [← hs, ← Set.image_id (s : Set M), Finsupp.mem_span_image_iff_total] at hn
    -- ⊢ ∃ a, ↑{ toAddHom := { toFun := fun f => { val := ∑ i in Finset.attach s, f i …
    rcases hn with ⟨l, hl1, hl2⟩
    -- ⊢ ∃ a, ↑{ toAddHom := { toFun := fun f => { val := ∑ i in Finset.attach s, f i …
    refine' ⟨fun x => l x, Subtype.ext _⟩
    -- ⊢ ↑(↑{ toAddHom := { toFun := fun f => { val := ∑ i in Finset.attach s, f i •  …
    change (∑ i in s.attach, l i • (i : M)) = n
    -- ⊢ ∑ i in Finset.attach s, ↑l ↑i • ↑i = n
    rw [@Finset.sum_attach M M s _ fun i => l i • i, ← hl2,
      Finsupp.total_apply, Finsupp.sum, eq_comm]
    refine' Finset.sum_subset hl1 fun x _ hx => _
    -- ⊢ ↑l x • id x = 0
    rw [Finsupp.not_mem_support_iff.1 hx, zero_smul]
    -- 🎉 no goals
#align is_noetherian_of_fg_of_noetherian isNoetherian_of_fg_of_noetherian

-- It would be nice to make this an instance but it is empirically problematic, possibly because
-- of the loop that it causes with `Module.IsNoetherian.finite`
theorem isNoetherian_of_isNoetherianRing_of_finite (R M : Type*)
    [Ring R] [AddCommGroup M] [Module R M] [IsNoetherianRing R] [Module.Finite R M] :
    IsNoetherian R M :=
  have : IsNoetherian R (⊤ : Submodule R M) :=
    isNoetherian_of_fg_of_noetherian _ $ Module.finite_def.mp inferInstance
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
  -- ⊢ WellFounded fun x x_1 => x > x_1
  exact OrderEmbedding.wellFounded (Ideal.orderEmbeddingOfSurjective f hf).dual H
  -- 🎉 no goals
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
  -- ⊢ IsNilpotent (nilradical R)
  exact ⟨n, eq_bot_iff.mpr hn⟩
  -- 🎉 no goals
#align is_noetherian_ring.is_nilpotent_nilradical IsNoetherianRing.isNilpotent_nilradical
