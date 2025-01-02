/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Algebra.Tower
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.RingTheory.Finiteness.Defs

/-!
# Basic results on finitely generated (sub)modules

This file contains the basic results on `Submodule.FG` and `Module.Finite` that do not need heavy
further imports.
-/

assert_not_exists Basis
assert_not_exists Ideal.radical
assert_not_exists Matrix
assert_not_exists Subalgebra

open Function (Surjective)
open Finsupp

namespace Submodule

variable {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

open Set

theorem fg_bot : (⊥ : Submodule R M).FG :=
  ⟨∅, by rw [Finset.coe_empty, span_empty]⟩

theorem fg_span {s : Set M} (hs : s.Finite) : FG (span R s) :=
  ⟨hs.toFinset, by rw [hs.coe_toFinset]⟩

theorem fg_span_singleton (x : M) : FG (R ∙ x) :=
  fg_span (finite_singleton x)

theorem FG.sup {N₁ N₂ : Submodule R M} (hN₁ : N₁.FG) (hN₂ : N₂.FG) : (N₁ ⊔ N₂).FG :=
  let ⟨t₁, ht₁⟩ := fg_def.1 hN₁
  let ⟨t₂, ht₂⟩ := fg_def.1 hN₂
  fg_def.2 ⟨t₁ ∪ t₂, ht₁.1.union ht₂.1, by rw [span_union, ht₁.2, ht₂.2]⟩

theorem fg_finset_sup {ι : Type*} (s : Finset ι) (N : ι → Submodule R M) (h : ∀ i ∈ s, (N i).FG) :
    (s.sup N).FG :=
  Finset.sup_induction fg_bot (fun _ ha _ hb => ha.sup hb) h

theorem fg_biSup {ι : Type*} (s : Finset ι) (N : ι → Submodule R M) (h : ∀ i ∈ s, (N i).FG) :
    (⨆ i ∈ s, N i).FG := by simpa only [Finset.sup_eq_iSup] using fg_finset_sup s N h

theorem fg_iSup {ι : Sort*} [Finite ι] (N : ι → Submodule R M) (h : ∀ i, (N i).FG) :
    (iSup N).FG := by
  cases nonempty_fintype (PLift ι)
  simpa [iSup_plift_down] using fg_biSup Finset.univ (N ∘ PLift.down) fun i _ => h i.down

variable {P : Type*} [AddCommMonoid P] [Module R P]
variable (f : M →ₗ[R] P)

theorem fg_pi {ι : Type*} {M : ι → Type*} [Finite ι] [∀ i, AddCommMonoid (M i)]
    [∀ i, Module R (M i)] {p : ∀ i, Submodule R (M i)} (hsb : ∀ i, (p i).FG) :
    (Submodule.pi Set.univ p).FG := by
  classical
    simp_rw [fg_def] at hsb ⊢
    choose t htf hts using hsb
    refine
      ⟨⋃ i, (LinearMap.single R _ i) '' t i, Set.finite_iUnion fun i => (htf i).image _, ?_⟩
    -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 changed `span_image` into `span_image _`
    simp_rw [span_iUnion, span_image _, hts, Submodule.iSup_map_single]

theorem FG.map {N : Submodule R M} (hs : N.FG) : (N.map f).FG :=
  let ⟨t, ht⟩ := fg_def.1 hs
  fg_def.2 ⟨f '' t, ht.1.image _, by rw [span_image, ht.2]⟩

variable {f}

theorem fg_of_fg_map_injective (f : M →ₗ[R] P) (hf : Function.Injective f) {N : Submodule R M}
    (hfn : (N.map f).FG) : N.FG :=
  let ⟨t, ht⟩ := hfn
  ⟨t.preimage f fun _ _ _ _ h => hf h,
    Submodule.map_injective_of_injective hf <| by
      rw [map_span, Finset.coe_preimage, Set.image_preimage_eq_inter_range,
        Set.inter_eq_self_of_subset_left, ht]
      rw [← LinearMap.range_coe, ← span_le, ht, ← map_top]
      exact map_mono le_top⟩

theorem fg_of_fg_map {R M P : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup P]
    [Module R P] (f : M →ₗ[R] P)
    (hf : LinearMap.ker f = ⊥) {N : Submodule R M}
    (hfn : (N.map f).FG) : N.FG :=
  fg_of_fg_map_injective f (LinearMap.ker_eq_bot.1 hf) hfn

theorem fg_top (N : Submodule R M) : (⊤ : Submodule R N).FG ↔ N.FG :=
  ⟨fun h => N.range_subtype ▸ map_top N.subtype ▸ h.map _, fun h =>
    fg_of_fg_map_injective N.subtype Subtype.val_injective <| by rwa [map_top, range_subtype]⟩

theorem fg_of_linearEquiv (e : M ≃ₗ[R] P) (h : (⊤ : Submodule R P).FG) : (⊤ : Submodule R M).FG :=
  e.symm.range ▸ map_top (e.symm : P →ₗ[R] M) ▸ h.map _

theorem fg_induction (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]
    (P : Submodule R M → Prop) (h₁ : ∀ x, P (Submodule.span R {x}))
    (h₂ : ∀ M₁ M₂, P M₁ → P M₂ → P (M₁ ⊔ M₂)) (N : Submodule R M) (hN : N.FG) : P N := by
  classical
    obtain ⟨s, rfl⟩ := hN
    induction s using Finset.induction with
    | empty =>
      rw [Finset.coe_empty, Submodule.span_empty, ← Submodule.span_zero_singleton]
      exact h₁ _
    | insert _ ih =>
      rw [Finset.coe_insert, Submodule.span_insert]
      exact h₂ _ _ (h₁ _) ih

theorem fg_restrictScalars {R S M : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M] (N : Submodule S M)
    (hfin : N.FG) (h : Function.Surjective (algebraMap R S)) :
    (Submodule.restrictScalars R N).FG := by
  obtain ⟨X, rfl⟩ := hfin
  use X
  exact (Submodule.restrictScalars_span R S h (X : Set M)).symm

lemma FG.of_restrictScalars (R) {A M} [CommSemiring R] [Semiring A] [AddCommMonoid M]
    [Algebra R A] [Module R M] [Module A M] [IsScalarTower R A M] (S : Submodule A M)
    (hS : (S.restrictScalars R).FG) : S.FG := by
  obtain ⟨s, e⟩ := hS
  refine ⟨s, Submodule.restrictScalars_injective R _ _ (le_antisymm ?_ ?_)⟩
  · show Submodule.span A s ≤ S
    have := Submodule.span_le.mp e.le
    rwa [Submodule.span_le]
  · rw [← e]
    exact Submodule.span_le_restrictScalars _ _ _

theorem FG.stabilizes_of_iSup_eq {M' : Submodule R M} (hM' : M'.FG) (N : ℕ →o Submodule R M)
    (H : iSup N = M') : ∃ n, M' = N n := by
  obtain ⟨S, hS⟩ := hM'
  have : ∀ s : S, ∃ n, (s : M) ∈ N n := fun s =>
    (Submodule.mem_iSup_of_chain N s).mp
      (by
        rw [H, ← hS]
        exact Submodule.subset_span s.2)
  choose f hf using this
  use S.attach.sup f
  apply le_antisymm
  · conv_lhs => rw [← hS]
    rw [Submodule.span_le]
    intro s hs
    exact N.2 (Finset.le_sup <| S.mem_attach ⟨s, hs⟩) (hf _)
  · rw [← H]
    exact le_iSup _ _

/-- Finitely generated submodules are precisely compact elements in the submodule lattice. -/
theorem fg_iff_compact (s : Submodule R M) : s.FG ↔ CompleteLattice.IsCompactElement s := by
  classical
    -- Introduce shorthand for span of an element
    let sp : M → Submodule R M := fun a => span R {a}
    -- Trivial rewrite lemma; a small hack since simp (only) & rw can't accomplish this smoothly.
    have supr_rw : ∀ t : Finset M, ⨆ x ∈ t, sp x = ⨆ x ∈ (↑t : Set M), sp x := fun t => by rfl
    constructor
    · rintro ⟨t, rfl⟩
      rw [span_eq_iSup_of_singleton_spans, ← supr_rw, ← Finset.sup_eq_iSup t sp]
      apply CompleteLattice.isCompactElement_finsetSup
      exact fun n _ => singleton_span_isCompactElement n
    · intro h
      -- s is the Sup of the spans of its elements.
      have sSup' : s = sSup (sp '' ↑s) := by
        rw [sSup_eq_iSup, iSup_image, ← span_eq_iSup_of_singleton_spans, eq_comm, span_eq]
      -- by h, s is then below (and equal to) the sup of the spans of finitely many elements.
      obtain ⟨u, ⟨huspan, husup⟩⟩ := h (sp '' ↑s) (le_of_eq sSup')
      have ssup : s = u.sup id := by
        suffices u.sup id ≤ s from le_antisymm husup this
        rw [sSup', Finset.sup_id_eq_sSup]
        exact sSup_le_sSup huspan
      obtain ⟨t, -, rfl⟩ := Finset.subset_set_image_iff.mp huspan
      rw [Finset.sup_image, Function.id_comp, Finset.sup_eq_iSup, supr_rw, ←
        span_eq_iSup_of_singleton_spans, eq_comm] at ssup
      exact ⟨t, ssup⟩

end Submodule

section ModuleAndAlgebra

variable (R A B M N : Type*)

namespace Module

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

namespace Finite

open Submodule Set

variable {R M N}

-- See note [lower instance priority]
instance (priority := 100) of_finite [Finite M] : Module.Finite R M := by
  cases nonempty_fintype M
  exact ⟨⟨Finset.univ, by rw [Finset.coe_univ]; exact Submodule.span_univ⟩⟩

theorem of_surjective [hM : Module.Finite R M] (f : M →ₗ[R] N) (hf : Surjective f) :
    Module.Finite R N :=
  ⟨by
    rw [← LinearMap.range_eq_top.2 hf, ← Submodule.map_top]
    exact hM.1.map f⟩

instance quotient (R) {A M} [Semiring R] [AddCommGroup M] [Ring A] [Module A M] [Module R M]
    [SMul R A] [IsScalarTower R A M] [Module.Finite R M]
    (N : Submodule A M) : Module.Finite R (M ⧸ N) :=
  Module.Finite.of_surjective (N.mkQ.restrictScalars R) N.mkQ_surjective

/-- The range of a linear map from a finite module is finite. -/
instance range {F : Type*} [FunLike F M N] [SemilinearMapClass F (RingHom.id R) M N]
    [Module.Finite R M] (f : F) : Module.Finite R (LinearMap.range f) :=
  of_surjective (SemilinearMapClass.semilinearMap f).rangeRestrict
    fun ⟨_, y, hy⟩ => ⟨y, Subtype.ext hy⟩

/-- Pushforwards of finite submodules are finite. -/
instance map (p : Submodule R M) [Module.Finite R p] (f : M →ₗ[R] N) : Module.Finite R (p.map f) :=
  of_surjective (f.restrict fun _ => Submodule.mem_map_of_mem) fun ⟨_, _, hy, hy'⟩ =>
    ⟨⟨_, hy⟩, Subtype.ext hy'⟩

instance pi {ι : Type*} {M : ι → Type*} [_root_.Finite ι] [∀ i, AddCommMonoid (M i)]
    [∀ i, Module R (M i)] [h : ∀ i, Module.Finite R (M i)] : Module.Finite R (∀ i, M i) :=
  ⟨by
    rw [← Submodule.pi_top]
    exact Submodule.fg_pi fun i => (h i).1⟩

variable (R)

instance self : Module.Finite R R :=
  ⟨⟨{1}, by simpa only [Finset.coe_singleton] using Ideal.span_singleton_one⟩⟩

variable (M)

theorem of_restrictScalars_finite (R A M : Type*) [CommSemiring R] [Semiring A] [AddCommMonoid M]
    [Module R M] [Module A M] [Algebra R A] [IsScalarTower R A M] [hM : Module.Finite R M] :
    Module.Finite A M := by
  rw [finite_def, Submodule.fg_def] at hM ⊢
  obtain ⟨S, hSfin, hSgen⟩ := hM
  refine ⟨S, hSfin, eq_top_iff.2 ?_⟩
  have := Submodule.span_le_restrictScalars R A S
  rw [hSgen] at this
  exact this

variable {R M}

theorem equiv [Module.Finite R M] (e : M ≃ₗ[R] N) : Module.Finite R N :=
  of_surjective (e : M →ₗ[R] N) e.surjective

theorem equiv_iff (e : M ≃ₗ[R] N) : Module.Finite R M ↔ Module.Finite R N :=
  ⟨fun _ ↦ equiv e, fun _ ↦ equiv e.symm⟩

instance ulift [Module.Finite R M] : Module.Finite R (ULift M) := equiv ULift.moduleEquiv.symm

theorem iff_fg {N : Submodule R M} : Module.Finite R N ↔ N.FG := Module.finite_def.trans (fg_top _)

variable (R M)

instance bot : Module.Finite R (⊥ : Submodule R M) := iff_fg.mpr fg_bot

instance top [Module.Finite R M] : Module.Finite R (⊤ : Submodule R M) := iff_fg.mpr out

variable {M}

/-- The submodule generated by a finite set is `R`-finite. -/
theorem span_of_finite {A : Set M} (hA : Set.Finite A) :
    Module.Finite R (Submodule.span R A) :=
  ⟨(Submodule.fg_top _).mpr ⟨hA.toFinset, hA.coe_toFinset.symm ▸ rfl⟩⟩

/-- The submodule generated by a single element is `R`-finite. -/
instance span_singleton (x : M) : Module.Finite R (R ∙ x) :=
  Module.Finite.span_of_finite R <| Set.finite_singleton _

/-- The submodule generated by a finset is `R`-finite. -/
instance span_finset (s : Finset M) : Module.Finite R (span R (s : Set M)) :=
  ⟨(Submodule.fg_top _).mpr ⟨s, rfl⟩⟩

variable {R}

section Algebra

theorem trans {R : Type*} (A M : Type*) [Semiring R] [Semiring A] [Module R A]
    [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M] :
    ∀ [Module.Finite R A] [Module.Finite A M], Module.Finite R M
  | ⟨⟨s, hs⟩⟩, ⟨⟨t, ht⟩⟩ =>
    ⟨Submodule.fg_def.2
        ⟨Set.image2 (· • ·) (↑s : Set A) (↑t : Set M),
          Set.Finite.image2 _ s.finite_toSet t.finite_toSet, by
          erw [Set.image2_smul, Submodule.span_smul_of_span_eq_top hs (↑t : Set M), ht,
            Submodule.restrictScalars_top]⟩⟩

lemma of_equiv_equiv {A₁ B₁ A₂ B₂ : Type*} [CommRing A₁] [CommRing B₁]
    [CommRing A₂] [CommRing B₂] [Algebra A₁ B₁] [Algebra A₂ B₂] (e₁ : A₁ ≃+* A₂) (e₂ : B₁ ≃+* B₂)
    (he : RingHom.comp (algebraMap A₂ B₂) ↑e₁ = RingHom.comp ↑e₂ (algebraMap A₁ B₁))
    [Module.Finite A₁ B₁] : Module.Finite A₂ B₂ := by
  letI := e₁.toRingHom.toAlgebra
  letI := ((algebraMap A₁ B₁).comp e₁.symm.toRingHom).toAlgebra
  haveI : IsScalarTower A₁ A₂ B₁ := IsScalarTower.of_algebraMap_eq
    (fun x ↦ by simp [RingHom.algebraMap_toAlgebra])
  let e : B₁ ≃ₐ[A₂] B₂ :=
    { e₂ with
      commutes' := fun r ↦ by
        simpa [RingHom.algebraMap_toAlgebra] using DFunLike.congr_fun he.symm (e₁.symm r) }
  haveI := Module.Finite.of_restrictScalars_finite A₁ A₂ B₁
  exact Module.Finite.equiv e.toLinearEquiv

end Algebra

end Finite

end Module

end ModuleAndAlgebra

namespace Submodule

open Module

variable {R V} [Ring R] [AddCommGroup V] [Module R V]

/-- The sup of two fg submodules is finite. Also see `Submodule.FG.sup`. -/
instance finite_sup (S₁ S₂ : Submodule R V) [h₁ : Module.Finite R S₁]
    [h₂ : Module.Finite R S₂] : Module.Finite R (S₁ ⊔ S₂ : Submodule R V) := by
  rw [finite_def] at *
  exact (fg_top _).2 (((fg_top S₁).1 h₁).sup ((fg_top S₂).1 h₂))

/-- The submodule generated by a finite supremum of finite dimensional submodules is
finite-dimensional.

Note that strictly this only needs `∀ i ∈ s, FiniteDimensional K (S i)`, but that doesn't
work well with typeclass search. -/
instance finite_finset_sup {ι : Type*} (s : Finset ι) (S : ι → Submodule R V)
    [∀ i, Module.Finite R (S i)] : Module.Finite R (s.sup S : Submodule R V) := by
  refine
    @Finset.sup_induction _ _ _ _ s S (fun i => Module.Finite R ↑i) (Module.Finite.bot R V)
      ?_ fun i _ => by infer_instance
  intro S₁ hS₁ S₂ hS₂
  exact Submodule.finite_sup S₁ S₂

end Submodule

namespace RingHom

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

namespace Finite

variable (A)

theorem id : Finite (RingHom.id A) :=
  Module.Finite.self A

variable {A}

theorem of_surjective (f : A →+* B) (hf : Surjective f) : f.Finite :=
  letI := f.toAlgebra
  Module.Finite.of_surjective (Algebra.linearMap A B) hf

theorem comp {g : B →+* C} {f : A →+* B} (hg : g.Finite) (hf : f.Finite) : (g.comp f).Finite := by
  algebraize [f, g, g.comp f]
  exact Module.Finite.trans B C

theorem of_comp_finite {f : A →+* B} {g : B →+* C} (h : (g.comp f).Finite) : g.Finite := by
  algebraize [f, g, g.comp f]
  exact Module.Finite.of_restrictScalars_finite A B C

end Finite

end RingHom

namespace AlgHom

variable {R A B C : Type*} [CommRing R]
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra R A] [Algebra R B] [Algebra R C]

namespace Finite

variable (R A)

theorem id : Finite (AlgHom.id R A) :=
  RingHom.Finite.id A

variable {R A}

theorem comp {g : B →ₐ[R] C} {f : A →ₐ[R] B} (hg : g.Finite) (hf : f.Finite) : (g.comp f).Finite :=
  RingHom.Finite.comp hg hf

theorem of_surjective (f : A →ₐ[R] B) (hf : Surjective f) : f.Finite :=
  RingHom.Finite.of_surjective f.toRingHom hf

theorem of_comp_finite {f : A →ₐ[R] B} {g : B →ₐ[R] C} (h : (g.comp f).Finite) : g.Finite :=
  RingHom.Finite.of_comp_finite h

end Finite

end AlgHom
