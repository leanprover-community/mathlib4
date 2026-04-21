/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Int
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!

# Finiteness properties under localization

In this file we establish behaviour of `Module.Finite` under localizations.

## Main results

- `Module.Finite.of_isLocalizedModule`: If `M` is a finite `R`-module,
  `S` is a submonoid of `R`, `Rₚ` is the localization of `R` at `S`
  and `Mₚ` is the localization of `M` at `S`, then `Mₚ` is a finite
  `Rₚ`-module.
- `Module.Finite.of_localizationSpan_finite`: If `M` is an `R`-module
  and `{ r }` is a finite set generating the unit ideal such that
  `Mᵣ` is a finite `Rᵣ`-module for each `r`, then `M` is a finite `R`-module.

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe u v w t

section

open scoped Pointwise

variable {R S : Type*} [CommRing R] [CommRing S] (M : Submonoid R) (f : R →+* S)
variable (R' S' : Type*) [CommRing R'] [CommRing S']
variable [Algebra R R'] [Algebra S S']

open scoped Classical in
/-- Let `S` be an `R`-algebra, `M` a submonoid of `R`, and `S' = M⁻¹S`.
If the image of some `x : S` falls in the span of some finite `s ⊆ S'` over `R`,
then there exists some `m : M` such that `m • x` falls in the
span of `IsLocalization.finsetIntegerMultiple _ s` over `R`.
-/
theorem IsLocalization.smul_mem_finsetIntegerMultiple_span [Algebra R S] [Algebra R S']
    [IsScalarTower R S S'] [IsLocalization (M.map (algebraMap R S)) S'] (x : S) (s : Finset S')
    (hx : algebraMap S S' x ∈ Submodule.span R (s : Set S')) :
    ∃ m : M, m • x ∈
      Submodule.span R
        (IsLocalization.finsetIntegerMultiple (M.map (algebraMap R S)) s : Set S) := by
  let g : S →ₐ[R] S' :=
    AlgHom.mk' (algebraMap S S') fun c x => by simp [Algebra.algebraMap_eq_smul_one]
  have g_apply : ∀ x, g x = algebraMap S S' x := fun _ => rfl
  -- We first obtain the `y' ∈ M` such that `s' = y' • s` is falls in the image of `S` in `S'`.
  let y := IsLocalization.commonDenomOfFinset (M.map (algebraMap R S)) s
  have hx₁ : (y : S) • (s : Set S') = g '' _ :=
    (IsLocalization.finsetIntegerMultiple_image _ s).symm
  obtain ⟨y', hy', e : algebraMap R S y' = y⟩ := y.prop
  have : algebraMap R S y' • (s : Set S') = y' • (s : Set S') := by
    simp_rw [Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]
  rw [← e, this] at hx₁
  replace hx₁ := congr_arg (Submodule.span R) hx₁
  rw [Submodule.span_smul] at hx₁
  replace hx : _ ∈ y' • Submodule.span R (s : Set S') := Set.smul_mem_smul_set hx
  rw [hx₁, ← g_apply, ← map_smul g, g_apply, ← Algebra.linearMap_apply, ← AlgHom.coe_toLinearMap,
    ← Submodule.map_span] at hx
  -- Since `x` falls in the span of `s` in `S'`, `y' • x : S` falls in the span of `s'` in `S'`.
  -- That is, there exists some `x' : S` in the span of `s'` in `S` and `x' = y' • x` in `S'`.
  -- Thus `a • (y' • x) = a • x' ∈ span s'` in `S` for some `a ∈ M`.
  obtain ⟨x', hx', hx'' : algebraMap _ _ _ = _⟩ := hx
  obtain ⟨⟨_, a, ha₁, rfl⟩, ha₂⟩ :=
    (IsLocalization.eq_iff_exists (M.map (algebraMap R S)) S').mp hx''
  use (⟨a, ha₁⟩ : M) * (⟨y', hy'⟩ : M)
  convert (Submodule.span R
    (IsLocalization.finsetIntegerMultiple (Submonoid.map (algebraMap R S) M) s : Set S)).smul_mem
      a hx' using 1
  convert ha₂.symm using 1
  · rw [Subtype.coe_mk, Submonoid.smul_def, Submonoid.coe_mul, ← smul_smul]
    exact Algebra.smul_def _ _
  · exact Algebra.smul_def _ _

/-- If `M` is an `R' = S⁻¹R` module, and `x ∈ span R' s`,
then `t • x ∈ span R s` for some `t : S`. -/
theorem multiple_mem_span_of_mem_localization_span
    {N : Type*} [AddCommMonoid N] [Module R N] [Module R' N]
    [IsScalarTower R R' N] [IsLocalization M R'] (s : Set N) (x : N)
    (hx : x ∈ Submodule.span R' s) : ∃ (t : M), t • x ∈ Submodule.span R s := by
  classical
  obtain ⟨s', hss', hs'⟩ := Submodule.mem_span_finite_of_mem_span hx
  rsuffices ⟨t, ht⟩ : ∃ t : M, t • x ∈ Submodule.span R (s' : Set N)
  · exact ⟨t, Submodule.span_mono hss' ht⟩
  clear hx hss' s
  induction s' using Finset.induction_on generalizing x with
  | empty => use 1; simpa using hs'
  | insert a s _ hs =>
  simp only [Finset.coe_insert,
    Submodule.mem_span_insert] at hs' ⊢
  rcases hs' with ⟨y, z, hz, rfl⟩
  rcases IsLocalization.surj M y with ⟨⟨y', s'⟩, e⟩
  apply congrArg (fun x ↦ x • a) at e
  simp only [algebraMap_smul] at e
  rcases hs _ hz with ⟨t, ht⟩
  refine ⟨t * s', t * y', _, (Submodule.span R (s : Set N)).smul_mem s' ht, ?_⟩
  rw [smul_add, ← smul_smul, mul_comm, ← smul_smul, ← smul_smul, ← e, mul_comm, ← Algebra.smul_def]
  simp [Submonoid.smul_def]

/-- If `S` is an `R' = M⁻¹R` algebra, and `x ∈ adjoin R' s`,
then `t • x ∈ adjoin R s` for some `t : M`. -/
theorem multiple_mem_adjoin_of_mem_localization_adjoin [Algebra R' S] [Algebra R S]
    [IsScalarTower R R' S] [IsLocalization M R'] (s : Set S) (x : S)
    (hx : x ∈ Algebra.adjoin R' s) : ∃ t : M, t • x ∈ Algebra.adjoin R s := by
  change ∃ t : M, t • x ∈ Subalgebra.toSubmodule (Algebra.adjoin R s)
  change x ∈ Subalgebra.toSubmodule (Algebra.adjoin R' s) at hx
  simp_rw [Algebra.adjoin_eq_span] at hx ⊢
  exact multiple_mem_span_of_mem_localization_span M R' _ _ hx

end

namespace Module.Finite

section

variable {R : Type u} [CommSemiring R] (S : Submonoid R)
variable {Rₚ : Type v} [CommSemiring Rₚ] [Algebra R Rₚ] [IsLocalization S Rₚ]
variable {M : Type w} [AddCommMonoid M] [Module R M]
variable {Mₚ : Type t} [AddCommMonoid Mₚ] [Module R Mₚ] [Module Rₚ Mₚ] [IsScalarTower R Rₚ Mₚ]
variable (f : M →ₗ[R] Mₚ) [IsLocalizedModule S f]

lemma of_isLocalization (R S) {Rₚ Sₚ : Type*} [CommSemiring R] [CommSemiring S]
    [CommSemiring Rₚ] [CommSemiring Sₚ] [Algebra R S] [Algebra R Rₚ] [Algebra R Sₚ] [Algebra S Sₚ]
    [Algebra Rₚ Sₚ] [IsScalarTower R S Sₚ] [IsScalarTower R Rₚ Sₚ] (M : Submonoid R)
    [IsLocalization M Rₚ] [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₚ]
    [hRS : Module.Finite R S] :
    Module.Finite Rₚ Sₚ := by
  classical
  have : algebraMap Rₚ Sₚ = IsLocalization.map (T := Algebra.algebraMapSubmonoid S M) Sₚ
      (algebraMap R S) (Submonoid.le_comap_map M) := by
    apply IsLocalization.ringHom_ext M
    simp only [IsLocalization.map_comp, ← IsScalarTower.algebraMap_eq]
  -- We claim that if `S` is generated by `T` as an `R`-module,
  -- then `S'` is generated by `T` as an `R'`-module.
  obtain ⟨T, hT⟩ := hRS
  use T.image (algebraMap S Sₚ)
  simpa using span_eq_top_localization_localization Rₚ M Sₚ hT

instance {R S : Type*} [CommRing R] {P : Ideal R} [CommRing S] [Algebra R S]
    [Module.Finite R S] [P.IsPrime] :
    Module.Finite (Localization.AtPrime P)
      (Localization (Algebra.algebraMapSubmonoid S P.primeCompl)) :=
  .of_isLocalization R S P.primeCompl

open Algebra nonZeroDivisors in
instance {A C : Type*} [CommRing A] [CommRing C] [Algebra A C] [Module.Finite A C] :
    Module.Finite (FractionRing A) (Localization (algebraMapSubmonoid C A⁰)) :=
  have : IsScalarTower A (FractionRing A) (Localization (algebraMapSubmonoid C A⁰)) :=
    instIsScalarTowerLocalizationAlgebraMapSubmonoid A⁰ C
  .of_isLocalization A C A⁰

include S f in
lemma of_isLocalizedModule [Module.Finite R M] : Module.Finite Rₚ Mₚ := by
  classical
  obtain ⟨T, hT⟩ := ‹Module.Finite R M›
  use T.image f
  simpa using span_eq_top_of_isLocalizedModule Rₚ S f hT

instance [Module.Finite R M] : Module.Finite (Localization S) (LocalizedModule S M) :=
  of_isLocalizedModule S (LocalizedModule.mkLinearMap S M)

end

variable {R : Type u} [CommRing R] {M : Type w} [AddCommMonoid M] [Module R M]

/--
If there exists a finite set `{ r }` of `R` such that `Mᵣ` is `Rᵣ`-finite for each `r`,
then `M` is a finite `R`-module.

General version for any modules `Mᵣ` and rings `Rᵣ` satisfying the correct universal properties.
See `Module.Finite.of_localizationSpan_finite` for the specialized version.

See `of_localizationSpan'` for a version without the finite set assumption.
-/
theorem of_localizationSpan_finite' (t : Finset R) (ht : Ideal.span (t : Set R) = ⊤)
    {Mₚ : ∀ (_ : t), Type*} [∀ (g : t), AddCommMonoid (Mₚ g)] [∀ (g : t), Module R (Mₚ g)]
    {Rₚ : ∀ (_ : t), Type u} [∀ (g : t), CommRing (Rₚ g)] [∀ (g : t), Algebra R (Rₚ g)]
    [∀ (g : t), IsLocalization.Away g.val (Rₚ g)]
    [∀ (g : t), Module (Rₚ g) (Mₚ g)] [∀ (g : t), IsScalarTower R (Rₚ g) (Mₚ g)]
    (f : ∀ (g : t), M →ₗ[R] Mₚ g) [∀ (g : t), IsLocalizedModule (Submonoid.powers g.val) (f g)]
    (H : ∀ (g : t), Module.Finite (Rₚ g) (Mₚ g)) :
    Module.Finite R M := by
  classical
  constructor
  choose s₁ s₂ using (fun g ↦ (H g).1)
  let sf := fun x : t ↦
    IsLocalizedModule.finsetIntegerMultiple (Submonoid.powers x.val) (f x) (s₁ x)
  use t.attach.biUnion sf
  rw [Submodule.span_attach_biUnion, eq_top_iff]
  rintro x -
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ (t : Set R) ht _ (fun r ↦ ?_)
  set S : Submonoid R := Submonoid.powers r.val
  obtain ⟨⟨_, n₁, rfl⟩, hn₁⟩ := multiple_mem_span_of_mem_localization_span S (Rₚ r)
    (s₁ r : Set (Mₚ r)) (IsLocalizedModule.mk' (f r) x (1 : S)) (by rw [s₂ r]; trivial)
  rw [Submonoid.smul_def, ← IsLocalizedModule.mk'_smul, IsLocalizedModule.mk'_one] at hn₁
  obtain ⟨⟨_, n₂, rfl⟩, hn₂⟩ := IsLocalizedModule.smul_mem_finsetIntegerMultiple_span
    S (f r) _ (s₁ r) hn₁
  rw [Submonoid.smul_def] at hn₂
  use n₂ + n₁
  apply le_iSup (fun x : t ↦ Submodule.span R (sf x : Set M)) r
  rw [pow_add, mul_smul]
  exact hn₂

/--
If there exists a set `{ r }` of `R` such that `Mᵣ` is `Rᵣ`-finite for each `r`,
then `M` is a finite `R`-module.

General version for any modules `Mᵣ` and rings `Rᵣ` satisfying the correct universal properties.
See `Module.Finite.of_localizationSpan_finite` for the specialized version.
-/
theorem of_localizationSpan' (t : Set R) (ht : Ideal.span t = ⊤)
    {Mₚ : ∀ (_ : t), Type*} [∀ (g : t), AddCommMonoid (Mₚ g)] [∀ (g : t), Module R (Mₚ g)]
    {Rₚ : ∀ (_ : t), Type u} [∀ (g : t), CommRing (Rₚ g)] [∀ (g : t), Algebra R (Rₚ g)]
    [h₁ : ∀ (g : t), IsLocalization.Away g.val (Rₚ g)]
    [∀ (g : t), Module (Rₚ g) (Mₚ g)] [∀ (g : t), IsScalarTower R (Rₚ g) (Mₚ g)]
    (f : ∀ (g : t), M →ₗ[R] Mₚ g) [h₂ : ∀ (g : t), IsLocalizedModule (Submonoid.powers g.val) (f g)]
    (H : ∀ (g : t), Module.Finite (Rₚ g) (Mₚ g)) :
    Module.Finite R M := by
  rw [Ideal.span_eq_top_iff_finite] at ht
  obtain ⟨t', hc, ht'⟩ := ht
  have (g : t') : IsLocalization.Away g.val (Rₚ ⟨g.val, hc g.property⟩) :=
    h₁ ⟨g.val, hc g.property⟩
  have (g : t') : IsLocalizedModule (Submonoid.powers g.val)
    ((fun g ↦ f ⟨g.val, hc g.property⟩) g) := h₂ ⟨g.val, hc g.property⟩
  apply of_localizationSpan_finite' t' ht' (fun g ↦ f ⟨g.val, hc g.property⟩)
    (fun g ↦ H ⟨g.val, hc g.property⟩)

/--
If there exists a finite set `{ r }` of `R` such that `Mᵣ` is `Rᵣ`-finite for each `r`,
then `M` is a finite `R`-module.

See `of_localizationSpan` for a version without the finite set assumption.
-/
theorem of_localizationSpan_finite (t : Finset R) (ht : Ideal.span (t : Set R) = ⊤)
    (H : ∀ (g : t), Module.Finite (Localization.Away g.val)
      (LocalizedModule (Submonoid.powers g.val) M)) :
    Module.Finite R M :=
  let f (g : t) : M →ₗ[R] LocalizedModule (Submonoid.powers g.val) M :=
    LocalizedModule.mkLinearMap (Submonoid.powers g.val) M
  of_localizationSpan_finite' t ht f H

/-- If there exists a set `{ r }` of `R` such that `Mᵣ` is `Rᵣ`-finite for each `r`,
then `M` is a finite `R`-module. -/
theorem of_localizationSpan (t : Set R) (ht : Ideal.span t = ⊤)
    (H : ∀ (g : t), Module.Finite (Localization.Away g.val)
      (LocalizedModule (Submonoid.powers g.val) M)) :
    Module.Finite R M :=
  let f (g : t) : M →ₗ[R] LocalizedModule (Submonoid.powers g.val) M :=
    LocalizedModule.mkLinearMap (Submonoid.powers g.val) M
  of_localizationSpan' t ht f H

end Finite

end Module

namespace Ideal

variable {R : Type u} [CommRing R]

/-- If `I` is an ideal such that there exists a set `{ r }` of `R` such
that the image of `I` in `Rᵣ` is finitely generated for each `r`, then `I` is finitely
generated. -/
lemma fg_of_localizationSpan {I : Ideal R} (t : Set R) (ht : Ideal.span t = ⊤)
    (H : ∀ (g : t), (I.map (algebraMap R (Localization.Away g.val))).FG) : I.FG := by
  apply Module.Finite.iff_fg.mp
  let k (g : t) : I →ₗ[R] (I.map (algebraMap R (Localization.Away g.val))) :=
    Algebra.idealMap I (S := Localization.Away g.val)
  exact Module.Finite.of_localizationSpan' t ht k (fun g ↦ .of_fg (H g))

end Ideal

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] {f : R →+* S}

/--
To check that the kernel of a ring homomorphism is finitely generated,
it suffices to check this after localizing at a spanning set of the source.
-/
lemma RingHom.ker_fg_of_localizationSpan (t : Set R) (ht : Ideal.span t = ⊤)
    (H : ∀ g : t, (RingHom.ker (Localization.awayMap f g.val)).FG) :
    (RingHom.ker f).FG := by
  apply Ideal.fg_of_localizationSpan t ht
  intro g
  rw [← IsLocalization.ker_map (Localization.Away (f g.val)) f (Submonoid.map_powers f g.val)]
  exact H g
