/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Module.LocalizedModule.Int
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.RingHom.Finite

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

universe u v w t

namespace Module.Finite

section

variable {R : Type u} [CommSemiring R] (S : Submonoid R)
variable {Rₚ : Type v} [CommSemiring Rₚ] [Algebra R Rₚ] [IsLocalization S Rₚ]
variable {M : Type w} [AddCommMonoid M] [Module R M]
variable {Mₚ : Type t} [AddCommMonoid Mₚ] [Module R Mₚ] [Module Rₚ Mₚ] [IsScalarTower R Rₚ Mₚ]
variable (f : M →ₗ[R] Mₚ) [IsLocalizedModule S f]

include S f in
lemma of_isLocalizedModule [Module.Finite R M] : Module.Finite Rₚ Mₚ := by
  classical
  obtain ⟨T, hT⟩ := ‹Module.Finite R M›
  use T.image f
  rw [eq_top_iff]
  rintro x -
  obtain ⟨⟨y, m⟩, (hyx : IsLocalizedModule.mk' f y m = x)⟩ :=
    IsLocalizedModule.mk'_surjective S f x
  have hy : y ∈ Submodule.span R T := by rw [hT]; trivial
  have : f y ∈ Submodule.map f (Submodule.span R T) := Submodule.mem_map_of_mem hy
  rw [Submodule.map_span] at this
  have H : Submodule.span R (f '' T) ≤
      (Submodule.span Rₚ (f '' T)).restrictScalars R := by
    rw [Submodule.span_le]; exact Submodule.subset_span
  convert (Submodule.span Rₚ (f '' T)).smul_mem
    (IsLocalization.mk' Rₚ (1 : R) m) (H this) using 0
  · rw [← hyx, ← IsLocalizedModule.mk'_one S, IsLocalizedModule.mk'_smul_mk']
    simp

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
  exact Module.Finite.of_localizationSpan' t ht k (fun g ↦ Module.Finite.iff_fg.mpr (H g))

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
