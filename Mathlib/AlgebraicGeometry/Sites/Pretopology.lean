/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Grothendieck topology defined by a morphism property

Given a multiplicative morphism property `P` that is stable under base change, we define the
associated (pre)topology on the category of schemes, where coverings are given
by jointly surjective families of morphisms satisfying `P`.

## Implementation details

The pretopology is obtained from the precoverage `AlgebraicGeometry.Scheme.precoverage` defined in
`Mathlib.AlgebraicGeometry.Sites.MorphismProperty`. The definition is postponed to this file,
because the former does not have `HasPullbacks Scheme`.
-/

universe v u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/--
The pretopology on the category of schemes defined by covering families where the components
satisfy `P`.
-/
def pretopology (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.IsMultiplicative] : Pretopology Scheme.{u} :=
  (precoverage P).toPretopology

/-- The Grothendieck topology on the category of schemes induced by the pretopology defined by
`P`-covers. -/
abbrev grothendieckTopology (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.IsMultiplicative] :
    GrothendieckTopology Scheme.{u} :=
  (pretopology P).toGrothendieck

instance : jointlySurjectivePrecoverage.IsStableUnderBaseChange where
  mem_coverings_of_isPullback {ι} S X f hf Y g T p₁ p₂ H x := by
    obtain ⟨-, -, ⟨i⟩, y, hy⟩ := hf (g.base x)
    clear Y
    have := (H i).hasPullback
    obtain ⟨w, hw⟩ := IsJointlySurjectivePreserving.exists_preimage_fst_triplet_of_prop (P := ⊤)
      trivial (f := g) x y hy.symm
    use T i, p₁ i, ⟨i⟩, (H i).isoPullback.inv.base w
    simpa [← Scheme.comp_base_apply]

/-- The pretopology on the category of schemes defined by jointly surjective families. -/
def jointlySurjectivePretopology : Pretopology Scheme.{u} :=
  jointlySurjectivePrecoverage.toPretopology

variable {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange] [P.IsMultiplicative]

lemma mem_iff_exists_cover {K : Precoverage Scheme.{u}} {X : Scheme.{u}} {R : Presieve X} :
    R ∈ K X ↔ ∃ (𝒰 : Cover.{u + 1} K X), R = Presieve.ofArrows 𝒰.X 𝒰.f :=
  K.mem_iff_exists_zeroHypercover

lemma mem_pretopology {X : Scheme.{u}} {R : Presieve X} :
    R ∈ pretopology P X ↔ ∃ (𝒰 : Cover.{u + 1} (precoverage P) X), R = Presieve.ofArrows 𝒰.X 𝒰.f :=
  (precoverage P).mem_iff_exists_zeroHypercover

alias ⟨exists_cover_of_mem_pretopology, _⟩ := mem_pretopology

lemma mem_grothendieckTopology {X : Scheme.{u}} {S : Sieve X} :
    S ∈ grothendieckTopology P X ↔
      ∃ (𝒰 : Cover.{u} (precoverage P) X), Presieve.ofArrows 𝒰.X 𝒰.f ≤ S := by
  simp_rw [grothendieckTopology, Pretopology.mem_toGrothendieck]
  refine ⟨fun ⟨R, hR, hle⟩ ↦ ?_, fun ⟨𝒰, hle⟩ ↦ ⟨.ofArrows 𝒰.X 𝒰.f, 𝒰.mem₀, hle⟩⟩
  rw [mem_pretopology] at hR
  obtain ⟨𝒰, rfl⟩ := hR
  use 𝒰.ulift, le_trans (fun Y g ⟨i⟩ ↦ .mk _) hle

alias ⟨exists_cover_of_mem_grothendieckTopology, _⟩ := mem_grothendieckTopology

@[grind ←]
lemma Cover.mem_pretopology {X : Scheme.{u}} {𝒰 : X.Cover (precoverage P)} :
    Presieve.ofArrows 𝒰.X 𝒰.f ∈ pretopology P X := 𝒰.mem₀

@[grind ←]
lemma Cover.mem_grothendieckTopology {X : Scheme.{u}} {𝒰 : X.Cover (precoverage P)} :
    Sieve.ofArrows 𝒰.X 𝒰.f ∈ grothendieckTopology P X := by
  rw [Pretopology.mem_toGrothendieck]
  use Presieve.ofArrows 𝒰.X 𝒰.f, 𝒰.mem₀
  exact Sieve.le_generate (Presieve.ofArrows 𝒰.X 𝒰.f)

@[deprecated (since := "2025-08-28")]
alias pretopology_cover := Cover.mem_pretopology

@[deprecated (since := "2025-08-28")]
alias grothendieckTopology_cover := Cover.mem_grothendieckTopology

section

@[deprecated (since := "2025-08-18")] alias surjectiveFamiliesPretopology :=
  jointlySurjectivePretopology

/-- The jointly surjective topology on `Scheme` is defined by the same condition as the jointly
surjective pretopology. -/
def jointlySurjectiveTopology : GrothendieckTopology Scheme.{u} :=
  jointlySurjectivePretopology.toGrothendieck.copy (fun X s ↦ jointlySurjectivePretopology X ↑s) <|
    funext fun _ ↦ Set.ext fun s ↦
      ⟨fun ⟨_, hp, hps⟩ x ↦ let ⟨Y, u, hu, hmem⟩ := hp x; ⟨Y, u, hps _ hu, hmem⟩,
      fun hs ↦ ⟨s, hs, le_rfl⟩⟩

theorem mem_jointlySurjectiveTopology_iff_jointlySurjectivePretopology
    {X : Scheme.{u}} {s : Sieve X} :
    s ∈ jointlySurjectiveTopology X ↔ jointlySurjectivePretopology X ↑s :=
  Iff.rfl

lemma jointlySurjectiveTopology_eq_toGrothendieck_jointlySurjectivePretopology :
    jointlySurjectiveTopology.{u} = jointlySurjectivePretopology.toGrothendieck :=
  GrothendieckTopology.copy_eq

variable (P)

/--
The pretopology defined by `P`-covers agrees with the
the intersection of the pretopology of surjective families with the pretopology defined by `P`.
-/
lemma pretopology_eq_inf : pretopology P = jointlySurjectivePretopology ⊓ P.pretopology := by
  ext : 1
  rw [pretopology, Precoverage.toPretopology_toPrecoverage]
  rfl

@[deprecated (since := "2025-08-28")]
alias pretopology_le_inf := pretopology_eq_inf

/--
The Grothendieck topology defined by `P`-covers agrees with the Grothendieck
topology induced by the intersection of the pretopology of surjective families with
the pretopology defined by `P`.
-/
lemma grothendieckTopology_eq_inf :
    grothendieckTopology P = (jointlySurjectivePretopology ⊓ P.pretopology).toGrothendieck := by
  rw [grothendieckTopology, pretopology_eq_inf]

end

section

variable {Q : MorphismProperty Scheme.{u}} [Q.IsMultiplicative] [Q.IsStableUnderBaseChange]

lemma pretopology_le_pretopology (hPQ : P ≤ Q) :
    pretopology P ≤ pretopology Q := by
  rintro X R hR
  obtain ⟨𝒰, rfl⟩ := exists_cover_of_mem_pretopology hR
  rw [mem_pretopology]
  use 𝒰.changeProp (fun j ↦ hPQ _ (𝒰.map_prop j))
  rfl

lemma grothendieckTopology_le_grothendieckTopology (hPQ : P ≤ Q) :
    grothendieckTopology P ≤ grothendieckTopology Q :=
  (Pretopology.gi Scheme.{u}).gc.monotone_l (pretopology_le_pretopology hPQ)

end

end AlgebraicGeometry.Scheme
