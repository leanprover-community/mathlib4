/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.FrameBridgeRoots
import Mathlib

set_option linter.minImports true

/-!
# The packet construction: the small-root packet product = the Weierstrass factor's root product

This is the mathematical core of the frame bridge (`FrameBridge`).  Given the Weierstrass
distinguished factor as a polynomial `Pω` over the Laurent frame `Ω` dividing `Φ` there, the packet
`S` — the roots of `Φ` in the splitting field whose `ψ`-image is a root of `Pω` — has
`ψ(∏_{β∈S} β) = ∏(Pω.roots)`.  Combined with Vieta (`∏(Pω.roots) = (-1)ᴹ Pω.coeff 0`) and the
Weierstrass value (`= c·t` under `hderiv`), this discharges the frame-side identity of
`GMC2FrameBridge.hS_of_splits` — with **no** valuation, purely by the root bijection `ψ` supplies.
-/

open Polynomial

namespace GMC2FrameBridgePacket

variable {F : Type*} [Field F]

/-- **The packet product.**  For any `RatFunc F`-embedding `ψ` of the splitting field of `Φ ≠ 0` into a
field `Ω`, and any polynomial `Pω` over `Ω` with distinct roots dividing `Φ` over `Ω`, there is a set
`S` of splitting-field roots of `Φ` whose product maps under `ψ` to the product of the roots of `Pω`.
`S` is the roots landing on `Pω`; the root-transport bijection (`aroots_map_embedding`) makes
`β ↦ ψ β` a bijection from `S` onto `Pω`'s roots. -/
theorem exists_packet_prod_eq (Φ : (RatFunc F)[X]) (hΦ0 : Φ ≠ 0)
    {Ω : Type*} [Field Ω] [Algebra (RatFunc F) Ω]
    (ψ : Φ.SplittingField →ₐ[RatFunc F] Ω)
    (Pω : Polynomial Ω) (hPωnd : Pω.roots.Nodup)
    (hdvd : Pω ∣ Φ.map (algebraMap (RatFunc F) Ω)) :
    ∃ S : Finset (Φ.rootSet Φ.SplittingField),
      ψ (∏ β ∈ S, (β : Φ.SplittingField)) = Pω.roots.prod := by
  classical
  have hψinj : Function.Injective (ψ : Φ.SplittingField → Ω) := ψ.toRingHom.injective
  have hΦΩ0 : Φ.map (algebraMap (RatFunc F) Ω) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap (RatFunc F) Ω).injective).mpr hΦ0
  have hle : Pω.roots ≤ Φ.aroots Ω := by
    rw [Polynomial.aroots_def]; exact Polynomial.roots.le_of_dvd hΦΩ0 hdvd
  have htrans : Φ.aroots Ω = (Φ.aroots Φ.SplittingField).map ψ :=
    (GMC2FrameBridgeRoots.aroots_map_embedding Φ ψ).symm
  -- product over the deduplicated roots of `Pω` is the multiset product
  have key : ∏ α ∈ Pω.roots.toFinset, (α : Ω) = Pω.roots.prod := by
    show (Pω.roots.toFinset.val.map (fun α => α)).prod = Pω.roots.prod
    rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hPωnd, Multiset.map_id']
  refine ⟨Finset.univ.filter (fun β => ψ (β : Φ.SplittingField) ∈ Pω.roots), ?_⟩
  rw [map_prod, ← key]
  -- `∏_{β∈S} ψ β = ∏_{α ∈ Pω.roots.toFinset} α` via the bijection `β ↦ ψ β`
  refine Finset.prod_bij (fun β _ => ψ (β : Φ.SplittingField)) ?_ ?_ ?_ ?_
  · -- lands in the target
    intro β hβ
    rw [Multiset.mem_toFinset]
    exact (Finset.mem_filter.mp hβ).2
  · -- injective
    intro β₁ _ β₂ _ heq
    exact Subtype.ext (hψinj heq)
  · -- surjective
    intro α hα
    rw [Multiset.mem_toFinset] at hα
    have hαΩ : α ∈ Φ.aroots Ω := Multiset.mem_of_le hle hα
    rw [htrans, Multiset.mem_map] at hαΩ
    obtain ⟨γ, hγ, hγα⟩ := hαΩ
    have hγroot : γ ∈ Φ.rootSet Φ.SplittingField := by
      rw [Polynomial.mem_rootSet']
      exact Polynomial.mem_aroots'.mp hγ
    refine ⟨⟨γ, hγroot⟩, ?_, hγα⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    show ψ γ ∈ Pω.roots
    rw [hγα]; exact hα
  · -- values agree
    intro β _; rfl

end GMC2FrameBridgePacket

