/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Quotienting out a free `ℤ`-module

If `G` is a rank `d` free `ℤ`-module, then `G/nG` is a finite group of cardinality `n ^ d`.
-/

open Finsupp Function Module

variable {G H M : Type*} [AddCommGroup G] {n : ℕ}

variable (G n) in
/-- `ModN G n` denotes the quotient of `G` by multiples of `n` -/
abbrev ModN : Type _ := G ⧸ LinearMap.range (LinearMap.lsmul ℤ G n)

namespace ModN

instance : Module (ZMod n) (ModN G n) := QuotientAddGroup.zmodModule (by simp)

/-- The universal property of `ModN G n` in terms of monoids: Monoid homomorphisms from `ModN G n`
are the same as monoid homomorphisms from `G` whose values are `n`-torsion. -/
protected def liftEquiv [AddMonoid M] : (ModN G n →+ M) ≃ {φ : G →+ M // ∀ g, n • φ g = 0} where
  toFun f := ⟨f.comp (QuotientAddGroup.mk' _), fun g ↦ by
    let Gn : AddSubgroup G := (LinearMap.range (LinearMap.lsmul ℤ G n)).toAddSubgroup
    suffices n • g ∈ (QuotientAddGroup.mk' Gn).ker by
      simp only [AddMonoidHom.coe_comp, comp_apply, ← map_nsmul]
      change f (QuotientAddGroup.mk' Gn (n • g)) = 0 -- Can we avoid `change`?
      rw [this, map_zero]
    simp [QuotientAddGroup.ker_mk', Gn]⟩
  invFun φ := QuotientAddGroup.lift _ φ <| by rintro - ⟨g, rfl⟩; simpa using φ.property g
  left_inv f := by
    ext x
    induction x using QuotientAddGroup.induction_on
    rfl -- Should `simp` suffice here?
  right_inv φ := by aesop

/-- The universal property of `ModN G n` in terms of `ZMod n`-modules: `ZMod n`-linear maps from
`ModN G n` are the same as monoid homomorphisms from `G` whose values are `n`-torsion. -/
protected def liftEquiv' [AddCommGroup H] [Module (ZMod n) H] :
    (ModN G n →ₗ[ZMod n] H) ≃ {φ : G →+ H // ∀ g, n • φ g = 0} :=
  (AddMonoidHom.toZModLinearMapEquiv n).symm.toEquiv.trans ModN.liftEquiv

variable (n) in
/-- The quotient map `G → G / nG`. -/
def mkQ : G →+ ModN G n := (LinearMap.range (LinearMap.lsmul ℤ G n)).mkQ

variable [NeZero n]

/-- Given a free module `G` over `ℤ`, construct the corresponding basis
of `G / ⟨n⟩` over `ℤ / nℤ`. -/
noncomputable def basis {ι : Type*} (b : Basis ι ℤ G) : Basis ι (ZMod n) (ModN G n) := by
  set ψ : G →+ G := zsmulAddGroupHom n
  set nG := LinearMap.range (LinearMap.lsmul ℤ G n)
  set H := G ⧸ nG
  set φ : G →ₗ[ℤ] H := nG.mkQ
  let mod : (ι →₀ ℤ) →ₗ[ℤ] (ι →₀ ZMod n) := mapRange.linearMap (Int.castAddHom _).toIntLinearMap
  let f : G →ₗ[ℤ] (ι →₀ ℤ) := b.repr
  have hker : nG ≤ LinearMap.ker (mod.comp f) := by
    rintro _ ⟨x, rfl⟩
    ext b
    simp [mod, f]
  let g : H →ₗ[ℤ] (ι →₀ ZMod n) := nG.liftQ (mod.comp f) hker
  refine ⟨.ofBijective (g.toAddMonoidHom.toZModLinearMap n) ⟨?_, ?_⟩⟩
  · rw [AddMonoidHom.coe_toZModLinearMap, LinearMap.toAddMonoidHom_coe, injective_iff_map_eq_zero,
      nG.mkQ_surjective.forall]
    intro x hx
    simp only [Submodule.mkQ_apply, g] at hx
    rw [Submodule.liftQ_apply] at hx
    replace hx : ∀ b, ↑n ∣ f x b := by
      simpa [mod, DFunLike.ext_iff, ZMod.intCast_zmod_eq_zero_iff_dvd] using hx
    simp only [Submodule.mkQ_apply]
    rw [Submodule.Quotient.mk_eq_zero]
    choose c hc using hx
    refine ⟨b.repr.symm ⟨(f x).support, c, by simp [hc, NeZero.ne]⟩, b.repr.injective ?_⟩
    simpa [DFunLike.ext_iff, eq_comm] using hc
  · suffices mod ∘ b.repr = g ∘ nG.mkQ by
      exact (this ▸ (mapRange_surjective _ (map_zero _) ZMod.intCast_surjective).comp
        b.repr.surjective).of_comp
    ext x b
    simp [mod, g, f, H]

lemma basis_apply_eq_mkQ {ι : Type*} (b : Basis ι ℤ G) (i : ι) : basis b i = mkQ n (b i) := by
  rw [Basis.apply_eq_iff]; simp [basis, mkQ]

variable [Module.Free ℤ G] [Module.Finite ℤ G]

instance instModuleFinite : Module.Finite (ZMod n) (ModN G n) :=
  .of_basis <| basis <| Module.Free.chooseBasis ℤ G

instance instFinite : Finite (ModN G n) := Module.finite_of_finite (ZMod n)

variable (G n)
@[simp] lemma natCard_eq : Nat.card (ModN G n) = n ^ Module.finrank ℤ G := by
  simp [Nat.card_congr (basis <| Module.Free.chooseBasis ℤ G).repr.toEquiv,
    Nat.card_eq_fintype_card, Module.finrank_eq_card_chooseBasisIndex]

end ModN
