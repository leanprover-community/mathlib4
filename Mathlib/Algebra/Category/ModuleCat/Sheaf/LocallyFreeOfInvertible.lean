/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.TensorTrivialization
public import Mathlib.Algebra.Category.Ring.Sheaf.Local
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# Tensor-invertible modules over locally ringed sites

Over a locally ringed site, a sheaf of modules with a tensor inverse is locally free of rank
one. The proof uses local bijectivity of the associated pairing of presheaves of modules,
and does not require points of the site.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite

universe u v w

namespace SheafOfModulesOfCommRing

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{w}}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {F G : SheafOfModulesOfCommRing.{w} R}
  (b : F.val ⊗ G.val ⟶ PresheafOfModulesOfCommRing.unit R.obj)

set_option backward.isDefEq.respectTransparency false in
/-- A section of a tensor product mapping to one is a nonempty finite sum of pure tensors
whose images sum to one. -/
private lemma exists_nonempty_sum_eq_one {X : C}
    (t : (F.val ⊗ G.val).obj (op X))
    (ht : (b.app' (op X)).hom t = (1 : R.obj.obj (op X))) :
    ∃ s : Finset (F.obj (op X) × G.obj (op X)), s.Nonempty ∧
      ∑ p ∈ s, (b.app' (op X)).hom (p.1 ⊗ₜ[R.obj.obj (op X)] p.2) =
        (1 : R.obj.obj (op X)) := by
  classical
  obtain ⟨s, rfl⟩ := TensorProduct.exists_finset t
  refine ⟨insert (0, 0) s, Finset.insert_nonempty _ _, ?_⟩
  rw [Finset.sum_insert_zero (by simp)]
  simpa only [map_sum] using ht

set_option backward.isDefEq.respectTransparency false in
/-- A locally surjective tensor pairing over a locally ringed site takes the value one on
a pure tensor locally. -/
lemma coversTop_tensor_pairing_eq_one [R.IsLocallyRinged]
    [Presheaf.IsLocallySurjective J ((PresheafOfModulesOfCommRing.toPresheaf R.obj).map b)] :
    J.CoversTop (fun X : { X : C // ∃ (m : F.obj (op X)) (n : G.obj (op X)),
      b.app' (op X) (m ⊗ₜ[R.obj.obj (op X)] n) = (1 : R.obj.obj (op X)) } ↦ X.val) := by
  intro X
  refine J.transitive (Presheaf.imageSieve_mem J
    ((PresheafOfModulesOfCommRing.toPresheaf R.obj).map b)
    (show (PresheafOfModulesOfCommRing.unit R.obj).obj (op X) from
      (1 : R.obj.obj (op X)))) _ ?_
  rintro Y f ⟨t, ht⟩
  change b.app' (op Y) t = R.obj.map f.op (1 : R.obj.obj (op X)) at ht
  rw [map_one] at ht
  obtain ⟨s, hs, hsum⟩ := exists_nonempty_sum_eq_one b t ht
  let a : F.obj (op Y) × G.obj (op Y) → R.obj.obj (op Y) :=
    fun p ↦ b.app' (op Y) (p.1 ⊗ₜ[R.obj.obj (op Y)] p.2)
  refine J.superset_covering ?_
    (R.finset_sup_isUnitSieve_mem_of_isUnit_sum hs a (hsum ▸ isUnit_one))
  intro Z g hg
  obtain ⟨p, _, hunit⟩ := (R.finset_sup_isUnitSieve_apply s a g).mp hg
  obtain ⟨c, hc⟩ := hunit.exists_left_inv
  refine ⟨⟨Z, c • F.map g.op p.1, G.map g.op p.2, ?_⟩, ⟨𝟙 Z⟩⟩
  rw [← TensorProduct.smul_tmul', map_smul]
  change c * (show R.obj.obj (op Z) from b.app' (op Z) ((F.val ⊗ G.val).map g.op
    (p.1 ⊗ₜ[R.obj.obj (op Y)] p.2))) = 1
  rw [PresheafOfModulesOfCommRing.naturality_apply]
  exact hc

variable [R.IsLocallyRinged]
  [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{w}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]

set_option backward.isDefEq.respectTransparency false in
/-- A locally bijective tensor pairing over a locally ringed site makes either factor
locally free of rank one. -/
theorem isLocallyFreeOfRank_one_of_tensor_pairing
    [Presheaf.IsLocallyInjective J ((PresheafOfModulesOfCommRing.toPresheaf R.obj).map b)]
    [Presheaf.IsLocallySurjective J ((PresheafOfModulesOfCommRing.toPresheaf R.obj).map b)] :
    F.IsLocallyFreeOfRank 1 := by
  let I := { X : C // ∃ (m : F.obj (op X)) (n : G.obj (op X)),
    b.app' (op X) (m ⊗ₜ[R.obj.obj (op X)] n) = (1 : R.obj.obj (op X)) }
  choose m n h using fun X : I ↦ X.property
  exact SheafOfModules.isLocallyFreeOfRank_one_of_coversTop
    (coversTop_tensor_pairing_eq_one b) (fun X ↦ isoUnitOfTensorPairing b (m X) (n X) (h X))

variable [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [(W R).IsMonoidal]

/-- A tensor-invertible sheaf of modules on a locally ringed site is locally free of rank
one. No assumption on the points of the site is needed. -/
@[stacks 0B8Q]
theorem isLocallyFreeOfRank_one_of_tensor_iso
    (η : F ⊗ G ≅ (𝟙_ (SheafOfModulesOfCommRing.{w} R))) : F.IsLocallyFreeOfRank 1 := by
  let b : F.val ⊗ G.val ⟶ PresheafOfModulesOfCommRing.unit R.obj :=
    Functor.LaxMonoidal.μ (forget R) F G ≫ (forget R).map η.hom
  have hb : W R b := (W R).comp_mem _ _ (W_μ R F G)
    ((W_forget_map_iff_isIso R η.hom).2 inferInstance)
  have : Presheaf.IsLocallyInjective J ((PresheafOfModulesOfCommRing.toPresheaf R.obj).map b) :=
    hb.isLocallyInjective
  have : Presheaf.IsLocallySurjective J ((PresheafOfModulesOfCommRing.toPresheaf R.obj).map b) :=
    hb.isLocallySurjective
  exact isLocallyFreeOfRank_one_of_tensor_pairing b

end SheafOfModulesOfCommRing
