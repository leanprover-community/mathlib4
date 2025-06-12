/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin
-/
import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.ZMod.QuotientRing

/-!
# Structure of finite(ly generated) abelian groups

* `AddCommGroup.equiv_free_prod_directSum_zmod` : Any finitely generated abelian group is the
  product of a power of `ℤ` and a direct sum of some `ZMod (p i ^ e i)` for some prime powers
  `p i ^ e i`.
* `AddCommGroup.equiv_directSum_zmod_of_finite` : Any finite abelian group is a direct sum of
  some `ZMod (p i ^ e i)` for some prime powers `p i ^ e i`.
* `CommGroup.equiv_prod_multiplicative_zmod_of_finite` is a version for multiplicative groups.
-/

open scoped DirectSum

/-
TODO: Here's a more general approach to dropping trivial factors from a direct sum:

def DirectSum.congr {ι κ : Type*} {α : ι → Type*} {β : κ → Type*} [DecidableEq ι] [DecidableEq κ]
    [∀ i, DecidableEq (α i)] [∀ j, DecidableEq (β j)] [∀ i, AddCommMonoid (α i)]
    [∀ j, AddCommMonoid (β j)] (f : ∀ i, Nontrivial (α i) → κ) (g : ∀ j, Nontrivial (β j) → ι)
    (F : ∀ i hi, α i →+ β (f i hi)) (G : ∀ j hj, β j →+ α (g j hj))
    (hfg : ∀ i hi hj, g (f i hi) hj = i) (hgf : ∀ j hj hi, f (g j hj) hi = j)
    (hFG : ∀ i hi hj a, hfg i hi hj ▸ G _ hj (F i hi a) = a)
    (hGF : ∀ j hj hi b, hgf j hj hi ▸ F _ hi (G j hj b) = b) :
    (⨁ i, α i) ≃+ ⨁ j, β j where
  toFun x := x.sum fun i a ↦ if ha : a = 0 then 0 else DFinsupp.single (f i ⟨a, 0, ha⟩) (F _ _ a)
  invFun y := y.sum fun j b ↦ if hb : b = 0 then 0 else DFinsupp.single (g j ⟨b, 0, hb⟩) (G _ _ b)
  -- The two sorries here are probably doable with the existing machinery, but quite painful
  left_inv x := DFinsupp.ext fun i ↦ sorry
  right_inv y := DFinsupp.ext fun j ↦ sorry
  map_add' x₁ x₂ := by
    dsimp
    refine DFinsupp.sum_add_index (by simp) fun i a₁ a₂ ↦ ?_
    split_ifs
    any_goals simp_all
    rw [← DFinsupp.single_add, ← map_add, ‹a₁ + a₂ = 0›, map_zero, DFinsupp.single_zero]

private def directSumNeZeroMulEquiv (ι : Type) [DecidableEq ι] (p : ι → ℕ) (n : ι → ℕ) :
    (⨁ i : {i // n i ≠ 0}, ZMod (p i ^ n i)) ≃+ ⨁ i, ZMod (p i ^ n i) :=
  DirectSum.congr
    (fun i _ ↦ i)
    (fun j hj ↦ ⟨j, fun h ↦ by simp [h, pow_zero, zmod_nontrivial] at hj⟩)
    (fun i _ ↦ AddMonoidHom.id _)
    (fun j _ ↦ AddMonoidHom.id _)
    (fun i hi hj ↦ rfl)
    (fun j hj hi ↦ rfl)
    (fun i hi hj a ↦ rfl)
    (fun j hj hi a ↦ rfl)
-/

private def directSumNeZeroMulHom {ι : Type} [DecidableEq ι] (p : ι → ℕ) (n : ι → ℕ) :
    (⨁ i : {i // n i ≠ 0}, ZMod (p i ^ n i)) →+ ⨁ i, ZMod (p i ^ n i) :=
  DirectSum.toAddMonoid fun i ↦ DirectSum.of (fun i ↦ ZMod (p i ^ n i)) i

private def directSumNeZeroMulEquiv (ι : Type) [DecidableEq ι] (p : ι → ℕ) (n : ι → ℕ) :
    (⨁ i : {i // n i ≠ 0}, ZMod (p i ^ n i)) ≃+ ⨁ i, ZMod (p i ^ n i) where
  toFun := directSumNeZeroMulHom p n
  invFun := DirectSum.toAddMonoid fun i ↦
    if h : n i = 0 then 0 else DirectSum.of (fun j : {i // n i ≠ 0} ↦ ZMod (p j ^ n j)) ⟨i, h⟩
  left_inv x := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      rw [directSumNeZeroMulHom, DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of,
        dif_neg i.prop]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  right_inv x := by
    induction x using DirectSum.induction_on with
    | zero => rw [map_zero, map_zero]
    | of i x =>
      rw [DirectSum.toAddMonoid_of]
      split_ifs with h
      · simp [(ZMod.subsingleton_iff.2 <| by rw [h, pow_zero]).elim x 0]
      · simp_rw [directSumNeZeroMulHom, DirectSum.toAddMonoid_of]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  map_add' := map_add (directSumNeZeroMulHom p n)

universe u

namespace Module

variable (M : Type u)

theorem finite_of_fg_torsion [AddCommGroup M] [Module ℤ M] [Module.Finite ℤ M]
    (hM : Module.IsTorsion ℤ M) : _root_.Finite M := by
  rcases Module.equiv_directSum_of_isTorsion hM with ⟨ι, _, p, h, e, ⟨l⟩⟩
  haveI : ∀ i : ι, NeZero (p i ^ e i).natAbs := fun i =>
    ⟨Int.natAbs_ne_zero.mpr <| pow_ne_zero (e i) (h i).ne_zero⟩
  haveI : ∀ i : ι, _root_.Finite <| ℤ ⧸ Submodule.span ℤ {p i ^ e i} := fun i =>
    Finite.of_equiv _ (p i ^ e i).quotientSpanEquivZMod.symm.toEquiv
  haveI : _root_.Finite (⨁ i, ℤ ⧸ (Submodule.span ℤ {p i ^ e i} : Submodule ℤ ℤ)) :=
    Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  exact Finite.of_equiv _ l.symm.toEquiv

end Module

variable (G : Type u)

namespace AddCommGroup

variable [AddCommGroup G]

/-- **Structure theorem of finitely generated abelian groups** : Any finitely generated abelian
group is the product of a power of `ℤ` and a direct sum of some `ZMod (p i ^ e i)` for some
prime powers `p i ^ e i`. -/
theorem equiv_free_prod_directSum_zmod [hG : AddGroup.FG G] :
    ∃ (n : ℕ) (ι : Type) (_ : Fintype ι) (p : ι → ℕ) (_ : ∀ i, Nat.Prime <| p i) (e : ι → ℕ),
      Nonempty <| G ≃+ (Fin n →₀ ℤ) × ⨁ i : ι, ZMod (p i ^ e i) := by
  obtain ⟨n, ι, fι, p, hp, e, ⟨f⟩⟩ :=
    @Module.equiv_free_prod_directSum _ _ _ _ _ _ _ (Module.Finite.iff_addGroup_fg.mpr hG)
  refine ⟨n, ι, fι, fun i => (p i).natAbs, fun i => ?_, e, ⟨?_⟩⟩
  · rw [← Int.prime_iff_natAbs_prime, ← irreducible_iff_prime]; exact hp i
  exact
    f.toAddEquiv.trans
      ((AddEquiv.refl _).prodCongr <|
        DFinsupp.mapRange.addEquiv fun i =>
          ((Int.quotientSpanEquivZMod _).trans <|
              ZMod.ringEquivCongr <| (p i).natAbs_pow _).toAddEquiv)

/-- **Structure theorem of finite abelian groups** : Any finite abelian group is a direct sum of
some `ZMod (p i ^ e i)` for some prime powers `p i ^ e i`. -/
theorem equiv_directSum_zmod_of_finite [Finite G] :
    ∃ (ι : Type) (_ : Fintype ι) (p : ι → ℕ) (_ : ∀ i, Nat.Prime <| p i) (e : ι → ℕ),
      Nonempty <| G ≃+ ⨁ i : ι, ZMod (p i ^ e i) := by
  cases nonempty_fintype G
  obtain ⟨n, ι, fι, p, hp, e, ⟨f⟩⟩ := equiv_free_prod_directSum_zmod G
  rcases n with - | n
  · have : Unique (Fin Nat.zero →₀ ℤ) :=
      { uniq := by simp only [eq_iff_true_of_subsingleton]; trivial }
    exact ⟨ι, fι, p, hp, e, ⟨f.trans AddEquiv.uniqueProd⟩⟩
  · haveI := @Fintype.prodLeft _ _ _ (Fintype.ofEquiv G f.toEquiv) _
    exact
      (Fintype.ofSurjective (fun f : Fin n.succ →₀ ℤ => f 0) fun a =>
            ⟨Finsupp.single 0 a, Finsupp.single_eq_same⟩).false.elim

/-- **Structure theorem of finite abelian groups** : Any finite abelian group is a direct sum of
some `ZMod (n i)` for some natural numbers `n i > 1`. -/
lemma equiv_directSum_zmod_of_finite' (G : Type*) [AddCommGroup G] [Finite G] :
    ∃ (ι : Type) (_ : Fintype ι) (n : ι → ℕ),
      (∀ i, 1 < n i) ∧ Nonempty (G ≃+ ⨁ i, ZMod (n i)) := by
  classical
  obtain ⟨ι, hι, p, hp, n, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite G
  refine ⟨{i : ι // n i ≠ 0}, inferInstance, fun i ↦ p i ^ n i, ?_,
    ⟨e.trans (directSumNeZeroMulEquiv ι _ _).symm⟩⟩
  rintro ⟨i, hi⟩
  exact one_lt_pow₀ (hp _).one_lt hi

theorem finite_of_fg_torsion [hG' : AddGroup.FG G] (hG : AddMonoid.IsTorsion G) : Finite G :=
  @Module.finite_of_fg_torsion _ _ _ (Module.Finite.iff_addGroup_fg.mpr hG') <|
    AddMonoid.isTorsion_iff_isTorsion_int.mp hG

end AddCommGroup

namespace CommGroup

theorem finite_of_fg_torsion [CommGroup G] [Group.FG G] (hG : Monoid.IsTorsion G) : Finite G :=
  @Finite.of_equiv _ _ (AddCommGroup.finite_of_fg_torsion (Additive G) hG) Multiplicative.ofAdd

/-- The **Structure Theorem For Finite Abelian Groups** in a multiplicative version:
A finite commutative group `G` is isomorphic to a finite product of finite cyclic groups. -/
theorem equiv_prod_multiplicative_zmod_of_finite (G : Type*) [CommGroup G] [Finite G] :
    ∃ (ι : Type) (_ : Fintype ι) (n : ι → ℕ),
       (∀ (i : ι), 1 < n i) ∧ Nonempty (G ≃* ((i : ι) → Multiplicative (ZMod (n i)))) := by
  obtain ⟨ι, inst, n, h₁, h₂⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' (Additive G)
  exact ⟨ι, inst, n, h₁, ⟨MulEquiv.toAdditive.symm <| h₂.some.trans <|
    (DirectSum.addEquivProd _).trans <| MulEquiv.toAdditive'' <| MulEquiv.piMultiplicative _⟩⟩

end CommGroup
