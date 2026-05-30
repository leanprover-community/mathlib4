/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin
-/
module

public import Mathlib.Algebra.Module.PID
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Data.ZMod.QuotientRing

/-!
# Structure of finite(ly generated) abelian groups

* `AddCommGroup.equiv_free_prod_directSum_zmod` : Any finitely generated abelian group is the
  product of a power of `ℤ` and a direct sum of some `ZMod (p i ^ e i)` for some prime powers
  `p i ^ e i`.
* `CommGroup.equiv_free_prod_prod_multiplicative_zmod` is a version for multiplicative groups.
* `AddCommGroup.equiv_directSum_zmod_of_finite` : Any finite abelian group is a direct sum of
  some `ZMod (p i ^ e i)` for some prime powers `p i ^ e i`.
* `CommGroup.equiv_prod_multiplicative_zmod_of_finite` is a version for multiplicative groups.
-/

@[expose] public section

open scoped DirectSum

/-- Drop trivial factors from a direct sum: given families of mutually inverse morphisms
`F : α i →+ β (f i hi)` and `G : β j →+ α (g j hj)` between the nontrivial components,
the direct sums `⨁ i, α i` and `⨁ j, β j` are isomorphic. The hypotheses `hFne` and `hGne`
assert that the morphisms preserve non-zeroness, which is needed to correctly identify
which components of the result are nontrivial. -/
def DirectSum.congr {ι κ : Type*} {α : ι → Type*} {β : κ → Type*}
    [DecidableEq ι] [DecidableEq κ]
    [∀ i, DecidableEq (α i)] [∀ j, DecidableEq (β j)]
    [∀ i, AddCommMonoid (α i)] [∀ j, AddCommMonoid (β j)]
    (f : ∀ i, Nontrivial (α i) → κ) (g : ∀ j, Nontrivial (β j) → ι)
    (F : ∀ i hi, α i →+ β (f i hi)) (G : ∀ j hj, β j →+ α (g j hj))
    (hfg : ∀ i hi hj, g (f i hi) hj = i) (hgf : ∀ j hj hi, f (g j hj) hi = j)
    (hFG : ∀ i hi hj a, hfg i hi hj ▸ G _ hj (F i hi a) = a)
    (hGF : ∀ j hj hi b, hgf j hj hi ▸ F _ hi (G j hj b) = b)
    (hFne : ∀ i hi a, a ≠ 0 → F i hi a ≠ 0)
    (hGne : ∀ j hj b, b ≠ 0 → G j hj b ≠ 0) :
    (⨁ i, α i) ≃+ ⨁ j, β j where
  toFun x := x.sum fun i a ↦ if ha : a = 0 then 0 else DFinsupp.single (f i ⟨a, 0, ha⟩) (F _ _ a)
  invFun y := y.sum fun j b ↦ if hb : b = 0 then 0 else DFinsupp.single (g j ⟨b, 0, hb⟩) (G _ _ b)
  map_add' x₁ x₂ := by
    show (x₁ + x₂).sum (fun i a ↦ if ha : a = 0 then 0 else
          DFinsupp.single (f i ⟨a, 0, ha⟩) (F _ _ a)) =
      x₁.sum (fun i a ↦ if ha : a = 0 then 0 else DFinsupp.single (f i ⟨a, 0, ha⟩) (F _ _ a)) +
      x₂.sum (fun i a ↦ if ha : a = 0 then 0 else DFinsupp.single (f i ⟨a, 0, ha⟩) (F _ _ a))
    refine DFinsupp.sum_add_index (by simp) fun i a₁ a₂ ↦ ?_
    split_ifs
    any_goals simp_all only [zero_add, add_zero, map_add, map_zero, DFinsupp.single_add, DFinsupp.single_zero]
    rw [← DFinsupp.single_add, ← map_add, ‹a₁ + a₂ = 0›, map_zero, DFinsupp.single_zero]
  left_inv x := by
    let Φ : ∀ i, α i → ⨁ j, β j :=
      fun i a ↦ if ha : a = 0 then 0 else DFinsupp.single (f i ⟨a, 0, ha⟩) (F _ _ a)
    let Ψ : ∀ j, β j → ⨁ i, α i :=
      fun j b ↦ if hb : b = 0 then 0 else DFinsupp.single (g j ⟨b, 0, hb⟩) (G _ _ b)
    have Φ0 : ∀ i, Φ i 0 = 0 := fun i ↦ dif_pos rfl
    have Ψ0 : ∀ j, Ψ j 0 = 0 := fun j ↦ dif_pos rfl
    have Φadd : ∀ i (a b : α i), Φ i (a + b) = Φ i a + Φ i b := by
      intro i a b
      by_cases hab : a + b = 0 <;> by_cases ha : a = 0 <;> by_cases hb : b = 0
      · subst ha; subst hb; simp [Φ0]
      · subst ha; rw [zero_add] at hab; exact absurd hab hb
      · subst hb; rw [add_zero] at hab; exact absurd hab ha
      · show (if h : a + b = 0 then 0 else DFinsupp.single (f i ⟨a+b,0,h⟩) (F _ _ (a+b))) =
             (if h : a = 0 then 0 else DFinsupp.single (f i ⟨a,0,h⟩) (F _ _ a)) +
             (if h : b = 0 then 0 else DFinsupp.single (f i ⟨b,0,h⟩) (F _ _ b))
        rw [dif_pos hab, dif_neg ha, dif_neg hb]; symm
        show DFinsupp.single (f i ⟨a, 0, ha⟩) (F i ⟨a, 0, ha⟩ a) +
             DFinsupp.single (f i ⟨a, 0, ha⟩) (F i ⟨a, 0, ha⟩ b) = 0
        rw [← DFinsupp.single_add, ← map_add, hab, map_zero, DFinsupp.single_zero]
      · subst ha; subst hb; simp at hab
      · subst ha; simp [Φ0, zero_add]
      · subst hb; simp [Φ0, add_zero]
      · show (if h : a + b = 0 then 0 else DFinsupp.single (f i ⟨a+b,0,h⟩) (F _ _ (a+b))) =
             (if h : a = 0 then 0 else DFinsupp.single (f i ⟨a,0,h⟩) (F _ _ a)) +
             (if h : b = 0 then 0 else DFinsupp.single (f i ⟨b,0,h⟩) (F _ _ b))
        rw [dif_neg hab, dif_neg ha, dif_neg hb]
        show DFinsupp.single (f i ⟨a+b, 0, hab⟩) (F i ⟨a+b, 0, hab⟩ (a+b)) =
             DFinsupp.single (f i ⟨a+b, 0, hab⟩) (F i ⟨a+b, 0, hab⟩ a) +
             DFinsupp.single (f i ⟨a+b, 0, hab⟩) (F i ⟨a+b, 0, hab⟩ b)
        rw [← DFinsupp.single_add, ← map_add]
    have Ψadd : ∀ j (a b : β j), Ψ j (a + b) = Ψ j a + Ψ j b := by
      intro j a b
      by_cases hab : a + b = 0 <;> by_cases ha : a = 0 <;> by_cases hb : b = 0
      · subst ha; subst hb; simp [Ψ0]
      · subst ha; rw [zero_add] at hab; exact absurd hab hb
      · subst hb; rw [add_zero] at hab; exact absurd hab ha
      · show (if h : a + b = 0 then 0 else DFinsupp.single (g j ⟨a+b,0,h⟩) (G _ _ (a+b))) =
             (if h : a = 0 then 0 else DFinsupp.single (g j ⟨a,0,h⟩) (G _ _ a)) +
             (if h : b = 0 then 0 else DFinsupp.single (g j ⟨b,0,h⟩) (G _ _ b))
        rw [dif_pos hab, dif_neg ha, dif_neg hb]; symm
        show DFinsupp.single (g j ⟨a, 0, ha⟩) (G j ⟨a, 0, ha⟩ a) +
             DFinsupp.single (g j ⟨a, 0, ha⟩) (G j ⟨a, 0, ha⟩ b) = 0
        rw [← DFinsupp.single_add, ← map_add, hab, map_zero, DFinsupp.single_zero]
      · subst ha; subst hb; simp at hab
      · subst ha; simp [Ψ0, zero_add]
      · subst hb; simp [Ψ0, add_zero]
      · show (if h : a + b = 0 then 0 else DFinsupp.single (g j ⟨a+b,0,h⟩) (G _ _ (a+b))) =
             (if h : a = 0 then 0 else DFinsupp.single (g j ⟨a,0,h⟩) (G _ _ a)) +
             (if h : b = 0 then 0 else DFinsupp.single (g j ⟨b,0,h⟩) (G _ _ b))
        rw [dif_neg hab, dif_neg ha, dif_neg hb]
        show DFinsupp.single (g j ⟨a+b, 0, hab⟩) (G j ⟨a+b, 0, hab⟩ (a+b)) =
             DFinsupp.single (g j ⟨a+b, 0, hab⟩) (G j ⟨a+b, 0, hab⟩ a) +
             DFinsupp.single (g j ⟨a+b, 0, hab⟩) (G j ⟨a+b, 0, hab⟩ b)
        rw [← DFinsupp.single_add, ← map_add]
    have φ_add : ∀ (x y : ⨁ i, α i), (x + y).sum Φ = x.sum Φ + y.sum Φ :=
      fun x y ↦ DFinsupp.sum_add_index Φ0 (fun i a b ↦ Φadd i a b)
    have ψ_add : ∀ (y₁ y₂ : ⨁ j, β j), (y₁ + y₂).sum Ψ = y₁.sum Ψ + y₂.sum Ψ :=
      fun y₁ y₂ ↦ DFinsupp.sum_add_index Ψ0 (fun j a b ↦ Ψadd j a b)
    show (x.sum Φ).sum Ψ = x
    induction x using DirectSum.induction_on with
    | zero => simp [DFinsupp.sum]
    | of i a =>
      by_cases ha : a = 0
      · subst ha; simp [map_zero, DFinsupp.sum]
      · have hi : Nontrivial (α i) := ⟨a, 0, ha⟩
        have hφ : (DirectSum.of α i a).sum Φ = DFinsupp.single (f i hi) (F i hi a) := by
          rw [show DirectSum.of α i a = DFinsupp.single i a from rfl,
              DFinsupp.sum_single_index (Φ0 i)]
          show (if ha' : a = 0 then 0 else DFinsupp.single (f i ⟨a, 0, ha'⟩) (F _ _ a)) =
               DFinsupp.single (f i hi) (F i hi a)
          rw [dif_neg ha]
        have hFa := hFne i hi a ha
        have hj : Nontrivial (β (f i hi)) := ⟨F i hi a, 0, hFa⟩
        rw [hφ, DFinsupp.sum_single_index (Ψ0 _)]
        have hΨ : Ψ (f i hi) (F i hi a) =
            DFinsupp.single (g (f i hi) hj) (G (f i hi) hj (F i hi a)) := by
          show (if hb : F i hi a = 0 then 0 else
                  DFinsupp.single (g (f i hi) ⟨F i hi a, 0, hb⟩) (G _ _ (F i hi a))) =
               DFinsupp.single (g (f i hi) hj) (G (f i hi) hj (F i hi a))
          rw [dif_neg hFa]
        rw [hΨ, show DirectSum.of α i a = DFinsupp.single i a from rfl]
        ext k; simp only [DFinsupp.single_apply]
        rcases Decidable.em (i = k) with rfl | hik
        · rw [dif_pos (hfg i hi hj), dif_pos rfl]; exact hFG i hi hj a
        · rw [dif_neg hik, dif_neg (fun h ↦ hik ((hfg i hi hj).symm.trans h))]
    | add x y hx hy => rw [φ_add, ψ_add, hx, hy]
  right_inv y := by
    let Φ : ∀ i, α i → ⨁ j, β j :=
      fun i a ↦ if ha : a = 0 then 0 else DFinsupp.single (f i ⟨a, 0, ha⟩) (F _ _ a)
    let Ψ : ∀ j, β j → ⨁ i, α i :=
      fun j b ↦ if hb : b = 0 then 0 else DFinsupp.single (g j ⟨b, 0, hb⟩) (G _ _ b)
    have Φ0 : ∀ i, Φ i 0 = 0 := fun i ↦ dif_pos rfl
    have Ψ0 : ∀ j, Ψ j 0 = 0 := fun j ↦ dif_pos rfl
    have Ψadd : ∀ j (a b : β j), Ψ j (a + b) = Ψ j a + Ψ j b := by
      intro j a b
      by_cases hab : a + b = 0 <;> by_cases ha : a = 0 <;> by_cases hb : b = 0
      · subst ha; subst hb; simp [Ψ0]
      · subst ha; rw [zero_add] at hab; exact absurd hab hb
      · subst hb; rw [add_zero] at hab; exact absurd hab ha
      · show (if h : a + b = 0 then 0 else DFinsupp.single (g j ⟨a+b,0,h⟩) (G _ _ (a+b))) =
             (if h : a = 0 then 0 else DFinsupp.single (g j ⟨a,0,h⟩) (G _ _ a)) +
             (if h : b = 0 then 0 else DFinsupp.single (g j ⟨b,0,h⟩) (G _ _ b))
        rw [dif_pos hab, dif_neg ha, dif_neg hb]; symm
        show DFinsupp.single (g j ⟨a, 0, ha⟩) (G j ⟨a, 0, ha⟩ a) +
             DFinsupp.single (g j ⟨a, 0, ha⟩) (G j ⟨a, 0, ha⟩ b) = 0
        rw [← DFinsupp.single_add, ← map_add, hab, map_zero, DFinsupp.single_zero]
      · subst ha; subst hb; simp at hab
      · subst ha; simp [Ψ0, zero_add]
      · subst hb; simp [Ψ0, add_zero]
      · show (if h : a + b = 0 then 0 else DFinsupp.single (g j ⟨a+b,0,h⟩) (G _ _ (a+b))) =
             (if h : a = 0 then 0 else DFinsupp.single (g j ⟨a,0,h⟩) (G _ _ a)) +
             (if h : b = 0 then 0 else DFinsupp.single (g j ⟨b,0,h⟩) (G _ _ b))
        rw [dif_neg hab, dif_neg ha, dif_neg hb]
        show DFinsupp.single (g j ⟨a+b, 0, hab⟩) (G j ⟨a+b, 0, hab⟩ (a+b)) =
             DFinsupp.single (g j ⟨a+b, 0, hab⟩) (G j ⟨a+b, 0, hab⟩ a) +
             DFinsupp.single (g j ⟨a+b, 0, hab⟩) (G j ⟨a+b, 0, hab⟩ b)
        rw [← DFinsupp.single_add, ← map_add]
    have Φadd : ∀ i (a b : α i), Φ i (a + b) = Φ i a + Φ i b := by
      intro i a b
      by_cases hab : a + b = 0 <;> by_cases ha : a = 0 <;> by_cases hb : b = 0
      · subst ha; subst hb; simp [Φ0]
      · subst ha; rw [zero_add] at hab; exact absurd hab hb
      · subst hb; rw [add_zero] at hab; exact absurd hab ha
      · show (if h : a + b = 0 then 0 else DFinsupp.single (f i ⟨a+b,0,h⟩) (F _ _ (a+b))) =
             (if h : a = 0 then 0 else DFinsupp.single (f i ⟨a,0,h⟩) (F _ _ a)) +
             (if h : b = 0 then 0 else DFinsupp.single (f i ⟨b,0,h⟩) (F _ _ b))
        rw [dif_pos hab, dif_neg ha, dif_neg hb]; symm
        show DFinsupp.single (f i ⟨a, 0, ha⟩) (F i ⟨a, 0, ha⟩ a) +
             DFinsupp.single (f i ⟨a, 0, ha⟩) (F i ⟨a, 0, ha⟩ b) = 0
        rw [← DFinsupp.single_add, ← map_add, hab, map_zero, DFinsupp.single_zero]
      · subst ha; subst hb; simp at hab
      · subst ha; simp [Φ0, zero_add]
      · subst hb; simp [Φ0, add_zero]
      · show (if h : a + b = 0 then 0 else DFinsupp.single (f i ⟨a+b,0,h⟩) (F _ _ (a+b))) =
             (if h : a = 0 then 0 else DFinsupp.single (f i ⟨a,0,h⟩) (F _ _ a)) +
             (if h : b = 0 then 0 else DFinsupp.single (f i ⟨b,0,h⟩) (F _ _ b))
        rw [dif_neg hab, dif_neg ha, dif_neg hb]
        show DFinsupp.single (f i ⟨a+b, 0, hab⟩) (F i ⟨a+b, 0, hab⟩ (a+b)) =
             DFinsupp.single (f i ⟨a+b, 0, hab⟩) (F i ⟨a+b, 0, hab⟩ a) +
             DFinsupp.single (f i ⟨a+b, 0, hab⟩) (F i ⟨a+b, 0, hab⟩ b)
        rw [← DFinsupp.single_add, ← map_add]
    have ψ_add : ∀ (y₁ y₂ : ⨁ j, β j), (y₁ + y₂).sum Ψ = y₁.sum Ψ + y₂.sum Ψ :=
      fun y₁ y₂ ↦ DFinsupp.sum_add_index Ψ0 (fun j a b ↦ Ψadd j a b)
    have φ_add : ∀ (x₁ x₂ : ⨁ i, α i), (x₁ + x₂).sum Φ = x₁.sum Φ + x₂.sum Φ :=
      fun x₁ x₂ ↦ DFinsupp.sum_add_index Φ0 (fun i a b ↦ Φadd i a b)
    show (y.sum Ψ).sum Φ = y
    induction y using DirectSum.induction_on with
    | zero => simp [DFinsupp.sum]
    | of j b =>
      by_cases hb : b = 0
      · subst hb; simp [map_zero, DFinsupp.sum]
      · have hj : Nontrivial (β j) := ⟨b, 0, hb⟩
        have hψ : (DirectSum.of β j b).sum Ψ = DFinsupp.single (g j hj) (G j hj b) := by
          rw [show DirectSum.of β j b = DFinsupp.single j b from rfl,
              DFinsupp.sum_single_index (Ψ0 j)]
          show (if hb' : b = 0 then 0 else DFinsupp.single (g j ⟨b, 0, hb'⟩) (G _ _ b)) =
               DFinsupp.single (g j hj) (G j hj b)
          rw [dif_neg hb]
        have hGb := hGne j hj b hb
        have hi : Nontrivial (α (g j hj)) := ⟨G j hj b, 0, hGb⟩
        rw [hψ, DFinsupp.sum_single_index (Φ0 _)]
        have hΦ : Φ (g j hj) (G j hj b) =
            DFinsupp.single (f (g j hj) hi) (F (g j hj) hi (G j hj b)) := by
          show (if ha : G j hj b = 0 then 0 else
                  DFinsupp.single (f (g j hj) ⟨G j hj b, 0, ha⟩) (F _ _ (G j hj b))) =
               DFinsupp.single (f (g j hj) hi) (F (g j hj) hi (G j hj b))
          rw [dif_neg hGb]
        rw [hΦ, show DirectSum.of β j b = DFinsupp.single j b from rfl]
        ext k; simp only [DFinsupp.single_apply]
        rcases Decidable.em (j = k) with rfl | hjk
        · rw [dif_pos (hgf j hj hi), dif_pos rfl]; exact hGF j hj hi b
        · rw [dif_neg hjk, dif_neg (fun h ↦ hjk ((hgf j hj hi).symm.trans h))]
    | add y₁ y₂ hy₁ hy₂ => rw [ψ_add, φ_add, hy₁, hy₂]

private def directSumNeZeroMulEquiv (ι : Type) [DecidableEq ι] (p : ι → ℕ) (n : ι → ℕ) :
    (⨁ i : {i // n i ≠ 0}, ZMod (p i ^ n i)) ≃+ ⨁ i, ZMod (p i ^ n i) :=
  DirectSum.congr
    (fun i _ ↦ i)
    (fun j hj ↦ ⟨j, fun h ↦ by simp [h, pow_zero, ZMod.nontrivial_iff] at hj⟩)
    (fun i _ ↦ AddMonoidHom.id _)
    (fun j _ ↦ AddMonoidHom.id _)
    (fun i hi hj ↦ rfl)
    (fun j hj hi ↦ rfl)
    (fun i hi hj a ↦ rfl)
    (fun j hj hi a ↦ rfl)
    (fun i hi a ha ↦ ha)
    (fun j hj b hb ↦ hb)

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
      { uniq := by subsingleton }
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
    (DirectSum.addEquivProd _).trans (MulEquiv.piMultiplicative _).toAdditiveRight⟩⟩

/-- The **Structure theorem of finitely generated abelian groups** in a multiplicative version :
    Any finitely generated abelian group is the product of a power of `ℤ`
    and a direct product of some `ZMod (p i ^ e i)` for some prime powers `p i ^ e i`. -/
theorem equiv_free_prod_prod_multiplicative_zmod (G : Type*) [CommGroup G] [hG : Group.FG G] :
    ∃ (ι j : Type) (_ : Fintype ι) (_ : Fintype j) (p : ι → ℕ)
    (_ : ∀ i, Nat.Prime <| p i) (e : ι → ℕ),
      Nonempty <| G ≃* (j → Multiplicative ℤ) × ((i : ι) → Multiplicative (ZMod (p i ^ e i))) := by
  obtain ⟨n, ι, inst, x, p, e, equiv⟩ := AddCommGroup.equiv_free_prod_directSum_zmod (Additive G)
  exact ⟨ι, Fin n, inst, inferInstance, x, p, e, ⟨MulEquiv.toAdditive.symm <| equiv.some.trans <|
    ((Finsupp.addEquivFunOnFinite.trans <| ((AddEquiv.piAdditive _).trans <|
        (AddEquiv.additiveMultiplicative ℤ).arrowCongr (Equiv.refl _)).symm).prodCongr
          (DirectSum.addEquivProd _ )).trans <| (AddEquiv.prodAdditive _ _).symm⟩⟩

end CommGroup

namespace Subgroup

@[to_additive]
lemma finiteIndex_range_powMonoidHom_of_fg (A : Type*) [CommGroup A] [Group.FG A] {n : ℕ}
    (hn : n ≠ 0) :
    (powMonoidHom (α := A) n).range.FiniteIndex :=
  finiteIndex_iff_finite_quotient.mpr <| CommGroup.finite_of_fg_torsion _ <|
    CommGroup.isTorsion_quotient_range_powMonoidHom A hn

@[to_additive]
lemma isFiniteRelIndex_map_powMonoidHom_of_fg {A : Type*} [CommGroup A] {B : Subgroup A}
    (hB : B.FG) {n : ℕ} (hn : n ≠ 0) :
    B.map (powMonoidHom (α := A) n) |>.IsFiniteRelIndex B := by
  rw [isFiniteRelIndex_iff_finiteIndex]
  have : (map (powMonoidHom (α := A) n) B).subgroupOf B = (powMonoidHom (α := B) n).range := by
    ext1
    simp [mem_subgroupOf, Subtype.ext_iff]
  rw [this]
  have := (Group.fg_iff_subgroup_fg B).mpr hB
  exact finiteIndex_range_powMonoidHom_of_fg B hn

end Subgroup

namespace Submodule

variable {R K M : Type*} [CommRing R] [CommRing K] [Algebra R K] [Module.Finite ℤ R]
  [AddCommGroup M] [Module R M]

lemma fg_toAddSubgroup {A : Submodule R M} (hfg : A.FG) : A.toAddSubgroup.FG := by
  rw [← AddSubgroup.toIntSubmodule_toAddSubgroup A.toAddSubgroup, ← fg_iff_addSubgroup_fg]
  exact FG.restrictScalars hfg

open AddSubgroup in
/-- If `A` and `B` are two `R`-submodules of the `R`-algebra `M`, where `R` is finitely generated
as a `ℤ`-module, `A` is finitely generated, and `B` contains `n • A`, then `B` has finite
relative index in `A`. -/
lemma isFiniteRelIndex_of_map_linearMapMulLeft_le {A B : Submodule R K} {n : ℕ} (hn : n ≠ 0)
    (hfg : A.FG) (h : A.map (LinearMap.mulLeft R (n : K)) ≤ B) :
    B.toAddSubgroup.IsFiniteRelIndex A.toAddSubgroup := by
  have := fg_toAddSubgroup hfg
  have := isFiniteRelIndex_map_nsmulAddMonoidHom_of_fg this hn
  refine isFiniteRelIndex_of_le_left (H := A.toAddSubgroup.map (nsmulAddMonoidHom n))
    A.toAddSubgroup ?_
  rw [SetLike.le_def] at h ⊢
  simpa using h

end Submodule
