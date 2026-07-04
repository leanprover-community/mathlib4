/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit

/-!
# Lifting properties in cochain complexes

Let `C` be an abelian category. Consider a commutative diagram
in the category `CochainComplex C ℤ`.
```
   t
 A ⟶ X
i|   |p
 v   v
 B ⟶ Y
   b
```
Assume that there exists a degreewise lifting `B.X n ⟶ X.X n` for any `n : ℤ`,
that `Q` is a cokernel of `i`, and `K` is a kernel of `p`. In this situation,
we construct a cocycle in `Cocycle Q K 1` and show that there exists
a lifting `B ⟶ X` if this cocycle is a coboundary.

-/

@[expose] public section

namespace CochainComplex

open CategoryTheory Limits HomComplex

variable {C : Type*} [Category* C] [Abelian C]

namespace Lifting

variable {A B X Y : CochainComplex C ℤ}
  {t : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {b : B ⟶ Y}
  (sq : CommSq t i p b)
  (hsq : ∀ n, (sq.map (HomologicalComplex.eval _ _ n)).LiftStruct)
  {Q : CochainComplex C ℤ} {π : B ⟶ Q} {hπ : i ≫ π = 0}
  (hQ : IsColimit (CokernelCofork.ofπ _ hπ))
  {K : CochainComplex C ℤ} {ι : K ⟶ X} {hι : ι ≫ p = 0}
  (hK : IsLimit (KernelFork.ofι _ hι))

/-- The `0`-cochain from `B` to `X` given by the degreewise liftings. -/
abbrev cochain₀ : Cochain B X 0 := Cochain.ofHoms (fun n ↦ (hsq n).l)

/-- A `1`-cocycle from `B` to `X` obtained as the boundary of
the `0`-cochain `cochain₀ sq hsq` consisting of the degreewise liftings.
This is refined below as a `1`-cocycle from `Q` to `K` where `Q` is a
cokernel of `i : A ⟶ B` and `K` a kernel of `p : X ⟶ Y` (see `cocycle₁`). -/
def cocycle₁' : Cocycle B X 1 :=
  Cocycle.mk (δ 0 1 (cochain₀ sq hsq)) 2 (by simp) (by simp [δ_δ])

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma coe_cocycle₁'_v_comp_eq_zero (n m : ℤ) (hnm : n + 1 = m := by lia) :
    (cocycle₁' sq hsq).1.v n m hnm ≫ p.f m = 0 := by
  have fac_right (k : ℤ) := (hsq k).fac_right
  dsimp at fac_right
  simp [cocycle₁', -HomologicalComplex.Hom.comm,
    ← p.comm, fac_right, reassoc_of% fac_right, b.comm]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma comp_coe_cocyle₁'_v_eq_zero (n m : ℤ) (hnm : n + 1 = m := by lia) :
    i.f n ≫ (cocycle₁' sq hsq).1.v n m hnm = 0 := by
  have fac_left (k : ℤ) := (hsq k).fac_left
  dsimp at fac_left
  simp [cocycle₁', fac_left, reassoc_of% fac_left]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include hQ hK in
lemma exists_hom (n m : ℤ) (hnm : n + 1 = m := by lia) :
    ∃ (φ : Q.X n ⟶ K.X m), π.f n ≫ φ ≫ ι.f m = (cocycle₁' sq hsq).1.v n m hnm := by
  have : Epi π := Cofork.IsColimit.epi hQ
  obtain ⟨l, hl⟩ := CokernelCofork.IsColimit.desc'
    ((CokernelCofork.isColimitMapCoconeEquiv _ _).1
    (isColimitOfPreserves (HomologicalComplex.eval _ _ n) hQ))
    ((cocycle₁' sq hsq).1.v n m hnm) (by simp)
  dsimp [CokernelCofork.map] at l hl
  obtain ⟨l', hl'⟩ := KernelFork.IsLimit.lift' ((KernelFork.isLimitMapConeEquiv _ _).1
    (isLimitOfPreserves (HomologicalComplex.eval _ _ m) hK)) l (by
      simp [← cancel_epi (π.f n), reassoc_of% hl])
  exact ⟨l', by cat_disch⟩

/-- The `1`-cochain from `Q` to `K` which refines `cocycle₁'`. -/
noncomputable def cochain₁ : Cochain Q K 1 :=
  Cochain.mk (fun n m hnm ↦ (exists_hom sq hsq hQ hK n m hnm).choose)

@[reassoc (attr := simp)]
lemma π_f_cochain₁_v_ι_f (n m : ℤ) (hnm : n + 1 = m) :
    π.f n ≫ (cochain₁ sq hsq hQ hK).v n m hnm ≫ ι.f m = (cocycle₁' sq hsq).1.v n m hnm :=
  (exists_hom sq hsq hQ hK n m hnm).choose_spec

/-- A `1`-cocycle from a cokernel `Q` of `i : A ⟶ B` to a kernel `K` of
`p : X ⟶ Y`. If this is a coboundary, then the square in `CochainComplex C ℤ`
has a lifting, see the lemma `hasLift` below. -/
noncomputable def cocycle₁ : Cocycle Q K 1 :=
  Cocycle.mk (cochain₁ sq hsq hQ hK) 2 (by simp) (by
    have : Epi π := Cofork.IsColimit.epi hQ
    have : Mono ι := Fork.IsLimit.mono hK
    ext n _ rfl
    have this := Cochain.congr_v ((cocycle₁' sq hsq).δ_eq_zero 2) n _ rfl
    rw [Cochain.zero_v, δ_v _ _ (by simp) _ _ _ _ (n + 1) _ (by lia) rfl,
      Int.negOnePow_even 2 ⟨1, by simp⟩, one_smul] at this ⊢
    rwa [← cancel_mono (ι.f (n + 2)), ← cancel_epi (π.f n),
      Preadditive.add_comp, Category.assoc, Category.assoc, Preadditive.comp_add,
      HomologicalComplex.Hom.comm_assoc,
      π_f_cochain₁_v_ι_f, zero_comp, comp_zero, ← ι.comm,
      π_f_cochain₁_v_ι_f_assoc])

lemma comp_coe_cocycle₁_comp :
    (Cochain.ofHom π).comp ((cocycle₁ sq hsq hQ hK).1.comp (.ofHom ι)
        (add_zero 1)) (zero_add 1) =
      (cocycle₁' sq hsq).1 := by
  ext n m hnm
  simp [cocycle₁]

set_option backward.defeqAttrib.useBackward true in
/--
Consider a commutative square in the category `CochainComplex C ℤ`
where `C` is an abelian category.
```
   t
 A ⟶ X
i|   |p
 v   v
 B ⟶ Y
   b
```
Assume that there exists a degreewise lifting `B.X n ⟶ X.X n` for any `n : ℤ`,
that `Q` is a cokernel of `i`, and `K` is a kernel of `p`.
If the cocycle `cocycle₁ sq hsq hQ hK : Cocycle Q K 1` is a coboundary,
we show that the square admits a lifting `B ⟶ X`. -/
lemma hasLift (α : Cochain Q K 0) (hα : δ 0 1 α = (cocycle₁ sq hsq hQ hK).1) :
    sq.HasLift where
  exists_lift := by
    replace hα : (Cochain.ofHom π).comp ((δ 0 1 α).comp (.ofHom ι) (add_zero 1)) (zero_add 1) =
        (cocycle₁' sq hsq).1 := by
      rw [← comp_coe_cocycle₁_comp sq hsq hQ hK, hα]
    let l : Cocycle B X 0 :=
      Cocycle.mk (cochain₀ sq hsq -
        (Cochain.ofHom π).comp
          (α.comp (.ofHom ι) (add_zero 0)) (zero_add 0)) 1 (by simp) (by
            ext p _ rfl
            replace hα := Cochain.congr_v hα p _ rfl
            simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.comp_zero_cochain_v,
              δ_zero_cochain_v, Preadditive.sub_comp, Category.assoc, Preadditive.comp_sub,
              HomologicalComplex.Hom.comm_assoc, cocycle₁', Cocycle.mk_coe, Cochain.ofHoms_v,
              HomologicalComplex.eval_obj, HomologicalComplex.eval_map] at hα
            simp [hα])
    exact ⟨{
      l := l.homOf
      fac_left := by
        ext n
        have h₁ : i.f n ≫ π.f n = 0 := by
          simp [← HomologicalComplex.comp_f, hπ]
        have h₂ := (hsq n).fac_left
        dsimp at h₁ h₂
        simp [l, reassoc_of% h₁, h₂]
      fac_right := by
        ext n
        have : ι.f n ≫ p.f n = 0 := by
          simp [← HomologicalComplex.comp_f, hι]
        simpa [l, this] using (hsq n).fac_right }⟩

end Lifting

end CochainComplex
