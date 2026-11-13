/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.Geometry.Convex.ConvexSpace.Barycenter
public import Mathlib.Geometry.Convex.ConvexSpace.ToSSet
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Affine chains and subdivision

If `Y` is a convex space, we define a subdivision endomorphism
`Convexity.ConvexSpace.toSSet.sd` of the chain complex of the
simplicial set `toSSet ℝ Y` (i.e. the chain complex of *affine* singular chains).
We define `sd` by modifying the identity by a null homotopic map given by
a sequence of morphisms (from affine `n`-chains to affine `(n + 1)`-chains)
which we define by induction on `n`.

## References
* [Allen Hatcher, *Algebraic topology*, §2.1][hatcher02]

-/

universe w

@[expose] public section

open CategoryTheory Limits Simplicial

namespace Convexity

variable {C : Type*} [Category C] [Preadditive C] [HasCoproducts.{w} C]
  (Y : Type w) [ConvexSpace ℝ Y] {Z : Type w} [ConvexSpace ℝ Z]
  (φ : ConvexSpace.AffineMap ℝ Y Z) (R : C)

namespace ConvexSpace.toSSet

/-- The data that is part of the homotopy between the identity and
the subdivision endomorphism `sd Y R` of the complex of affine
chains with coefficients in `R` in the convex space `Y`.
(We mostly follow the proof in Proposition 2.21 in Hatcher's book.
We use the same induction formula, but we can set `hSd` to be zero
when `n = 0`, which does not coincide with the definition in the book.) -/
noncomputable def hSd : ∀ (n : ℕ),
    ((toSSet ℝ Y).chainComplex R).X n ⟶
      ((toSSet ℝ Y).chainComplex R).X (n + 1)
  | 0 => 0
  | n + 1 =>
      Sigma.desc (fun s ↦
        (SSet.ιChainComplex _ s - SSet.ιChainComplex _ s ≫
          ((toSSet ℝ Y).chainComplex R).d (n + 1) n ≫ hSd n) ≫
            toSSet.cone s.barycenter _ (n + 1))

@[simp]
lemma hSd_zero : hSd Y R 0 = 0 := rfl

variable {Y} in
@[reassoc (attr := simp)]
lemma ι_hSd_succ {n : ℕ}
    (s : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 2))) Y) :
    SSet.ιChainComplex _ s ≫ hSd Y R (n + 1) =
      (SSet.ιChainComplex (toSSet ℝ Y) s - SSet.ιChainComplex _ s ≫
        ((toSSet ℝ Y).chainComplex R).d (n + 1) n ≫ hSd Y R n) ≫
          toSSet.cone s.barycenter _ (n + 1) :=
  Sigma.ι_comp_desc ..

variable {Y} in
@[reassoc]
lemma hSd_naturality (n : ℕ) :
    (SSet.chainComplexMap φ.toSSetMap R).f n ≫ hSd Z R n =
    hSd Y R n ≫ (SSet.chainComplexMap φ.toSSetMap R).f (n + 1) := by
  induction n with
  | zero => simp
  | succ n hn =>
    ext x
    simp only [ι_hSd_succ_assoc, ← AffineMap.cone_naturality, Preadditive.sub_comp,
      Category.assoc, ← reassoc_of% hn, SSet.ι_chainComplexMap_f_assoc,
      ι_hSd_succ, AffineMap.toSSetMap_app, ← (SSet.chainComplexMap φ.toSSetMap R).comm_assoc]
    dsimp

@[inherit_doc hSd]
noncomputable def hSd' (n m : ℕ) :
    ((toSSet ℝ Y).chainComplex R).X n ⟶ ((toSSet ℝ Y).chainComplex R).X m :=
  if h : n + 1 = m then hSd Y R n ≫ eqToHom (by simp [h]) else 0

@[simp]
lemma hSd'_eq (n : ℕ) : hSd' Y R n (n + 1) = hSd Y R n := by simp [hSd']

lemma hSd'_zero (n m : ℕ) (h : n + 1 ≠ m) : hSd' Y R n m = 0 := by grind [hSd']

/-- The subdivision operator on the complex of affine chains with coefficients
in `R` of a convex space `Y`. By definition, it is homotopic to the identity
(see `homotopyIdSd`). -/
noncomputable def sd :
    (toSSet ℝ Y).chainComplex R ⟶ (toSSet ℝ Y).chainComplex R :=
  𝟙 _ - Homotopy.nullHomotopicMap (hSd' Y R)

/-- The homotopy from the identity to the subdivision endomorphism `sd Y R`
of the complex of affine chains with coefficients in `R` in the convex space `Y`. -/
noncomputable def homotopyIdSd : Homotopy (𝟙 _) (sd Y R) :=
  Homotopy.equivSubZero.symm
    (.trans (.ofEq (by simp [sd])) (.nullHomotopy (hSd' Y R) (hSd'_zero Y R)))

lemma homotopyIdSd_hom_eq_hSd' (n m : ℕ) :
    (homotopyIdSd Y R).hom n m = hSd' Y R n m := by
  simp only [homotopyIdSd, Homotopy.equivSubZero, Equiv.symm_mk, Equiv.coe_fn_mk,
    Homotopy.trans_hom, Homotopy.ofEq_hom, Pi.zero_apply, zero_add]
  apply Homotopy.nullHomotopy_hom

variable {Y} in
@[reassoc]
lemma homotopyIdSd_hom_naturality (n m : ℕ) :
    (SSet.chainComplexMap φ.toSSetMap R).f n ≫ (homotopyIdSd Z R).hom n m =
    (homotopyIdSd Y R).hom n m ≫ (SSet.chainComplexMap φ.toSSetMap R).f m := by
  by_cases hm : n + 1 = m
  · subst hm
    simp only [homotopyIdSd_hom_eq_hSd', hSd'_eq, hSd_naturality]
  · rw [Homotopy.zero _ _ _ (by simpa), Homotopy.zero _ _ _ (by simpa),
      comp_zero, zero_comp]

variable {Y} in
@[reassoc]
lemma ι_toSSetMap_app_homotopyIdSd_hom {n : ℕ} (x : toSSet ℝ Y _⦋n⦌) (m : ℕ) :
    SSet.ιChainComplex _ (φ.toSSetMap.app _ x) ≫ (homotopyIdSd Z R).hom n m =
    SSet.ιChainComplex _ x ≫ (homotopyIdSd Y R).hom n m ≫
      (SSet.chainComplexMap φ.toSSetMap R).f m := by
  simpa using SSet.ιChainComplex _ x ≫= homotopyIdSd_hom_naturality φ R n m

@[simp]
lemma sd_f_0 : (sd Y R).f 0 = 𝟙 _ := by
  simp [sd, Homotopy.nullHomotopicMap_f_of_not_rel_left (ComplexShape.down_mk 1 0 rfl) (by simp)]

lemma sd_f_succ (n : ℕ) :
    (sd Y R).f (n + 1) = 𝟙 _
      - ((toSSet ℝ Y).chainComplex R).d (n + 1) n ≫ hSd Y R n
      - hSd Y R (n + 1) ≫ ((toSSet ℝ Y).chainComplex R).d (n + 2) (n + 1) := by
  simp [sd, Homotopy.nullHomotopicMap_f (ComplexShape.down_mk (n + 2) (n + 1) rfl)
    (ComplexShape.down_mk (n + 1) n rfl), sub_sub]

variable {Y} in
@[reassoc]
lemma ι_sd_f_succ {n : ℕ} (s : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 2))) Y) :
    SSet.ιChainComplex _ s ≫ (sd Y R).f (n + 1) =
      SSet.ιChainComplex _ s ≫ ((toSSet ℝ Y).chainComplex R).d (n + 1) n ≫
        (sd Y R).f n ≫ toSSet.cone (R := ℝ) s.barycenter R n := by
  obtain _ | n := n
  · simp [sd_f_succ, cone_comp_d_eq_sub]
  · simp [sd_f_succ, ι_hSd_succ_assoc, cone_comp_d_eq_sub]

variable {n : ℕ}

open Equiv.Perm in
variable {Y} in
@[reassoc]
lemma ι_sd_f_eq_sum {n : ℕ} (s : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 1))) Y) :
    SSet.ιChainComplex _ s ≫ (sd Y R).f n =
      ∑ (σ : Equiv.Perm (Fin (n + 1))),
        σ.sign • (SSet.ιChainComplex _ (ConvexSpace.AffineMap.sd s σ)) := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [ι_sd_f_succ]
    obtain ⟨s, rfl⟩ := StdSimplex.affineMapMk_surjective s
    simp only [SSet.ιChainComplex_d_assoc, δ_affineMapMk.{w}, Preadditive.sum_comp,
      Linear.smul_comp, reassoc_of% hn, ι_cone, ← decomposeFin'.symm.sum_comp,
      Finset.sum_finset_product .univ .univ (fun _ ↦ .univ) (by simp),
      Equiv.Perm.decomposeFin'_symm, Finset.smul_sum, Units.smul_def,
      smul_smul, sign_decomposeFin'Symm]
    congr 1
    ext i
    congr 1
    ext σ
    congr 2
    ext j
    obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ
    · simp
    · simp only [AffineMap.cone_single_succ, StdSimplex.affineMapMk_single,
        AffineMap.sdVertex_def, Equiv.Perm.coe_inv,
        AffineMap.subBarycenter_mk_comp_of_injective _ _ _ _ Fin.succAbove_right_injective]
      congr 1
      ext k
      obtain ⟨k, rfl⟩ := (decomposeFin'Symm i σ).surjective k
      obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_eq_succ <;> simp

end ConvexSpace.toSSet

end Convexity
