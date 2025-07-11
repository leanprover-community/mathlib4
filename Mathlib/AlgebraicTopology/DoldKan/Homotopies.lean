/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.AlgebraicTopology.DoldKan.Notations

/-!

# Construction of homotopies for the Dold-Kan correspondence

(The general strategy of proof of the Dold-Kan correspondence is explained
in `Equivalence.lean`.)

The purpose of the files `Homotopies.lean`, `Faces.lean`, `Projections.lean`
and `PInfty.lean` is to construct an idempotent endomorphism
`PInfty : K[X] ⟶ K[X]` of the alternating face map complex
for each `X : SimplicialObject C` when `C` is a preadditive category.
In the case `C` is abelian, this `PInfty` shall be the projection on the
normalized Moore subcomplex of `K[X]` associated to the decomposition of the
complex `K[X]` as a direct sum of this normalized subcomplex and of the
degenerate subcomplex.

In `PInfty.lean`, this endomorphism `PInfty` shall be obtained by
passing to the limit idempotent endomorphisms `P q` for all `(q : ℕ)`.
These endomorphisms `P q` are defined by induction. The idea is to
start from the identity endomorphism `P 0` of `K[X]` and to ensure by
induction that the `q` higher face maps (except $d_0$) vanish on the
image of `P q`. Then, in a certain degree `n`, the image of `P q` for
a big enough `q` will be contained in the normalized subcomplex. This
construction is done in `Projections.lean`.

It would be easy to define the `P q` degreewise (similarly as it is done
in *Simplicial Homotopy Theory* by Goerrs-Jardine p. 149), but then we would
have to prove that they are compatible with the differential (i.e. they
are chain complex maps), and also that they are homotopic to the identity.
These two verifications are quite technical. In order to reduce the number
of such technical lemmas, the strategy that is followed here is to define
a series of null homotopic maps `Hσ q` (attached to families of maps `hσ`)
and use these in order to construct `P q` : the endomorphisms `P q`
shall basically be obtained by altering the identity endomorphism by adding
null homotopic maps, so that we get for free that they are morphisms
of chain complexes and that they are homotopic to the identity. The most
technical verifications that are needed about the null homotopic maps `Hσ`
are obtained in `Faces.lean`.

In this file `Homotopies.lean`, we define the null homotopic maps
`Hσ q : K[X] ⟶ K[X]`, show that they are natural (see `natTransHσ`) and
compatible the application of additive functors (see `map_Hσ`).

## References
* [Albrecht Dold, *Homology of Symmetric Products and Other Functors of Complexes*][dold1958]
* [Paul G. Goerss, John F. Jardine, *Simplicial Homotopy Theory*][goerss-jardine-2009]

-/


open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Preadditive
  CategoryTheory.SimplicialObject Homotopy Opposite Simplicial DoldKan

noncomputable section

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type*} [Category C] [Preadditive C]
variable {X : SimplicialObject C}

/-- As we are using chain complexes indexed by `ℕ`, we shall need the relation
`c` such `c m n` if and only if `n+1=m`. -/
abbrev c :=
  ComplexShape.down ℕ

/-- Helper when we need some `c.rel i j` (i.e. `ComplexShape.down ℕ`),
e.g. `c_mk n (n+1) rfl` -/
theorem c_mk (i j : ℕ) (h : j + 1 = i) : c.Rel i j :=
  ComplexShape.down_mk i j h

/-- This lemma is meant to be used with `nullHomotopicMap'_f_of_not_rel_left` -/
theorem cs_down_0_not_rel_left (j : ℕ) : ¬c.Rel 0 j := by
  intro hj
  dsimp at hj
  apply Nat.not_succ_le_zero j
  rw [Nat.succ_eq_add_one, hj]

/-- The sequence of maps which gives the null homotopic maps `Hσ` that shall be in
the inductive construction of the projections `P q : K[X] ⟶ K[X]` -/
def hσ (q : ℕ) (n : ℕ) : X _⦋n⦌ ⟶ X _⦋n + 1⦌ :=
  if n < q then 0 else (-1 : ℤ) ^ (n - q) • X.σ ⟨n - q, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩

/-- We can turn `hσ` into a datum that can be passed to `nullHomotopicMap'`. -/
def hσ' (q : ℕ) : ∀ n m, c.Rel m n → (K[X].X n ⟶ K[X].X m) := fun n m hnm =>
  hσ q n ≫ eqToHom (by congr)

theorem hσ'_eq_zero {q n m : ℕ} (hnq : n < q) (hnm : c.Rel m n) :
    (hσ' q n m hnm : X _⦋n⦌ ⟶ X _⦋m⦌) = 0 := by
  simp only [hσ', hσ]
  split_ifs
  exact zero_comp

theorem hσ'_eq {q n a m : ℕ} (ha : n = a + q) (hnm : c.Rel m n) :
    (hσ' q n m hnm : X _⦋n⦌ ⟶ X _⦋m⦌) =
      ((-1 : ℤ) ^ a • X.σ ⟨a, Nat.lt_succ_iff.mpr (Nat.le.intro (Eq.symm ha))⟩) ≫
        eqToHom (by congr) := by
  simp only [hσ', hσ]
  split_ifs
  · omega
  · have h' := tsub_eq_of_eq_add ha
    congr

theorem hσ'_eq' {q n a : ℕ} (ha : n = a + q) :
    (hσ' q n (n + 1) rfl : X _⦋n⦌ ⟶ X _⦋n + 1⦌) =
      (-1 : ℤ) ^ a • X.σ ⟨a, Nat.lt_succ_iff.mpr (Nat.le.intro (Eq.symm ha))⟩ := by
  rw [hσ'_eq ha rfl, eqToHom_refl, comp_id]

/-- The null homotopic map $(hσ q) ∘ d + d ∘ (hσ q)$ -/
def Hσ (q : ℕ) : K[X] ⟶ K[X] :=
  nullHomotopicMap' (hσ' q)

/-- `Hσ` is null homotopic -/
def homotopyHσToZero (q : ℕ) : Homotopy (Hσ q : K[X] ⟶ K[X]) 0 :=
  nullHomotopy' (hσ' q)

/-- In degree `0`, the null homotopic map `Hσ` is zero. -/
theorem Hσ_eq_zero (q : ℕ) : (Hσ q : K[X] ⟶ K[X]).f 0 = 0 := by
  unfold Hσ
  rw [nullHomotopicMap'_f_of_not_rel_left (c_mk 1 0 rfl) cs_down_0_not_rel_left]
  rcases q with (_|q)
  · rw [hσ'_eq (show 0 = 0 + 0 by rfl) (c_mk 1 0 rfl)]
    simp only [pow_zero, Fin.mk_zero, one_zsmul, eqToHom_refl, Category.comp_id]
    -- This `erw` is needed to show `0 + 1 = 1`.
    erw [ChainComplex.of_d]
    rw [AlternatingFaceMapComplex.objD, Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero,
      pow_one, one_smul, neg_smul, one_smul, comp_add, comp_neg, add_neg_eq_zero,
      ← Fin.succ_zero_eq_one, δ_comp_σ_succ, δ_comp_σ_self' X (by rw [Fin.castSucc_zero'])]
  · rw [hσ'_eq_zero (Nat.succ_pos q) (c_mk 1 0 rfl), zero_comp]

/-- The maps `hσ' q n m hnm` are natural on the simplicial object -/
theorem hσ'_naturality (q : ℕ) (n m : ℕ) (hnm : c.Rel m n) {X Y : SimplicialObject C} (f : X ⟶ Y) :
    f.app (op ⦋n⦌) ≫ hσ' q n m hnm = hσ' q n m hnm ≫ f.app (op ⦋m⦌) := by
  have h : n + 1 = m := hnm
  subst h
  simp only [hσ', eqToHom_refl, comp_id]
  unfold hσ
  split_ifs
  · rw [zero_comp, comp_zero]
  · simp

/-- For each q, `Hσ q` is a natural transformation. -/
def natTransHσ (q : ℕ) : alternatingFaceMapComplex C ⟶ alternatingFaceMapComplex C where
  app _ := Hσ q
  naturality _ _ f := by
    unfold Hσ
    rw [nullHomotopicMap'_comp, comp_nullHomotopicMap']
    congr
    ext n m hnm
    simp only [alternatingFaceMapComplex_map_f, hσ'_naturality]

/-- The maps `hσ' q n m hnm` are compatible with the application of additive functors. -/
theorem map_hσ' {D : Type*} [Category D] [Preadditive D] (G : C ⥤ D) [G.Additive]
    (X : SimplicialObject C) (q n m : ℕ) (hnm : c.Rel m n) :
    (hσ' q n m hnm : K[((whiskering _ _).obj G).obj X].X n ⟶ _) =
      G.map (hσ' q n m hnm : K[X].X n ⟶ _) := by
  unfold hσ' hσ
  split_ifs
  · simp only [Functor.map_zero, zero_comp]
  · simp only [eqToHom_map, Functor.map_comp, Functor.map_zsmul]
    rfl

/-- The null homotopic maps `Hσ` are compatible with the application of additive functors. -/
theorem map_Hσ {D : Type*} [Category D] [Preadditive D] (G : C ⥤ D) [G.Additive]
    (X : SimplicialObject C) (q n : ℕ) :
    (Hσ q : K[((whiskering C D).obj G).obj X] ⟶ _).f n = G.map ((Hσ q : K[X] ⟶ _).f n) := by
  unfold Hσ
  have eq := HomologicalComplex.congr_hom (map_nullHomotopicMap' G (@hσ' _ _ _ X q)) n
  simp only [Functor.mapHomologicalComplex_map_f, ← map_hσ'] at eq
  rw [eq]
  let h := (Functor.congr_obj (map_alternatingFaceMapComplex G) X).symm
  congr

end DoldKan

end AlgebraicTopology
