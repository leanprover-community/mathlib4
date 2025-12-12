import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
import Mathlib.CFT.Stuff
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

open scoped Polynomial
open TensorProduct

variable (R S T : Type*) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
variable (n m k : ℕ) (hn : n = m + k)

variable {R n} (p : Polynomial.MonicDegreeEq R n)

namespace Polynomial

local notation "𝓡" => UniversalFactorizationRing m k hn p

local notation "𝓡'" => UniversalCoprimeFactorizationRing m k hn p

open scoped nonZeroDivisors

/-- If a monic polynomial `p : R[X]` factors into a product of coprime monic polynomials `p = f * g`
in the residue field `κ(P)` of some `P : Spec R`,
then there exists `Q : Spec R_univ` in the universal coprime factorization ring lying over `P`,
such that `κ(P) = κ(Q)` and `f` and `g` are the image of the universal factors. -/
@[stacks 00UH]
lemma UniversalCoprimeFactorizationRing.exists_liesOver_residueFieldMap_bijective
    (P : Ideal R) [P.IsPrime]
    (f : MonicDegreeEq P.ResidueField m) (g : MonicDegreeEq P.ResidueField k)
    (H : p.1.map (algebraMap R _) = f.1 * g.1) (Hpq : IsCoprime f.1 g.1) :
    ∃ (Q : Ideal 𝓡') (_ : Q.IsPrime) (_ : Q.LiesOver P),
    Function.Bijective (Ideal.ResidueField.mapₐ P Q (Algebra.ofId _ _) (Ideal.over_def Q P)) ∧
    f.map (Ideal.ResidueField.mapₐ P Q (Algebra.ofId _ _) (Ideal.over_def Q P)).toRingHom =
      (factor₁ m k hn p).map (algebraMap _ _) ∧
    g.map (Ideal.ResidueField.mapₐ P Q (Algebra.ofId _ _) (Ideal.over_def Q P)).toRingHom =
      (factor₂ m k hn p).map (algebraMap _ _) := by
  let φ : 𝓡' →ₐ[R] P.ResidueField :=
    (UniversalCoprimeFactorizationRing.homEquiv _ m k hn p).symm ⟨(f, g), H.symm, Hpq⟩
  let Q := RingHom.ker φ.toRingHom
  have : Q.IsPrime := RingHom.ker_isPrime _
  have : Q.LiesOver P := ⟨by rw [Ideal.under, RingHom.comap_ker, AlgHom.toRingHom_eq_coe,
      φ.comp_algebraMap, Ideal.ker_algebraMap_residueField]⟩
  let φ' : Q.ResidueField →ₐ[R] P.ResidueField := Ideal.ResidueField.liftₐ _ φ le_rfl (by
    simp [SetLike.le_def, IsUnit.mem_submonoid_iff, Q])
  let φi : P.ResidueField →ₐ[R] Q.ResidueField :=
    Ideal.ResidueField.mapₐ _ _ (Algebra.ofId _ _) (Ideal.over_def _ _)
  let e : P.ResidueField ≃ₐ[R] Q.ResidueField :=
    .ofAlgHom φi φ' (AlgHom.ext fun x ↦ φ'.injective <|
      show (φ'.comp φi) (φ' x) = AlgHom.id R _ (φ' x) by congr; ext) (by ext)
  have H : φi.comp φ = (IsScalarTower.toAlgHom _ _ _) :=
    AlgHom.ext fun x ↦ e.eq_symm_apply.mp (by simp [e, φ'])
  refine ⟨Q, ‹_›, ‹_›, e.bijective, ?_, ?_⟩
  · trans ((homEquiv Q.ResidueField m k hn p) (φi.comp φ)).1.1
    · simp [homEquiv_comp_fst, φ, φi]
    · rw [H]
      simp [homEquiv, UniversalFactorizationRing.homEquiv, factor₁,
        MonicDegreeEq.map, Polynomial.map_map]
      rfl
  · trans ((homEquiv Q.ResidueField m k hn p) (φi.comp φ)).1.2
    · simp [homEquiv_comp_snd, φ, φi]
    · rw [H]
      simp [homEquiv, UniversalFactorizationRing.homEquiv, factor₂,
        MonicDegreeEq.map, Polynomial.map_map]
      rfl

open UniversalCoprimeFactorizationRing in
/-- If a monic polynomial `p : R[X]` factors into a product of coprime monic polynomials `p = f * g`
in the residue field `κ(P)` of some `P : Spec R`,
then there exists `Q : Spec R_univ` in the universal coprime factorization ring lying over `P`,
such that `κ(P) = κ(Q)` and `f` and `g` are the image of the universal factors. -/
@[stacks 00UH]
lemma exists_etale_bijective_residueFieldMap_and_map_eq_mul_and_isCoprime.{u}
    {R : Type u} [CommRing R]
    (P : Ideal R) [P.IsPrime] (p : R[X])
    (f g : P.ResidueField[X]) (hp : p.Monic) (hf : f.Monic) (hg : g.Monic)
    (H : p.map (algebraMap R _) = f * g) (Hpq : IsCoprime f g) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (Q : Ideal R') (_ : Q.IsPrime) (_ : Q.LiesOver P) (f' g' : R'[X]),
    Function.Bijective (Ideal.ResidueField.mapₐ P Q (Algebra.ofId _ _) (Ideal.over_def Q P)) ∧
    f'.Monic ∧ g'.Monic ∧ p.map (algebraMap R R') = f' * g' ∧ IsCoprime f' g' ∧
    f.map (Ideal.ResidueField.mapₐ P Q (Algebra.ofId _ _) (Ideal.over_def Q P)).toRingHom =
      f'.map (algebraMap _ _) ∧
    g.map (Ideal.ResidueField.mapₐ P Q (Algebra.ofId _ _) (Ideal.over_def Q P)).toRingHom =
      g'.map (algebraMap _ _) := by
  obtain ⟨Q, _, _, h₁, h₂, h₃⟩ :=
    exists_liesOver_residueFieldMap_bijective f.natDegree g.natDegree
    (by simpa [hf.natDegree_mul hg, hp.natDegree_map] using congr(($H).natDegree)) (.mk p hp rfl)
    P (.mk f hf rfl) (.mk g hg rfl) H Hpq
  exact ⟨_, _, _, inferInstance, Q, ‹_›, ‹_›, (factor₁ ..).1, (factor₂ ..).1, h₁,
    (factor₁ ..).monic, (factor₂ ..).monic, (factor₁_mul_factor₂ ..).symm,
    isCoprime_factor₁_factor₂ .., congr(($h₂).1), congr(($h₃).1)⟩

end Polynomial
