/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Homology.Factorizations.CM5a
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.ModelCategory.Lifting
public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# The model category structure on bounded below complexes

Let `C` be an abelian category with enough injectives. In this file,
we define a model category structure on the category `CochainComplex.Plus C`
of bounded below cochain complexes in `C`.
The cofibrations are monomorphisms, the weak equivalences are
quasi-isomorphisms and the fibrations are those morphisms
that are degreewise epimorphisms with an injective kernel.
The `ModelCategory` instance is scoped in the namespace
`CochainComplex.Plus.modelCategoryQuillen`.

## References
* [Daniel G. Quillen, Homotopical algebra, §I.1, Example B][Quillen1967]

-/

@[expose] public section

open CategoryTheory HomotopicalAlgebra Limits

namespace CochainComplex.Plus.modelCategoryQuillen

variable {C : Type*} [Category C] [Abelian C]

/-- The weak equivalences in the category `CochainComplex.Plus C` of bounded
below cochain complexes are quasi-isomorphisms. -/
scoped instance : CategoryWithWeakEquivalences (CochainComplex.Plus C) where
  weakEquivalences := quasiIso C

/-- The cofibrations in the category `CochainComplex.Plus C` of bounded
below cochain complexes are monomorphisms. -/
scoped instance : CategoryWithCofibrations (CochainComplex.Plus C) where
  cofibrations := .monomorphisms _

/-- The fibrations in the category `CochainComplex.Plus C` of bounded
below cochain complexes are the morphisms that are degreewise epi with
an injective kernel. -/
scoped instance : CategoryWithFibrations (CochainComplex.Plus C) where
  fibrations := degreewiseEpiWithInjectiveKernel.inverseImage (ι C)

instance : (weakEquivalences (Plus C)).HasTwoOutOfThreeProperty :=
  inferInstanceAs (quasiIso C).HasTwoOutOfThreeProperty

instance : (weakEquivalences (Plus C)).IsStableUnderRetracts :=
  inferInstanceAs (quasiIso C).IsStableUnderRetracts

instance : (cofibrations (Plus C)).IsStableUnderRetracts :=
  inferInstanceAs (MorphismProperty.monomorphisms _).IsStableUnderRetracts

instance : (fibrations (Plus C)).IsStableUnderRetracts :=
  inferInstanceAs (degreewiseEpiWithInjectiveKernel.inverseImage (ι C)).IsStableUnderRetracts

lemma cofibration_iff {X Y : Plus C} (f : X ⟶ Y) :
    Cofibration f ↔ Mono f :=
  HomotopicalAlgebra.cofibration_iff _

lemma fibration_iff {X Y : Plus C} (f : X ⟶ Y) :
    Fibration f ↔ degreewiseEpiWithInjectiveKernel f.hom :=
  HomotopicalAlgebra.fibration_iff _

lemma isFibrant_iff (X : Plus C) :
    IsFibrant X ↔ ∀ (n : ℤ), Injective (X.obj.X n) := by
  rw [HomotopicalAlgebra.isFibrant_iff, fibration_iff,
    degreewiseEpiWithInjectiveKernel_iff_of_isZero]
  exact Functor.map_isZero (Plus.ι C) (IsZero.of_mono_zero _ X)

lemma weakEquivalence_iff {X Y : Plus C} (f : X ⟶ Y) :
    WeakEquivalence f ↔ QuasiIso f.hom :=
  HomotopicalAlgebra.weakEquivalence_iff _

instance {A B : CochainComplex.Plus C} (i : A ⟶ B) [Cofibration i] :
    Mono i := by
  rwa [← cofibration_iff]

open HomComplex in
/-- Let `sq` be a commutative square in the category of bounded below cochain complexes
in an abelian category. We assume that the left morphism `i` is a monomorphism,
and `p` an epimorphism with a degreewise injective kernel. Then, there exists
a lifting for `sq` if `i` or `p` is a quasi-isomorphism. -/
lemma lifting {A B X Y : CochainComplex.Plus C} (i : A ⟶ B) (p : X ⟶ Y)
    [Mono i] [Fibration p] (hip : WeakEquivalence i ∨ WeakEquivalence p) :
    HasLiftingProperty i p where
  sq_hasLift {t b} sq := by
    /- The proof is similar in both cases (whether `i` or `p` is a quasi-isomorphism).
    We first transform the variables so as to get a commutative square in `CochainComplex C ℤ`
    instead of the full subcategory `CochainComplex.Plus C`. -/
    obtain ⟨A, hA⟩ := A
    obtain ⟨B, hB⟩ := B
    obtain ⟨X, hX⟩ := X
    obtain ⟨Y, hY⟩ := Y
    have := (mono_iff i).1 inferInstance
    have hp : degreewiseEpiWithInjectiveKernel p.hom :=
      (fibration_iff p).1 inferInstance
    obtain ⟨i, rfl⟩ := ObjectProperty.homMk_surjective i
    obtain ⟨p, rfl⟩ := ObjectProperty.homMk_surjective p
    obtain ⟨t, rfl⟩ := ObjectProperty.homMk_surjective t
    obtain ⟨b, rfl⟩ := ObjectProperty.homMk_surjective b
    dsimp at i p t b hp
    have : Mono i := by assumption
    have hip : QuasiIso i ∨ QuasiIso p := by
      simpa only [weakEquivalence_iff] using hip
    replace sq : CommSq t i p b := sq.map (ObjectProperty.ι _)
    suffices sq.HasLift from ⟨⟨{ l := ObjectProperty.homMk sq.lift }⟩⟩
    have sq' (n : ℤ) : CommSq (t.f n) (i.f n) (p.f n) (b.f n) :=
      (sq.map (HomologicalComplex.eval _ _ n))
    /- The commutative square in `C` obtained by evaluating in a degree `n`
    admits a lifting because `i.f n` is a monomorphism and `p.f n` is
    an epimorphism with injective kernel. -/
    have (n : ℤ) : (sq' n).HasLift := by
      have := (hp n).hasLiftingProperty (i.f n)
      infer_instance
    /- In order to obtain a lifting in the original square, the obstruction
    lies in a cocycle `β : Cocycle (cokernel i) (kernel p) 1`. Thanks to the
    lemma `CochainComplex.Lifting.hasLift`, it suffices to show that `β`
    is a coboundary. -/
    let β : Cocycle (cokernel i) (kernel p) 1 :=
      Lifting.cocycle₁ sq (fun n ↦ { l := (sq' n).lift })
        (cokernelIsCokernel i) (kernelIsKernel p) (hπ := by simp) (hι := by simp)
    have (n : ℤ) : Injective ((kernel p).X n) :=
      Injective.of_iso
        (asIso (kernelComparison p (HomologicalComplex.eval _ _ n))).symm (hp n).2
    have : (kernel p).IsKInjective := by
      obtain ⟨d, hd⟩ := hX
      have : (kernel p).IsStrictlyGE d := by
        rw [isStrictlyGE_iff]
        intro i hi
        rw [IsZero.iff_id_eq_zero, ← cancel_mono ((kernel.ι p).f i)]
        apply (X.isZero_of_isStrictlyGE d i).eq_of_tgt
      exact isKInjective_of_injective _ d
    /- The cocycle `β` is a coboundary when `i` or `p` is a quasi-isomorphism. -/
    obtain ⟨α, hα⟩ : ∃ (α : Cochain (cokernel i) (kernel p) 0), δ 0 1 α = β.1 := by
      cases hip
      · refine IsKInjective.eq_δ_of_cocycle β ?_ 0 (by simp)
        have : (ShortComplex.mk _ _ (cokernel.condition i)).ShortExact :=
          { exact := ShortComplex.exact_cokernel i }
        exact this.acyclic_X₃ (by dsimp; infer_instance)
      · refine IsKInjective.eq_δ_of_cocycle' β ?_ 0 (by simp)
        have := hp.epi
        have : (ShortComplex.mk _ _ (kernel.condition p)).ShortExact :=
          { exact := ShortComplex.exact_kernel p }
        exact this.acyclic_X₁ (by dsimp; infer_instance)
    exact Lifting.hasLift sq _ (cokernelIsCokernel _) (kernelIsKernel _) α hα

instance {A B X Y : CochainComplex.Plus C} (i : A ⟶ B) (p : X ⟶ Y)
    [Mono i] [WeakEquivalence i] [Fibration p] :
    HasLiftingProperty i p :=
  lifting _ _ (Or.inl inferInstance)

instance {A B X Y : CochainComplex.Plus C} (i : A ⟶ B) (p : X ⟶ Y)
    [Mono i] [Fibration p] [WeakEquivalence p] :
    HasLiftingProperty i p :=
  lifting _ _ (Or.inr inferInstance)

variable [EnoughInjectives C]

instance : (trivialCofibrations (Plus C)).HasFactorization (fibrations (Plus C)) where
  nonempty_mapFactorizationData := by
    rintro ⟨K, n, hn⟩ ⟨L, m, hm⟩ f
    obtain ⟨(f : K ⟶ L), rfl⟩ := ObjectProperty.homMk_surjective f
    obtain ⟨d, _, _⟩ : ∃ (d : ℤ), K.IsStrictlyGE (d + 1) ∧ L.IsStrictlyGE d :=
      ⟨min (n - 1) m, K.isStrictlyGE_of_ge _ n (by grind),
        L.isStrictlyGE_of_ge _ m (by simp)⟩
    obtain ⟨K', _, i, p, _, _, hp, fac⟩ := cm5a f d
    exact ⟨{
      Z := ⟨K', d, inferInstance⟩
      i := ObjectProperty.homMk i
      p := ObjectProperty.homMk p
      hi :=
        ⟨by rwa [← HomotopicalAlgebra.cofibration_iff, cofibration_iff, Plus.mono_iff],
          by assumption⟩
      hp := hp }⟩

instance : (cofibrations (Plus C)).HasFactorization (trivialFibrations (Plus C)) where
  nonempty_mapFactorizationData := by
    rintro ⟨K, n, hn⟩ ⟨L, m, hm⟩ f
    obtain ⟨(f : K ⟶ L), rfl⟩ := ObjectProperty.homMk_surjective f
    obtain ⟨d, _, _⟩ : ∃ (d : ℤ), K.IsStrictlyGE (d + 1) ∧ L.IsStrictlyGE d :=
      ⟨min (n - 1) m, K.isStrictlyGE_of_ge _ n (by grind),
        L.isStrictlyGE_of_ge _ m (by simp)⟩
    obtain ⟨K', _, i, p, _, hp, _, fac⟩ := CochainComplex.cm5b f d
    exact ⟨{
      Z := ⟨K', d, inferInstance⟩
      i := ObjectProperty.homMk i
      p := ObjectProperty.homMk p
      hi := by rwa [← HomotopicalAlgebra.cofibration_iff, cofibration_iff, Plus.mono_iff]
      hp := ⟨hp, by assumption⟩ }⟩

/-- The Quillen model category structure on the category `CochainComplex.Plus C`
of bounded below cochain complexes in an abelian category `C` with enough injectives. -/
scoped instance : ModelCategory (CochainComplex.Plus C) where

end CochainComplex.Plus.modelCategoryQuillen
