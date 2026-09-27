/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.Factorizations.Basic

/-!
# Factorization lemma

Let `C` be an abelian category with enough injectives. We show that
any morphism `f : K ⟶ L` between bounded below cochain complexes in `C`
can be factored as `i ≫ p` where `i : K ⟶ L'` is a monomorphism (with
`L'` bounded below) and `p : L' ⟶ L` a quasi-isomorphism that is an epimorphism
with a degreewise injective kernel. (This is part of the factorization axiom CM5
for a model category structure on bounded below cochain complexes (TODO @joelriou).)

-/

@[expose] public section

open CategoryTheory Limits Abelian

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C] [EnoughInjectives C]
  {K L : CochainComplex C ℤ} (f : K ⟶ L)

namespace cm5b

variable (K L) in
/-- Given a cochain complex `K`, this is a cochain complex `I K` with
zero differentials which in degree `n` consists of the injective
object `Injective.under (K.X n)`. -/
@[simps]
noncomputable def I : CochainComplex C ℤ where
  X n := Injective.under (K.X n)
  d _ _ := 0

set_option backward.defeqAttrib.useBackward true in
instance (n : ℤ) : Injective ((I K).X n) := by
  dsimp
  infer_instance

instance (n : ℤ) [K.IsStrictlyGE n] : (I K).IsStrictlyGE n := by
  rw [isStrictlyGE_iff]
  intro i hi
  exact Injective.isZero_under _ (K.isZero_of_isStrictlyGE n i hi)

instance (n : ℤ) [K.IsStrictlyGE (n + 1)] [L.IsStrictlyGE n] :
    (mappingCone (𝟙 (I K)) ⊞ L).IsStrictlyGE n := by
  rw [isStrictlyGE_iff]
  intro i hi
  refine IsZero.of_iso ?_ ((HomologicalComplex.eval C (ComplexShape.up ℤ) i).mapBiprod _ _)
  simp only [HomologicalComplex.eval_obj, biprod_isZero_iff, mappingCone.isZero_X_iff, I_X]
  refine ⟨⟨?_, ?_⟩, L.isZero_of_isStrictlyGE n i hi⟩
  all_goals exact (I K).isZero_of_isStrictlyGE (n + 1) _

variable (K L) in
/-- The second projection `mappingCone (𝟙 (I K)) ⊞ L ⟶ L`. -/
noncomputable abbrev p : mappingCone (𝟙 (I K)) ⊞ L ⟶ L := biprod.snd

set_option backward.isDefEq.respectTransparency false in
/-- A lift of a morphism `f : K ⟶ L` between bounded below cochain complexes
as a monomorphism `K ⟶ mappingCone (𝟙 (I K)) ⊞ L`. -/
noncomputable def i : K ⟶ mappingCone (𝟙 (I K)) ⊞ L :=
  biprod.lift (mappingCone.lift _
    (HomComplex.Cocycle.mk (HomComplex.Cochain.mk (fun p q _ => K.d p q ≫ Injective.ι _)) 2
      (by lia) (by
        ext p q hpq
        simp [HomComplex.δ_v 1 2 (by lia) _ p q hpq (p + 1) (p + 1) (by lia) rfl]))
    (HomComplex.Cochain.ofHoms (fun n => Injective.ι _)) (by cat_disch)) f

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma i_f_comp (n : ℤ) : (i f).f n ≫
    (biprod.fst : mappingCone (𝟙 (I K)) ⊞ L ⟶ _).f n ≫
      (mappingCone.snd (𝟙 (I K))).v n n (add_zero n) = Injective.ι (K.X n) := by
  simp [i]

set_option backward.isDefEq.respectTransparency false in
instance (n : ℤ) : Mono ((i f).f n) := mono_of_mono_fac (i_f_comp f n)

instance : Mono (i f) := HomologicalComplex.mono_of_mono_f (i f) inferInstance

@[reassoc (attr := simp)]
lemma fac : i f ≫ p K L = f := by simp [i]

instance (n : ℤ) : Injective ((mappingCone (𝟙 (I K))).X n) :=
  Injective.of_iso (HomologicalComplex.homotopyCofiber.XIsoBiprod (𝟙 (I K)) n (n + 1) rfl).symm
    inferInstance

variable (K L) in
lemma degreewiseEpiWithInjectiveKernel_p :
    degreewiseEpiWithInjectiveKernel (p K L) := by
  intro n
  rw [epiWithInjectiveKernel_iff]
  refine ⟨(mappingCone (𝟙 (I K))).X n, inferInstance,
    (biprod.inl :_ ⟶ (mappingCone (𝟙 (I K))) ⊞ L).f n, ?_,
    (biprod.fst : (mappingCone (𝟙 (I K))) ⊞ L ⟶ _).f n,
    (biprod.inr :_ ⟶ (mappingCone (𝟙 (I K))) ⊞ L).f n, ?_, ?_, ?_⟩
  all_goals simp [← HomologicalComplex.comp_f, ← HomologicalComplex.add_f_apply]

variable (K L) in
/-- The second projection `p K L : mappingCone (𝟙 (I K)) ⊞ L ⟶ L` is a homotopy equivalence. -/
noncomputable def homotopyEquiv : HomotopyEquiv (mappingCone (𝟙 (I K)) ⊞ L) L where
  hom := p K L
  inv := biprod.inr
  homotopyHomInvId :=
    let h₀ : Homotopy (𝟙 (mappingCone (𝟙 (I K)))) 0 :=
      mappingCone.liftHomotopy _ _ _ (mappingCone.snd _) 0 (by simp) (by simp)
    let h₁ := (h₀.compRight
      (biprod.inl : _ ⟶ mappingCone (𝟙 (I K)) ⊞ L)).compLeft
        (biprod.fst : mappingCone (𝟙 (I K)) ⊞ L ⟶ _)
    let h₂ := Homotopy.add h₁ (Homotopy.refl (biprod.snd ≫ biprod.inr))
    (Homotopy.ofEq (by simp [p])).trans (h₂.symm.trans (Homotopy.ofEq (by simp)))
  homotopyInvHomId := Homotopy.ofEq (by simp)

instance : QuasiIso (p K L) := (homotopyEquiv K L).quasiIso_hom

end cm5b

lemma cm5b (n : ℤ) [K.IsStrictlyGE (n + 1)] [L.IsStrictlyGE n] :
    ∃ (L' : CochainComplex C ℤ) (_hL' : L'.IsStrictlyGE n)
      (i : K ⟶ L') (p : L' ⟶ L) (_hi : Mono i)
      (_hp : degreewiseEpiWithInjectiveKernel p) (_hp' : QuasiIso p),
      i ≫ p = f :=
  ⟨_ , by infer_instance, cm5b.i f, cm5b.p K L, inferInstance,
    cm5b.degreewiseEpiWithInjectiveKernel_p K L, inferInstance, by simp⟩

end CochainComplex
