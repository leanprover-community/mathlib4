/-
Copyright (c) 2026 Edward van de Meent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edward van de Meent
-/
module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.Closed
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification


public import Mathlib.CategoryTheory.Topos.Classifier


/-!

# (Elementary) Sheaf Topos

We define a subobject classifier for categories of sheaves of (large enough) types.

adapted from:
https://github.com/edegeltje/CwFTT/blob/591d4505390172ae70e1bc97544d293a35cc0b3f/CwFTT/Classifier/Sheaf.lean

## Main definitions

Let `C` refer to a category with grothendieck topology `J`.

* `Sheaf.classifier J` is the data of a subobject classifier in `Sheaf J (Type (max u v))`.

* `Sheaf.instHasClassifier J` says that there is at least one subobject classifier
  in `Sheaf J (Type (max u v))`

## Main results

* Any category of sheaves of (large enough) types has a subobject classifier.

* As a consequence, (because categories of sheaves are cartesian monoidal and have finite limits
  as well), such categories are Elementary Topoi.

-/

@[expose] public section

universe w v u


namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
open Limits

section

/-- A construction of a terminal object in a sheaf category, given by the constant `PUnit` sheaf. -/
@[simps]
def Sheaf.terminal (J : GrothendieckTopology C) : Sheaf J (Type w) where
  val := (CategoryTheory.Functor.const _).obj PUnit
  cond := Presheaf.isSheaf_of_isTerminal J Types.isTerminalPUnit

/-- The constant `PUnit` sheaf is a terminal object in `Sheaf J (Type w)` -/
def Sheaf.terminal.isTerminal {J : GrothendieckTopology C} : IsTerminal (Sheaf.terminal.{w} J) :=
  .ofUniqueHom (fun F => { val := { app X := (fun _ => .unit) } }) (by intros; ext; rfl)

/-- The sheaf of closed sieves w/r/t `J` -/
@[simps val]
def Sheaf.Ω {J : GrothendieckTopology C} : Sheaf J (Type (max u v)) where
  val := .closedSieves J
  cond := by
    rw [CategoryTheory.isSheaf_iff_isSheaf_of_type]
    exact CategoryTheory.classifier_isSheaf J

/-- The morphism `t : 1 ⟶ Ω` which picks out the maximal sieve -/
@[simps]
def Sheaf.truth {J : GrothendieckTopology C} : Sheaf.terminal J ⟶ Sheaf.Ω where
  val.app X := fun _ => ⟨⊤,_⟩

/--
given a monomorphism of sheaves `η : F ⟶ G`, a point X of the site, map an element `x : G(X)`
to the (closed) sieve on X where `f : Y → X` is in the sieve iff
  ∃ a ∈ F(Y), G(f)(x) = η_Y(a)
-/
@[simps]
def Sheaf.χ {J : GrothendieckTopology C} {F G : Sheaf J (Type (max u v))} (m : F ⟶ G) [Mono m] :
    G ⟶ Sheaf.Ω where
  val.app X := fun x => by
    let S : Sieve X.unop := by
      refine ⟨
        fun Y f => ∃ a, (G.val.map f.op) x = m.val.app (.op Y) a,
          ?_⟩
      intro Y Z f ⟨a,ha⟩ g
      simp only [Opposite.op_unop, op_comp, FunctorToTypes.map_comp_apply]
      rw [ha]
      use F.val.map g.op a
      rw [FunctorToTypes.naturality]
    dsimp
    refine ⟨S ,?_⟩
    · rintro Y f hf
      dsimp [S]
      have foo : Presieve.IsSheafFor F.val (S.pullback f).arrows := by
        exact F.cond.isSheafFor _ hf
      have foo₂ : Presieve.IsSheafFor G.val (S.pullback f).arrows := by
        exact G.cond.isSheafFor _ hf
      refine ⟨?_,?_⟩
      · refine foo.amalgamate (fun Z g hg => hg.choose) ?_
        introv Y₁ h
        simp only [Opposite.op_unop, op_comp, FunctorToTypes.map_comp_apply]
        have : (m.val.app (.op Z)).Injective := by
          rw [← mono_iff_injective]
          apply (NatTrans.mono_iff_mono_app _).mp
          exact (sheafToPresheaf _ _).map_mono m
        apply this
        simp_rw [FunctorToTypes.naturality]
        generalize_proofs h1 h2
        rw [← h1.choose_spec, ← h2.choose_spec]
        simp_rw [← FunctorToTypes.map_comp_apply, ← op_comp,reassoc_of% h]
      · simp only [Sieve.pullback_apply, Opposite.op_unop, op_comp, FunctorToTypes.map_comp_apply]
        generalize_proofs h1 h2 h3
        refine (foo₂.isSeparatedFor).ext ?_
        intro Z f' hf'
        rw [← FunctorToTypes.naturality, foo.valid_glue _ _ hf', ← (h1 _ _ _).choose_spec]
        exact hf'

lemma Sheaf.classifier_isPullback {J : GrothendieckTopology C} {F G : Sheaf J (Type (max u v))}
    (m : F ⟶ G) [Mono m] :
  IsPullback m ((Sheaf.terminal.isTerminal).from F) (Sheaf.χ m) (Sheaf.truth) where
    w := by
      dsimp only [χ, Ω_val, Opposite.op_unop, Functor.closedSieves_obj, id_eq,
        Lean.Elab.WF.paramLet, terminal.isTerminal, terminal_val, truth, Functor.const_obj_obj]
      ext X a
      simp only [Ω_val, Functor.closedSieves_obj, comp_val, FunctorToTypes.comp, terminal_val,
        Subtype.mk.injEq]
      ext Y f
      simp [Sieve.top_apply, ← FunctorToTypes.naturality]
    isLimit' := ⟨PullbackCone.IsLimit.mk _
      (fun s =>
      have (x : Cᵒᵖ) (a : s.pt.val.obj x) ⦃Y : C⦄ (f : Y ⟶ Opposite.unop x) :
          ∃ a_1, G.val.map f.op (s.fst.val.app x a) = m.val.app (Opposite.op Y) a_1 := by
        convert congr((($(s.condition).val.app x) a).val.arrows f)
        simp [χ,truth]
      {
        val.app X := (fun a => (this X a (𝟙 _)).choose)
        val.naturality X := by
          intro Y f
          ext a
          simp only [Opposite.op_unop, types_comp_apply]
          have hi: Function.Injective (m.val.app Y) := by
            rw [← mono_iff_injective]
            apply (NatTrans.mono_iff_mono_app _).mp
            exact (sheafToPresheaf _ _).map_mono m
          apply hi
          rw [← Exists.choose_spec (this _ _ _), FunctorToTypes.naturality,
            ← FunctorToTypes.map_comp_apply]
          simp only [Opposite.op_unop, op_id, Category.comp_id, FunctorToTypes.map_id_apply]
          rw [FunctorToTypes.naturality]
          generalize_proofs h
          rw [← Exists.choose_spec h]
        })
      (by
        simp only [Opposite.op_unop, op_id, FunctorToTypes.map_id_apply, Sheaf.hom_ext_iff,
          comp_val, NatTrans.ext'_iff, funext_iff, NatTrans.comp_app, CategoryTheory.types_ext_iff,
          types_comp_apply]
        intro s X a
        generalize_proofs h
        rw [← h.choose_spec])
      (fun s => by simpa using ((terminal.isTerminal).hom_ext _ _))
      (by
        intro s m' hm1 hm2
        clear hm2
        ext X a
        simp only [Opposite.op_unop, op_id, FunctorToTypes.map_id_apply]
        generalize_proofs h
        have hi: Function.Injective (m.val.app X) := by
          rw [← mono_iff_injective]
          apply (NatTrans.mono_iff_mono_app _).mp
          exact (sheafToPresheaf _ _).map_mono m
        apply hi
        rw [← h.choose_spec,← hm1]
        simp)⟩

lemma Sheaf.χ_unique {J : GrothendieckTopology C} {F G : Sheaf J (Type (max u v))} (m : F ⟶ G)
    [Mono m] (χ' : G ⟶ Sheaf.Ω)
    (hχ' : IsPullback m ((Sheaf.terminal.isTerminal).from F) χ' (Sheaf.truth)) :
    χ' = Sheaf.χ m := by
  ext X a
  simp only [Ω_val, Functor.closedSieves_obj, χ_val_app, Opposite.op_unop, id_eq]
  simp only [Subtype.ext_iff, Sieve.ext_iff]
  intro Y f
  have : IsPullback (m.val.app (.op Y))
      (((Sheaf.terminal.isTerminal (J := J)).from F).val.app (.op Y)) (χ'.val.app (.op Y))
      ((Sheaf.truth (J := J)).val.app (.op Y)) :=
    (hχ').map (sheafToPresheaf J (Type (max u v)) ⋙ (evaluation Cᵒᵖ (Type (max u v))).obj (.op Y))
  simp only [terminal_val, Functor.const_obj_obj, Ω_val, Functor.closedSieves_obj] at this
  have hfst := CategoryTheory.Limits.Types.range_fst_of_isPullback (this)
  simp only [truth, terminal_val, Ω_val, Functor.const_obj_obj, Set.range_const, Set.ext_iff,
    Set.mem_range, Set.mem_preimage, Set.mem_singleton_iff, Subtype.ext_iff] at hfst
  nth_rw 1 [← Category.id_comp f, ← Sieve.pullback_apply, Sieve.id_mem_iff_eq_top]
  change (((Sheaf.Ω).val.map f.op) (χ'.val.app X a)).val = ⊤ ↔ _
  simp_rw [← FunctorToTypes.naturality, ← hfst,eq_comm]

/--
A construction of subobject classifier for sheaf categories. `Ω` is the sheaf of closed sieves,
and `truth` maps for each object `X : C`, an element of `PUnit` to the maximal `Sieve X`.
-/
@[simps! Ω truth Ω₀ χ χ₀]
def Sheaf.classifier (J : GrothendieckTopology C) : Classifier (Sheaf J (Type (max u v))) :=
  .mkOfTerminalΩ₀
    (.terminal J)
    (Sheaf.terminal.isTerminal)
    (Sheaf.Ω)
    (Sheaf.truth)
    (Sheaf.χ)
    (Sheaf.classifier_isPullback)
    (Sheaf.χ_unique)

/-- Sheaf categories have a subobject classifier. -/
instance (J : GrothendieckTopology C) : HasClassifier (Sheaf J (Type (max u v))) where
  exists_classifier := ⟨Sheaf.classifier J⟩

end
end CategoryTheory

end
