/-
Copyright (c) 2025 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import Mathlib.CategoryTheory.Adjunction.Triple
import Mathlib.CategoryTheory.Sites.GlobalSections

/-!
# Local sites
A site (C,J) is called local if it has a terminal object whose only covering sieve is trivial -
this makes it possible to define codiscrete sheaves on it, giving its sheaf topos the structure
of a local topos. This makes them an important stepping stone to cohesive sites.

See https://ncatlab.org/nlab/show/local+site.

## Main definitions / results
* `LocalSite J`: typeclass stating that (C,J) is a local site.
* `Sheaf.codisc`: the codiscrete functor `Type w ⥤ Sheaf J (Type max v w)` defined on any
  local site.
* `Sheaf.ΓCodiscAdj`: the adjunction between the global sections functor `Γ` and `Sheaf.codisc`.
* `Sheaf.fullyFaithfulCodisc`: `Sheaf.codisc` is fully faithful.
* `fullyFaithfulConstantSheaf`: on local sites, the constant sheaf functor is fully faithful.
All together this shows that for local sites `Sheaf J (Type max u v w)` forms a local topos, but
since we don't yet have local topoi this can't be stated yet.
-/

universe u v w

open CategoryTheory Limits Sheaf Opposite GrothendieckTopology

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- A local site is a site that has a terminal object with only a single covering sieve. -/
class LocalSite extends HasTerminal C where
  /-- The only covering sieve of the terminal object is the trivial sieve. -/
  eq_top_of_mem : ∀ S ∈ J (⊤_ C), S = ⊤

/-- On a local site, every covering sieve contains every morphism from the terminal object. -/
lemma LocalSite.from_terminal_mem_of_mem [LocalSite J] {X : C} (f : ⊤_ C ⟶ X) {S : Sieve X}
    (hS : S ∈ J X) : S.arrows f :=
  (S.mem_iff_pullback_eq_top f).2 <| LocalSite.eq_top_of_mem _ <| J.pullback_stable f hS

/-- Every category with a terminal object becomes a local site with the trivial topology. -/
instance {C : Type u} [Category.{v} C] [HasTerminal C] : LocalSite (trivial C) where
  eq_top_of_mem _ := trivial_covering.1

/-- The functor that sends any set `A` to the functor `Cᵒᵖ → Type _` that sends any `X : C`
to the set of all functions `A → (⊤_ C ⟶ X)`. This can be defined on any site with a terminal
object, but has values in sheaves in the case of local sites. -/
noncomputable def Presheaf.codisc {C : Type u} [Category.{v} C] [HasTerminal C] :
    Type w ⥤ (Cᵒᵖ ⥤ Type max v w) :=
  uliftFunctor ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj
    (coyoneda.obj (op (⊤_ C)) ⋙ uliftFunctor).op

/-- On local sites, `Presheaf.codisc` actually takes values in sheaves. -/
lemma Presheaf.codisc_isSheaf [LocalSite J] (X : Type w) : IsSheaf J (codisc.obj X) := by
  refine (isSheaf_iff_isSheaf_of_type J _).2 fun Y S hS f hf ↦ ?_
  refine ⟨fun g ↦ f g.down (LocalSite.from_terminal_mem_of_mem J g.down hS) ⟨𝟙 _⟩, ?_, ?_⟩
  · intro Z g hg
    exact funext fun (x : ULift (_ ⟶ _)) ↦
      (congrFun (f.comp_of_compatible S hf hg x.down) _).trans (congrArg (f g hg) <| by simp)
  · intro g hg
    exact funext fun h : ULift (⊤_ C ⟶ Y) ↦ Eq.trans (by simp [Presheaf.codisc]) <|
      congrFun (hg h.down ((LocalSite.from_terminal_mem_of_mem J h.down hS))) _

/-- The right adjoint to the global sections functor that exists over any local site.
Takes a type `X` to the sheaf that sends each `Y : C` to the type of functions `Y → X`. -/
noncomputable def Sheaf.codisc [LocalSite J] :
    Type w ⥤ Sheaf J (Type (max v w)) where
  obj X := ⟨Presheaf.codisc.obj X, Presheaf.codisc_isSheaf J X⟩
  map f := ⟨Presheaf.codisc.map f⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- On local sites, the global sections functor `Γ` is left-adjoint to the codiscrete functor. -/
noncomputable def Sheaf.ΓCodiscAdj [LocalSite J] : Γ J (Type max u v w) ⊣ codisc J := by
  refine Adjunction.ofNatIsoLeft ?_ (ΓNatIsoSheafSections J _ terminalIsTerminal).symm
  exact Adjunction.mkOfUnitCounit {
    unit := {
      app X := ⟨{
        app Y (x : X.val.obj Y) y := ⟨X.val.map (op y.down) x⟩
        naturality Y Z f := by
          ext (x : X.val.obj Y); dsimp [codisc, Presheaf.codisc]; ext z
          exact (FunctorToTypes.map_comp_apply X.val _ _ x).symm
      }⟩
      naturality X Y f := by
        ext Z (x : X.val.obj Z); dsimp [codisc, Presheaf.codisc]; ext z
        exact congrFun (f.val.naturality _).symm x
    }
    counit := { app X := fun f : ULift (_ ⟶ _) → _ ↦ (f default).down }
    left_triangle := by
      ext X (x : X.val.obj _)
      dsimp; convert congrFun (X.val.map_id _) x; exact Subsingleton.elim _ _
    right_triangle := by
      ext X Y (f : _ → _); dsimp [codisc, Presheaf.codisc]; ext y
      dsimp; congr; convert Category.id_comp _; exact Subsingleton.elim _ _
  }

instance [LocalSite J] : (Γ J (Type max u v w)).IsLeftAdjoint :=
  ⟨codisc J, ⟨ΓCodiscAdj J⟩⟩

instance [LocalSite J] : (codisc.{u,v,max u v w} J).IsRightAdjoint :=
  ⟨Γ J _, ⟨ΓCodiscAdj J⟩⟩

/-- The global sections of the codiscrete sheaf on a type are naturally isomorphic to that type. -/
noncomputable def Sheaf.codiscΓNatIsoId [LocalSite J] :
    codisc J ⋙ Γ J _ ≅ 𝟭 (Type max u v w) := by
  refine (isoWhiskerLeft _ (ΓNatIsoSheafSections J _ terminalIsTerminal)).trans ?_
  exact (NatIso.ofComponents (fun X ↦ {
    hom x := fun _ ↦ ⟨x⟩
    inv f := (f (default : ULift (⊤_ C ⟶ ⊤_ C))).down
    inv_hom_id := by
      dsimp [codisc, Presheaf.codisc]; ext; dsimp
      congr; exact Subsingleton.elim _ _
  })).symm

/-- `Sheaf.codisc` is fully faithful. -/
noncomputable def Sheaf.fullyFaithfulCodisc [LocalSite J] :
    (codisc.{u,v,max u v w} J).FullyFaithful :=
  (ΓCodiscAdj J).fullyFaithfulROfCompIsoId (codiscΓNatIsoId J)

instance [LocalSite J] : (codisc.{u,v,max u v w} J).Full :=
  (fullyFaithfulCodisc J).full

instance [LocalSite J] : (codisc.{u,v,max u v w} J).Faithful :=
  (fullyFaithfulCodisc J).faithful

/-- On local sites, the constant sheaf functor is fully faithful. -/
noncomputable def fullyFaithfulConstantSheaf [HasWeakSheafify J (Type max u v w)] [LocalSite J] :
    (constantSheaf J (Type max u v w)).FullyFaithful :=
  ((constantSheafΓAdj J _).fullyFaithfulEquiv (Sheaf.ΓCodiscAdj J)).symm <|
    Sheaf.fullyFaithfulCodisc J

instance [HasWeakSheafify J (Type max u v w)] [LocalSite J] :
    (constantSheaf J (Type max u v w)).Full :=
  (fullyFaithfulConstantSheaf J).full

instance [HasWeakSheafify J (Type max u v w)] [LocalSite J] :
    (constantSheaf J (Type max u v w)).Faithful :=
  (fullyFaithfulConstantSheaf J).faithful

end CategoryTheory
