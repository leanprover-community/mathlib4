import Mathlib.Topology.Category.LightProfinite.IsLight

open CategoryTheory Limits Function Profinite

namespace LightProfinite

variable (S : LightProfinite)

def transitionMap (n : ℕ) : S.diagram.obj ⟨n+1⟩ ⟶ S.diagram.obj ⟨n⟩ :=
  S.diagram.map ⟨homOfLE (Nat.le_succ _)⟩

def iso : S ≅ ofIsLight S.toProfinite where
  hom := 𝟙 S.toProfinite
  inv := 𝟙 S.toProfinite

variable (T : Profinite) [T.IsLight]

lemma transitionMap_surjective_aux {d e : DiscreteQuotient T} (h : d ≤ e) :
    Surjective (T.diagram.map (homOfLE h)) := by
  have : Surjective ((T.fintypeDiagram.map (homOfLE h)) ∘ d.proj) := by
    change Surjective e.proj; exact e.proj_surjective
  exact Surjective.of_comp this

lemma transitionMap_surjective (n : ℕ) : Surjective ((ofIsLight T).transitionMap n) :=
  transitionMap_surjective_aux _ (sequentialFunctor_map _ (Nat.le_succ _))

def natTrans_nat_mk {C : Type*} [Category C] {F G : ℕᵒᵖ ⥤ C} (f : (n : ℕ) → F.obj ⟨n⟩ ⟶ G.obj ⟨n⟩)
    (w : ∀ n, F.map ⟨homOfLE (Nat.le_succ _)⟩ ≫ f n = f (n + 1) ≫ G.map ⟨homOfLE (Nat.le_succ _)⟩) :
    F ⟶ G where
  app n := f n.unop
  naturality := sorry

def homMk {X Y : LightProfinite}
    (f : (n : ℕ) → X ⟶ fintypeCatToLightProfinite.obj (Y.diagram.obj ⟨n⟩))
    (w : ∀ n, Y.transitionMap n ∘ f (n + 1) = f n) : X ⟶ Y := by
  let c : Cone (Y.diagram ⋙ FintypeCat.toProfinite) := ⟨X.toProfinite, ?_, ?_⟩
  · exact Y.isLimit.lift c
  · intro ⟨n⟩
    refine ⟨f n, (f n).continuous⟩
  · intro ⟨n⟩ ⟨m⟩ ⟨⟨⟨(h : m ≤ n)⟩⟩⟩
    ext x
    simp only [Functor.comp_obj, Functor.const_obj_obj, Functor.const_obj_map,
      FintypeCat.toProfinite_obj_toCompHaus_toTop_α, Category.id_comp, Functor.comp_map,
      CategoryTheory.comp_apply]
    sorry
