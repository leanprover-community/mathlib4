import Mathlib.Topology.Category.LightProfinite.IsLight

open CategoryTheory Limits Function Profinite

namespace LightProfinite

variable (S : LightProfinite)

def component (n : ℕ) : LightProfinite := fintypeCatToLightProfinite.obj <| S.diagram.obj ⟨n⟩

def transitionMap (n : ℕ) : S.diagram.obj ⟨n+1⟩ ⟶ S.diagram.obj ⟨n⟩ :=
  S.diagram.map ⟨homOfLE (Nat.le_succ _)⟩

def transitionMap' (n : ℕ) :  S.component (n+1) ⟶ S.component n :=
  fintypeCatToLightProfinite.map (S.transitionMap n)

def isoMk {X Y : LightProfinite} (i : X.toProfinite ≅ Y.toProfinite) : X ≅ Y where
  hom := i.hom
  inv := i.inv
  hom_inv_id := i.hom_inv_id
  inv_hom_id := i.inv_hom_id

noncomputable def iso : S ≅ ofIsLight S.toProfinite := isoMk <| (Iso.refl _)

lemma transitionMap_surjective_aux {T : Profinite} [T.IsLight] {d e : DiscreteQuotient T}
    (h : d ≤ e) : Surjective (T.diagram.map (homOfLE h)) := by
  have : Surjective ((T.fintypeDiagram.map (homOfLE h)) ∘ d.proj) := by
    change Surjective e.proj; exact e.proj_surjective
  exact Surjective.of_comp this

lemma transitionMap_surjective (T : Profinite) [T.IsLight] (n : ℕ) :
    Surjective ((ofIsLight T).transitionMap n) :=
  transitionMap_surjective_aux (sequentialFunctor_map _ (Nat.le_succ _))

def proj (n : ℕ) : S ⟶ S.component n := S.cone.π.app ⟨n⟩

@[simp]
lemma proj_comp_transitionMap (n : ℕ) : S.proj (n + 1) ≫ S.transitionMap' n = S.proj n :=
  S.cone.w (homOfLE (Nat.le_succ n)).op

def natTrans_nat_mk {C : Type*} [Category C] {F G : ℕ ⥤ C} (f : (n : ℕ) → F.obj n ⟶ G.obj n)
    (w : ∀ n, F.map (homOfLE (Nat.le_succ _)) ≫ f (n + 1) = f n ≫ G.map (homOfLE (Nat.le_succ _))) :
    F ⟶ G where
  app n := f n
  naturality n m h := by
    have h' : n ≤ m := leOfHom h
    induction h' with
    | refl =>
      change F.map (𝟙 _) ≫ _ = _ ≫ G.map (𝟙 _)
      simp
    | @step k a ih =>
      have a' : n ≤ k := a
      have : h = homOfLE a' ≫ homOfLE (Nat.le_succ k) := rfl
      simp only [this, Functor.map_comp, Category.assoc]
      rw [w k, ← Category.assoc, ih (homOfLE _)]
      simp

def natTrans_nat_op_mk {C : Type*} [Category C] {F G : ℕᵒᵖ ⥤ C} (f : (n : ℕ) → F.obj ⟨n⟩ ⟶ G.obj ⟨n⟩)
    (w : ∀ n, F.map ⟨homOfLE (Nat.le_succ _)⟩ ≫ f n = f (n + 1) ≫ G.map ⟨homOfLE (Nat.le_succ _)⟩) :
    F ⟶ G where
  app := fun ⟨n⟩ ↦ f n
  naturality := by
    intro ⟨n⟩ ⟨m⟩ h
    have h' : m ≤ n := leOfHom h.unop
    induction h' with
    | refl =>
      change F.map (𝟙 _) ≫ _ = _ ≫ G.map (𝟙 _)
      simp
    | @step k a ih =>
      have a' : m ≤ k := a
      have : h = (homOfLE a' ≫ homOfLE (Nat.le_succ k)).op := rfl
      rw [op_comp] at this
      simp only [this, Functor.map_comp, Category.assoc]
      rw [ih, ← Category.assoc]
      have := w k
      change F.map (homOfLE _).op ≫ _ = _ at this
      rw [this, Category.assoc]
      rfl

def homMk {X Y : LightProfinite}
    (f : (n : ℕ) → X ⟶ fintypeCatToLightProfinite.obj (Y.diagram.obj ⟨n⟩))
    (w : ∀ n, Y.transitionMap n ∘ f (n + 1) = f n) : X ⟶ Y :=
  let c : Cone (Y.diagram ⋙ FintypeCat.toProfinite) := ⟨X.toProfinite, natTrans_nat_op_mk f
    (by intro n; ext; exact congrFun (w n).symm _)⟩
  Y.isLimit.lift c

def homMk' {X Y : LightProfinite}
    (f : (n : ℕ) → LocallyConstant X (Y.diagram.obj ⟨n⟩))
    (w : ∀ n, Y.transitionMap n ∘ f (n + 1) = f n) : X ⟶ Y :=
  let _ : ∀ n, TopologicalSpace (Y.diagram.obj ⟨n⟩) := ⊥
  homMk (fun n ↦ ⟨f n, (f n).2.continuous⟩) w
