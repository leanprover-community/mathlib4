import Mathlib.Topology.Category.LightProfinite.IsLight
import Mathlib.CategoryTheory.Limits.FintypeCat

open CategoryTheory Limits Function Profinite

namespace LightProfinite

variable (S : LightProfinite)

def component (n : ℕ) : LightProfinite := fintypeCatToLightProfinite.obj <| S.diagram.obj ⟨n⟩

def transitionMap (n : ℕ) : S.diagram.obj ⟨n+1⟩ ⟶ S.diagram.obj ⟨n⟩ :=
  S.diagram.map ⟨homOfLE (Nat.le_succ _)⟩

def transitionMapLE {n m : ℕ} (h : n ≤ m) : S.diagram.obj ⟨m⟩ ⟶ S.diagram.obj ⟨n⟩ :=
  S.diagram.map ⟨homOfLE h⟩

def transitionMap' (n : ℕ) :  S.component (n+1) ⟶ S.component n :=
  fintypeCatToLightProfinite.map (S.transitionMap n)

def transitionMapLE' {n m : ℕ} (h : n ≤ m) : S.component m ⟶ S.component n :=
  fintypeCatToLightProfinite.map (S.transitionMapLE h)

noncomputable def iso : S ≅ ofIsLight S.toProfinite := isoMk <| (Iso.refl _)

lemma transitionMap_surjective_aux {T : Profinite} [T.IsLight] {d e : DiscreteQuotient T}
    (h : d ≤ e) : Surjective (T.diagram.map (homOfLE h)) :=
  Surjective.of_comp (g := d.proj) e.proj_surjective

lemma transitionMap_surjective (T : Profinite) [T.IsLight] (n : ℕ) :
    Surjective ((ofIsLight T).transitionMap n) :=
  transitionMap_surjective_aux (sequentialFunctor_map _ (Nat.le_succ _))

lemma _root_.CategoryTheory.FintypeCat.epi_iff_surjective {X Y : FintypeCat} (f : X ⟶ Y) :
    Epi f ↔ Surjective f := by
  change _ ↔ Surjective (FintypeCat.incl.map f)
  rw [← CategoryTheory.epi_iff_surjective]
  refine ⟨fun _ ↦ inferInstance, FintypeCat.incl.epi_of_epi_map⟩

instance (T : Profinite) [T.IsLight] (n : ℕ) :
    Epi ((ofIsLight T).transitionMap n) := by
  rw [FintypeCat.epi_iff_surjective]
  exact transitionMap_surjective T n

instance (T : Profinite) [T.IsLight] {n m : ℕ} (h : n ≤ m) :
    Epi ((ofIsLight T).transitionMapLE h) := by
  induction h with
  | refl =>
    change Epi ((ofIsLight T).diagram.map (𝟙 _))
    simp only [CategoryTheory.Functor.map_id]
    infer_instance
  | @step k h ih =>
    have : Epi ((transitionMap (ofIsLight T) k ≫
      (transitionMapLE (ofIsLight T) h))) := epi_comp _ _
    convert this
    simp only [transitionMapLE, transitionMap, ← Functor.map_comp]
    congr

noncomputable def _root_.CategoryTheory.FintypeCat.splitEpi_of_epi {X Y : FintypeCat}
    (f : X ⟶ Y) [Epi f] : SplitEpi f where
  section_ := surjInv ((FintypeCat.epi_iff_surjective f).1 inferInstance)
  id := by ext; exact surjInv_eq _ _

instance : SplitEpiCategory FintypeCat where
  isSplitEpi_of_epi f _ := ⟨⟨FintypeCat.splitEpi_of_epi f⟩⟩

instance {X Y : FintypeCat} (f : X ⟶ Y) [Epi f] : IsSplitEpi f := isSplitEpi_of_epi f

def proj (n : ℕ) : S ⟶ S.component n := S.cone.π.app ⟨n⟩

@[simp, reassoc]
lemma proj_comp_transitionMap' (n : ℕ) : S.proj (n + 1) ≫ S.transitionMap' n = S.proj n :=
  S.cone.w (homOfLE (Nat.le_succ n)).op

@[simp]
lemma proj_comp_transitionMap (n : ℕ) : S.transitionMap n ∘ S.proj (n + 1)  = S.proj n := by
  rw [← S.proj_comp_transitionMap' n, transitionMap]
  rfl

@[simp]
lemma proj_comp_transitionMap_assoc (n : ℕ) {Y : LightProfinite} (f : Y → S) :
    S.transitionMap n ∘ S.proj (n + 1) ∘ f  = S.proj n ∘ f := by
  rw [← S.proj_comp_transitionMap' n, transitionMap]
  rfl

@[simp]
lemma proj_comp_transitionMapLE' {n m : ℕ} (h : n ≤ m) :
    S.proj m ≫ S.transitionMapLE' h = S.proj n :=
  S.cone.w (homOfLE h).op

@[simp]
lemma proj_comp_transitionMapLE {n m : ℕ} (h : n ≤ m) :
    S.transitionMapLE' h ∘ S.proj m  = S.proj n := by
  rw [← S.proj_comp_transitionMapLE' h]
  rfl

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

def fromProfinite {X : Profinite} {Y : LightProfinite}
    (f : (n : ℕ) → X ⟶ (Y.component n).toProfinite)
    (w : ∀ n, Y.transitionMap n ∘ f (n + 1) = f n) : X ⟶ Y.toProfinite :=
  let c : Cone (Y.diagram ⋙ FintypeCat.toProfinite) := ⟨X, natTrans_nat_op_mk f
    (by intro n; ext; exact congrFun (w n).symm _)⟩
  Y.isLimit.lift c

abbrev fromProfinite' {X : Profinite} {Y : LightProfinite}
    (f : (n : ℕ) → LocallyConstant X (Y.diagram.obj ⟨n⟩))
    (w : ∀ n, Y.transitionMap n ∘ f (n + 1) = f n) : X ⟶ Y.toProfinite :=
  let _ : ∀ n, TopologicalSpace (Y.diagram.obj ⟨n⟩) := ⊥
  fromProfinite (fun n ↦ ⟨f n, (f n).2.continuous⟩) w

def homMk {X Y : LightProfinite}
    (f : (n : ℕ) → X ⟶ Y.component n)
    (w : ∀ n, Y.transitionMap n ∘ f (n + 1) = f n) : X ⟶ Y :=
  fromProfinite f w

abbrev homMk' {X Y : LightProfinite}
    (f : (n : ℕ) → LocallyConstant X (Y.diagram.obj ⟨n⟩))
    (w : ∀ n, Y.transitionMap n ∘ f (n + 1) = f n) : X ⟶ Y :=
  let _ : ∀ n, TopologicalSpace (Y.diagram.obj ⟨n⟩) := ⊥
  homMk (fun n ↦ ⟨f n, (f n).2.continuous⟩) w

abbrev homMk'' {X Y : LightProfinite}
    (f : (n : ℕ) → X ⟶ Y.component n)
    (w : ∀ n, f (n + 1) ≫ Y.transitionMap' n = f n) : X ⟶ Y :=
  homMk f fun n ↦ funext fun x ↦ DFunLike.ext_iff.mp (w n) x

theorem extracted_3 {X : Profinite} {Y : LightProfinite}
    (f : (n : ℕ) → X ⟶ (Y.component n).toProfinite)
    (w : ∀ n, Y.transitionMap n ∘ f (n + 1) = f n) (n : ℕ) :
    (proj Y n) ∘ (fromProfinite f w) = (f n) := by
  ext
  change (Y.isLimit.lift _ ≫ Y.cone.π.app _) _ = _
  simp only [Functor.comp_obj, IsLimit.fac]
  rfl

lemma homMk_injective {X : Profinite} {Y : LightProfinite}
    (f : (n : ℕ) → X ⟶ (Y.component n).toProfinite)
    (w : ∀ n, Y.transitionMap n ∘ f (n + 1) = f n)
    (h : ∀ (a b : X), (∀ n, f n a = f n b) → a = b) : Function.Injective (fromProfinite f w) := by
  intro a b hab
  apply h a b
  intro n
  have : Y.proj n ∘ fromProfinite f w = f n := extracted_3 f w n
  rw [← congrFun this a, ← congrFun this b]
  simp only [concreteCategory_forget_obj, Function.comp_apply]
  erw [hab]

theorem ext' {Y : LightProfinite} {a b : Y} (h : ∀ n, Y.proj n a = Y.proj n b) : a = b :=
  ext fun n ↦ h n.unop

lemma homMk_surjective {X : Profinite} {Y : LightProfinite}
    (f : (n : ℕ) → X ⟶ (Y.component n).toProfinite)
    (w : ∀ n, Y.transitionMap n ∘ f (n + 1) = f n)
    (h : ∀ (a : Y) n, ∃ (b : X), f n b = Y.proj n a) : Function.Surjective (fromProfinite f w) := by
  intro a
  replace h : ∀ n, Set.Nonempty ((f n) ⁻¹' {Y.proj n a}) := fun n ↦ h a n
  have := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _ ?_ h ?_ ?_
  · obtain ⟨x, hx⟩ := this
    refine ⟨x, ?_⟩
    apply ext'
    intro n
    have := congrFun (extracted_3 f w n) x
    simp only [concreteCategory_forget_obj, Function.comp_apply] at this
    erw [this]
    exact Set.mem_iInter.1 hx n
  · apply directed_of_isDirected_le
    intro i j hij x
    simp only [concreteCategory_forget_obj, Set.mem_preimage, Set.mem_singleton_iff]
    intro hx
    erw [← congrFun (Y.proj_comp_transitionMapLE hij) a]
    simp only [concreteCategory_forget_obj, Function.comp_apply]
    rw [← hx]
    erw [← congrFun (extracted_3 f w j) x, ← congrFun (extracted_3 f w i) x]
    simp only [concreteCategory_forget_obj, Function.comp_apply]
    exact (congrFun (Y.proj_comp_transitionMapLE hij) _).symm
  · exact fun i ↦ (IsClosed.preimage (f i).2 isClosed_singleton).isCompact
  · exact fun i ↦ IsClosed.preimage (f i).2 isClosed_singleton

def locallyConstant_of_hom {X Y : LightProfinite} (f : X ⟶ Y) (n : ℕ) :
    LocallyConstant X (Y.diagram.obj ⟨n⟩) where
  toFun x := Y.proj n (f x)
  isLocallyConstant := by
    let _ : TopologicalSpace (Y.diagram.obj ⟨n⟩) := ⊥
    have : DiscreteTopology (Y.diagram.obj ⟨n⟩) := ⟨rfl⟩
    rw [IsLocallyConstant.iff_continuous]
    exact (f ≫ Y.proj n).continuous

def locallyConstant_of_hom_w {X Y : LightProfinite} (f : X ⟶ Y) (n : ℕ) :
    Y.transitionMap n ∘ locallyConstant_of_hom f (n + 1) = locallyConstant_of_hom f n := by
  change Y.transitionMap n ∘ (Y.proj _) ∘ f = _
  simp [← Function.comp.assoc]
  erw [proj_comp_transitionMap]
  rfl

lemma eq_homMk {X Y : LightProfinite} (f : X ⟶ Y) :
    f = homMk' (locallyConstant_of_hom f) (locallyConstant_of_hom_w f) := by
  apply Y.isLimit.hom_ext
  intro ⟨n⟩
  ext
  simp only [Functor.comp_obj, CategoryTheory.comp_apply, homMk', homMk, fromProfinite,
    locallyConstant_of_hom, concreteCategory_forget_obj, LocallyConstant.coe_mk, IsLimit.fac]
  rfl
