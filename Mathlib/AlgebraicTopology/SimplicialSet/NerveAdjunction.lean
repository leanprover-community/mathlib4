/-
Copyright (c) 2024 Mario Carneiro and Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl, Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty
import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!

# The adjunction between the nerve and the homotopy category functor.

We define an adjunction `nerveAdjunction : hoFunctor ⊣ nerveFunctor` between the functor that
takes a simplicial set to its homotopy category and the functor that takes a category to its nerve.

Up to natural isomorphism, this is constructed as the composite of two other adjunctions,
namely `nerve₂Adj : hoFunctor₂ ⊣ nerveFunctor₂` between analogously-defined functors involving
the category of 2-truncated simplicial sets and `coskAdj 2 : truncation 2 ⊣ Truncated.cosk 2`. The
aforementioned natural isomorphism

`cosk₂Iso : nerveFunctor ≅ nerveFunctor₂ ⋙ Truncated.cosk 2`

exists because nerves of categories are 2-coskeletal.

We also prove that `nerveFunctor` is fully faithful, demonstrating that `nerveAdjunction` is
reflective. Since the category of simplicial sets is cocomplete, we conclude in
`Mathlib/CategoryTheory/Category/Cat/Colimit.lean` that the category of categories has colimits.

-/

namespace CategoryTheory

open Category Functor Limits Opposite SimplexCategory Simplicial SSet Nerve
open SSet.Truncated SimplexCategory.Truncated SimplicialObject.Truncated
universe v u v' u'

section

/-- The components of the counit of `nerve₂Adj`. -/
@[simps!]
def nerve₂Adj.counit.app (C : Type u) [SmallCategory C] :
    (nerveFunctor₂.obj (Cat.of C)).HomotopyCategory ⥤ C := by
  fapply Quotient.lift
  · exact
    (whiskerRight (OneTruncation₂.ofNerve₂.natIso).hom _ ≫ ReflQuiv.adj.{u}.counit).app (Cat.of C)
  · intro x y f g rel
    obtain ⟨φ⟩ := rel
    simpa [ReflQuiv.adj, Quot.liftOn, Cat.FreeRefl.quotientFunctor, Quotient.functor,
        pathComposition, Quiv.adj, OneTruncation₂.nerveHomEquiv] using
      φ.map_comp (X := 0) (Y := 1) (Z := 2) (homOfLE (by decide)) (homOfLE (by decide))

@[simp]
theorem nerve₂Adj.counit.app_eq (C : Type u) [SmallCategory C] :
    SSet.Truncated.HomotopyCategory.quotientFunctor (nerveFunctor₂.obj (Cat.of C)) ⋙
      nerve₂Adj.counit.app.{u} C =
    (whiskerRight OneTruncation₂.ofNerve₂.natIso.hom _ ≫
      ReflQuiv.adj.{u}.counit).app (Cat.of C) := rfl

/-- The naturality of `nerve₂Adj.counit.app`. -/
theorem nerve₂Adj.counit.naturality {C D : Type u} [SmallCategory C] [SmallCategory D]
    (F : C ⥤ D) :
    (nerveFunctor₂ ⋙ hoFunctor₂).map F ⋙ nerve₂Adj.counit.app D =
      nerve₂Adj.counit.app C ⋙ F := by
  apply HomotopyCategory.lift_unique'
  change ((oneTruncation₂ ⋙ Cat.freeRefl).map (nerveFunctor₂.map _)) ⋙
    HomotopyCategory.quotientFunctor (nerveFunctor₂.obj (Cat.of D)) ⋙ app D = _
  rw [nerve₂Adj.counit.app_eq D]
  rw [← Functor.assoc _ _ F, nerve₂Adj.counit.app_eq C]
  exact (whiskerRight OneTruncation₂.ofNerve₂.natIso.{u}.hom Cat.freeRefl ≫
    ReflQuiv.adj.counit).naturality _

/-- The counit of `nerve₂Adj.` -/
@[simps]
def nerve₂Adj.counit : nerveFunctor₂ ⋙ hoFunctor₂.{u} ⟶ 𝟭 Cat where
  app _ := nerve₂Adj.counit.app _
  naturality _ _ _ := nerve₂Adj.counit.naturality _

end

end CategoryTheory

namespace SSet.Truncated

open SimplexCategory Simplicial SSet CategoryTheory Category Functor Opposite Limits
open SSet.Truncated SimplexCategory.Truncated SimplicialObject.Truncated
universe v u v' u'

section
variable {X Y : SSet.Truncated 2} (sy : StrictSegal Y) (F : OneTruncation₂ X ⥤rq OneTruncation₂ Y)

/-- The components of a map of 2-truncated simplicial sets built from a map on underlying reflexive
quivers, under the assumption that the codomain is `StrictSegal`. -/
def toStrictSegal₂.mk.app (n : SimplexCategory.Truncated 2) : X.obj (op n) ⟶ Y.obj (op n) := by
  obtain ⟨n, hn⟩ := n
  induction' n using SimplexCategory.rec with n
  match n with
  | 0 => exact fun x => F.obj x
  | 1 => exact fun f => (F.map ⟨f, rfl, rfl⟩).edge
  | 2 => exact fun φ => StrictSegal.spineToSimplex sy _ _ (oneTruncation₂.pathMap F (X.spine _ _ φ))

@[simp] theorem toStrictSegal₂.mk.app_zero (x : X _⦋0⦌₂) :
    mk.app sy F ⦋0⦌₂ x = F.obj x := rfl

@[simp] theorem toStrictSegal₂.mk.app_one (f : X _⦋1⦌₂) :
    mk.app sy F ⦋1⦌₂ f = (F.map ⟨f, rfl, rfl⟩).edge := rfl

@[simp] theorem toStrictSegal₂.mk.app_two (φ : X _⦋2⦌₂) :
    mk.app sy F ⦋2⦌₂ φ =
      StrictSegal.spineToSimplex sy _ _ (oneTruncation₂.pathMap F (X.spine _ _ φ)) := rfl

/-- Naturality of the components defined by `toStrictSegal₂.mk.app` as a morphism property of
maps in `SimplexCategory.Truncated 2`. -/
abbrev toStrictSegal₂.mk.naturalityProperty : MorphismProperty (SimplexCategory.Truncated 2) :=
  (MorphismProperty.naturalityProperty (fun n => toStrictSegal₂.mk.app sy F n.unop)).unop

lemma ReflPrefunctor.congr_map_edge
    {U : Type u'} [ReflQuiver.{v'} U] (G : U ⥤rq OneTruncation₂ X)
    {x₁ y₁ x₂ y₂ : U} (f : x₁ ⟶ y₁) (g : x₂ ⟶ y₂)
    (hx : x₁ = x₂) (hy : y₁ = y₂) (hfg : Quiver.homOfEq f hx hy = g) :
    (G.map f).edge = (G.map g).edge := by
  subst hx hy hfg; rfl

lemma toStrictSegal₂.mk_naturality_σ00 :
    toStrictSegal₂.mk.naturalityProperty sy F (σ₂ (n := 0) 0) := by
  ext (x : OneTruncation₂ X)
  dsimp
  rw [← OneTruncation₂.id_edge (F.obj x), ← ReflPrefunctor.map_id F x]
  fapply ReflPrefunctor.congr_map_edge (G := F) (g := 𝟙rq x)
  · simp [← FunctorToTypes.map_comp_apply, ← op_comp]
    rw [δ₂_one_comp_σ₂_zero]
    simp only [op_id, FunctorToTypes.map_id_apply]
  · simp [← FunctorToTypes.map_comp_apply, ← op_comp]
    rw [δ₂_zero_comp_σ₂_zero]
    simp only [op_id, FunctorToTypes.map_id_apply]
  · aesop

lemma toStrictSegal₂.mk_naturality_δ0i (i : Fin 2) :
    toStrictSegal₂.mk.naturalityProperty sy F (δ₂ i) := by
  ext f
  fin_cases i <;> dsimp
  · rw [(F.map ⟨f, rfl, rfl⟩).tgt_eq]
  · rw [(F.map ⟨f, rfl, rfl⟩).src_eq]

section
variable (hyp : (φ : X _⦋2⦌₂) → (F.map (ev02₂ φ)).edge =
  Y.map (δ₂ (1 : Fin 3) _ _).op
    (StrictSegal.spineToSimplex sy 2 (by omega) (oneTruncation₂.pathMap F (X.spine _ _ φ))))

include hyp

lemma toStrictSegal₂.mk_naturality_δ1i (i : Fin 3) :
    toStrictSegal₂.mk.naturalityProperty sy F (δ₂ i) := by
  ext φ
  dsimp
  fin_cases i
  · simp only [Fin.zero_eta]
    have :=
      StrictSegal.spineToSimplex_arrow sy 2 (by omega) 1 (oneTruncation₂.pathMap F (X.spine 2 _ φ))
    rw [← δ₂_zero_eq_mkOfSucc] at this
    rw [this]
    rw [oneTruncation₂.pathMap_arrow]
    fapply ReflPrefunctor.congr_map_edge
    · rw [← FunctorToTypes.map_comp_apply, ← op_comp]
      simp only [spine_vertex]
      congr!
      apply δ_one_δ_zero_eq_const
    · rw [← FunctorToTypes.map_comp_apply, ← op_comp]
      simp only [spine_vertex]
      congr!
      apply δ_zero_δ_zero_eq_const
    · simp only [Nat.reduceAdd, len_mk, id_eq, Fin.isValue, Fin.castSucc_one, spine_vertex,
      Fin.succ_one_eq_two, spine_arrow, OneTruncation₂.Quiver_homOfEq]
      congr!
      exact δ_zero_eq_mkOfSucc
  · simp only [Fin.mk_one]
    rw [← hyp]
    fapply ReflPrefunctor.congr_map_edge
    · unfold ev0₂
      rw [← FunctorToTypes.map_comp_apply, ← op_comp]
      dsimp [ι0₂]
    · unfold ev2₂
      rw [← FunctorToTypes.map_comp_apply, ← op_comp]
      dsimp [ι2₂]
    · unfold ev02₂
      simp only [Fin.isValue, OneTruncation₂.Quiver_homOfEq]
      dsimp [δ1₂]
  · simp only [Fin.reduceFinMk]
    have :=
      StrictSegal.spineToSimplex_arrow sy 2 (by omega) 0 (oneTruncation₂.pathMap F (X.spine 2 _ φ))
    rw [← δ₂_two_eq_mkOfSucc] at this
    rw [this, oneTruncation₂.pathMap_arrow]
    fapply ReflPrefunctor.congr_map_edge
    · rw [← FunctorToTypes.map_comp_apply, ← op_comp]
      simp only [spine_vertex]
      congr!
      apply δ_one_δ_two_eq_const
    · rw [← FunctorToTypes.map_comp_apply, ← op_comp]
      simp only [spine_vertex]
      congr!
      apply δ_zero_δ_two_eq_const
    · simp only [Nat.reduceAdd, len_mk, id_eq, Fin.isValue, Fin.castSucc_zero, spine_vertex,
      Fin.succ_zero_eq_one, OneTruncation₂.Quiver_homOfEq, spine_arrow]
      congr!
      exact δ_two_eq_mkOfSucc

lemma toStrictSegal₂.mk_naturality_σ1i (i : Fin 2) :
    toStrictSegal₂.mk.naturalityProperty sy F (σ₂ i) := by
  have := StrictSegal.mono_segalSpine sy
  apply (cancel_mono (segalSpine (Z := Y)) ).1
  simp only [segalSpine, prod.comp_lift, assoc]
  congr 1 <;> rw [← map_comp]
  · show _ ≫ _ ≫ Y.map (δ₂ _).op = _ ≫ Y.map (_ ≫ (δ₂ _).op)
    rw [← op_comp, ← toStrictSegal₂.mk_naturality_δ1i sy F hyp, ← assoc, ← map_comp, ← op_comp]
    change toStrictSegal₂.mk.naturalityProperty sy F (δ₂ 2 ≫ σ₂ i)
    fin_cases i
    · dsimp only [Fin.zero_eta]
      rw [δ₂_two_comp_σ₂_zero]
      exact (toStrictSegal₂.mk.naturalityProperty sy F).comp_mem _ _
        (toStrictSegal₂.mk_naturality_σ00 sy F) (toStrictSegal₂.mk_naturality_δ0i sy F _)
    · dsimp only [Fin.mk_one]
      rw [δ₂_two_comp_σ₂_one]
      exact (toStrictSegal₂.mk.naturalityProperty sy F).id_mem _
  · show _ ≫ _ ≫ Y.map (δ₂ _).op = _ ≫ Y.map (_ ≫ (δ₂ _).op)
    rw [← op_comp, ← toStrictSegal₂.mk_naturality_δ1i sy F hyp, ← assoc, ← map_comp, ← op_comp]
    change toStrictSegal₂.mk.naturalityProperty sy F (δ₂ 0 ≫ σ₂ i)
    fin_cases i <;> dsimp only [Fin.zero_eta, Fin.isValue, Fin.mk_one]
    · rw [δ₂_zero_comp_σ₂_zero]
      exact (toStrictSegal₂.mk.naturalityProperty sy F).id_mem _
    · rw [δ₂_zero_comp_σ₂_one]
      exact (toStrictSegal₂.mk.naturalityProperty sy F).comp_mem _ _
        (toStrictSegal₂.mk_naturality_σ00 sy F) (toStrictSegal₂.mk_naturality_δ0i sy F _)

/-- A proof that the components defined by `toNerve₂.mk.app` are natural. -/
theorem toStrictSegal₂.mk_naturality : toStrictSegal₂.mk.naturalityProperty sy F = ⊤ :=
  Truncated.morphismProperty_eq_top (toStrictSegal₂.mk.naturalityProperty sy F)
    (fun
      | 0, _, _ => toStrictSegal₂.mk_naturality_δ0i sy F _
      | 1, _, _ => toStrictSegal₂.mk_naturality_δ1i sy F hyp _)
    (fun
      | 0, _, 0 => toStrictSegal₂.mk_naturality_σ00 sy F
      | 1, _, _ => toStrictSegal₂.mk_naturality_σ1i sy F hyp _)

/-- A map `X → Y` of 2-truncated simplicial sets that is constructed from a refl prefunctor
`F : OneTruncation₂ X ⥤rq OneTruncation₂ Y` assuming `∀ (φ : X _⦋2⦌₂),`
`(F.map (ev02₂ φ)).edge =`
`StrictSegal.spineToDiagonal sy 2 (by omega) (oneTruncation₂.pathMap F (X.spine _ _ φ)))`. -/
@[simps!]
def toStrictSegal₂.mk : X ⟶ Y where
  app n := toStrictSegal₂.mk.app sy F n.unop
  naturality _ _ α := MorphismProperty.of_eq_top (toStrictSegal₂.mk_naturality sy F hyp) α.unop

/-- A computation about `toStrictSegal₂.mk`. -/
theorem oneTruncation₂_toStrictSegal₂Mk :
    oneTruncation₂.map (toStrictSegal₂.mk sy F hyp) = F := by
  refine ReflPrefunctor.ext' (fun _ ↦ rfl) (fun X Y f ↦ ?_)
  · dsimp [oneTruncation₂]
    ext
    dsimp
    exact ReflPrefunctor.congr_map_edge F { edge := f.edge, src_eq := rfl, tgt_eq := rfl }
      f f.src_eq f.tgt_eq (by simp only [OneTruncation₂.Quiver_homOfEq]; rfl)

end

/-- An equality between maps into the 2-truncated nerve is detected by an equality between their
underlying refl prefunctors. -/
theorem toStrictSegal₂.ext (F G : X ⟶ Y) (sy : StrictSegal Y)
    (hyp : SSet.oneTruncation₂.map F = SSet.oneTruncation₂.map G) : F = G := by
  have eq₀ (x : X _⦋0⦌₂) : F.app (op ⦋0⦌₂) x = G.app (op ⦋0⦌₂) x := congr(($hyp).obj x)
  have eq₁ (x : X _⦋1⦌₂) : F.app (op ⦋1⦌₂) x = G.app (op ⦋1⦌₂) x :=
    congr((($hyp).map ⟨x, rfl, rfl⟩).1)
  ext ⟨⟨n, hn⟩⟩ x
  induction' n using SimplexCategory.rec with n
  match n with
  | 0 => apply eq₀
  | 1 => apply eq₁
  | 2 =>
    apply sy.spineInjective 2
    unfold StrictSegal.spineEquiv
    simp only [Nat.reduceAdd, Equiv.coe_fn_mk]
    ext i
    have h1 := congr_fun (F.naturality (Hom.tr (mkOfSucc i)).op) x
    have h2 := congr_fun (G.naturality (Hom.tr (mkOfSucc i)).op) x
    simp only [types_comp_apply, Nat.reduceAdd] at h1 h2
    simp only [Equiv.coe_fn_mk, spine_arrow, ← h1, ← h2, eq₁]

end

end SSet.Truncated

namespace CategoryTheory

open Category Functor Limits Opposite SimplexCategory Simplicial SSet Nerve
open SSet.Truncated SimplexCategory.Truncated SimplicialObject.Truncated
universe v u v' u'

section
variable {C : Type u} [SmallCategory C] {X : SSet.Truncated.{u} 2}
    (F : SSet.oneTruncation₂.obj X ⟶ ReflQuiv.of C)

section
variable
  (hyp : ∀ φ, F.map (ev02₂ φ) = CategoryStruct.comp (obj := C) (F.map (ev01₂ φ)) (F.map (ev12₂ φ)))
include hyp


/-- The morphism `X ⟶ nerveFunctor₂.obj (Cat.of C)` of 2-truncated simplicial sets that is
constructed from a refl prefunctor `F : SSet.oneTruncation₂.obj X ⟶ ReflQuiv.of C` assuming
`∀ (φ : : X _⦋2⦌₂), F.map (ev02₂ φ) = F.map (ev01₂ φ) ≫ F.map (ev12₂ φ)`. -/
@[simps!] def toNerve₂.mk : X ⟶ nerveFunctor₂.obj (Cat.of C) := by
  refine toStrictSegal₂.mk (Nerve.strictSegal₂ C)
    (F ⋙rq (OneTruncation₂.ofNerve₂.natIso.app (Cat.of C)).inv) ?_
  intro φ
  have := hyp φ
  unfold δ₂ nerveFunctor₂ nerveFunctor
  simp only [comp_obj, Cat.of_α]
  erw [Nerve.mkOfObjOfMapSucc₂_δ_one]
  simp only [ReflQuiv.of_val, oneTruncation₂_obj, ReflQuiv.forget_obj,
    Iso.app_inv, ReflPrefunctor.comp_obj, ReflPrefunctor.comp_map,
    OneTruncation₂.ofNerve₂.natIso_inv_app_map,
    oneTruncation₂.pathMap_vertex, Truncated.spine_vertex,
    OneTruncation₂.ofNerve₂.natIso_inv_app_obj_obj,
    oneTruncation₂.pathMap_arrow, Truncated.spine_arrow, toCat_map,
    ComposableArrows.whiskerLeft_obj, eqToHom_refl, comp_id, id_comp, Fin.castSucc_zero,
    Fin.succ_one_eq_two]
  unfold OneTruncation₂.nerveHomEquiv
  simp only [OneTruncation₂.nerveEquiv_apply, ComposableArrows.mk₀_obj, Equiv.coe_fn_symm_mk]
  fapply ComposableArrows.ext₁ <;> simp only [ComposableArrows.mk₁_obj, ComposableArrows.Mk₁.obj]
  · unfold ev0₂ ι0₂ δ₂
    congr!
    exact δ_one_δ_one_eq_const
  · unfold ev2₂ ι2₂ δ₂
    congr!
    exact δ_zero_δ_one_eq_const
  · rw [hyp]
    simp only [oneTruncation₂_obj, ReflQuiv.of_val, Nat.reduceAdd,
      Fin.zero_eta, Fin.isValue, Fin.mk_one, ComposableArrows.mk₁_map,
      ComposableArrows.Mk₁.map, len_mk, homOfLE_leOfHom]
    have zero_eq : ev0₂ φ = (X.spine 2 _ φ).vertex 0 := by
      unfold ev0₂ ι0₂
      simp only [Truncated.spine_vertex]
      congr!
      exact δ_one_δ_one_eq_const
    have one_eq : ev1₂ φ = (X.spine 2 _ φ).vertex 1 := by
      unfold ev1₂ ι1₂
      simp only [Truncated.spine_vertex]
      congr!
      exact δ_zero_δ_two_eq_const
    have two_eq : ev2₂ φ = (X.spine 2 _ φ).vertex 2 := by
      unfold ev2₂ ι2₂
      simp only [Truncated.spine_vertex]
      congr!
      exact δ_zero_δ_one_eq_const
    have left : Quiver.homOfEq (ev01₂ φ) zero_eq one_eq =
      ⟨(X.spine 2 _ φ).arrow 0, (X.spine 2 _ φ).arrow_src 0, (X.spine 2 _ φ).arrow_tgt 0⟩ := by
      unfold ev01₂ δ2₂
      simp [OneTruncation₂.Quiver_homOfEq]
      congr!
      exact δ_two_eq_mkOfSucc
    have right : Quiver.homOfEq (ev12₂ φ) one_eq two_eq =
      ⟨(X.spine 2 _ φ).arrow 1, (X.spine 2 _ φ).arrow_src 1, (X.spine 2 _ φ).arrow_tgt 1⟩ := by
      unfold ev12₂ δ0₂
      simp [OneTruncation₂.Quiver_homOfEq]
      congr!
      exact δ_zero_eq_mkOfSucc
    erw [← left, ← right]
    simp [Prefunctor.homOfEq_map, eqToHom_quiverHomOfEq]

end
section

variable (F : SSet.oneTruncation₂.obj X ⟶ SSet.oneTruncation₂.obj (nerveFunctor₂.obj (Cat.of C)))
variable (hyp : (φ : X _⦋2⦌₂) →
            (F ⋙rq (OneTruncation₂.ofNerve₂.natIso.app (Cat.of C)).hom).map (ev02₂ φ) =
              CategoryStruct.comp (obj := C)
              ((F ⋙rq (OneTruncation₂.ofNerve₂.natIso.app (Cat.of C)).hom).map (ev01₂ φ))
              ((F ⋙rq (OneTruncation₂.ofNerve₂.natIso.app (Cat.of C)).hom).map (ev12₂ φ)))

/-- An alternate version of `toNerve₂.mk`, which constructs a map of 2-truncated simplicial sets
`X ⟶ nerveFunctor₂.obj (Cat.of C)` from the underlying refl prefunctor under a composition
hypothesis, where that prefunctor the central hypothesis is conjugated by the isomorphism
`nerve₂Adj.NatIso.app C`. The `ALT` pathway includes the new infrastructure above. -/
@[simps!] def toNerve₂.mk' : X ⟶ nerveFunctor₂.obj (Cat.of C) :=
  toNerve₂.mk (F ≫ (OneTruncation₂.ofNerve₂.natIso.app (Cat.of C)).hom) hyp

/-- A computation about `toNerve₂.mk'`. -/
theorem oneTruncation₂_toNerve₂Mk : oneTruncation₂.map (toNerve₂.mk' F hyp) = F := by
  unfold toNerve₂.mk'
  unfold toNerve₂.mk
  rw [oneTruncation₂_toStrictSegal₂Mk, ← ReflQuiv.comp_eq_comp]
  simp

end

/-- An equality between maps into the 2-truncated nerve is detected by an equality between their
underlying refl prefunctors. -/
theorem toNerve₂.ext (F G : X ⟶ nerveFunctor₂.obj (Cat.of C))
    (hyp : SSet.oneTruncation₂.map F = SSet.oneTruncation₂.map G) : F = G := by
  unfold nerveFunctor₂ at F G
  dsimp at F G
  exact toStrictSegal₂.ext F G (Nerve.strictSegal₂ C) hyp

/-- The components of the 2-truncated nerve adjunction unit. -/
def nerve₂Adj.unit.app (X : SSet.Truncated.{u} 2) :
    X ⟶ nerveFunctor₂.obj (hoFunctor₂.obj X) := by
  fapply toNerve₂.mk' (C := hoFunctor₂.obj X)
  · exact (ReflQuiv.adj.{u}.unit.app (SSet.oneTruncation₂.obj X) ⋙rq
      (SSet.Truncated.HomotopyCategory.quotientFunctor X).toReflPrefunctor ⋙rq
      (OneTruncation₂.ofNerve₂.natIso).inv.app (hoFunctor₂.obj X))
  · exact fun φ ↦ Quotient.sound _ (HoRel₂.mk φ)

theorem nerve₂Adj.unit.map_app_eq (X : SSet.Truncated.{u} 2) :
    SSet.oneTruncation₂.map (nerve₂Adj.unit.app X) =
    ReflQuiv.adj.{u}.unit.app (SSet.oneTruncation₂.obj X) ⋙rq
    (SSet.Truncated.HomotopyCategory.quotientFunctor X).toReflPrefunctor ⋙rq
    (OneTruncation₂.ofNerve₂.natIso).inv.app (hoFunctor₂.obj X) := by
  apply oneTruncation₂_toNerve₂Mk

@[reassoc]
lemma nerve₂Adj.unit.naturality {X Y : SSet.Truncated.{u} 2} (f : X ⟶ Y) :
    f ≫ unit.app Y = unit.app X ≫ nerveFunctor₂.map (hoFunctor₂.map f) :=
  toNerve₂.ext _ _ (by
    have := (OneTruncation₂.ofNerve₂.natIso).inv.naturality (hoFunctor₂.map f)
    dsimp at this ⊢
    rw [Functor.map_comp, Functor.map_comp, nerve₂Adj.unit.map_app_eq,
      nerve₂Adj.unit.map_app_eq, ← ReflQuiv.comp_eq_comp (Y := ReflQuiv.of _),
      ← ReflQuiv.comp_eq_comp (Y := ReflQuiv.of _), assoc, ← this]
    rfl)

/-- The 2-truncated nerve adjunction unit. -/
@[simps]
def nerve₂Adj.unit : 𝟭 (SSet.Truncated.{u} 2) ⟶ hoFunctor₂ ⋙ nerveFunctor₂ where
  app := nerve₂Adj.unit.app
  naturality _ _ _ := unit.naturality _

/-- The adjunction between the 2-truncated nerve functor and the 2-truncated homotopy category
functor. -/
nonrec def nerve₂Adj : hoFunctor₂.{u} ⊣ nerveFunctor₂ :=
  Adjunction.mkOfUnitCounit {
    unit := nerve₂Adj.unit
    counit := nerve₂Adj.counit
    left_triangle := by
      ext X
      apply HomotopyCategory.lift_unique'
      dsimp
      rw [Cat.comp_eq_comp, ← Functor.assoc]
      dsimp only [hoFunctor₂]
      rw [← hoFunctor₂_naturality (nerve₂Adj.unit.app X)]
      dsimp
      rw [nerve₂Adj.unit.map_app_eq X, Functor.assoc, id_comp]
      show _ ⋙ (HomotopyCategory.quotientFunctor _ ⋙ nerve₂Adj.counit.app (hoFunctor₂.obj X)) = _
      rw [nerve₂Adj.counit.app_eq]
      dsimp
      rw [← Cat.comp_eq_comp, ← assoc, ← Cat.freeRefl.map_comp, ReflQuiv.comp_eq_comp,
        ReflPrefunctor.comp_assoc]
      dsimp
      rw [← ReflQuiv.comp_eq_comp, Iso.inv_hom_id_app, ReflQuiv.id_eq_id]
      dsimp
      rw [ReflPrefunctor.comp_id (V := hoFunctor₂.obj X), ← ReflQuiv.comp_eq_comp (Z := .of _),
        Cat.freeRefl.map_comp, assoc]
      have := ReflQuiv.adj.counit.naturality
        (X := Cat.freeRefl.obj (ReflQuiv.of (OneTruncation₂ X)))
        (Y := hoFunctor₂.obj X) (SSet.Truncated.HomotopyCategory.quotientFunctor X)
      dsimp at this
      rw [this]
      apply Adjunction.left_triangle_components_assoc
    right_triangle := by
      refine NatTrans.ext (funext fun C ↦ ?_)
      apply toNerve₂.ext
      dsimp
      simp only [id_comp, map_comp, oneTruncation₂_obj, map_id]
      rw [nerve₂Adj.unit.map_app_eq, ReflPrefunctor.comp_assoc]
      rw [← ReflQuiv.comp_eq_comp,
        ← ReflQuiv.comp_eq_comp (X := ReflQuiv.of _) (Y := ReflQuiv.of _),
        assoc, assoc, ← Functor.comp_map, ← OneTruncation₂.ofNerve₂.natIso.inv.naturality]
      conv => lhs; rhs; rw [← assoc]
      show _ ≫ (ReflQuiv.forget.map _ ≫ ReflQuiv.forget.map _) ≫ _ = _
      rw [← ReflQuiv.forget.map_comp]
      dsimp
      conv => lhs; rhs; lhs; rw [Cat.comp_eq_comp]
      have : HomotopyCategory.quotientFunctor (nerveFunctor₂.obj C) ⋙ _ = _ :=
        nerve₂Adj.counit.app_eq C
      rw [this]
      dsimp
      rw [← assoc, Cat.comp_eq_comp, toReflPrefunctor.map_comp]
      rw [← ReflQuiv.comp_eq_comp (X := ReflQuiv.of _) (Y := ReflQuiv.of _) (Z := ReflQuiv.of _)]
      have := ReflQuiv.adj.unit.naturality (OneTruncation₂.ofNerve₂.natIso.hom.app C)
      dsimp at this ⊢
      rw [← assoc, ← this]
      have := ReflQuiv.adj.right_triangle_components C
      dsimp [ReflQuiv.forget] at this
      simp [reassoc_of% this]
  }

instance nerveFunctor₂.faithful : nerveFunctor₂.{u, u}.Faithful :=
  Functor.Faithful.of_comp_iso
    (G := oneTruncation₂) (H := ReflQuiv.forget) OneTruncation₂.ofNerve₂.natIso

instance nerveFunctor₂.full : nerveFunctor₂.{u, u}.Full where
  map_surjective := by
    intro X Y F
    let uF := SSet.oneTruncation₂.map F
    let uF' : X ⥤rq Y :=
      OneTruncation₂.ofNerve₂.natIso.inv.app X ≫ uF ≫ OneTruncation₂.ofNerve₂.natIso.hom.app Y
    have {a b c : X} (h : a ⟶ b) (k : b ⟶ c) :
        uF'.map (h ≫ k) = uF'.map h ≫ uF'.map k := by
      let hk := ComposableArrows.mk₂ h k
      let Fh : ComposableArrows Y 1 := F.app (op ⦋1⦌₂) (.mk₁ h)
      let Fk : ComposableArrows Y 1 := F.app (op ⦋1⦌₂) (.mk₁ k)
      let Fhk' : ComposableArrows Y 1 := F.app (op ⦋1⦌₂) (.mk₁ (h ≫ k))
      let Fhk : ComposableArrows Y 2 := F.app (op ⦋2⦌₂) hk
      have lem0 := congr_arg_heq (·.map' 0 1) (congr_fun (F.naturality δ0₂.op) hk)
      have lem1 := congr_arg_heq (·.map' 0 1) (congr_fun (F.naturality δ1₂.op) hk)
      have lem2 := congr_arg_heq (·.map' 0 1) (congr_fun (F.naturality δ2₂.op) hk)
      have eq0 : (nerveFunctor₂.obj X).map δ0₂.op hk = .mk₁ k := by
        apply ComposableArrows.ext₁ rfl rfl
        simp [nerveFunctor₂, SSet.truncation, forget₂, HasForget₂.forget₂]
      have eq2 : (nerveFunctor₂.obj X).map δ2₂.op hk = .mk₁ h := by
        apply ComposableArrows.ext₁ (by rfl) (by rfl)
        simp [nerveFunctor₂, SSet.truncation, forget₂, HasForget₂.forget₂]; rfl
      have eq1 : (nerveFunctor₂.obj X).map δ1₂.op hk = .mk₁ (h ≫ k) := by
        apply ComposableArrows.ext₁ (by rfl) (by rfl)
        simp [nerveFunctor₂, SSet.truncation, forget₂, HasForget₂.forget₂]; rfl
      dsimp at lem0 lem1 lem2
      rw [eq0] at lem0
      rw [eq1] at lem1
      rw [eq2] at lem2
      replace lem0 : HEq (uF'.map k) (Fhk.map' 1 2) := by
        refine HEq.trans (b := Fk.map' 0 1) ?_ lem0
        simp [uF', nerveFunctor₂, SSet.truncation, forget₂, HasForget₂.forget₂,
          ReflQuiv.comp_eq_comp, OneTruncation₂.nerveHomEquiv, Fk, uF]
      replace lem2 : HEq (uF'.map h) (Fhk.map' 0 1) := by
        refine HEq.trans (b := Fh.map' 0 1) ?_ lem2
        simp [uF', nerveFunctor₂, SSet.truncation, forget₂, HasForget₂.forget₂,
          ReflQuiv.comp_eq_comp, OneTruncation₂.nerveHomEquiv, Fk, uF, ComposableArrows.hom, Fh]
      replace lem1 : HEq (uF'.map (h ≫ k)) (Fhk.map' 0 2) := by
        refine HEq.trans (b := Fhk'.map' 0 1) ?_ lem1
        simp only [Nat.reduceAdd, id_eq, Int.reduceNeg, Int.cast_ofNat_Int, Int.reduceSub,
          Int.reduceAdd, Nat.cast_ofNat, Fin.zero_eta, Fin.isValue, Fin.mk_one,
          ComposableArrows.map', homOfLE_leOfHom, Fk, uF, Fh, uF']
        dsimp
        simp [uF', nerveFunctor₂, SSet.truncation, forget₂, HasForget₂.forget₂,
          ReflQuiv.comp_eq_comp, OneTruncation₂.nerveHomEquiv, Fk, uF, ComposableArrows.hom, Fhk']
      rw [Fhk.map'_comp 0 1 2] at lem1
      refine eq_of_heq (lem1.trans (heq_comp ?_ ?_ ?_ lem2.symm lem0.symm)) <;>
        simp [uF', nerveFunctor₂, SSet.truncation, forget₂, HasForget₂.forget₂,
          ReflQuiv.comp_eq_comp, OneTruncation₂.nerveHomEquiv, Fk, uF, Fhk] <;>
        [let ι := ι0₂; let ι := ι1₂; let ι := ι2₂] <;>
      · replace := congr_arg (·.obj 0) (congr_fun (F.naturality ι.op) hk)
        dsimp [oneTruncation₂, ComposableArrows.left, SimplicialObject.truncation,
          nerveFunctor₂, SSet.truncation, forget₂, HasForget₂.forget₂] at this ⊢
        convert this.symm
        apply ComposableArrows.ext₀; rfl
    let fF : X ⥤ Y := ReflPrefunctor.toFunctor uF' this
    have eq : fF.toReflPrefunctor = uF' := rfl
    refine ⟨fF, toNerve₂.ext (nerveFunctor₂.{u,u}.map fF) F ?_⟩
    · have nat := OneTruncation₂.ofNerve₂.natIso.hom.naturality fF
      simp at nat
      rw [eq] at nat
      simp [uF', uF] at nat
      exact (Iso.cancel_iso_hom_right (oneTruncation₂.map (nerveFunctor₂.map fF))
        (oneTruncation₂.map F) (OneTruncation₂.ofNerve₂.natIso.app Y)).mp nat

/-- The 2-truncated nerve functor is both full and faithful and thus is fully faithful. -/
noncomputable def nerveFunctor₂.fullyfaithful : nerveFunctor₂.FullyFaithful :=
  FullyFaithful.ofFullyFaithful nerveFunctor₂

instance nerve₂Adj.reflective : Reflective nerveFunctor₂.{u, u} :=
  Reflective.mk hoFunctor₂ nerve₂Adj

end

/-- The adjunction between the nerve functor and the homotopy category functor is, up to
isomorphism, the composite of the adjunctions `SSet.coskAdj 2` and `nerve₂Adj`. -/
noncomputable def nerveAdjunction : hoFunctor ⊣ nerveFunctor :=
  Adjunction.ofNatIsoRight ((SSet.coskAdj 2).comp nerve₂Adj) Nerve.cosk₂Iso.symm

/-- Repleteness exists for full and faithful functors but not fully faithful functors, which is
why we do this inefficiently. -/
instance nerveFunctor.faithful : nerveFunctor.{u, u}.Faithful :=
  have : (Nerve.nerveFunctor₂ ⋙ SSet.Truncated.cosk 2).Faithful :=
    Faithful.comp nerveFunctor₂ (SSet.Truncated.cosk 2)
  Functor.Faithful.of_iso Nerve.cosk₂Iso.symm

instance nerveFunctor.full : nerveFunctor.{u, u}.Full :=
  have : (Nerve.nerveFunctor₂ ⋙ SSet.Truncated.cosk 2).Full :=
    Full.comp nerveFunctor₂ (SSet.Truncated.cosk 2)
  Functor.Full.of_iso Nerve.cosk₂Iso.symm

/-- The nerve functor is both full and faithful and thus is fully faithful. -/
noncomputable def nerveFunctor.fullyfaithful : nerveFunctor.FullyFaithful :=
  FullyFaithful.ofFullyFaithful nerveFunctor

instance nerveAdjunction.isIso_counit : IsIso nerveAdjunction.counit :=
  Adjunction.counit_isIso_of_R_fully_faithful _

/-- The counit map of `nerveAdjunction` is an isomorphism since the nerve functor is fully
faithful. -/
noncomputable def nerveFunctorCompHoFunctorIso : nerveFunctor.{u, u} ⋙ hoFunctor ≅ 𝟭 Cat :=
  asIso (nerveAdjunction.counit)

noncomputable instance : Reflective nerveFunctor where
  L := hoFunctor
  adj := nerveAdjunction

end CategoryTheory
