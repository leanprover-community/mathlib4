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
`CategoryTheory.Category.Cat.Colimit` that the category of categories has colimits.

-/

namespace CategoryTheory

open Category Functor Limits Opposite SimplexCategory Simplicial SSet Nerve Truncated
universe v u

section

set_option quotPrecheck false
local macro:max (priority := high) "[" n:term "]₂" : term =>
  `((⟨SimplexCategory.mk $n, by decide⟩ : SimplexCategory.Truncated 2))

local macro:1000 (priority := high) X:term " _[" n:term "]₂" : term =>
    `(($X : SSet.Truncated 2).obj (Opposite.op ⟨SimplexCategory.mk $n, by decide⟩))

/-- The components of the counit of `nerve₂Adj`. -/
@[simps!]
def nerve₂Adj.counit.app (C : Type u) [SmallCategory C] :
    (nerveFunctor₂.obj (Cat.of C)).HomotopyCategory ⥤ C := by
  fapply Quotient.lift
  · exact
      (whiskerRight (OneTruncation₂.ofNerve₂.natIso).hom _ ≫ ReflQuiv.adj.{u}.counit).app (Cat.of C)
  · intro x y f g rel
    cases rel; rename_i φ
    simp [ReflQuiv.adj, Quot.liftOn, Cat.FreeRefl.quotientFunctor, Quotient.functor,
      Quiv.adj, Quiv.id_eq_id]
    simp only [OneTruncation₂.nerveHomEquiv, Fin.isValue, OneTruncation₂.nerveEquiv_apply, op_obj,
      ComposableArrows.obj', Fin.zero_eta, Nat.reduceAdd, Equiv.coe_fn_mk, eqToHom_refl, comp_id,
      id_comp]
    exact φ.map_comp (X := (0 : Fin 3)) (Y := 1) (Z := 2)
      (homOfLE (by decide)) (homOfLE (by decide))

@[simp]
theorem nerve₂Adj.counit.app_eq (C : Type u) [SmallCategory C] :
    SSet.Truncated.HomotopyCategory.quotientFunctor (nerveFunctor₂.obj (Cat.of C)) ⋙
      nerve₂Adj.counit.app.{u} C =
    (whiskerRight OneTruncation₂.ofNerve₂.natIso.hom _ ≫
      ReflQuiv.adj.{u}.counit).app (Cat.of C) := rfl

/-- Naturality of `nerve₂Adj.counit.app` is proven using `HomotopyCategory.lift_unique'`. -/
theorem nerve₂Adj.counit.naturality ⦃C D : Type u⦄ [SmallCategory C] [SmallCategory D]
    (F : C ⥤ D) :
    (nerveFunctor₂ ⋙ hoFunctor₂).map F ⋙ nerve₂Adj.counit.app D =
      nerve₂Adj.counit.app C ⋙ F := by
  apply HomotopyCategory.lift_unique'
  conv => lhs; rw [← Functor.assoc]; lhs; apply (hoFunctor₂_naturality _).symm
  simp only [Cat.freeRefl_obj_α, ReflQuiv.of_val, comp_obj, Functor.comp_map]
  rw [← Functor.assoc _ _ F]
  conv => rhs; lhs; exact (nerve₂Adj.counit.app_eq C)
  let F' : (Cat.of C) ⟶ (Cat.of D) := F
  conv => rhs; exact ((whiskerRight OneTruncation₂.ofNerve₂.natIso.hom Cat.freeRefl ≫
    ReflQuiv.adj.counit).naturality F').symm
  simp only [app, Cat.comp_eq_comp, Functor.comp_map, Functor.assoc,
    SSet.Truncated.HomotopyCategory.quotientFunctor]
  rw [Quotient.lift_spec]

/-- The counit of `nerve₂Adj.` -/
def nerve₂Adj.counit : nerveFunctor₂ ⋙ hoFunctor₂.{u} ⟶ (𝟭 Cat) where
  app := fun _ ↦ nerve₂Adj.counit.app (Cat.of _)
  naturality := fun _ _ F ↦ nerve₂Adj.counit.naturality F

local notation (priority := high) "[" n "]" => SimplexCategory.mk n

/-- Because nerves are 2-coskeletal, the components of a map of 2-truncated simplicial sets valued
in a nerve can be recovered from the underlying ReflPrefunctor. -/
def toNerve₂.mk.app {X : SSet.Truncated 2} {C : Type u} [SmallCategory C]
    (F : SSet.oneTruncation₂.obj X ⟶ ReflQuiv.of C)
    (n : SimplexCategory.Truncated 2) :
    X.obj (op n) ⟶ (nerveFunctor₂.obj (Cat.of C)).obj (op n) := by
  obtain ⟨n, hn⟩ := n
  induction' n using SimplexCategory.rec with n
  match n with
  | 0 => exact fun x => .mk₀ (F.obj x)
  | 1 => exact fun f => .mk₁ (F.map ⟨f, rfl, rfl⟩)
  | 2 => exact fun φ => .mk₂ (F.map (ev01₂ φ)) (F.map (ev12₂ φ))

@[simp] theorem toNerve₂.mk.app_zero {X : SSet.Truncated 2} {C : Type u} [SmallCategory C]
    (F : SSet.oneTruncation₂.obj X ⟶ ReflQuiv.of C) (x : X _[0]₂) :
    mk.app F [0]₂ x = .mk₀ (F.obj x) := rfl

@[simp] theorem toNerve₂.mk.app_one {X : SSet.Truncated 2} {C : Type u} [SmallCategory C]
    (F : SSet.oneTruncation₂.obj X ⟶ ReflQuiv.of C) (f : X _[1]₂) :
    mk.app F [1]₂ f = .mk₁ (F.map ⟨f, rfl, rfl⟩) := rfl

@[simp] theorem toNerve₂.mk.app_two {X : SSet.Truncated 2} {C : Type u} [SmallCategory C]
    (F : SSet.oneTruncation₂.obj X ⟶ ReflQuiv.of C) (φ : X _[2]₂) :
    mk.app F [2]₂ φ = .mk₂ (F.map (ev01₂ φ)) (F.map (ev12₂ φ)) := rfl

/-- This is similar to one of the famous Segal maps, except valued in a product rather than a
pullback.-/
noncomputable def nerve₂.seagull (C : Type u) [Category C] :
    (nerveFunctor₂.obj (Cat.of C)).obj (op [2]₂) ⟶
    (nerveFunctor₂.obj (Cat.of C)).obj (op [1]₂) ⨯ (nerveFunctor₂.obj (Cat.of C)).obj (op [1]₂) :=
  prod.lift
    ((nerveFunctor₂.obj (Cat.of C)).map (.op δ2₂)) ((nerveFunctor₂.obj (Cat.of C)).map (.op δ0₂))

instance (C : Type u) [Category C] : Mono (nerve₂.seagull C) where
  right_cancellation {X} (f g : X → ComposableArrows C 2) eq := by
    ext x
    simp [nerve₂.seagull] at eq
    have eq1 := congr($eq ≫ prod.fst)
    have eq2 := congr($eq ≫ prod.snd)
    simp at eq1 eq2
    replace eq1 := congr_fun eq1 x
    replace eq2 := congr_fun eq2 x
    simp at eq1 eq2
    generalize f x = fx at *
    generalize g x = gx at *
    fapply ComposableArrows.ext₂
    · exact congrArg (·.obj 0) <| eq1
    · exact congrArg (·.obj 1) <| eq1
    · exact congrArg (·.obj 1) <| eq2
    · exact (conj_eqToHom_iff_heq' _ _ _ _).2 (congr_arg_heq (·.hom) <| eq1)
    · exact (conj_eqToHom_iff_heq' _ _ _ _).2 (congr_arg_heq (·.hom) <| eq2)

/-- Naturality of the components defined by `toNerve₂.mk.app` as a morphism property of
maps in `SimplexCategory.Truncated 2).` -/
abbrev toNerve₂.mk.naturalityProperty {X : SSet.Truncated.{u} 2}  {C : Type u} [SmallCategory C]
    (F : SSet.oneTruncation₂.obj X ⟶ ReflQuiv.of C) :
    MorphismProperty (SimplexCategory.Truncated 2) :=
  (MorphismProperty.naturalityProperty (fun n => toNerve₂.mk.app F n.unop)).unop

lemma toNerve₂.mk_naturality_σ00 {X : SSet.Truncated.{u} 2}  {C : Type u} [SmallCategory C]
    (F : SSet.oneTruncation₂.obj X ⟶ ReflQuiv.of C) :
    toNerve₂.mk.naturalityProperty F (σ₂ (n := 0) 0) := by
  ext x
  dsimp only [Nat.reduceAdd, types_comp_apply, mk.app_one]
  fapply ComposableArrows.ext₁
  · simp only [ComposableArrows.mk₁_obj, ComposableArrows.Mk₁.obj]
    congr 1
    refine congr_fun (?_ : X.map _ ≫ X.map _ = 𝟙 _) x
    rw [← map_comp, ← map_id]; congr 1
    apply Quiver.Hom.unop_inj
    apply SimplexCategory.hom_zero_zero
  · simp only [ComposableArrows.mk₁_obj, ComposableArrows.Mk₁.obj]
    congr 1
    refine congr_fun (?_ : X.map _ ≫ X.map _ = 𝟙 _) x
    rw [← map_comp, ← map_id]; congr 1
    apply Quiver.Hom.unop_inj
    apply SimplexCategory.hom_zero_zero
  · refine eq_of_heq <|
      (?_ : HEq _ (ComposableArrows.mk₁ (C := C) (𝟙rq (F.obj x))).hom).trans ?_
    · have : ∀ x' a b (h1 : X.map (δ₂ 1).op x' = a) (h2 : X.map (δ₂ 0).op x' = b),
        x = a → x = b → x' = X.map (σ₂ (n := 0) 0).op x →
        HEq (ComposableArrows.mk₁ (C := C) (F.map ⟨x', h1, h2⟩)).hom
          (ComposableArrows.mk₁ (C := C) (𝟙rq (F.obj x))).hom := by
        rintro _ _ _ _ _ rfl rfl rfl
        exact congr_arg_heq (fun a => (ComposableArrows.mk₁ (C := C) a).hom) (F.map_id x)
      apply this
      · simp only [SimplexCategory.len_mk]
        refine congr_fun (?_ : X.map _ ≫ X.map _ = 𝟙 _).symm x
        rw [← map_comp, ← map_id]; congr 1
        exact Quiver.Hom.unop_inj (SimplexCategory.hom_zero_zero _)
      · simp only [SimplexCategory.len_mk]
        refine congr_fun (?_ : X.map _ ≫ X.map _ = 𝟙 _).symm x
        rw [← map_comp, ← map_id]; congr 1
        exact Quiver.Hom.unop_inj (SimplexCategory.hom_zero_zero _)
      · simp
    · simp; rfl

lemma toNerve₂.mk_naturality_δ0i {X : SSet.Truncated.{u} 2}  {C : Type u} [SmallCategory C]
    (F : SSet.oneTruncation₂.obj X ⟶ ReflQuiv.of C) (i : Fin 2) :
    toNerve₂.mk.naturalityProperty F (δ₂ i) := by
  ext x
  apply ComposableArrows.ext₀
  fin_cases i <;> rfl

lemma toNerve₂.mk_naturality_δ1i {X : SSet.Truncated.{u} 2}  {C : Type u} [SmallCategory C]
    (F : SSet.oneTruncation₂.obj X ⟶ ReflQuiv.of C)
    (hyp : (φ : X _[2]₂) →
      F.map (ev02₂ φ) =
        CategoryStruct.comp (obj := C) (F.map (ev01₂ φ)) (F.map (ev12₂ φ))) (i : Fin 3) :
    toNerve₂.mk.naturalityProperty F (δ₂ i) := by
  ext x
  simp only [types_comp_apply, mk.app_two, ComposableArrows.mk₂]
  fapply ComposableArrows.ext₁
  · simp only [mk.app_one, ComposableArrows.mk₁_obj, ComposableArrows.Mk₁.obj]
    fin_cases i <;> congr 1 <;> refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
      <;> rw [← map_comp] <;> (try rfl) <;>
    · rw [← op_comp]; congr 2
      ext ⟨j, hj⟩; match j with | 0 => rfl
  · simp only [mk.app_one, ComposableArrows.mk₁_obj, ComposableArrows.Mk₁.obj]
    fin_cases i <;>
    · congr 1
      refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
      rw [← map_comp]; rfl
  · dsimp only [nerveFunctor₂, SimplicialObject.truncation,
      SSet.truncation, comp_obj, nerveFunctor_obj,
      whiskeringLeft_obj_obj, Functor.comp_map, nerve_map,
      ComposableArrows.whiskerLeft_map, ComposableArrows.precomp_map,
      Nat.reduceAdd, mk.app_two, ComposableArrows.mk₂]
    have : ∀ {A B A' B' : OneTruncation₂ X} (x₁ : A ⟶ B) (x₂ : A' ⟶ B'),
        A = A' → B = B' → x₁.1 = x₂.1 → HEq (F.map x₁) (F.map x₂) := by
        rintro _ _ _ _ ⟨⟩ ⟨⟩ rfl rfl ⟨⟩; rfl
    fin_cases i <;> [
      show _ = _ ≫ ComposableArrows.Precomp.map _ _ ⟨1, _⟩ ⟨2, _⟩ _ ≫ _;
      show _ = _ ≫ ComposableArrows.Precomp.map _ _ ⟨0, _⟩ ⟨2, _⟩ _ ≫ _;
      show _ = _ ≫ ComposableArrows.Precomp.map _ _ ⟨0, _⟩ ⟨1, _⟩ _ ≫ _]
    all_goals
      rw [ComposableArrows.Precomp.map]
      apply (conj_eqToHom_iff_heq' ..).2
      dsimp only [Fin.isValue, Nat.reduceAdd, δ₂, ev1₂, homOfLE_leOfHom]
    · show HEq _ (F.map _)
      apply this
      · refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
        rw [← map_comp, ← op_comp]; congr 2
        ext (i : Fin 1); match i with | 0 => rfl
      · refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
        rw [← map_comp]; rfl
      · rfl
    · refine HEq.trans ?_ (heq_of_eq (hyp x))
      apply this
      · refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
        rw [← map_comp]; rfl
      · refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
        rw [← map_comp]; rfl
      · rfl
    · apply this
      · refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
        rw [← map_comp, ← op_comp]; congr 2
        ext (i : Fin 1); match i with | 0 => rfl
      · refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
        rw [← map_comp]; rfl
      · rfl

lemma toNerve₂.mk_naturality_σ1i {X : SSet.Truncated.{u} 2}  {C : Type u} [SmallCategory C]
    (F : SSet.oneTruncation₂.obj X ⟶ ReflQuiv.of C)
    (hyp : (φ : X _[2]₂) →
      F.map (ev02₂ φ) =
        CategoryStruct.comp (obj := C) (F.map (ev01₂ φ)) (F.map (ev12₂ φ))) (i : Fin 2) :
    toNerve₂.mk.naturalityProperty F (σ₂ i) := by
  apply (cancel_mono (nerve₂.seagull _)).1
  simp [nerve₂.seagull]
  congr 1 <;> rw [← map_comp, ← op_comp]
  · unfold δ2₂
    rw [← toNerve₂.mk_naturality_δ1i, ← assoc, ← map_comp, ← op_comp]
    change toNerve₂.mk.naturalityProperty F (δ₂ 2 ≫ σ₂ i)
    · fin_cases i
      · show mk.naturalityProperty F (δ₂ 2 ≫ σ₂ 0)
        rw [δ₂_two_comp_σ₂_zero]
        exact (toNerve₂.mk.naturalityProperty F).comp_mem _ _
          (toNerve₂.mk_naturality_σ00 F) (toNerve₂.mk_naturality_δ0i F _)
      · show mk.naturalityProperty F (δ₂ 2 ≫ σ₂ 1)
        rw [δ₂_two_comp_σ₂_one]
        exact (toNerve₂.mk.naturalityProperty F).id_mem _
    · exact hyp
  · unfold δ0₂
    rw [← toNerve₂.mk_naturality_δ1i, ← assoc, ← map_comp, ← op_comp]
    change toNerve₂.mk.naturalityProperty F (δ₂ 0 ≫ σ₂ i)
    · fin_cases i <;> dsimp only [Fin.zero_eta, Fin.isValue, Fin.mk_one]
      · rw [δ₂_zero_comp_σ₂_zero']
        exact (toNerve₂.mk.naturalityProperty F).id_mem _
      · rw [δ₂_zero_comp_σ₂_one]
        exact (toNerve₂.mk.naturalityProperty F).comp_mem _ _
          (toNerve₂.mk_naturality_σ00 F) (toNerve₂.mk_naturality_δ0i F _)
    · exact hyp

/-- A proof that the components defined by `toNerve₂.mk.app` are natural. -/
theorem toNerve₂.mk_naturality {X : SSet.Truncated.{u} 2} {C : Type u} [SmallCategory C]
    (F : SSet.oneTruncation₂.obj X ⟶ ReflQuiv.of C)
    (hyp : (φ : X _[2]₂) →
      F.map (ev02₂ φ) =
        CategoryStruct.comp (obj := C) (F.map (ev01₂ φ)) (F.map (ev12₂ φ))) :
    toNerve₂.mk.naturalityProperty F = ⊤ :=
  Truncated.morphismProperty_eq_top (toNerve₂.mk.naturalityProperty F)
    (fun
      | 0, _, _ => toNerve₂.mk_naturality_δ0i F _
      | 1, _, _ => toNerve₂.mk_naturality_δ1i F hyp _)
    (fun
      | 0, _, 0 => toNerve₂.mk_naturality_σ00 F
      | 1, _, _ => toNerve₂.mk_naturality_σ1i _ hyp _)

/-- Because nerves are 2-coskeletal, a map of 2-truncated simplicial sets valued in a nerve can be
recovered from the underlying ReflPrefunctor. -/
@[simps!]
def toNerve₂.mk {X : SSet.Truncated.{u} 2} {C : Type u} [SmallCategory C]
    (F : SSet.oneTruncation₂.obj X ⟶ ReflQuiv.of C)
    (hyp : (φ : X _[2]₂) →
      F.map (ev02₂ φ) =
        CategoryStruct.comp (obj := C) (F.map (ev01₂ φ)) (F.map (ev12₂ φ))) :
    X ⟶ nerveFunctor₂.obj (Cat.of C) where
  app := fun n => toNerve₂.mk.app F n.unop
  naturality _ _ f := MorphismProperty.of_eq_top (toNerve₂.mk_naturality F hyp) f.unop

/-- An alternate version of `toNerve₂.mk`, which constructs a map of 2-truncated simplicial sets
valued in a nerve  from the underlying ReflPrefunctor, where the central hypothesis is conjugated
by the isomorphism `nerve₂Adj.NatIso.app C`. -/
@[simps!] def toNerve₂.mk' {X : SSet.Truncated.{u} 2} {C : Type u} [SmallCategory C]
    (f : SSet.oneTruncation₂.obj X ⟶ SSet.oneTruncation₂.obj (nerveFunctor₂.obj (Cat.of C)))
    (hyp : (φ : X _[2]₂) →
      (f ≫ (OneTruncation₂.ofNerve₂.natIso.app (Cat.of C)).hom).map (ev02₂ φ)
      = CategoryStruct.comp (obj := (Cat.of C))
        ((f ≫ (OneTruncation₂.ofNerve₂.natIso.app (Cat.of C)).hom).map (ev01₂ φ))
        ((f ≫ (OneTruncation₂.ofNerve₂.natIso.app (Cat.of C)).hom).map (ev12₂ φ)))
    : X ⟶ nerveFunctor₂.obj (Cat.of C) :=
  toNerve₂.mk (f ≫ (OneTruncation₂.ofNerve₂.natIso.app (Cat.of C)).hom) hyp

/-- A computation about `toNerve₂.mk'`. -/
theorem oneTruncation₂_toNerve₂Mk' {X : SSet.Truncated 2} {C : Type u} [SmallCategory C]
    (f : SSet.oneTruncation₂.obj X ⟶ SSet.oneTruncation₂.obj (nerveFunctor₂.obj (Cat.of C)))
    (hyp : (φ : X _[2]₂) →
      (f ≫ (OneTruncation₂.ofNerve₂.natIso.app (Cat.of C)).hom).map (ev02₂ φ)
      = CategoryStruct.comp (obj := C)
        ((f ≫ (OneTruncation₂.ofNerve₂.natIso.app (Cat.of C)).hom).map (ev01₂ φ))
        ((f ≫ (OneTruncation₂.ofNerve₂.natIso.app (Cat.of C)).hom).map (ev12₂ φ))) :
    oneTruncation₂.map (toNerve₂.mk' f hyp) = f := by
  refine ReflPrefunctor.ext (fun _ ↦ ComposableArrows.ext₀ rfl)
    (fun X Y g ↦ eq_of_heq (heq_eqRec_iff_heq.2 <| heq_eqRec_iff_heq.2 ?_))
  simp [oneTruncation₂]
  have {A B A' B' : OneTruncation₂ (nerveFunctor₂.obj (Cat.of C))}
      : A = A' → B = B' → ∀ (x : A ⟶ B) (y : A' ⟶ B'), x.1 = y.1 → HEq x y := by
    rintro rfl rfl ⟨⟩ ⟨⟩ ⟨⟩; rfl
  apply this
  · exact ComposableArrows.ext₀ rfl
  · exact ComposableArrows.ext₀ rfl
  · simp
    fapply ComposableArrows.ext₁ <;> simp [ReflQuiv.comp_eq_comp]
    · rw [g.src_eq]; exact congr_arg (·.obj 0) (f.map g).src_eq.symm
    · rw [g.tgt_eq]; exact congr_arg (·.obj 1) (f.map g).tgt_eq.symm
    · refine (conj_eqToHom_iff_heq' _ _ _ _).2 ?_
      simp [OneTruncation₂.nerveHomEquiv]
      obtain ⟨g, rfl, rfl⟩ := g
      rfl

/-- An equality between maps into the 2-truncated nerve is detected by an equality beteween their
underlying refl prefunctors. -/
theorem toNerve₂.ext {X : SSet.Truncated 2} {C : Type u} [SmallCategory C]
    (f g : X ⟶ nerveFunctor₂.obj (Cat.of C))
    (hyp : SSet.oneTruncation₂.map f = SSet.oneTruncation₂.map g) : f = g := by
  have eq₀ x : f.app (op [0]₂) x = g.app (op [0]₂) x := congr(($hyp).obj x)
  have eq₁ x : f.app (op [1]₂) x = g.app (op [1]₂) x := congr((($hyp).map ⟨x, rfl, rfl⟩).1)
  ext ⟨⟨n, hn⟩⟩ x
  induction' n using SimplexCategory.rec with n
  match n with
  | 0 => apply eq₀
  | 1 => apply eq₁
  | 2 =>
    apply Functor.hext (fun i : Fin 3 => ?_) (fun (i j : Fin 3) k => ?_)
    · let pt : [0]₂ ⟶ [2]₂ := SimplexCategory.const _ _ i
      refine congr(($(congr_fun (f.naturality pt.op) x)).obj 0).symm.trans ?_
      refine .trans ?_ congr(($(congr_fun (g.naturality pt.op) x)).obj 0)
      exact congr($(eq₀ _).obj 0)
    · let ar : [1]₂ ⟶ [2]₂ := mkOfLe _ _ k.le
      have h1 := congr_arg_heq (fun x => x.map' 0 1) (congr_fun (f.naturality (op ar)) x)
      have h2 := congr_arg_heq (fun x => x.map' 0 1) (congr_fun (g.naturality (op ar)) x)
      exact h1.symm.trans <| .trans (congr_arg_heq (fun x => x.map' 0 1) (eq₁ _)) h2

end
end CategoryTheory
