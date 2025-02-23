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
universe v u v' u'

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
    obtain ⟨φ⟩ := rel
    simpa [ReflQuiv.adj, Quot.liftOn, Cat.FreeRefl.quotientFunctor, Quotient.functor,
        Quiv.adj, OneTruncation₂.nerveHomEquiv] using
      φ.map_comp (X := 0) (Y := 1) (Z := 2) (homOfLE (by decide)) (homOfLE (by decide))

@[simp]
theorem nerve₂Adj.counit.app_eq (C : Type u) [SmallCategory C] :
    SSet.Truncated.HomotopyCategory.quotientFunctor (nerveFunctor₂.obj (Cat.of C)) ⋙
      nerve₂Adj.counit.app.{u} C =
    (whiskerRight OneTruncation₂.ofNerve₂.natIso.hom _ ≫
      ReflQuiv.adj.{u}.counit).app (Cat.of C) := rfl

/-- Naturality of `nerve₂Adj.counit.app` is proven using `HomotopyCategory.lift_unique'`. -/
theorem nerve₂Adj.counit.naturality {C D : Type u} [SmallCategory C] [SmallCategory D]
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
  app C := nerve₂Adj.counit.app (Cat.of C)
  naturality _ _ F := nerve₂Adj.counit.naturality F

local notation (priority := high) "[" n "]" => SimplexCategory.mk n

variable {C : Type u} [SmallCategory C] {X : SSet.Truncated.{u} 2}
    (F : SSet.oneTruncation₂.obj X ⟶ ReflQuiv.of C)

/-- Because nerves are 2-coskeletal, the components of a map of 2-truncated simplicial sets valued
in a nerve can be recovered from the underlying ReflPrefunctor. -/
def toNerve₂.mk.app (n : SimplexCategory.Truncated 2) :
    X.obj (op n) ⟶ (nerveFunctor₂.obj (Cat.of C)).obj (op n) := by
  obtain ⟨n, hn⟩ := n
  induction' n using SimplexCategory.rec with n
  match n with
  | 0 => exact fun x => .mk₀ (F.obj x)
  | 1 => exact fun f => .mk₁ (F.map ⟨f, rfl, rfl⟩)
  | 2 => exact fun φ => .mk₂ (F.map (ev01₂ φ)) (F.map (ev12₂ φ))

@[simp] theorem toNerve₂.mk.app_zero (x : X _[0]₂) : mk.app F [0]₂ x = .mk₀ (F.obj x) := rfl

@[simp] theorem toNerve₂.mk.app_one (f : X _[1]₂) :
    mk.app F [1]₂ f = .mk₁ (F.map ⟨f, rfl, rfl⟩) := rfl

@[simp] theorem toNerve₂.mk.app_two (φ : X _[2]₂) :
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
    simp only [limit.lift_π, BinaryFan.mk_fst, BinaryFan.mk_snd] at eq1 eq2
    replace eq1 := congr_fun eq1 x
    replace eq2 := congr_fun eq2 x
    simp only [types_comp_apply] at eq1 eq2
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
abbrev toNerve₂.mk.naturalityProperty : MorphismProperty (SimplexCategory.Truncated 2) :=
  (MorphismProperty.naturalityProperty (fun n => toNerve₂.mk.app F n.unop)).unop

lemma nerve.σ_zero_eq_mk_id (x : C) : (nerve C).σ (0 : Fin 1) (.mk₀ x) = .mk₁ (𝟙 x) :=
  ComposableArrows.ext₁ rfl rfl (by simp; rfl)

lemma ReflPrefunctor.congr_mk₁_map
    {Y : Type u'} [ReflQuiver.{v'} Y] {C : Type u} [Category.{v} C]
    (F : ReflPrefunctor Y (ReflQuiv.of C))
    {x₁ y₁ x₂ y₂ : Y} (f : x₁ ⟶ y₁) (g : x₂ ⟶ y₂)
    (hx : x₁ = x₂) (hy : y₁ = y₂) (hfg : Quiver.homOfEq f hx hy = g) :
    ComposableArrows.mk₁ (C := C) (F.map f) = ComposableArrows.mk₁ (C := C) (F.map g) := by
  subst hx hy hfg; rfl

lemma toNerve₂.mk_naturality_σ00 : toNerve₂.mk.naturalityProperty F (σ₂ (n := 0) 0) := by
  ext x
  refine Eq.trans ?_ (nerve.σ_zero_eq_mk_id (C := C) (F.obj x)).symm
  have := ReflPrefunctor.map_id F x
  dsimp at this ⊢
  rw [← this, ← OneTruncation₂.id_edge x]
  fapply ReflPrefunctor.congr_mk₁_map
  · simp [← FunctorToTypes.map_comp_apply, ← op_comp]
  · simp [← FunctorToTypes.map_comp_apply, ← op_comp]
  · aesop

lemma toNerve₂.mk_naturality_δ0i (i : Fin 2) : toNerve₂.mk.naturalityProperty F (δ₂ i) := by
  ext x
  apply ComposableArrows.ext₀
  fin_cases i <;> rfl

section
variable {X₀ X₁ X₂ : C} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂)

theorem nerve_δ22 : (nerve C).map (δ 2).op (ComposableArrows.mk₂ f g) = ComposableArrows.mk₁ f :=
  ComposableArrows.ext₁ rfl rfl (by simp; rfl)

theorem nerve_δ20 : (nerve C).map (δ 0).op (ComposableArrows.mk₂ f g) = ComposableArrows.mk₁ g :=
  ComposableArrows.ext₁ rfl rfl (by simp; rfl)

theorem nerve_δ21 : (nerve C).map (δ 1).op (ComposableArrows.mk₂ f g) =
    ComposableArrows.mk₁ (f ≫ g) :=
  ComposableArrows.ext₁ rfl rfl (by simp; rfl)

end

section
variable
  (hyp : ∀ φ, F.map (ev02₂ φ) = CategoryStruct.comp (obj := C) (F.map (ev01₂ φ)) (F.map (ev12₂ φ)))
include hyp

lemma toNerve₂.mk_naturality_δ1i (i : Fin 3) : toNerve₂.mk.naturalityProperty F (δ₂ i) := by
  ext x
  simp only [types_comp_apply, mk.app_two, ComposableArrows.mk₂]
  rw [toNerve₂.mk.app_one]
  unfold nerveFunctor₂ truncation SimplicialObject.truncation
  simp only [comp_obj, nerveFunctor_obj, Cat.of_α, whiskeringLeft_obj_obj, id_eq, op_obj,
    nerve_obj, oneTruncation₂_obj, ReflQuiv.of_val, Nat.reduceAdd, mk.app_two,
    Functor.comp_map, op_map, Quiver.Hom.unop_op]
  unfold δ₂ inclusion
  simp only [fullSubcategoryInclusion.map]
  fin_cases i
  · simp only [Fin.zero_eta]
    rw [nerve_δ20]
    fapply ReflPrefunctor.congr_mk₁_map
    · unfold ev1₂ ι1₂ δ₂
      simp only [← FunctorToTypes.map_comp_apply, ← op_comp]
      have := δ_comp_δ (n := 0) (i := 0) (j := 1) (by decide)
      dsimp at this
      exact congrFun (congrArg X.map (congrArg Quiver.Hom.op this.symm)) x
    · unfold ev2₂ ι2₂ δ₂
      simp only [← FunctorToTypes.map_comp_apply, ← op_comp]
      have := δ_comp_δ (n := 0) (i := 0) (j := 0) (by decide)
      dsimp at this
      exact congrFun (congrArg X.map (congrArg Quiver.Hom.op this.symm)) x
    · aesop
  · simp only [Fin.mk_one]
    rw [nerve_δ21]
    rw [← hyp]
    fapply ReflPrefunctor.congr_mk₁_map
    · unfold ev0₂ ι0₂ δ₂
      simp [← FunctorToTypes.map_comp_apply, ← op_comp]
    · unfold ev2₂ ι2₂ δ₂
      simp [← FunctorToTypes.map_comp_apply, ← op_comp]
    · aesop
  · simp only [Fin.reduceFinMk]
    rw [nerve_δ22]
    fapply ReflPrefunctor.congr_mk₁_map
    · unfold ev0₂ ι0₂ δ₂
      simp only [← FunctorToTypes.map_comp_apply, ← op_comp]
      have := δ_comp_δ (n := 0) (i := 1) (j := 1) (by decide)
      dsimp at this
      exact congrFun (congrArg X.map (congrArg Quiver.Hom.op this)) x
    · unfold ev1₂ ι1₂ δ₂
      simp [← FunctorToTypes.map_comp_apply, ← op_comp]
    · aesop

lemma toNerve₂.mk_naturality_σ1i (i : Fin 2) : toNerve₂.mk.naturalityProperty F (σ₂ i) := by
  apply (cancel_mono (nerve₂.seagull _)).1
  simp [nerve₂.seagull]
  congr 1 <;> rw [← map_comp, ← op_comp]
  · unfold δ2₂
    rw [← toNerve₂.mk_naturality_δ1i F hyp, ← assoc, ← map_comp, ← op_comp]
    change toNerve₂.mk.naturalityProperty F (δ₂ 2 ≫ σ₂ i)
    fin_cases i
    · dsimp only [Fin.zero_eta]
      rw [δ₂_two_comp_σ₂_zero]
      exact (toNerve₂.mk.naturalityProperty F).comp_mem _ _
        (toNerve₂.mk_naturality_σ00 F) (toNerve₂.mk_naturality_δ0i F _)
    · dsimp only [Fin.mk_one]
      rw [δ₂_two_comp_σ₂_one]
      exact (toNerve₂.mk.naturalityProperty F).id_mem _
  · unfold δ0₂
    rw [← toNerve₂.mk_naturality_δ1i F hyp, ← assoc, ← map_comp, ← op_comp]
    change toNerve₂.mk.naturalityProperty F (δ₂ 0 ≫ σ₂ i)
    fin_cases i <;> dsimp only [Fin.zero_eta, Fin.isValue, Fin.mk_one]
    · rw [δ₂_zero_comp_σ₂_zero]
      exact (toNerve₂.mk.naturalityProperty F).id_mem _
    · rw [δ₂_zero_comp_σ₂_one]
      exact (toNerve₂.mk.naturalityProperty F).comp_mem _ _
        (toNerve₂.mk_naturality_σ00 F) (toNerve₂.mk_naturality_δ0i F _)

/-- A proof that the components defined by `toNerve₂.mk.app` are natural. -/
theorem toNerve₂.mk_naturality : toNerve₂.mk.naturalityProperty F = ⊤ :=
  Truncated.morphismProperty_eq_top (toNerve₂.mk.naturalityProperty F)
    (fun
      | 0, _, _ => toNerve₂.mk_naturality_δ0i F _
      | 1, _, _ => toNerve₂.mk_naturality_δ1i F hyp _)
    (fun
      | 0, _, 0 => toNerve₂.mk_naturality_σ00 F
      | 1, _, _ => toNerve₂.mk_naturality_σ1i F hyp _)

/-- Because nerves are 2-coskeletal, a map of 2-truncated simplicial sets valued in a nerve can be
recovered from the underlying ReflPrefunctor. -/
@[simps!]
def toNerve₂.mk : X ⟶ nerveFunctor₂.obj (Cat.of C) where
  app := fun n => toNerve₂.mk.app F n.unop
  naturality _ _ f := MorphismProperty.of_eq_top (toNerve₂.mk_naturality F hyp) f.unop

end

/-- An alternate version of `toNerve₂.mk`, which constructs a map of 2-truncated simplicial sets
valued in a nerve  from the underlying ReflPrefunctor, where the central hypothesis is conjugated
by the isomorphism `nerve₂Adj.NatIso.app C`. -/
@[simps!] def toNerve₂.mk'
    (f : SSet.oneTruncation₂.obj X ⟶ SSet.oneTruncation₂.obj (nerveFunctor₂.obj (Cat.of C)))
    (hyp : (φ : X _[2]₂) →
      (f ≫ (OneTruncation₂.ofNerve₂.natIso.app (Cat.of C)).hom).map (ev02₂ φ) =
      CategoryStruct.comp (obj := (Cat.of C))
        ((f ≫ (OneTruncation₂.ofNerve₂.natIso.app (Cat.of C)).hom).map (ev01₂ φ))
        ((f ≫ (OneTruncation₂.ofNerve₂.natIso.app (Cat.of C)).hom).map (ev12₂ φ)))
    : X ⟶ nerveFunctor₂.obj (Cat.of C) :=
  toNerve₂.mk (f ≫ (OneTruncation₂.ofNerve₂.natIso.app (Cat.of C)).hom) hyp

/-- A computation about `toNerve₂.mk'`. -/
theorem oneTruncation₂_toNerve₂Mk'
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
theorem toNerve₂.ext
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
