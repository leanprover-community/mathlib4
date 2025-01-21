/-
Copyright (c) 2024 Mario Carneiro and Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl, Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat

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
def nerve₂Adj.counit.app (C : Cat.{u, u}) :
    (nerveFunctor₂.obj C).HomotopyCategory ⥤ C := by
  fapply Quotient.lift
  · exact (whiskerRight (OneTruncation₂.ofNerve₂.natIso).hom _ ≫ ReflQuiv.adj.{u}.counit).app C
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
theorem nerve₂Adj.counit.app_eq (C : Cat) :
    SSet.Truncated.HomotopyCategory.quotientFunctor (nerveFunctor₂.obj C) ⋙
      nerve₂Adj.counit.app.{u} C =
    (whiskerRight OneTruncation₂.ofNerve₂.natIso.hom _ ≫
      ReflQuiv.adj.{u}.counit).app C := rfl

/-- Naturality of `nerve₂Adj.counit.app` is proven using `HomotopyCategory.lift_unique'`. -/
theorem nerve₂Adj.counit.naturality ⦃C D : Cat.{u, u}⦄ (F : C ⟶ D) :
    (nerveFunctor₂ ⋙ hoFunctor₂).map F ⋙ nerve₂Adj.counit.app D =
      nerve₂Adj.counit.app C ⋙ F := by
  apply HomotopyCategory.lift_unique'
  have := hoFunctor₂_naturality (nerveFunctor₂.map F)
  conv => lhs; rw [← Functor.assoc]; lhs; apply this.symm
  simp only [Cat.freeRefl_obj_α, ReflQuiv.of_val, comp_obj, Functor.comp_map]
  rw [← Functor.assoc _ _ F]
  conv => rhs; lhs; exact (nerve₂Adj.counit.app_eq C)
  conv => rhs; exact ((whiskerRight OneTruncation₂.ofNerve₂.natIso.hom Cat.freeRefl ≫
    ReflQuiv.adj.counit).naturality F).symm
  simp only [app, Cat.comp_eq_comp, Functor.comp_map, Functor.assoc,
    SSet.Truncated.HomotopyCategory.quotientFunctor]
  rw [Quotient.lift_spec]

/-- The counit of `nerve₂Adj.` -/
def nerve₂Adj.counit : nerveFunctor₂ ⋙ hoFunctor₂.{u} ⟶ (𝟭 Cat) where
  app := nerve₂Adj.counit.app
  naturality := nerve₂Adj.counit.naturality

local notation (priority := high) "[" n "]" => SimplexCategory.mk n

/-- Because nerves are 2-coskeletal, the components of a map of 2-truncated simplicial sets valued
in a nerve can be recovered from the underlying ReflPrefunctor. -/
def toNerve₂.mk.app {X : SSet.Truncated 2} {C : Cat}
    (F : SSet.oneTruncation₂.obj X ⟶ ReflQuiv.of C)
    (n : SimplexCategory.Truncated 2) :
    X.obj (op n) ⟶ (nerveFunctor₂.obj C).obj (op n) := by
  obtain ⟨n, hn⟩ := n
  induction' n using SimplexCategory.rec with n
  match n with
  | 0 => exact fun x => .mk₀ (F.obj x)
  | 1 => exact fun f => .mk₁ (F.map ⟨f, rfl, rfl⟩)
  | 2 => exact fun φ => .mk₂ (F.map (ev01₂ φ)) (F.map (ev12₂ φ))

@[simp] theorem toNerve₂.mk.app_zero {X : SSet.Truncated 2} {C : Cat}
    (F : SSet.oneTruncation₂.obj X ⟶ ReflQuiv.of C) (x : X _[0]₂) :
    mk.app F [0]₂ x = .mk₀ (F.obj x) := rfl

@[simp] theorem toNerve₂.mk.app_one {X : SSet.Truncated 2} {C : Cat}
    (F : SSet.oneTruncation₂.obj X ⟶ ReflQuiv.of C) (f : X _[1]₂) :
    mk.app F [1]₂ f = .mk₁ (F.map ⟨f, rfl, rfl⟩) := rfl

@[simp] theorem toNerve₂.mk.app_two {X : SSet.Truncated 2} {C : Cat}
    (F : SSet.oneTruncation₂.obj X ⟶ ReflQuiv.of C) (φ : X _[2]₂) :
    mk.app F [2]₂ φ = .mk₂ (F.map (ev01₂ φ)) (F.map (ev12₂ φ)) := rfl

/-- This is similar to one of the famous Segal maps, except valued in a product rather than a
pullback.-/
noncomputable def nerve₂.seagull (C : Cat.{v, u}) :
    (nerveFunctor₂.obj C).obj (op [2]₂) ⟶
    (nerveFunctor₂.obj C).obj (op [1]₂) ⨯ (nerveFunctor₂.obj C).obj (op [1]₂) :=
  prod.lift ((nerveFunctor₂.obj C).map (.op δ2₂)) ((nerveFunctor₂.obj C).map (.op δ0₂))

instance (C : Cat) : Mono (nerve₂.seagull C) where
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

/-- Because nerves are 2-coskeletal, a map of 2-truncated simplicial sets valued in a nerve can be
recovered from the underlying ReflPrefunctor. -/
@[simps!]
def toNerve₂.mk {X : SSet.Truncated.{u} 2} {C : Cat}
    (F : SSet.oneTruncation₂.obj X ⟶ ReflQuiv.of C)
    (hyp : (φ : X _[2]₂) →
      F.map (ev02₂ φ) =
        CategoryStruct.comp (obj := C) (F.map (ev01₂ φ)) (F.map (ev12₂ φ)))
    : X ⟶ nerveFunctor₂.obj C where
      app := fun n => toNerve₂.mk.app F n.unop
      naturality := by
        rintro ⟨⟨m, hm⟩⟩ ⟨⟨n, hn⟩⟩ ⟨α : (⟨n, hn⟩ : SimplexCategory.Truncated 2) ⟶ ⟨m, hm⟩⟩
        rw [show Opposite.op α = α.op by rfl]
        induction' m using SimplexCategory.rec with m
        induction' n using SimplexCategory.rec with n
        dsimp at α ⊢
        let OK {n m hn hm} (f : (⟨[n], hn⟩ : SimplexCategory.Truncated 2) ⟶ ⟨[m], hm⟩) :=
          X.map f.op ≫ mk.app F ⟨[n], hn⟩ = mk.app F ⟨[m], hm⟩ ≫ (nerveFunctor₂.obj C).map f.op
        show OK α
        have fac : ∀ {n m hn hm} {α : (⟨[n], hn⟩ : SimplexCategory.Truncated 2) ⟶ ⟨[m], hm⟩} k hk
            {β : (⟨[n], hn⟩ : SimplexCategory.Truncated 2) ⟶ ⟨[k], hk⟩}
            {γ : (⟨[k], hk⟩ : SimplexCategory.Truncated 2) ⟶ ⟨[m], hm⟩},
            α = β ≫ γ → OK β → OK γ → OK α := by
          rintro _ _ _ _ _ k hk β γ rfl h1 h2
          dsimp only [OK] at h1 h2 ⊢
          rw [op_comp, map_comp, map_comp, assoc, h1, ← assoc, h2, assoc]
        have const10 (α : [1]₂ ⟶ [0]₂) : OK α := by
          ext x
          cases SimplexCategory.eq_const_to_zero α
          dsimp
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
              · rw [← eq_const_to_zero]
            · simp; rfl
        have const01 (α : [0]₂ ⟶ [1]₂) : OK α := by
          ext x
          apply ComposableArrows.ext₀
          simp only [SimplexCategory.len_mk]
          obtain ⟨i : Fin 2, rfl⟩ := exists_eq_const_of_zero α
          match i with
          | 0 =>
            revert x; intro f
            refine congrArg F.obj ?_
            refine eq_of_heq (congr_arg_heq (fun x => X.map (op x) f) (?_ : [0].const [1] 0 = δ₂ 1))
            ext i; match i with | 0 => rfl
          | 1 =>
            revert x; intro f
            refine congrArg F.obj ?_
            refine eq_of_heq (congr_arg_heq (fun x => X.map (op x) f) (?_ : [0].const [1] 1 = δ₂ 0))
            ext i; match i with | 0 => rfl
        have const02 (α : [0]₂ ⟶ [2]₂) : OK α := by
          ext x
          apply ComposableArrows.ext₀
          obtain ⟨i : Fin 3, rfl⟩ := exists_eq_const_of_zero α
          match i with
          | 0 =>
            revert x; intro f
            refine congrArg F.obj (?_ : _ = X.map _ _)
            refine eq_of_heq (congr_arg_heq (fun x => X.map (op x) f) (?_ : [0].const [2] 0 = ι0₂))
            ext i; match i with | 0 => rfl
          | 1 =>
            revert x; intro f
            refine congrArg F.obj ?_
            refine eq_of_heq (congr_arg_heq (fun x => X.map (op x) f) (?_ : [0].const [2] 1 = ι1₂))
            ext i; match i with | 0 => rfl
          | 2 =>
            revert x; intro f
            refine congrArg F.obj ?_
            refine eq_of_heq (congr_arg_heq (fun x => X.map (op x) f) (?_ : [0].const [2] 2 = ι2₂))
            ext i; match i with | 0 => rfl
        have nat1m {m hm} (α : [1]₂ ⟶ ⟨[m], hm⟩) : OK α := by
          match m with
          | 0 => apply const10
          | 1 =>
            match α, eq_of_one_to_one α with
            | _, .inr rfl =>
              dsimp [OK]
              rw [(_ : X.map _ = id), (_ : Prefunctor.map _ _ = id)]; rfl
              all_goals apply map_id
            | _, .inl ⟨i, rfl⟩ =>
              exact fac 0 (by decide) (const_fac_thru_zero ..) (const10 ..) (const01 ..)
          | 2 =>
            match α, eq_of_one_to_two α with
            | _, .inl rfl =>
              ext x
              simp only [types_comp_apply, mk.app_two, ComposableArrows.mk₂]
              fapply ComposableArrows.ext₁
              · simp only [mk.app_one, ComposableArrows.mk₁_obj, ComposableArrows.Mk₁.obj]
                congr 1
                refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
                rw [← map_comp, ← op_comp]; congr 2
                ext ⟨i, hi⟩; match i with | 0 => rfl
              · simp only [mk.app_one, ComposableArrows.mk₁_obj, ComposableArrows.Mk₁.obj]
                congr 1
                refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
                rw [← map_comp]; rfl
              · clear fac const01 const10 const02 OK
                dsimp only [nerveFunctor₂, SimplicialObject.truncation,
                  SSet.truncation, comp_obj, nerveFunctor_obj,
                  whiskeringLeft_obj_obj, Functor.comp_map, nerve_map,
                  ComposableArrows.whiskerLeft_map, ComposableArrows.precomp_map]
                show _ = _ ≫ ComposableArrows.Precomp.map _ _ ⟨1, _⟩ ⟨2, _⟩ _ ≫ _
                rw [ComposableArrows.Precomp.map]; dsimp
                apply (conj_eqToHom_iff_heq' ..).2
                dsimp only [Fin.isValue, Nat.reduceAdd, δ₂, ev1₂, homOfLE_leOfHom]
                have : ∀ {A B A' B' : OneTruncation₂ X} (x₁ : A ⟶ B) (x₂ : A' ⟶ B'),
                    A = A' → B = B' → x₁.1 = x₂.1 → HEq (F.map x₁) (F.map x₂) := by
                    rintro _ _ _ _ ⟨⟩ ⟨⟩ rfl rfl ⟨⟩; rfl
                apply this
                · refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
                  rw [← map_comp, ← op_comp]; congr 2
                  ext (i : Fin 1); match i with | 0 => rfl
                · refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
                  rw [← map_comp]; rfl
                · rfl
            | _, .inr (.inl rfl) =>
              ext x
              simp only [types_comp_apply, mk.app_two, ComposableArrows.mk₂]
              fapply ComposableArrows.ext₁
              · simp only [mk.app_one, ComposableArrows.mk₁_obj, ComposableArrows.Mk₁.obj]
                congr 1
                refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
                rw [← map_comp]; rfl
              · simp only [mk.app_one, ComposableArrows.mk₁_obj, ComposableArrows.Mk₁.obj]
                congr 1
                refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
                rw [← map_comp]; rfl
              · clear fac const01 const10 const02 OK
                dsimp only [nerveFunctor₂, SimplicialObject.truncation,
                  SSet.truncation, comp_obj, nerveFunctor_obj,
                  whiskeringLeft_obj_obj, Functor.comp_map, nerve_map,
                  ComposableArrows.whiskerLeft_map, ComposableArrows.precomp_map]
                show _ = _ ≫ ComposableArrows.Precomp.map _ _ ⟨0, _⟩ ⟨2, _⟩ _ ≫ _
                rw [ComposableArrows.Precomp.map]; dsimp
                apply (conj_eqToHom_iff_heq' ..).2
                dsimp only [Fin.isValue, Nat.reduceAdd, δ₂, ev1₂]
                have : ∀ {A B A' B' : OneTruncation₂ X} (x₁ : A ⟶ B) (x₂ : A' ⟶ B'),
                    A = A' → B = B' → x₁.1 = x₂.1 → HEq (F.map x₁) (F.map x₂) := by
                    rintro _ _ _ _ ⟨⟩ ⟨⟩ rfl rfl ⟨⟩; rfl
                refine HEq.trans ?_ (heq_of_eq (hyp x))
                apply this
                · refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
                  rw [← map_comp]; rfl
                · refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
                  rw [← map_comp]; rfl
                · rfl
            | _, .inr (.inr (.inl rfl)) =>
              ext x
              simp only [types_comp_apply, mk.app_two, ComposableArrows.mk₂]
              fapply ComposableArrows.ext₁
              · simp only [mk.app_one, ComposableArrows.mk₁_obj, ComposableArrows.Mk₁.obj]
                congr 1
                refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
                rw [← map_comp, ← op_comp]; congr 2
                ext ⟨i, hi⟩; match i with | 0 => rfl
              · simp only [mk.app_one, ComposableArrows.mk₁_obj, ComposableArrows.Mk₁.obj]
                congr 1
                refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
                rw [← map_comp]; rfl
              · clear fac const01 const10 const02 OK
                dsimp only [nerveFunctor₂, SimplicialObject.truncation,
                  SSet.truncation, comp_obj, nerveFunctor_obj,
                  whiskeringLeft_obj_obj, Functor.comp_map, nerve_map,
                  ComposableArrows.whiskerLeft_map, ComposableArrows.precomp_map]
                show _ = _ ≫ ComposableArrows.Precomp.map _ _ ⟨0, _⟩ ⟨1, _⟩ _ ≫ _
                rw [ComposableArrows.Precomp.map]; dsimp
                apply (conj_eqToHom_iff_heq' ..).2
                dsimp only [Fin.isValue, Nat.reduceAdd, δ₂, ev1₂]
                have : ∀ {A B A' B' : OneTruncation₂ X} (x₁ : A ⟶ B) (x₂ : A' ⟶ B'),
                    A = A' → B = B' → x₁.1 = x₂.1 → HEq (F.map x₁) (F.map x₂) := by
                    rintro _ _ _ _ ⟨⟩ ⟨⟩ rfl rfl ⟨⟩; rfl
                apply this
                · refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
                  rw [← map_comp, ← op_comp]; congr 2
                  ext (i : Fin 1); match i with | 0 => rfl
                · refine congr_fun (?_ : X.map _ ≫ X.map _ = _) x
                  rw [← map_comp]; rfl
                · rfl
            | _, .inr (.inr (.inr ⟨i, rfl⟩)) =>
              exact fac 0 (by decide) (const_fac_thru_zero ..) (const10 ..) (const02 ..)
        have nat2m (α : [2]₂ ⟶ ⟨[m], hm⟩) : OK α := by
          dsimp [OK]
          apply (cancel_mono (nerve₂.seagull _)).1
          simp [nerve₂.seagull]
          congr 1 <;> rw [← map_comp, ← op_comp, ← nat1m, ← nat1m, op_comp, map_comp, assoc]
        match n with
        | 0 =>
          match m with
          | 0 =>
            ext x
            simp [SimplexCategory.rec]
            apply ComposableArrows.ext₀
            simp only [ComposableArrows.obj', ComposableArrows.mk₀_obj]
            cases SimplexCategory.hom_zero_zero α
            congr 1
            exact congr_fun (X.map_id _) x
          | 1 => apply const01
          | 2 => apply const02
        | 1 => apply nat1m
        | 2 => apply nat2m

/-- We might prefer this version where we are using the analogue of the hypothesis hyp
conjugated by the isomorphism nerve₂Adj.NatIso.app C -/
@[simps!] def toNerve₂.mk' {X : SSet.Truncated.{u} 2} {C : Cat}
    (f : SSet.oneTruncation₂.obj X ⟶ SSet.oneTruncation₂.obj (nerveFunctor₂.obj C))
    (hyp : (φ : X _[2]₂) →
      (f ≫ (OneTruncation₂.ofNerve₂.natIso.app C).hom).map (ev02₂ φ)
      = CategoryStruct.comp (obj := C)
        ((f ≫ (OneTruncation₂.ofNerve₂.natIso.app C).hom).map (ev01₂ φ))
        ((f ≫ (OneTruncation₂.ofNerve₂.natIso.app C).hom).map (ev12₂ φ)))
    : X ⟶ nerveFunctor₂.obj C :=
  toNerve₂.mk (f ≫ (OneTruncation₂.ofNerve₂.natIso.app C).hom) hyp

/-- A computation about `toNerve₂.mk'`. -/
theorem oneTruncation₂_toNerve₂Mk' {X : SSet.Truncated 2} {C : Cat}
    (f : SSet.oneTruncation₂.obj X ⟶ SSet.oneTruncation₂.obj (nerveFunctor₂.obj C))
    (hyp : (φ : X _[2]₂) →
      (f ≫ (OneTruncation₂.ofNerve₂.natIso.app C).hom).map (ev02₂ φ)
      = CategoryStruct.comp (obj := C)
        ((f ≫ (OneTruncation₂.ofNerve₂.natIso.app C).hom).map (ev01₂ φ))
        ((f ≫ (OneTruncation₂.ofNerve₂.natIso.app C).hom).map (ev12₂ φ))) :
    oneTruncation₂.map (toNerve₂.mk' f hyp) = f := by
  refine ReflPrefunctor.ext (fun _ ↦ ComposableArrows.ext₀ rfl)
    (fun X Y g ↦ eq_of_heq (heq_eqRec_iff_heq.2 <| heq_eqRec_iff_heq.2 ?_))
  simp [oneTruncation₂]
  have {A B A' B' : OneTruncation₂ (nerveFunctor₂.obj C)}
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

/-- Now do a case split. For n = 0 and n = 1 this is covered by the hypothesis.
         For n = 2 this is covered by the new lemma above.-/
theorem toNerve₂.ext {X : SSet.Truncated 2} {C : Cat} (f g : X ⟶ nerveFunctor₂.obj C)
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

/-- ER: This is dumb. -/
theorem toNerve₂.ext' {X : SSet.Truncated 2} {C : Cat} (f g : X ⟶ nerveFunctor₂.obj C)
    (hyp : SSet.oneTruncation₂.map f = SSet.oneTruncation₂.map g) : f = g := by
  let f' : X ⟶ nerveFunctor₂.obj C := f
  let g' : X ⟶ nerveFunctor₂.obj C := g
  exact toNerve₂.ext f' g' hyp

/-- The components of the 2-truncated nerve adjunction unit. -/
def nerve₂Adj.unit.component (X : SSet.Truncated.{u} 2) :
    X ⟶ nerveFunctor₂.obj (hoFunctor₂.obj X) := by
  fapply toNerve₂.mk' (C := hoFunctor₂.obj X)
  · exact (ReflQuiv.adj.{u}.unit.app (SSet.oneTruncation₂.obj X) ⋙rq
    (SSet.Truncated.HomotopyCategory.quotientFunctor X).toReflPrefunctor ⋙rq
    (OneTruncation₂.ofNerve₂.natIso).inv.app (hoFunctor₂.obj X))
  · exact fun φ ↦ Quotient.sound _ (HoRel₂.mk φ)

theorem nerve₂Adj.unit.component_eq (X : SSet.Truncated.{u} 2) :
    SSet.oneTruncation₂.map (nerve₂Adj.unit.component X) =
    ReflQuiv.adj.{u}.unit.app (SSet.oneTruncation₂.obj X) ⋙rq
    (SSet.Truncated.HomotopyCategory.quotientFunctor X).toReflPrefunctor ⋙rq
    (OneTruncation₂.ofNerve₂.natIso).inv.app (hoFunctor₂.obj X) := by
  apply oneTruncation₂_toNerve₂Mk'

/-- The 2-truncated nerve adjunction unit. -/
def nerve₂Adj.unit : 𝟭 (SSet.Truncated.{u} 2) ⟶ hoFunctor₂ ⋙ nerveFunctor₂ where
  app := nerve₂Adj.unit.component
  naturality := by
    refine fun V W f ↦ toNerve₂.ext' (f ≫ nerve₂Adj.unit.component W)
      (nerve₂Adj.unit.component V ≫ nerveFunctor₂.map (hoFunctor₂.map f)) ?_
    rw [Functor.map_comp, Functor.map_comp, nerve₂Adj.unit.component_eq,
      nerve₂Adj.unit.component_eq]
    have nat₁ := (OneTruncation₂.ofNerve₂.natIso).inv.naturality (hoFunctor₂.map f)
    repeat rw [← ReflQuiv.comp_eq_comp (X := ReflQuiv.of _) (Y := ReflQuiv.of _)]
    repeat rw [assoc]
    simp at nat₁
    rw [← nat₁]
    rfl

/-- The adjunction between the 2-truncated nerve functor and the 2-truncated homotopy category
functor. -/
nonrec def nerve₂Adj : hoFunctor₂.{u} ⊣ nerveFunctor₂ := by
  refine Adjunction.mkOfUnitCounit {
    unit := nerve₂Adj.unit
    counit := nerve₂Adj.counit
    left_triangle := ?_
    right_triangle := ?_
  }
  · ext X
    apply HomotopyCategory.lift_unique'
    simp only [id_obj, Cat.freeRefl_obj_α, ReflQuiv.of_val, comp_obj, NatTrans.comp_app,
      whiskerRight_app, associator_hom_app, whiskerLeft_app, id_comp, NatTrans.id_app']
    show _ = _ ⋙ (𝟭 X.HomotopyCategory)
    rw [Functor.comp_id, Cat.comp_eq_comp, ← Functor.assoc]
    conv =>
      lhs; lhs; apply (hoFunctor₂_naturality (nerve₂Adj.unit.component X)).symm
    simp only [comp_obj, Cat.freeRefl_obj_α, Functor.comp_map]
    rw [nerve₂Adj.unit.component_eq X, Functor.assoc]
    conv =>
      lhs; rhs
      apply (nerve₂Adj.counit.app_eq (hoFunctor₂.obj X))
    simp only [comp_obj, ReflQuiv.forget_obj, Cat.freeRefl_obj_α, ReflQuiv.of_val,
      ReflPrefunctor.comp_assoc, NatTrans.comp_app, id_obj, whiskerRight_app]
    rw [← Cat.comp_eq_comp, ← assoc, ← Cat.freeRefl.map_comp, ReflQuiv.comp_eq_comp,
      ReflPrefunctor.comp_assoc]
    simp only [ReflQuiv.forget_obj, Cat.freeRefl_obj_α, ReflQuiv.of_val, ReflPrefunctor.comp_assoc]
    rw [← ReflQuiv.comp_eq_comp]
    simp only [ReflQuiv.forget_obj, comp_obj, Iso.inv_hom_id_app]
    rw [ReflQuiv.id_eq_id]
    simp_rw [ReflPrefunctor.comp_id
      (U := ReflQuiv.of _) (V := ReflQuiv.of ↑(hoFunctor₂.obj X))
      ((SSet.Truncated.HomotopyCategory.quotientFunctor X).toReflPrefunctor)]
    rw [← ReflQuiv.comp_eq_comp (Z := ReflQuiv.of _)
      (ReflQuiv.adj.{u}.unit.app (SSet.oneTruncation₂.obj X))
      ((SSet.Truncated.HomotopyCategory.quotientFunctor X).toReflPrefunctor)]
    simp only [ReflQuiv.forget_obj, Cat.freeRefl_obj_α, ReflQuiv.of_val, map_comp, assoc]
    have nat := ReflQuiv.adj.counit.naturality
      (X := Cat.freeRefl.obj (ReflQuiv.of (OneTruncation₂ X)))
      (Y := hoFunctor₂.obj X) (SSet.Truncated.HomotopyCategory.quotientFunctor X)
    dsimp at nat
    rw [nat, ← assoc]
    conv => lhs; lhs; apply ReflQuiv.adj.left_triangle_components (SSet.oneTruncation₂.obj X)
    simp
  · refine NatTrans.ext (funext fun C ↦ ?_)
    simp only [comp_obj, id_obj, NatTrans.comp_app, whiskerLeft_app, associator_inv_app,
      whiskerRight_app, id_comp, NatTrans.id_app']
    apply toNerve₂.ext
    simp only [map_comp, map_id]
    rw [nerve₂Adj.unit, nerve₂Adj.unit.component_eq]
    simp only [comp_obj, ReflQuiv.forget_obj, Cat.freeRefl_obj_α, ReflQuiv.of_val,
      ReflPrefunctor.comp_assoc]
    rw [← ReflQuiv.comp_eq_comp, ← ReflQuiv.comp_eq_comp (X := ReflQuiv.of _) (Y := ReflQuiv.of _)
      (Z := ReflQuiv.of _), assoc, assoc, ← Functor.comp_map,
        ← OneTruncation₂.ofNerve₂.natIso.inv.naturality]
    conv => lhs; rhs; rw [← assoc]
    show _ ≫ (ReflQuiv.forget.map _ ≫ ReflQuiv.forget.map _) ≫ _ = _
    rw [← ReflQuiv.forget.map_comp]
    rw [nerve₂Adj.counit]
    simp only [oneTruncation₂_obj, ReflQuiv.forget_obj, Cat.freeRefl_obj_α, ReflQuiv.of_val]
    have := nerve₂Adj.counit.app_eq C
    conv => lhs; rhs; lhs; rw [Cat.comp_eq_comp]
    rw [nerve₂Adj.counit.app_eq]
    simp only [ReflQuiv.forget_obj, Cat.freeRefl_obj_α, ReflQuiv.of_val, NatTrans.comp_app,
      comp_obj, id_obj, whiskerRight_app]
    rw [ReflQuiv.forget.map_comp, ← Functor.comp_map, ← assoc, ← assoc]
    have := ReflQuiv.adj.unit.naturality (OneTruncation₂.ofNerve₂.natIso.hom.app C)
    simp only [Functor.comp_obj] at this
    conv => lhs; lhs; lhs; apply this.symm
    simp only [Cat.freeRefl_obj_α, id_obj, Functor.id_map]
    slice_lhs 2 3 => rw [ReflQuiv.adj.right_triangle_components C]
    simp

instance nerveFunctor₂.faithful : nerveFunctor₂.{u, u}.Faithful := by
  exact Functor.Faithful.of_comp_iso
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
      let Fh : ComposableArrows Y 1 := F.app (op [1]₂) (.mk₁ h)
      let Fk : ComposableArrows Y 1 := F.app (op [1]₂) (.mk₁ k)
      let Fhk' : ComposableArrows Y 1 := F.app (op [1]₂) (.mk₁ (h ≫ k))
      let Fhk : ComposableArrows Y 2 := F.app (op [2]₂) hk
      have lem0 := congr_fun (F.naturality δ0₂.op) hk
      have lem1 := congr_fun (F.naturality δ1₂.op) hk
      have lem2 := congr_fun (F.naturality δ2₂.op) hk
      replace lem0 := congr_arg_heq (·.map' 0 1) lem0
      replace lem1 := congr_arg_heq (·.map' 0 1) lem1
      replace lem2 := congr_arg_heq (·.map' 0 1) lem2
      have eq0 : (nerveFunctor₂.obj X).map δ0₂.op hk = .mk₁ k := by
        apply ComposableArrows.ext₁ rfl rfl
        simp [nerveFunctor₂, SSet.truncation, forget₂, HasForget₂.forget₂]
      have eq2 : (nerveFunctor₂.obj X).map δ2₂.op hk = .mk₁ h := by
        apply ComposableArrows.ext₁ (by rfl) (by rfl)
        simp [nerveFunctor₂, SSet.truncation, forget₂, HasForget₂.forget₂]; rfl
      have eq1 : (nerveFunctor₂.obj X).map δ1₂.op hk = .mk₁ (h ≫ k) := by
        apply ComposableArrows.ext₁ (by rfl) (by rfl)
        simp [nerveFunctor₂, SSet.truncation, forget₂, HasForget₂.forget₂]; rfl
      simp at lem0 lem1 lem2
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
          ReflQuiv.comp_eq_comp, OneTruncation₂.nerveHomEquiv, Fk, uF]
      replace lem1 : HEq (uF'.map (h ≫ k)) (Fhk.map' 0 2) := by
        refine HEq.trans (b := Fhk'.map' 0 1) ?_ lem1
        simp [uF', nerveFunctor₂, SSet.truncation, forget₂, HasForget₂.forget₂,
          ReflQuiv.comp_eq_comp, OneTruncation₂.nerveHomEquiv, Fk, uF]
      rw [Fhk.map'_comp 0 1 2] at lem1
      refine eq_of_heq (lem1.trans (heq_comp ?_ ?_ ?_ lem2.symm lem0.symm))
      · simp [uF', nerveFunctor₂, SSet.truncation, forget₂, HasForget₂.forget₂,
          ReflQuiv.comp_eq_comp, OneTruncation₂.nerveHomEquiv, Fk, uF, Fhk]
        have := congr_arg (·.obj 0) (congr_fun (F.naturality ι0₂.op) hk)
        dsimp [oneTruncation₂, ComposableArrows.left, SimplicialObject.truncation,
          nerveFunctor₂, SSet.truncation, forget₂, HasForget₂.forget₂] at this ⊢
        convert this.symm
        apply ComposableArrows.ext₀; rfl
      · simp [uF', nerveFunctor₂, SSet.truncation, forget₂, HasForget₂.forget₂,
          ReflQuiv.comp_eq_comp, OneTruncation₂.nerveHomEquiv, Fk, uF, Fhk]
        have := congr_arg (·.obj 0) (congr_fun (F.naturality ι1₂.op) hk)
        dsimp [oneTruncation₂, ComposableArrows.left, SimplicialObject.truncation,
          nerveFunctor₂, SSet.truncation, forget₂, HasForget₂.forget₂] at this ⊢
        convert this.symm
        apply ComposableArrows.ext₀; rfl
      · simp [uF', nerveFunctor₂, SSet.truncation, forget₂, HasForget₂.forget₂,
          ReflQuiv.comp_eq_comp, OneTruncation₂.nerveHomEquiv, Fk, uF, Fhk]
        have := congr_arg (·.obj 0) (congr_fun (F.naturality ι2₂.op) hk)
        dsimp [oneTruncation₂, ComposableArrows.left, SimplicialObject.truncation,
          nerveFunctor₂, SSet.truncation, forget₂, HasForget₂.forget₂] at this ⊢
        convert this.symm
        apply ComposableArrows.ext₀; rfl
    let fF : X ⥤ Y := ReflPrefunctor.toFunctor uF' this
    have eq : fF.toReflPrefunctor = uF' := rfl
    refine ⟨fF, toNerve₂.ext' (nerveFunctor₂.map fF) F ?_⟩
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

instance nerveCounit_isIso : IsIso nerveAdjunction.counit :=
  Adjunction.counit_isIso_of_R_fully_faithful _

/-- The counit map of `nerveAdjunction` is an isomorphism since the nerve functor is fully
faithful. -/
noncomputable def nerveCounitNatIso : nerveFunctor.{u, u} ⋙ hoFunctor ≅ 𝟭 Cat :=
  asIso (nerveAdjunction.counit)

noncomputable instance : Reflective nerveFunctor where
  L := hoFunctor
  adj := nerveAdjunction

end CategoryTheory
