/-
Copyright (c) 2024 Charlie Conneen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Conneen
-/
import Mathlib.CategoryTheory.Monoidal.OfHasFiniteProducts
import Mathlib.CategoryTheory.Topos.Basic

/-!
# Exponential Objects

Proves that a topos has exponential objects (internal homs).
Consequently, every topos is Cartesian closed.

## Main definitions

* `Hom A B` is the exponential object, and `eval A B` is the associated
  "evaluation map" `A ⨯ Hom A B ⟶ B`.

* `IsExponentialObject` says what it means to be an exponential object.

## Main results

* `ToposHasExponentials` shows that a topos has exponential objects.
  This is done by showing `IsExponentialObject (eval A B)`.

* `ExpAdjEquiv` exhibits `(A ⨯ X ⟶ B) ≃ (X ⟶ Hom A B)` for any `A B X : C`
  in a topos `C`.

## References

* [S. MacLane and I. Moerdijk, *Sheaves in Geometry and Logic*][MLM92]

-/

open CategoryTheory Category Limits Classifier Power Topos

universe u v

variable {C : Type u} [Category.{v} C] [Topos C]

namespace CategoryTheory.Topos

noncomputable section

/-- The exponential object B^A. -/
def Hom (A B : C) : C :=
  pullback
    ((((prod.associator _ _ _).inv ≫ in_ (B ⨯ A))^ ≫ Predicate.isSingleton B)^)
    ⌈Predicate.true_ A⌉

/-- The map which sends `A ⟶ B` to its graph as a subobject of `B ⨯ A`. -/
def Hom_toGraph (A B : C) : Hom A B ⟶ Pow (B ⨯ A) := pullback.fst _ _

/-- The map sending a morphism to its graph is a monomorphism, so that
the graphs of morphisms `A ⟶ B` may be regarded as subobjects of `B ⨯ A`.
-/
instance Hom_toGraph_Mono {A B : C} : Mono (Hom_toGraph A B) := pullback.fst_of_mono

/-- Convenience lemma used in `Hom_comm`. -/
lemma ExpConeSnd_Terminal (A B : C) :
    pullback.snd _ _ = terminal.from (Hom A B) := Unique.eq_default _

/-- Convenience lemma used in `EvalDef_comm`. -/
lemma Hom_comm (A B : C) :
    Hom_toGraph A B ≫ ((((prod.associator _ _ _).inv ≫ in_ (B ⨯ A))^ ≫ Predicate.isSingleton B)^)
    = terminal.from (Hom A B) ≫ ⌈Predicate.true_ A⌉ := by
  rw [←ExpConeSnd_Terminal]; exact pullback.condition

/-- This lemma states that the following diagram commutes:
```
    A ⨯ Hom A B ---------terminal.from _----------> ⊤_ C
      |                                               |
      |                                               |
(𝟙 A) ⨯ Hom_toGraph A B                              t C
      |                                               |
      |                                               |
      v                                               v
    A ⨯ Pow (B ⨯ A) ------------u-------------------> Ω
```
where `u` intuitively is the predicate:
(a,S) ↦ "there is exactly one b in B such that (b,a) in S".
This is used to define the map `eval A B : A ⨯ Hom A B ⟶ B`
as a `pullback.lift` where the object `B` serves as the pullback.
-/
lemma evalDef_comm (A B : C) :
  (prod.map (𝟙 A) (Hom_toGraph A B)
  ≫ ((prod.associator _ _ _).inv ≫ in_ (B ⨯ A))^) ≫ Predicate.isSingleton B
  = Predicate.true_ (A ⨯ Hom A B) := by
    let id_m : A ⨯ Hom A B ⟶ A ⨯ Pow (B ⨯ A) := prod.map (𝟙 _) (Hom_toGraph A B)
    let v := (((prod.associator _ _ _).inv ≫ in_ (B ⨯ A))^)
    let σ_B := Predicate.isSingleton B
    let u := ((v ≫ Predicate.isSingleton B)^)
    let id_u := prod.map (𝟙 A) u
    have comm_middle : v ≫ σ_B = id_u ≫ (in_ A) := (Pow_powerizes A (v ≫ σ_B)).symm
    have comm_left :
    id_m ≫ id_u
    =  prod.map (𝟙 _) (terminal.from _) ≫ prod.map (𝟙 _) ⌈Predicate.true_ A⌉ := by
      rw [prod.map_map, prod.map_map]
      ext; simp
      rw [prod.map_snd, prod.map_snd, Hom_comm]
    have h_terminal :
    (prod.map (𝟙 A) (terminal.from (Hom A B)) ≫ prod.fst) ≫ terminal.from A = terminal.from _ :=
      Unique.eq_default _
    rw [assoc, comm_middle, ←assoc, comm_left, assoc, Predicate.NameDef]
    dsimp [Predicate.true_]
    rw [←assoc, ←assoc, h_terminal]

/-- The evaluation map eval : A ⨯ B^A ⟶ B. -/
def eval (A B : C) : A ⨯ (Hom A B) ⟶ B :=
  ClassifierCone_into (comm' := evalDef_comm A B)

/-- This states the commutativity of the square relating
`eval A B` to `singleton B` and `Hom_toGraph A B`, which
arises from its definition.
-/
lemma evalCondition (A B : C) :
    eval A B ≫ singleton B
    = prod.map (𝟙 _) (Hom_toGraph A B) ≫ ((prod.associator _ _ _).inv ≫ in_ (B ⨯ A))^ :=
  ClassifierCone_into_comm _ _ _

/-- A map `f_exp : X ⟶ HomAB` exponentiates `f : A ⨯ X ⟶ B` with respect to
an "evaluation map" `e : A ⨯ HomAB ⟶ B` if the following diagram commutes:
```

        A ⨯ X ---f----> B
          |             ^
          |            /
          |           /
    (𝟙 A) ⨯ f_exp    /
          |         /
          |        e
          |       /
          |      /
          |     /
          |    /
          v   /
        A ⨯ HomAB
```
-/
abbrev Exponentiates {A B X HomAB : C}  (e : A ⨯ HomAB ⟶ B) (f : A ⨯ X ⟶ B) (f_exp : X ⟶ HomAB) :=
  (prod.map (𝟙 _) f_exp) ≫ e = f

/-- An object `HomAB` and a map `e : A ⨯ HomAB ⟶ B` form an exponential object for `A B : C`
if, for any map `f : A ⨯ X ⟶ B`, there is a unique map `f_exp : A ⟶ PB` such that
the following diagram commutes:
```

        A ⨯ X ---f----> B
          |             ^
          |            /
          |           /
    (𝟙 A) ⨯ f_exp    /
          |         /
          |        e
          |       /
          |      /
          |     /
          |    /
          v   /
        A ⨯ HomAB
```
-/
class IsExponentialObject {A B HomAB : C} (e : A ⨯ HomAB ⟶ B) where
  /-- The map that sends morphisms `A ⨯ X ⟶ B` to morphisms `X ⟶ Hom A B`. -/
  exp : ∀ {X} (_ : A ⨯ X ⟶ B), X ⟶ HomAB
  /-- `exp f` satisfies commutativity of the above diagram. -/
  exponentiates : ∀ {X} (f : A ⨯ X ⟶ B), Exponentiates e f (exp f)
  /-- `exp f` is the only map that satisfies the above commutativity condition. -/
  unique' : ∀ {X} {f : A ⨯ X ⟶ B} {exp' : X ⟶ HomAB}, Exponentiates e f exp' → exp f = exp'

/-- What it means for a pair `A B : C` to have an exponential object.
See `IsExponentialObject`.
-/
class HasExponentialObject (A B : C) where
  /-- The "internal hom" object. -/
  HomAB : C
  /-- The evaluation map. -/
  e : A ⨯ HomAB ⟶ B
  /-- `HomAB` and `e` form an exponential object for `A B : C`. -/
  is_exp : IsExponentialObject e

variable (C)

/-- A category has exponential objects if each pair of objects therein has an exponential object. -/
class HasExponentialObjects where
  has_exponential_object (A B : C) : HasExponentialObject A B

variable {C}

attribute [instance] HasExponentialObjects.has_exponential_object

variable {A B X : C} (f : A ⨯ X ⟶ B)

/-- Useful definition in the context of the construction of `eval A B`.
This is the composition of `Hom_map f` with `Hom_toGraph A B`, as exhibited
in `Hom_mapCondition` below.
-/
abbrev h_map : X ⟶ Pow (B ⨯ A) :=
  ((prod.associator _ _ _).hom ≫ prod.map (𝟙 _) f ≫ Predicate.eq _)^


/-- Helper lemma which shows that the appropriate square commutes
in the definition of `Hom_map`.
-/
lemma HomMapSquareComm :
    h_map f ≫ (((prod.associator B A (Power.Pow (B ⨯ A))).inv
    ≫ in_ (B ⨯ A))^ ≫ Predicate.isSingleton B)^ =
    terminal.from X ≫ ⌈Predicate.true_ A⌉ := by
  -- consider (1⨯f) ≫ (eq B) : B ⨯ A ⨯ X ⟶ Ω C.
  let id_f'eq : B ⨯ A ⨯ X ⟶ Ω C := prod.map (𝟙 _) f ≫ Predicate.eq _
  -- h is the map that, in `Set`, takes an element of X to the graph of the corresponding function.
  -- We want to lift this to a map X ⟶ Exp A B.
  -- The idea is to show that this map actually "maps elements of X to graphs of functions", which,
  -- in an arbitrary topos, is the same as checking commutativity of the obvious square.
  let h : X ⟶ Pow (B ⨯ A) := (((prod.associator _ _ _).hom ≫ id_f'eq)^)
  -- h is by definition a P-transpose
  have h_condition : (prod.associator _ _ _).hom ≫ id_f'eq
  = (prod.map (prod.map (𝟙 _) (𝟙 _)) h) ≫ in_ _ := by
    rw [prod.map_id_id]
    symm
    apply Pow_powerizes
  -- moving the associator to the rhs of `h_condition`.
  have h_condition₂ : id_f'eq
  = (prod.associator _ _ _).inv ≫ (prod.map (prod.map (𝟙 _) (𝟙 _)) h) ≫ in_ _ := by
    rw [←h_condition, ←assoc, (prod.associator _ _ _).inv_hom_id, id_comp]
  -- this is the map v: A ⨯ P(B⨯A) ⟶ P(B) which was used in the definition of `Exp A B`.
  let v : A ⨯ Pow (B ⨯ A) ⟶ Pow B := (((prod.associator _ _ _).inv ≫ in_ (B ⨯ A))^)
  -- v is by definition a P-transpose
  have v_condition : (prod.associator _ _ _).inv ≫ in_ (B ⨯ A)
  = prod.map (𝟙 _) v ≫ in_ _ := (Pow_powerizes _ _).symm
  have lhs : (prod.map (𝟙 A) h ≫ v ≫ Predicate.isSingleton B)^
  = h ≫ (v ≫ Predicate.isSingleton B)^ := by
    apply Pow_unique
    rw [prod.map_id_comp, assoc _ _ (in_ A), Pow_powerizes, ←assoc]
  rw [←lhs]
  -- Claim that f ≫ {•}_B = (1⨯h) ≫ v.
  -- This is obtained by showing that both maps are the P-transpose of (1⨯f) ≫ (eq B).
  -- There might be a slightly faster way to do this.
  have transpose₁ : id_f'eq^ = f ≫ singleton _ := by
    apply Pow_unique
    dsimp only [Topos.singleton]
    rw [prod.map_id_comp, assoc, (Pow_powerizes B (Predicate.eq B))]
  have shuffle_h_around : (prod.associator B A X).inv ≫ (prod.map (prod.map (𝟙 _) (𝟙 _)) h)
  = prod.map (𝟙 _) (prod.map (𝟙 _) h) ≫ (prod.associator _ _ _).inv := by simp
  have transpose₂ : id_f'eq^ = (prod.map (𝟙 _) h) ≫ v := by
    apply Pow_unique
    rw [h_condition₂, ←assoc, shuffle_h_around, prod.map_id_comp, assoc _ _ (in_ B),
    ←v_condition, assoc]
  have eqn₁ : f ≫ singleton _ = (prod.map (𝟙 _) h) ≫ v := transpose₁.symm.trans transpose₂
  -- now compose by the `isSingleton B` predicate.
  have eqn₂ : f ≫ singleton _ ≫ Predicate.isSingleton _
  = (prod.map (𝟙 _) h) ≫ v ≫ Predicate.isSingleton _ := by
    rw [←assoc, ←assoc, eqn₁]
  rw [←eqn₂]
  -- from here, the argument is mostly definition unpacking.
  apply Pow_unique
  dsimp only [Name, Predicate.true_, Predicate.isSingleton]
  have f_terminal : f ≫ terminal.from B = terminal.from _ := Unique.eq_default _
  have rightUnitor_terminal : (Limits.prod.rightUnitor A).hom ≫ terminal.from A
  = terminal.from _ :=
    Unique.eq_default _
  have A_X_terminal : prod.map (𝟙 A) (terminal.from X) ≫ terminal.from (A ⨯ ⊤_ C)
  = terminal.from _ :=
    Unique.eq_default _
  have obv : terminal.from (A ⨯ ⊤_ C) ≫ t C
  = prod.map (𝟙 A) (P_transpose (terminal.from (A ⨯ ⊤_ C) ≫ t C)) ≫ in_ A :=
    (Pow_powerizes _ _).symm
  have map_def : (Limits.prod.rightUnitor A).hom = prod.fst := rfl
  rw [ClassifierComm (singleton _), ←assoc, ←map_def, rightUnitor_terminal, ←assoc,
  f_terminal, prod.map_id_comp, assoc, ←obv, ←assoc, A_X_terminal]

/-- Given a map `f : A ⨯ X ⟶ B`, `Hom_map f`
is the associated map `X ⟶ Hom A B`.
-/
def Hom_map : X ⟶ Hom A B :=
  pullback.lift (h_map f) (terminal.from X) (HomMapSquareComm f)

/-- composing `Hom_map f` with the map sending a morphism to its graph
is the map `h_map f` defined above.
-/
@[simp]
lemma Hom_mapCondition : Hom_map f ≫ (Hom_toGraph A B) = h_map f :=
  pullback.lift_fst _ _ _

/-- `Hom_map f` satisfies the condition that
the following diagram commutes:
```
        A ⨯ X ---f----> B
          |             ^
          |            /
          |           /
    (𝟙 A) ⨯ Hom_map  /
          |         /
          |     eval A B
          |       /
          |      /
          |     /
          |    /
          v   /
        A ⨯ (Hom A B)
```
-/
theorem Hom_Exponentiates : Exponentiates (eval A B) f (Hom_map f) := by
  dsimp only [Exponentiates]
  rw [←cancel_mono (singleton B), assoc, evalCondition, ←assoc,
    prod.map_map, id_comp, Hom_mapCondition]
  have h : P_transpose_inv (f ≫ singleton B)
      = P_transpose_inv (prod.map (𝟙 A) (h_map f)
      ≫ P_transpose ((prod.associator B A (Power.Pow (B ⨯ A))).inv ≫ in_ (B ⨯ A))) := by
    rw [P_transpose_inv, P_transpose_inv, prod.map_id_comp, assoc, singleton,
      Pow_powerizes, prod.map_id_comp, assoc, Pow_powerizes, ←assoc]
    have h' : (prod.map (𝟙 B) (prod.map (𝟙 A) (h_map f))
        ≫ (prod.associator B A (Power.Pow (B ⨯ A))).inv)
      = (prod.associator B A X).inv ≫ (prod.map (𝟙 _) (h_map f)) := by simp
    rw [h', assoc, h_map, Pow_powerizes, ←assoc, Iso.inv_hom_id, id_comp]
  have h₀ := congrArg (fun k => P_transpose k) h
  have t₁ : ((f ≫ singleton B)^)^ = f ≫ singleton B := (transposeEquiv _ _).right_inv _
  have t₂ : (((prod.map (𝟙 A) (h_map f)
      ≫ ((prod.associator B A (Power.Pow (B ⨯ A))).inv ≫ in_ (B ⨯ A))^))^)^
    = (prod.map (𝟙 A) (h_map f) ≫ ((prod.associator B A (Power.Pow (B ⨯ A))).inv ≫ in_ (B ⨯ A))^) :=
      P_transpose_right_inv _
  simp only [t₁, t₂] at h₀
  exact h₀.symm

/-- Proof of the uniqueness of `Hom_map f` as a map
`X ⟶ Hom A B` satisfying commutativity of the associated
diagram. See `Hom_Exponentiates`.
-/
theorem Hom_Unique {exp' : X ⟶ Hom A B} (h : Exponentiates (eval A B) f exp') :
    Hom_map f = exp' := by
  dsimp only [Exponentiates] at h
  have h_singleton := congrArg (fun k ↦ k ≫ singleton B) h
  simp only at h_singleton
  let v : A ⨯ Pow (B ⨯ A) ⟶ Pow B := (((prod.associator _ _ _).inv ≫ in_ (B ⨯ A))^)
  -- want to rewrite (1⨯g) ≫ eval A B ≫ singleton B = (1⨯(g≫m)) ≫ v
  have rhs : eval A B ≫ singleton B = prod.map (𝟙 _) (Hom_toGraph A B) ≫ v := by
    apply PullbackCone.IsLimit.lift_fst
  rw [assoc, rhs, ←assoc, ←prod.map_id_comp] at h_singleton
  let id_f'eq : B ⨯ A ⨯ X ⟶ Ω C := prod.map (𝟙 _) f ≫ Predicate.eq _
  have h₁ : id_f'eq^ = f ≫ singleton B := by
    apply Pow_unique
    dsimp only [id_f'eq, singleton]
    rw [prod.map_id_comp, assoc, Pow_powerizes _ (Predicate.eq B)]
  have h₂ : (prod.map (𝟙 _) (prod.map (𝟙 _) (exp' ≫ Hom_toGraph A B))
      ≫ (prod.associator _ _ _).inv ≫ in_ (B ⨯ A))^
      = prod.map (𝟙 _) (exp' ≫ Hom_toGraph A B) ≫ v := by
    apply Pow_unique
    rw [prod.map_id_comp, assoc, Pow_powerizes]
  have h₃ := Pow_powerizes _ ((prod.map (𝟙 B) (prod.map (𝟙 A) (exp' ≫ Hom_toGraph A B))
      ≫ (prod.associator B A (Power.Pow (B ⨯ A))).inv ≫ in_ (B ⨯ A)))
  rw [h₂, h_singleton, ←h₁, Pow_powerizes _ id_f'eq, ←assoc] at h₃
  have h' := Hom_Exponentiates f
  dsimp only [Exponentiates] at h'
  have h'_singleton := congrArg (fun k ↦ k ≫ singleton B) h'
  simp only at h'_singleton
  rw [assoc, rhs, ←assoc, ←prod.map_id_comp] at h'_singleton
  have h₂' : (prod.map (𝟙 _) (prod.map (𝟙 _) (Hom_map f ≫ Hom_toGraph A B))
      ≫ (prod.associator _ _ _).inv ≫ in_ (B ⨯ A))^
      = prod.map (𝟙 _) (Hom_map f ≫ Hom_toGraph A B) ≫ v := by
    apply Pow_unique
    rw [prod.map_id_comp, assoc, Pow_powerizes]
  have h₃' := Pow_powerizes _ ((prod.map (𝟙 B) (prod.map (𝟙 A) (Hom_map f ≫ Hom_toGraph A B))
    ≫ (prod.associator B A (Power.Pow (B ⨯ A))).inv ≫ in_ (B ⨯ A)))
  rw [h₂', h'_singleton, ←h₁, Pow_powerizes _ id_f'eq, ←assoc] at h₃'

  have hx := h₃'.symm.trans h₃
  have c₀ : prod.map (𝟙 B) (prod.map (𝟙 A) (exp' ≫ Hom_toGraph A B)) ≫ (prod.associator _ _ _).inv
    = (prod.associator _ _ _).inv ≫ (prod.map (𝟙 _) (exp' ≫ Hom_toGraph A B)) := by simp
  have c₁ : prod.map (𝟙 B) (prod.map (𝟙 A) (Hom_map f ≫ Hom_toGraph A B))
      ≫ (prod.associator _ _ _).inv
      = (prod.associator _ _ _).inv ≫ (prod.map (𝟙 _) (Hom_map f ≫ Hom_toGraph A B)) := by simp
  rw [c₀, c₁] at hx
  have hy := congrArg (fun k ↦ (prod.associator B A X).hom ≫ k) hx
  simp only at hy
  rw [←assoc, ←assoc, Iso.hom_inv_id, id_comp, ←assoc, ←assoc, Iso.hom_inv_id, id_comp] at hy
  have hz := congrArg (fun k ↦ P_transpose k) hy
  simp only at hz
  rw [P_transpose_right_inv, P_transpose_right_inv] at hz
  rw [cancel_mono] at hz
  assumption

/-- `eval A B` is an exponential object for the pair `A B : C` -/
instance Hom_isExponential : IsExponentialObject (eval A B) where
  exp := Hom_map
  exponentiates := Hom_Exponentiates
  unique' := by apply Hom_Unique

/-- A topos `C` has an exponential object for every pair of objects `A B : C` -/
instance ExponentialObject_inst (A B : C) : HasExponentialObject A B where
  HomAB := Hom A B
  e := eval A B
  is_exp := Hom_isExponential

/-- A topos has all exponential objects. -/
instance ToposHasExponentials : HasExponentialObjects C where
  has_exponential_object := ExponentialObject_inst

variable (X Y Z W)

/-- Internal composition in a topos, defined in terms of `Hom_map` -/
def InternalComposition : (Hom X Y) ⨯ (Hom Y Z) ⟶ Hom X Z :=
  Hom_map ((prod.associator X (Hom X Y) (Hom Y Z)).inv ≫ (prod.map (eval X Y) (𝟙 _)) ≫ eval Y Z)

variable {X Y Z W}

/-- The global element of `Hom X Y` associated to a morphism `X ⟶ Y`. -/
def FnName (f : X ⟶ Y) : ⊤_ C ⟶ Hom X Y :=
  Hom_map (prod.fst ≫ f)

/-- The inverse to `Hom_map`, which sends a morphism `X ⟶ Hom Y Z`
to its "un-curried" version `Y ⨯ X ⟶ Z`.
-/
abbrev Hom_map_inv (f : X ⟶ Hom Y Z) := prod.map (𝟙 _) f ≫ eval _ _

/-- The equivalence between arrows `A ⨯ X ⟶ B` and arrows `X ⟶ Hom A B`. -/
def ExpAdjEquiv (A B X : C) : (A ⨯ X ⟶ B) ≃ (X ⟶ Hom A B) where
  toFun := Hom_map
  invFun := Hom_map_inv
  left_inv := fun f => Hom_Exponentiates f
  right_inv := by
    intro g
    apply Hom_Unique; rfl

variable (X Y)

/-- The map `Hom A X ⟶ Hom A Y` associated to a map `X ⟶ Y`.
This is how `ExpFunctor` acts on morphisms.
-/
def ExpHom {X Y : C} (A : C) (f : X ⟶ Y) : Hom A X ⟶ Hom A Y := Hom_map (eval A _ ≫ f)

/-- The covariant functor `C ⥤ C` associated to an object `A : C`
sending an object `B` to the "internal hom" `Hom A B`.
-/
def ExpFunctor (A : C) : C ⥤ C where
  obj := fun B ↦ Hom A B
  map := fun {X Y} f ↦ ExpHom A f
  map_id := by
    intro X
    dsimp only [ExpHom]
    rw [comp_id]
    apply Hom_Unique
    dsimp only [Exponentiates]
    rw [prod.map_id_id, id_comp]
  map_comp := by
    intro X Y Z f g
    change ExpHom A (f ≫ g) = ExpHom A f ≫ ExpHom A g
    dsimp only [ExpHom]
    apply Hom_Unique
    dsimp only [Exponentiates]
    rw [prod.map_id_comp, assoc, Hom_Exponentiates, ←assoc, Hom_Exponentiates, assoc]

/-- A topos is a monoidal category with monoidal structure coming from binary products. -/
instance ToposMonoidal : MonoidalCategory C := monoidalOfHasFiniteProducts C

/-- The adjunction between the product and the "internal hom" `Hom A B`. -/
def TensorHomAdjunction (A : C) : MonoidalCategory.tensorLeft A ⊣ ExpFunctor A := by
  apply Adjunction.mkOfHomEquiv
  fapply Adjunction.CoreHomEquiv.mk

  · intro X B
    exact ExpAdjEquiv A B X

  · intro X X' Y f g
    change prod.map (𝟙 _) (f ≫ g) ≫ eval _ _ = (prod.map (𝟙 _) f) ≫ prod.map (𝟙 _) g ≫ eval _ _
    rw [←assoc, prod.map_map, id_comp]

  · intro X Y Y' f g
    change Hom_map (f ≫ g) = Hom_map f ≫ ExpHom A g
    apply Hom_Unique
    dsimp only [Exponentiates, ExpHom]
    rw [prod.map_id_comp, assoc, Hom_Exponentiates, ←assoc, Hom_Exponentiates]

-- note: wholly unsure why `C` is already CC.
-- the following produces no errors, but #lint gets mad about it.
-- /-- A topos is cartesian closed. -/
-- instance CartesianClosed : CartesianClosed C := by assumption

end
end CategoryTheory.Topos
