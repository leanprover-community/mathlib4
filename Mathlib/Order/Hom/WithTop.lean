/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Hom.Lattice

/-!
# Order homomorphisms between `WithTop` and `WithBot`
-/

assert_not_exists HeytingAlgebra

open Function OrderDual

variable {F ι α β γ δ : Type*}

/-! ### `WithTop`, `WithBot` -/

namespace SupHom
variable [SemilatticeSup α] [SemilatticeSup β] [SemilatticeSup γ]

/-- Adjoins a `⊤` to the domain and codomain of a `SupHom`. -/
@[simps]
protected def withTop (f : SupHom α β) : SupHom (WithTop α) (WithTop β) where
  -- Porting note: this was `Option.map f`
  toFun := WithTop.map f
  map_sup' a b :=
    match a, b with
    | ⊤, ⊤ => rfl
    | ⊤, (b : α) => rfl
    | (a : α), ⊤ => rfl
    | (a : α), (b : α) => congr_arg _ (f.map_sup' _ _)

@[simp]
theorem withTop_id : (SupHom.id α).withTop = SupHom.id _ := DFunLike.coe_injective Option.map_id

@[simp]
theorem withTop_comp (f : SupHom β γ) (g : SupHom α β) :
    (f.comp g).withTop = f.withTop.comp g.withTop :=
  DFunLike.coe_injective <| Eq.symm <| Option.map_comp_map _ _

/-- Adjoins a `⊥` to the domain and codomain of a `SupHom`. -/
@[simps]
protected def withBot (f : SupHom α β) : SupBotHom (WithBot α) (WithBot β) where
  toFun := Option.map f
  map_sup' a b :=
    match a, b with
    | ⊥, ⊥ => rfl
    | ⊥, (b : α) => rfl
    | (a : α), ⊥ => rfl
    | (a : α), (b : α) => congr_arg _ (f.map_sup' _ _)
  map_bot' := rfl

@[simp]
theorem withBot_id : (SupHom.id α).withBot = SupBotHom.id _ := DFunLike.coe_injective Option.map_id

@[simp]
theorem withBot_comp (f : SupHom β γ) (g : SupHom α β) :
    (f.comp g).withBot = f.withBot.comp g.withBot :=
  DFunLike.coe_injective <| Eq.symm <| Option.map_comp_map _ _

/-- Adjoins a `⊤` to the codomain of a `SupHom`. -/
@[simps]
def withTop' [OrderTop β] (f : SupHom α β) : SupHom (WithTop α) β where
  toFun a := a.elim ⊤ f
  map_sup' a b :=
    match a, b with
    | ⊤, ⊤ => (top_sup_eq _).symm
    | ⊤, (b : α) => (top_sup_eq _).symm
    | (a : α), ⊤ => (sup_top_eq _).symm
    | (a : α), (b : α) => f.map_sup' _ _

/-- Adjoins a `⊥` to the domain of a `SupHom`. -/
@[simps]
def withBot' [OrderBot β] (f : SupHom α β) : SupBotHom (WithBot α) β where
  toFun a := a.elim ⊥ f
  map_sup' a b :=
    match a, b with
    | ⊥, ⊥ => (bot_sup_eq _).symm
    | ⊥, (b : α) => (bot_sup_eq _).symm
    | (a : α), ⊥ => (sup_bot_eq _).symm
    | (a : α), (b : α) => f.map_sup' _ _
  map_bot' := rfl

end SupHom

namespace InfHom

variable [SemilatticeInf α] [SemilatticeInf β] [SemilatticeInf γ]

/-- Adjoins a `⊤` to the domain and codomain of an `InfHom`. -/
@[simps]
protected def withTop (f : InfHom α β) : InfTopHom (WithTop α) (WithTop β) where
  toFun := Option.map f
  map_inf' a b :=
    match a, b with
    | ⊤, ⊤ => rfl
    | ⊤, (b : α) => rfl
    | (a : α), ⊤ => rfl
    | (a : α), (b : α) => congr_arg _ (f.map_inf' _ _)
  map_top' := rfl

@[simp]
theorem withTop_id : (InfHom.id α).withTop = InfTopHom.id _ := DFunLike.coe_injective Option.map_id

@[simp]
theorem withTop_comp (f : InfHom β γ) (g : InfHom α β) :
    (f.comp g).withTop = f.withTop.comp g.withTop :=
  DFunLike.coe_injective <| Eq.symm <| Option.map_comp_map _ _

/-- Adjoins a `⊥` to the domain and codomain of an `InfHom`. -/
@[simps]
protected def withBot (f : InfHom α β) : InfHom (WithBot α) (WithBot β) where
  toFun := Option.map f
  map_inf' a b :=
    match a, b with
    | ⊥, ⊥ => rfl
    | ⊥, (b : α) => rfl
    | (a : α), ⊥ => rfl
    | (a : α), (b : α) => congr_arg _ (f.map_inf' _ _)

@[simp]
theorem withBot_id : (InfHom.id α).withBot = InfHom.id _ := DFunLike.coe_injective Option.map_id

@[simp]
theorem withBot_comp (f : InfHom β γ) (g : InfHom α β) :
    (f.comp g).withBot = f.withBot.comp g.withBot :=
  DFunLike.coe_injective <| Eq.symm <| Option.map_comp_map _ _

/-- Adjoins a `⊤` to the codomain of an `InfHom`. -/
@[simps]
def withTop' [OrderTop β] (f : InfHom α β) : InfTopHom (WithTop α) β where
  toFun a := a.elim ⊤ f
  map_inf' a b :=
    match a, b with
    | ⊤, ⊤ => (top_inf_eq _).symm
    | ⊤, (b : α) => (top_inf_eq _).symm
    | (a : α), ⊤ => (inf_top_eq _).symm
    | (a : α), (b : α) => f.map_inf' _ _
  map_top' := rfl

/-- Adjoins a `⊥` to the codomain of an `InfHom`. -/
@[simps]
def withBot' [OrderBot β] (f : InfHom α β) : InfHom (WithBot α) β where
  toFun a := a.elim ⊥ f
  map_inf' a b :=
    match a, b with
    | ⊥, ⊥ => (bot_inf_eq _).symm
    | ⊥, (b : α) => (bot_inf_eq _).symm
    | (a : α), ⊥ => (inf_bot_eq _).symm
    | (a : α), (b : α) => f.map_inf' _ _

end InfHom

namespace LatticeHom

variable [Lattice α] [Lattice β] [Lattice γ]

/-- Adjoins a `⊤` to the domain and codomain of a `LatticeHom`. -/
@[simps]
protected def withTop (f : LatticeHom α β) : LatticeHom (WithTop α) (WithTop β) :=
  { f.toInfHom.withTop with toSupHom := f.toSupHom.withTop }

-- Porting note: `simps` doesn't generate those
@[simp, norm_cast]
lemma coe_withTop (f : LatticeHom α β) : ⇑f.withTop = WithTop.map f := rfl

lemma withTop_apply (f : LatticeHom α β) (a : WithTop α) : f.withTop a = a.map f := rfl

@[simp]
theorem withTop_id : (LatticeHom.id α).withTop = LatticeHom.id _ :=
  DFunLike.coe_injective Option.map_id

@[simp]
theorem withTop_comp (f : LatticeHom β γ) (g : LatticeHom α β) :
    (f.comp g).withTop = f.withTop.comp g.withTop :=
  DFunLike.coe_injective <| Eq.symm <| Option.map_comp_map _ _

/-- Adjoins a `⊥` to the domain and codomain of a `LatticeHom`. -/
@[simps]
protected def withBot (f : LatticeHom α β) : LatticeHom (WithBot α) (WithBot β) :=
  { f.toInfHom.withBot with toSupHom := f.toSupHom.withBot }

-- Porting note: `simps` doesn't generate those
@[simp, norm_cast]
lemma coe_withBot (f : LatticeHom α β) : ⇑f.withBot = Option.map f := rfl

lemma withBot_apply (f : LatticeHom α β) (a : WithBot α) : f.withBot a = a.map f := rfl

@[simp]
theorem withBot_id : (LatticeHom.id α).withBot = LatticeHom.id _ :=
  DFunLike.coe_injective Option.map_id

@[simp]
theorem withBot_comp (f : LatticeHom β γ) (g : LatticeHom α β) :
    (f.comp g).withBot = f.withBot.comp g.withBot :=
  DFunLike.coe_injective <| Eq.symm <| Option.map_comp_map _ _

/-- Adjoins a `⊤` and `⊥` to the domain and codomain of a `LatticeHom`. -/
@[simps]
def withTopWithBot (f : LatticeHom α β) :
    BoundedLatticeHom (WithTop <| WithBot α) (WithTop <| WithBot β) :=
  ⟨f.withBot.withTop, rfl, rfl⟩

-- Porting note: `simps` doesn't generate those
@[simp, norm_cast]
lemma coe_withTopWithBot (f : LatticeHom α β) : ⇑f.withTopWithBot = Option.map (Option.map f) := rfl

lemma withTopWithBot_apply (f : LatticeHom α β) (a : WithTop <| WithBot α) :
    f.withTopWithBot a = a.map (Option.map f) := rfl

@[simp]
theorem withTopWithBot_id : (LatticeHom.id α).withTopWithBot = BoundedLatticeHom.id _ :=
  DFunLike.coe_injective <| by
    refine (congr_arg Option.map ?_).trans Option.map_id
    rw [withBot_id]
    rfl

@[simp]
theorem withTopWithBot_comp (f : LatticeHom β γ) (g : LatticeHom α β) :
    (f.comp g).withTopWithBot = f.withTopWithBot.comp g.withTopWithBot := by
  ext; simp

/-- Adjoins a `⊥` to the codomain of a `LatticeHom`. -/
@[simps]
def withTop' [OrderTop β] (f : LatticeHom α β) : LatticeHom (WithTop α) β :=
  { f.toSupHom.withTop', f.toInfHom.withTop' with }

/-- Adjoins a `⊥` to the domain and codomain of a `LatticeHom`. -/
@[simps]
def withBot' [OrderBot β] (f : LatticeHom α β) : LatticeHom (WithBot α) β :=
  { f.toSupHom.withBot', f.toInfHom.withBot' with }

/-- Adjoins a `⊤` and `⊥` to the codomain of a `LatticeHom`. -/
@[simps]
def withTopWithBot' [BoundedOrder β] (f : LatticeHom α β) :
    BoundedLatticeHom (WithTop <| WithBot α) β where
  toLatticeHom := f.withBot'.withTop'
  map_top' := rfl
  map_bot' := rfl

end LatticeHom
