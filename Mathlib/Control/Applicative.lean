/-
Copyright (c) 2017 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Control.Functor

#align_import control.applicative from "leanprover-community/mathlib"@"70d50ecfd4900dd6d328da39ab7ebd516abe4025"

/-!
# `applicative` instances

This file provides `Applicative` instances for concrete functors:
* `id`
* `Functor.comp`
* `Functor.const`
* `Functor.add_const`
-/

universe u v w

section Lemmas

open Function

variable {F : Type u → Type v}

variable [Applicative F] [LawfulApplicative F]

variable {α β γ σ : Type u}

theorem Applicative.map_seq_map (f : α → β → γ) (g : σ → β) (x : F α) (y : F σ) :
    f <$> x <*> g <$> y = (flip (· ∘ ·) g ∘ f) <$> x <*> y := by simp [flip, functor_norm]
                                                                 -- 🎉 no goals
#align applicative.map_seq_map Applicative.map_seq_map

theorem Applicative.pure_seq_eq_map' (f : α → β) : (· <*> ·) (pure f : F (α → β)) = (· <$> ·) f :=
  by ext; simp [functor_norm]
     -- ⊢ (fun x x_1 => Seq.seq x fun x => x_1) (pure f) x✝ = (fun x x_1 => x <$> x_1) …
          -- 🎉 no goals
#align applicative.pure_seq_eq_map' Applicative.pure_seq_eq_map'

theorem Applicative.ext {F} :
    ∀ {A1 : Applicative F} {A2 : Applicative F} [@LawfulApplicative F A1] [@LawfulApplicative F A2],
      (∀ {α : Type u} (x : α), @Pure.pure _ A1.toPure _ x = @Pure.pure _ A2.toPure _ x) →
      (∀ {α β : Type u} (f : F (α → β)) (x : F α),
          @Seq.seq _ A1.toSeq _ _ f (fun _ => x) = @Seq.seq _ A2.toSeq _ _ f (fun _ => x)) →
      A1 = A2
  | { toFunctor := F1, seq := s1, pure := p1, seqLeft := sl1, seqRight := sr1 },
    { toFunctor := F2, seq := s2, pure := p2, seqLeft := sl2, seqRight := sr2 },
    L1, L2, H1, H2 => by
    obtain rfl : @p1 = @p2 := by
      funext α x
      apply H1
    obtain rfl : @s1 = @s2 := by
      funext α β f x
      exact H2 f (x Unit.unit)
    obtain ⟨seqLeft_eq1, seqRight_eq1, pure_seq1, -⟩ := L1
    -- ⊢ mk = mk
    obtain ⟨seqLeft_eq2, seqRight_eq2, pure_seq2, -⟩ := L2
    -- ⊢ mk = mk
    obtain rfl : F1 = F2 := by
      apply Functor.ext
      intros
      exact (pure_seq1 _ _).symm.trans (pure_seq2 _ _)
    congr <;> funext α β x y
    -- ⊢ sl1 = sl2
              -- ⊢ sl1 x y = sl2 x y
              -- ⊢ sr1 x y = sr2 x y
    · exact (seqLeft_eq1 _ (y Unit.unit)).trans (seqLeft_eq2 _ _).symm
      -- 🎉 no goals
    · exact (seqRight_eq1 _ (y Unit.unit)).trans (seqRight_eq2 _ (y Unit.unit)).symm
      -- 🎉 no goals
#align applicative.ext Applicative.ext

end Lemmas

-- Porting note: mathport failed to see the #align on `CommApplicative`,
-- therefore using `IsCommApplicative` instead.

-- Porting note: we have a monad instance for `Id` but not `id`, mathport can't tell
-- which one is intended

instance : CommApplicative Id := by refine' { .. } <;> intros <;> rfl
                                                       -- ⊢ Functor.mapConst = Functor.map ∘ Function.const β✝
                                                       -- ⊢ id <$> x✝ = x✝
                                                       -- ⊢ (h✝ ∘ g✝) <$> x✝ = h✝ <$> g✝ <$> x✝
                                                       -- ⊢ (SeqLeft.seqLeft x✝ fun x => y✝) = Seq.seq (Function.const β✝ <$> x✝) fun x  …
                                                       -- ⊢ (SeqRight.seqRight x✝ fun x => y✝) = Seq.seq (Function.const α✝ id <$> x✝) f …
                                                       -- ⊢ (Seq.seq (pure g✝) fun x => x✝) = g✝ <$> x✝
                                                       -- ⊢ g✝ <$> pure x✝ = pure (g✝ x✝)
                                                       -- ⊢ (Seq.seq g✝ fun x => pure x✝) = (fun h => h x✝) <$> g✝
                                                       -- ⊢ (Seq.seq h✝ fun x => Seq.seq g✝ fun x => x✝) = Seq.seq (Seq.seq (Function.co …
                                                       -- ⊢ (Seq.seq (Prod.mk <$> a✝) fun x => b✝) = Seq.seq ((fun b a => (a, b)) <$> b✝ …
                                                                  -- 🎉 no goals
                                                                  -- 🎉 no goals
                                                                  -- 🎉 no goals
                                                                  -- 🎉 no goals
                                                                  -- 🎉 no goals
                                                                  -- 🎉 no goals
                                                                  -- 🎉 no goals
                                                                  -- 🎉 no goals
                                                                  -- 🎉 no goals
                                                                  -- 🎉 no goals

namespace Functor

namespace Comp

open Function hiding comp

open Functor

variable {F : Type u → Type w} {G : Type v → Type u}

variable [Applicative F] [Applicative G]

variable [LawfulApplicative F] [LawfulApplicative G]

variable {α β γ : Type v}

theorem map_pure (f : α → β) (x : α) : (f <$> pure x : Comp F G β) = pure (f x) :=
  Comp.ext <| by simp
                 -- 🎉 no goals
#align functor.comp.map_pure Functor.Comp.map_pure

theorem seq_pure (f : Comp F G (α → β)) (x : α) : f <*> pure x = (fun g : α → β => g x) <$> f :=
  Comp.ext <| by simp [(· ∘ ·), functor_norm]
                 -- 🎉 no goals
#align functor.comp.seq_pure Functor.Comp.seq_pure

theorem seq_assoc (x : Comp F G α) (f : Comp F G (α → β)) (g : Comp F G (β → γ)) :
    g <*> (f <*> x) = @Function.comp α β γ <$> g <*> f <*> x :=
  Comp.ext <| by simp [(· ∘ ·), functor_norm]
                 -- 🎉 no goals
#align functor.comp.seq_assoc Functor.Comp.seq_assoc

theorem pure_seq_eq_map (f : α → β) (x : Comp F G α) : pure f <*> x = f <$> x :=
  Comp.ext <| by simp [Applicative.pure_seq_eq_map', functor_norm]
                 -- 🎉 no goals
#align functor.comp.pure_seq_eq_map Functor.Comp.pure_seq_eq_map

-- TODO: the first two results were handled by `control_laws_tac` in mathlib3
instance instLawfulApplicativeComp : LawfulApplicative (Comp F G) where
  seqLeft_eq := by intros; rfl
                   -- ⊢ (SeqLeft.seqLeft x✝ fun x => y✝) = Seq.seq (const β✝ <$> x✝) fun x => y✝
                           -- 🎉 no goals
  seqRight_eq := by intros; rfl
                    -- ⊢ (SeqRight.seqRight x✝ fun x => y✝) = Seq.seq (const α✝ id <$> x✝) fun x => y✝
                            -- 🎉 no goals
  pure_seq := @Comp.pure_seq_eq_map F G _ _ _ _
  map_pure := @Comp.map_pure F G _ _ _ _
  seq_pure := @Comp.seq_pure F G _ _ _ _
  seq_assoc := @Comp.seq_assoc F G _ _ _ _

-- Porting note: mathport wasn't aware of the new implicit parameter omission in these `fun` binders

theorem applicative_id_comp {F} [AF : Applicative F] [LawfulApplicative F] :
    @instApplicativeComp Id F _ _ = AF :=
  @Applicative.ext F _ _ (@instLawfulApplicativeComp Id F _ _ _ _) _
    (fun _ => rfl) (fun _ _ => rfl)
#align functor.comp.applicative_id_comp Functor.Comp.applicative_id_comp

theorem applicative_comp_id {F} [AF : Applicative F] [LawfulApplicative F] :
    @Comp.instApplicativeComp F Id _ _ = AF :=
  @Applicative.ext F _ _ (@Comp.instLawfulApplicativeComp F Id _ _ _ _) _
    (fun _ => rfl) (fun f x => show id <$> f <*> x = f <*> x by rw [id_map])
                                                                -- 🎉 no goals
#align functor.comp.applicative_comp_id Functor.Comp.applicative_comp_id

open CommApplicative

instance {f : Type u → Type w} {g : Type v → Type u} [Applicative f] [Applicative g]
    [CommApplicative f] [CommApplicative g] : CommApplicative (Comp f g) := by
  refine' { @instLawfulApplicativeComp f g _ _ _ _ with .. }
  -- ⊢ ∀ {α β : Type v} (a : Comp f g α) (b : Comp f g β), (Seq.seq (Prod.mk <$> a) …
  intros
  -- ⊢ (Seq.seq (Prod.mk <$> a✝) fun x => b✝) = Seq.seq ((fun b a => (a, b)) <$> b✝ …
  simp! [map, Seq.seq, functor_norm]
  -- ⊢ mk (Seq.seq ((fun x x_1 => Seq.seq x fun x => x_1) <$> mk ((fun x => Prod.mk …
  rw [commutative_map]
  -- ⊢ mk (Seq.seq ((flip fun x x_1 => Seq.seq x fun x => x_1) <$> b✝) fun x => mk  …
  simp [Comp.mk, flip, (· ∘ ·), functor_norm]
  -- ⊢ (Seq.seq ((fun x x_1 => Seq.seq (Prod.mk <$> x_1) fun x_2 => x) <$> b✝) fun  …
  congr
  -- ⊢ (fun x x_1 => Seq.seq (Prod.mk <$> x_1) fun x_2 => x) = fun x x_1 => Seq.seq …
  funext x y
  -- ⊢ (Seq.seq (Prod.mk <$> y) fun x_1 => x) = Seq.seq ((fun b a => (a, b)) <$> x) …
  rw [commutative_map]
  -- ⊢ (Seq.seq (flip Prod.mk <$> x) fun x => y) = Seq.seq ((fun b a => (a, b)) <$> …
  congr
  -- 🎉 no goals

end Comp

end Functor

open Functor

@[functor_norm]
theorem Comp.seq_mk {α β : Type w} {f : Type u → Type v} {g : Type w → Type u} [Applicative f]
    [Applicative g] (h : f (g (α → β))) (x : f (g α)) :
    Comp.mk h <*> Comp.mk x = Comp.mk ((· <*> ·) <$> h <*> x) :=
  rfl
#align comp.seq_mk Comp.seq_mk

-- Porting note: There is some awkwardness in the following definition now that we have `HMul`.

instance {α} [One α] [Mul α] : Applicative (Const α) where
  pure _ := (1 : α)
  seq f x := (show α from f) * (show α from x Unit.unit)

-- Porting note: `(· <*> ·)` needed to change to `Seq.seq` in the `simp`.
-- Also, `simp` didn't close `refl` goals.

instance {α} [Monoid α] : LawfulApplicative (Const α) := by
  refine' { .. } <;> intros <;> simp [mul_assoc, (· <$> ·), Seq.seq, pure] <;> rfl
                     -- ⊢ mapConst = map ∘ Function.const β✝
                     -- ⊢ id <$> x✝ = x✝
                     -- ⊢ (h✝ ∘ g✝) <$> x✝ = h✝ <$> g✝ <$> x✝
                     -- ⊢ (SeqLeft.seqLeft x✝ fun x => y✝) = Seq.seq (Function.const β✝ <$> x✝) fun x  …
                     -- ⊢ (SeqRight.seqRight x✝ fun x => y✝) = Seq.seq (Function.const α✝ id <$> x✝) f …
                     -- ⊢ (Seq.seq (pure g✝) fun x => x✝) = g✝ <$> x✝
                     -- ⊢ g✝ <$> pure x✝ = pure (g✝ x✝)
                     -- ⊢ (Seq.seq g✝ fun x => pure x✝) = (fun h => h x✝) <$> g✝
                     -- ⊢ (Seq.seq h✝ fun x => Seq.seq g✝ fun x => x✝) = Seq.seq (Seq.seq (Function.co …
                                -- ⊢ mapConst = Const.map ∘ Function.const β✝
                                -- ⊢ Const.map id x✝ = x✝
                                -- ⊢ Const.map (h✝ ∘ g✝) x✝ = Const.map h✝ (Const.map g✝ x✝)
                                -- ⊢ (SeqLeft.seqLeft x✝ fun x => y✝) = Const.map (Function.const β✝) x✝ * y✝
                                -- ⊢ (SeqRight.seqRight x✝ fun x => y✝) = Const.map (Function.const α✝ id) x✝ * y✝
                                -- ⊢ x✝ = Const.map g✝ x✝
                                -- ⊢ Const.map g✝ 1 = 1
                                -- ⊢ g✝ = Const.map (fun h => h x✝) g✝
                                -- ⊢ h✝ * (g✝ * x✝) = Const.map Function.comp h✝ * (g✝ * x✝)
                                                                               -- 🎉 no goals
                                                                               -- 🎉 no goals
                                                                               -- 🎉 no goals
                                                                               -- 🎉 no goals
                                                                               -- 🎉 no goals
                                                                               -- 🎉 no goals
                                                                               -- 🎉 no goals
                                                                               -- 🎉 no goals
                                                                               -- 🎉 no goals

instance {α} [Zero α] [Add α] : Applicative (AddConst α) where
  pure _ := (0 : α)
  seq f x := (show α from f) + (show α from x Unit.unit)

instance {α} [AddMonoid α] : LawfulApplicative (AddConst α) := by
  refine' { .. } <;> intros <;> simp [add_assoc, (· <$> ·), Seq.seq, pure] <;> rfl
                     -- ⊢ mapConst = map ∘ Function.const β✝
                     -- ⊢ id <$> x✝ = x✝
                     -- ⊢ (h✝ ∘ g✝) <$> x✝ = h✝ <$> g✝ <$> x✝
                     -- ⊢ (SeqLeft.seqLeft x✝ fun x => y✝) = Seq.seq (Function.const β✝ <$> x✝) fun x  …
                     -- ⊢ (SeqRight.seqRight x✝ fun x => y✝) = Seq.seq (Function.const α✝ id <$> x✝) f …
                     -- ⊢ (Seq.seq (pure g✝) fun x => x✝) = g✝ <$> x✝
                     -- ⊢ g✝ <$> pure x✝ = pure (g✝ x✝)
                     -- ⊢ (Seq.seq g✝ fun x => pure x✝) = (fun h => h x✝) <$> g✝
                     -- ⊢ (Seq.seq h✝ fun x => Seq.seq g✝ fun x => x✝) = Seq.seq (Seq.seq (Function.co …
                                -- ⊢ mapConst = Const.map ∘ Function.const β✝
                                -- ⊢ Const.map id x✝ = x✝
                                -- ⊢ Const.map (h✝ ∘ g✝) x✝ = Const.map h✝ (Const.map g✝ x✝)
                                -- ⊢ (SeqLeft.seqLeft x✝ fun x => y✝) = Const.map (Function.const β✝) x✝ + y✝
                                -- ⊢ (SeqRight.seqRight x✝ fun x => y✝) = Const.map (Function.const α✝ id) x✝ + y✝
                                -- ⊢ x✝ = Const.map g✝ x✝
                                -- ⊢ Const.map g✝ 0 = 0
                                -- ⊢ g✝ = Const.map (fun h => h x✝) g✝
                                -- ⊢ h✝ + (g✝ + x✝) = Const.map Function.comp h✝ + (g✝ + x✝)
                                                                               -- 🎉 no goals
                                                                               -- 🎉 no goals
                                                                               -- 🎉 no goals
                                                                               -- 🎉 no goals
                                                                               -- 🎉 no goals
                                                                               -- 🎉 no goals
                                                                               -- 🎉 no goals
                                                                               -- 🎉 no goals
                                                                               -- 🎉 no goals
