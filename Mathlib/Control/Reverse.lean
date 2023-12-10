/-
Copyright (c) 2023 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
import Mathlib.Control.Basic

universe u v

-- reverses the control flow imposed by `m`'s sequence operation
structure SeqOpposite (m : Type u → Type v) (α : Type u) where
  op :: unop : m α

namespace SeqOpposite

variable (m : Type u → Type v)

postfix:max "ʳᵉᵛ" => SeqOpposite

@[elab_as_elim] protected def rec' {α} {F : ∀ _ : mʳᵉᵛ α, Sort v} (h : ∀ X, F (op X)) : ∀ X, F X := fun X => h (unop X)

instance instFunctor [Functor m] : Functor mʳᵉᵛ where
  mapConst := fun a b => op (Functor.mapConst a (unop b))
  map := fun f x => op (Functor.map f (unop x))

instance instPure [Pure m] : Pure mʳᵉᵛ where
  pure x := op (pure x)

instance instApplicative [Applicative m] : Applicative mʳᵉᵛ :=
  { SeqOpposite.instFunctor m, SeqOpposite.instPure m with
    seq := fun f x => op $ (fun y g => g y) <$> unop (x ()) <*> unop f }

instance [Functor m] [LawfulFunctor m] : LawfulFunctor mʳᵉᵛ where
  map_const := by intros; funext x y; induction y; refine congrArg op ?_
                  exact congrFun (congrFun LawfulFunctor.map_const _) _
  id_map := by intros α x; induction x; refine congrArg op ?_
               exact LawfulFunctor.id_map _
  comp_map := by intros α β γ g h x; induction x; refine congrArg op ?_
                 exact LawfulFunctor.comp_map _ _ _

instance [Applicative m] [LawfulApplicative m] : LawfulApplicative mʳᵉᵛ where
  seqLeft_eq := by intros; exact rfl
  seqRight_eq := by intros; exact rfl
  pure_seq := by intros α β g x; induction x; refine congrArg op ?_;
                 refine Eq.trans (seq_pure _ _) ?_
                 exact Eq.trans (Eq.symm (comp_map _ _ _)) rfl
  map_pure := fun _ _ => congrArg op (map_pure _ _)
  seq_pure := by intros α β g x; induction g; refine congrArg op ?_;
                 exact Eq.trans (congrFun (congrArg _ $ map_pure _ _) _) (pure_seq _ _)
  seq_assoc := by intros α β γ x g h; induction x; induction g; induction h;
                  refine congrArg op ?_
                  refine Eq.trans ?_ $ Eq.symm $ seq_assoc _ _ _
                  dsimp only [instApplicative, instFunctor]
                  rw [← comp_map, seq_map_assoc, seq_map_assoc,
                      map_seq, map_seq, ← comp_map, ← comp_map, ← comp_map]
                  exact rfl

end SeqOpposite
