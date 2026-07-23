/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
import Mathlib.Computability.SingleOracle.Jump

/-!
# Reducibility theorems

This file formalises basic reducibility results.

-/

namespace Oracle.Single.RecursiveIn.Rin
open Oracle.Single
open Part Nat

alias zero  := RecursiveIn.zero
alias succ  := RecursiveIn.succ
alias left  := RecursiveIn.left
alias right := RecursiveIn.right
alias oracle := RecursiveIn.oracle
alias pair  := RecursiveIn.pair
alias comp  := RecursiveIn.comp
alias prec  := RecursiveIn.prec
alias rfind := RecursiveIn.rfind

theorem of_eq {O : ℕ → ℕ} {f g : ℕ →. ℕ} (hf : RecursiveIn O f) (H : ∀ n, f n = g n) :
    RecursiveIn O g :=
  (funext H : f = g) ▸ hf

theorem of_eq_tot {O : ℕ → ℕ} {f : ℕ →. ℕ} {g : ℕ → ℕ} (hf : RecursiveIn O f) (H : ∀ n, g n ∈ f n) :
    RecursiveIn O g :=
  of_eq hf fun n => eq_some_iff.2 (H n)
theorem of_primrecIn {O : ℕ → ℕ} {f : ℕ → ℕ} (hf : PrimrecIn O f) : RecursiveIn O f := by
  induction hf with
  | zero => exact zero
  | succ => exact succ
  | left => exact left
  | right => exact right
  | oracle => exact oracle
  | pair _ _ pf pg =>
    refine of_eq_tot (pair pf pg) fun n => ?_
    simp [Seq.seq]
  | comp _ _ pf pg =>
    refine of_eq_tot (comp pf pg) fun n => (by simp)
  | prec _ _ pf pg =>
    refine of_eq_tot (prec pf pg) fun n => ?_
    simp only [unpaired, PFun.coe_val, bind_eq_bind]
    induction n.unpair.2 with
    | zero => simp
    | succ m IH =>
      simp only [mem_bind_iff, mem_some_iff]
      exact ⟨_, IH, rfl⟩

@[simp] lemma partCompTotal {O : ℕ → ℕ} {f : ℕ →. ℕ} {g : ℕ → ℕ}
    (h1 : RecursiveIn O f) (h2 : RecursiveIn O g) :
    (RecursiveIn O ↑(f∘g)) := by
  have h3 : (↑(f∘g) : ℕ →. ℕ) = fun x => g x >>= (↑f : ℕ →. ℕ) := by
    funext xs
    simp only [Function.comp_apply, Part.coe_some, Part.bind_eq_bind, Part.bind_some]
  rw [h3]
  exact comp h1 h2
@[simp] lemma totalComp {O : ℕ → ℕ} {f g : ℕ → ℕ}
  (h1 : RecursiveIn O f) (h2 : RecursiveIn O g) : (RecursiveIn O ↑(f∘g)) := by
  have h3 : (↑(f∘g) : ℕ →. ℕ) = fun x => g x >>= (↑f : ℕ →. ℕ) := by
    funext xs
    simp only [PFun.coe_val, Function.comp_apply, Part.coe_some, Part.bind_eq_bind, Part.bind_some]
  rw [h3]
  exact comp h1 h2
@[simp] lemma id {O : ℕ → ℕ} : RecursiveIn O fun x => x := of_primrecIn PrimrecIn.id
@[simp] lemma someTotal (O : ℕ → ℕ) (f : ℕ → ℕ) (h1 : RecursiveIn O f) :
  RecursiveIn O fun x => Part.some (f x) := by
  apply totalComp
  · exact h1
  · apply id
@[simp] lemma pair' (f g : ℕ → ℕ) :
    ((↑fun x ↦ Nat.pair (f x) (g x)) : ℕ →. ℕ)= fun (x : ℕ) => (Nat.pair <$> (f x) <*> (g x)) := by
  simp only [Seq.seq, coe_some, map_eq_map, map_some, bind_some]
  funext xs
  simp only [PFun.coe_val]
@[simp] lemma totalComp' {O : ℕ → ℕ} {f g : ℕ → ℕ}
    (hf : RecursiveIn O f) (hg : RecursiveIn O g) :
    (RecursiveIn O (fun x => (f (g x)) : ℕ → ℕ) ) := totalComp (hf) (hg)
@[simp] lemma comp₂ {O : ℕ → ℕ} {f : ℕ → ℕ →. ℕ} {g h : ℕ → ℕ}
    (hf : RecursiveIn O fun x => f x.unpair.1 x.unpair.2)
    (hg : RecursiveIn O g) (hh : RecursiveIn O h) :
    (RecursiveIn O (fun x => (f (g x) (h x))) ) := by
  have main :
      (fun x => (f (g x) (h x))) =
      ((fun x => f x.unpair.1 x.unpair.2) ∘ (fun n ↦ Nat.pair (g n) (h n))) := by
    funext xs
    simp only [Function.comp_apply, unpair_pair]
  rw [main]
  refine partCompTotal hf ?_
  · rw [pair']
    apply pair hg hh
@[simp] lemma totalComp₂ {O : ℕ → ℕ} {f : ℕ → ℕ → ℕ} {g h : ℕ → ℕ}
    (hf : RecursiveIn O fun x => f x.unpair.1 x.unpair.2)
    (hg : RecursiveIn O g) (hh : RecursiveIn O h) :
    (RecursiveIn O (fun x => (f (g x) (h x)) : ℕ → ℕ) ) := by
  have main :
      (fun x => (f (g x) (h x)) : ℕ → ℕ) =
      ((fun x => f x.unpair.1 x.unpair.2) ∘ (fun n ↦ Nat.pair (g n) (h n))) := by
    funext xs
    simp only [Function.comp_apply, Nat.unpair_pair]
  rw [main]
  apply totalComp
  · exact hf
  · rw [pair']
    apply pair hg hh

@[simp] lemma PrimrecIn.totalComp {O : ℕ → ℕ} {f g : ℕ → ℕ}
    (h1 : PrimrecIn O f) (h2 : PrimrecIn O g) : PrimrecIn O ↑(f∘g) := by
  rw [show (f∘g) = fun x => f (g x) from rfl]
  exact PrimrecIn.comp h1 h2
@[simp] lemma PrimrecIn.comp₂ {O : ℕ → ℕ} {f : ℕ → ℕ → ℕ} {g h : ℕ → ℕ}
    (hf : PrimrecIn O fun x => f x.unpair.1 x.unpair.2)
    (hg : PrimrecIn O g) (hh : PrimrecIn O h) :
    (PrimrecIn O (fun x => (f (g x) (h x)) : ℕ → ℕ) ) := by
  have main :
      (fun x => (f (g x) (h x)) : ℕ → ℕ) =
      ((fun x => f x.unpair.1 x.unpair.2) ∘ (fun n ↦ Nat.pair (g n) (h n))) := by
    funext xs
    simp only [Function.comp_apply, Nat.unpair_pair]
  rw [main]
  apply PrimrecIn.totalComp
  · exact hf
  · apply PrimrecIn.pair hg hh

open Computability
open Oracle.Single.Code
theorem eval_K_computable {O : ℕ → ℕ} :
    RecursiveIn O (fun x ↦ Oracle.Single.eval O x x) := by
  have h :
      (fun (x : ℕ) ↦ Oracle.Single.eval O x x) =
      (fun (x : ℕ) => Oracle.Single.eval O x.unpair.1 x.unpair.2) ∘ (fun x=>Nat.pair x x) := by
    funext xs
    simp only [Function.comp_apply, Nat.unpair_pair]
  rw [h]
  refine RecursiveIn.Rin.partCompTotal rec_eval₁ ?_
  exact RecursiveIn.Rin.of_primrecIn (PrimrecIn.pair PrimrecIn.id PrimrecIn.id)

end Oracle.Single.RecursiveIn.Rin
namespace Oracle.Single.Code
def c_pair_proj (x : ℕ) : Code := pair (c_const x) c_id
theorem c_pair_proj_evp {O x} : evalp O (c_pair_proj x) = Nat.pair x := by simp [c_pair_proj]
lemma PrimrecIn.pair_proj {O x} : PrimrecIn O (Nat.pair x) := by
  rw [←c_pair_proj_evp]
  exact code_prim_prop

end Oracle.Single.Code
