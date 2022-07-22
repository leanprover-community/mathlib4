/-
Copyright (c) 2022 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: E.W.Ayers
-/
import Mathlib.Control.Profunctor
import Mathlib.Data.Prod
import Mathlib.Control.Traversable
/-!
# Profunctor optics
Definitions of profunctor optics.

One way to think about profunctor optics is to look at traversal:

```
traverse : (f : α → M β) → (l : List α) → M (List β)
```

`traverse` selects all the objects in `l` and performs `f` to them under
the monad `M`, then wraps all these up back in to a list.

Optics generalise this notion of unpacking a datastructure, performing some arbitrary action and then repackaging the datastructure.
Let's define `P α β := α → M β`, then we have `traverse : P α β → P (List α) (List β)`.


### References:
- https://hackage.haskell.org/package/profunctor-optics-0.0.2/docs/index.html
- https://dl.acm.org/doi/pdf/10.1145/3236779
- https://golem.ph.utexas.edu/category/2020/01/profunctor_optics_the_categori.html
- http://www.cs.ox.ac.uk/people/jeremy.gibbons/publications/poptics.pdf
- https://github.com/hablapps/DontFearTheProfunctorOptics
-/

namespace Control

open Profunctor

set_option checkBinderAnnotations false in
/-- A general profunctor optic. -/
def Optic (π : (Type u → Type u → Type v) → Type w) (α β σ τ : Type u) :=
  ∀ ⦃P⦄ [π P], P α β → P σ τ

namespace Optic

def Iso := Optic Profunctor

def Lens               := Optic Strong
def Lens' (α β)        := Lens α α β β

def Prism              := Optic Choice
def Prism' (α β)       := Prism α α β β

/-- Also known as an affine traversal or a traversal0.

I am going off-book here and calling it "modification" because that is what it is doing.
You can also think of it as a `Traversal` where the inner profunctor is 'called' at most once.
 -/
def Modification            := Optic Affine
def Modification' (α β)     := Modification α α β β

def Traversal          := Optic Traversing

def Setter := Optic Mapping

def Grate := Optic Closed

variable {α β σ τ χ : Type u}

namespace Iso
  def mk (g : σ → α) (f : β → τ) : Iso α β σ τ
  | _, _, p => Profunctor.dimap g f p
end Iso

namespace Lens
  def mk (g : σ → α) (s : β → σ → τ) : Lens α β σ τ
  | _, _, f => dimap (Prod.intro g id) (Prod.elim s) $ first σ $ f

  def view (l : Lens α β σ τ) : σ → α :=
    let p : Star (Const α) α β := id
    l p

  def update (l : Lens α β σ τ) (b : β) (s : σ) : τ :=
    let p : Star (Reader β) α β := fun _ b => b
    l p s b

  def matching (sca : σ → γ × α) (cbt : γ × β → τ) : Lens α β σ τ :=
  mk (Prod.snd ∘ sca) (fun b s => cbt (Prod.fst $ sca s,b))

  protected def id : Lens α β α β := mk (λ a => a) (λ b _ => b)

end Lens


namespace Prism

  def view (p : Prism α β σ τ) : σ → τ ⊕ α :=
    let f : Star (Sum α) α β := Sum.inl
    Sum.swap ∘ p f

  -- [todo] there will be a more general form but not sure what it is.
  private instance : Choice (Costar (Const β)) := {
      left := fun _ fab b => Sum.inl <| fab b,
      right := fun _ fab b => Sum.inr <| fab b,
    }

  def update (p : Prism α β σ τ) : β → τ :=
    let f : Costar (Const β) α β := id
    p f

  def mk (g : σ → τ ⊕ α) (s : β → τ) : Prism α β σ τ
    | _, _, f => dimap g (Sum.elim id s) $ right _ $ f

end Prism

namespace Modification

  def mk (f : σ → τ ⊕ α) (g : σ → β → τ) : Modification α β σ τ
    | _, _, p => dimap (Prod.intro id f) (Function.uncurry $ Sum.elim id ∘ g) $ second σ $ right τ p

end Modification

namespace Grate

  def Concrete (α β σ τ : Type u) := ((σ → α) → β) → τ
  instance : Closed (Concrete α β) where
    dimap := fun yx st g yab => st $ g $ fun xa => yab $ xa ∘ yx
    close := fun _ g f s => g <| fun i => f <| fun j => i <| j s

  protected def mk (f : ((σ → α) → β) → τ) : Grate α β σ τ
    | _, _, p => dimap (fun a s => s a) f (close (σ → α) p)

  def run (g : Grate α β σ τ) : ((σ → α) → β) → τ :=
    let o : Concrete α β α β := fun x => x id
    g o

  def zipWith {F : Type u → Type u} [Functor F] : Grate α β σ τ → (F α → β) → (F σ → τ)
    | g, c => show Costar F σ τ by exact g c

  def zip2:  Grate α β σ τ  → (α → α → β) → σ → σ → τ
    | g, p =>
      let p : Costar Prod.Square α β := Function.uncurry p
      Function.curry $ g $ p

  def distributed [Functor F] [Distributive F] : Grate α β (F α) (F β) :=
    Grate.mk fun k => k <$> Distributive.distReader id

  def endomorphed (χ : Type u) : Grate α α (χ → α) (χ → α)
    | _, _, p => close _ p

end Grate

def traversing (F) [Traversable F] : Traversal σ τ (F σ) (F τ)
| _, t => Representable.lift (@traverse _ _ _ t.a _ _)

def arrays (t : Traversal α β σ τ) : σ → Array α :=
  let f : Star (Const (Array α)) α β := fun a => #[a]
  t f

def united : Lens PUnit PUnit α α :=
  Lens.mk (fun _ => PUnit.unit) (fun _ a => a)

def voided : Lens α α PEmpty PEmpty :=
  Lens.mk (fun e => by cases e) (fun _ e => e)

def fst : Lens α β (α × χ) (β × χ) :=
  Lens.mk Prod.fst (fun b (_,x) => (b,x))

def snd : Lens α β (χ × α) (χ × β) :=
  Lens.mk Prod.snd (fun b (x,_) => (x,b))

def the : Prism α β (Option α) (Option β) :=
  Prism.mk (fun | none => Sum.inl none | some a => Sum.inr a) some

def both : Traversal α β (α × α) (β × β) :=
  traversing Prod.Square

def never : Prism PEmpty PEmpty α α :=
  Prism.mk Sum.inl (fun x => by cases x)

end Optic

end Control
