import Mathlib.Data.FunLike.Basic

-- IGNORE FROM HERE TO LINE 41
variable (T:Type*) {a:Type*} {b:Type*}
def PX (foo:a → b) : Prop := sorry
structure XHom (a:Type*) (b:Type*) where
  toFun : a → b
  xProp : PX toFun

instance (a:Type*) (b:Type*): FunLike (XHom a b) a b := {
  coe := XHom.toFun
  coe_injective' := fun f g h => by
    cases f; cases g; congr
}

@[ext]
lemma XHom.ext ⦃f:XHom a b⦄ ⦃g:XHom a b⦄ (h:∀ x, f x = g x): f = g :=
  DFunLike.ext _ _ h
variable (a b)

class XHomClass [FunLike T a b] where
  xProp' : ∀ (f:T), PX f

instance XHom.instXHomClass: XHomClass (XHom a b) a b where
  xProp' := XHom.xProp

protected def XHom.copy {a} {b} (f : XHom a b) (f' : a → b) (h : f' = f) :
    XHom a b where
  toFun := f'
  xProp := h.symm ▸ f.xProp

@[simp]
theorem XHom.coe_copy (f : XHom a b) (f' : a → b) (h : f' = f) :
    (f.copy f' h) = f' := rfl


@[simps]
def XHom.id (a:Type*) : XHom a a where
  toFun x := x
  xProp := sorry


def XHom.comp {a} {b} {c:Type*} (hnp : XHom b c) (hmn : XHom a b) : XHom a c where
  toFun := hnp ∘ hmn
  xProp := sorry

@[simp]
theorem XHom.coe_comp {a} {b} {c:Type*} (g : XHom b c) (f : XHom a b) :
    ↑(g.comp f) = g ∘ f := rfl

theorem XHom.comp_apply {a} {b} {c:Type*} (g : XHom b c) (f : XHom a b) (x : a) :
    g.comp f x = g (f x) := rfl


theorem XHom.comp_assoc {a} {b} {c:Type*} {d : Type*}
    (f : XHom a b) (g : XHom b c) (h : XHom c d) :
    (h.comp g).comp f = h.comp (g.comp f) := rfl

theorem XHom.cancel_right {a} {b} {c:Type*} {g₁ g₂ : XHom b c} {f : XHom a b}
    (hf : Function.Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => XHom.ext <| hf.forall.2 (DFunLike.ext_iff.1 h), fun h => h ▸ rfl⟩

theorem XHom.cancel_left {a} {b} {c:Type*} {g : XHom b c} {f₁ f₂ : XHom a b}
    (hg : Function.Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => XHom.ext fun x => hg <| by rw [← XHom.comp_apply, h, XHom.comp_apply],
    fun h => h ▸ rfl⟩

@[simp]
theorem XHom.comp_id (f : XHom a b) : f.comp (XHom.id a) = f :=
  XHom.ext fun _ => rfl

@[simp]
theorem XHom.id_comp (f : XHom a b) : (XHom.id b).comp f = f :=
  XHom.ext fun _ => rfl

variable {a} {s:a→ Prop} {b}

section

def PY (foo:a → b) (s:a → Prop) : Prop := sorry-- some statement about foo and s
end

structure YHom (s:a→Prop) (b) where
  toFun : a → b
  yProp : PY toFun s -- a proof that P holds for toFun and s


class YHomClass (T) (s) (b) [FunLike T a b] where
  yProp' : ∀ f:T, PY f s

instance (s:a → Prop) (b): FunLike (YHom s b) a b := {
  coe := YHom.toFun
  coe_injective' := fun f g h => by
    cases f; cases g; congr
}

@[ext]
lemma YHom.ext ⦃f:YHom s b⦄ ⦃g:YHom s b⦄ (h:∀ x, f x = g x): f = g :=
  DFunLike.ext _ _ h

instance YHom.instYHomClass (s:a→ Prop) (b) : YHomClass (YHom s b) s b where
  yProp' := yProp


section
protected def YHom.copy (f : YHom s b) (f' : a → b) (h : f' = f) :
    YHom s b where
  toFun := f'
  yProp := h.symm ▸ f.yProp

@[simp]
theorem YHom.coe_copy (f : YHom s b) (f' : a → b) (h : f' = f) :
    (f.copy f' h) = f' := rfl

@[simps]
def YHom.id (s:a → Prop) : YHom s a where
  toFun x := x
  yProp := sorry


def YHom.comp {s₂:b → Prop} {c:Type*} (hnp : YHom s₂ c) (hmn : YHom s b) : YHom s c where
  toFun := hnp ∘ hmn
  yProp := sorry

@[simp]
theorem YHom.coe_comp {s₂:b → Prop} {c:Type*} (g : YHom s₂ c) (f : YHom s b) :
    ↑(g.comp f) = g ∘ f := rfl

theorem YHom.comp_apply {s₂:b → Prop} {c:Type*} (g : YHom s₂ c) (f : YHom s b) (x : a) :
    g.comp f x = g (f x) := rfl

theorem YHom.comp_assoc {s₂:b → Prop} {c:Type*} {s₃: c → Prop} {d : Type*}
    (f : YHom s b) (g : YHom s₂ c) (h : YHom s₃ d) :
    (h.comp g).comp f = h.comp (g.comp f) := rfl

theorem YHom.cancel_right {s₂:b → Prop} {c:Type*} {g₁ g₂ : YHom s₂ c} {f : YHom s b}
    (hf : Function.Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => YHom.ext <| hf.forall.2 (DFunLike.ext_iff.1 h), fun h => h ▸ rfl⟩

theorem YHom.cancel_left {s₂:b → Prop} {c:Type*} {g : YHom s₂ c} {f₁ f₂ : YHom s b}
    (hg : Function.Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => YHom.ext fun x => hg <| by rw [← YHom.comp_apply, h, YHom.comp_apply],
    fun h => h ▸ rfl⟩

@[simp]
theorem YHom.comp_id (f : YHom s b) : f.comp (YHom.id s) = f :=
  YHom.ext fun _ => rfl

@[simp]
theorem YHom.id_comp {s₂:b → Prop} (f : YHom s b) : (YHom.id s₂).comp f = f :=
  YHom.ext fun _ => rfl
