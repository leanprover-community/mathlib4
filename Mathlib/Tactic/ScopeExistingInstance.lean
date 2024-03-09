import Mathlib.Tactic.ScopedNS

macro (name := scopeExistingInstance) "scope_existing_instance" "[" name:ident "]" e:ident : command =>
  `(attribute [-instance] $e
    scoped[$name] attribute [instance] $e)

