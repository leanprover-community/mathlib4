/-
Copyright (c) 2023 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Jon Eugster, Marcelo Lynch
-/

import Cache.Commands

/-!
# The `cache` executable

The entry point of `lake exe cache`; the commands are `Cache.Commands`.
-/

def main (args : List String) : IO UInt32 := Cache.Commands.main args
