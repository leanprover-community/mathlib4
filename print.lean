import Mathlib

open Lean Meta IO FS

#check show MetaM Unit from do
  let env ← getEnv
  let decls := env.constants.toList.filter fun e =>
    !e.snd.isUnsafe && !e.fst.isInternalOrNum && e.snd.hasValue true && !isMatcherCore env e.fst &&
    !isAuxRecursor env e.fst && !env.isProjectionFn e.fst &&
    !(e.fst.splitAt 1).fst.lastComponentAsString == "Simps" &&
    e.snd.type.getForallBody.withApp fun f _ => f.isBVar
  println decls.length
  let str := "" |> decls.foldl
    fun rest e => s!"{rest}{e.fst},{(env.getModuleFor? e.fst).getD `none}\n"
  withFile (.mk "working.csv") .write fun handle => handle.putStr str
