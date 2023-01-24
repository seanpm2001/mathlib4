import Mathlib

open Lean

#eval show MetaM _ from do
  let m := Mathlib.Prelude.Rename.getRenameMap (← getEnv)
  for (fr, to') in ToAdditive.translations.getState (← getEnv) do
    match m.toLean3.contains fr, m.toLean3.contains to' with
    | true, false => println! "Good ❌ {to'} <- ✅ {fr}"
    | false, true => println! "Bad  ❌ {fr} -> ✅ {to'}"
    | _, _ => pure ()

