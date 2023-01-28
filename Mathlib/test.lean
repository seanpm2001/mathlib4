import Mathlib

open Lean
open System.FilePath
open IO.FS

def String.condense (s : String) : String :=
(String.join (s.splitOn (sep := "_"))).map .toLower

def Lean.Name.condense : Name → Name
| .str p s => .str p.condense s.condense
| n => n

def readMissers : IO (HashMap String String) := do
  let missers ← lines ⟨"/home/jmc/repos/mathlib4/missers"⟩
  let res : HashMap String String := mkHashMap 5000
  return missers.foldl (fun h s ↦ h.insert s.condense s) res

#eval show MetaM _ from do
  let missers ← readMissers
  let env := ← getEnv
  env.constants.forM fun n ci ↦ do
    let k := toString n.condense
    if missers.contains k then
      let r := declRangeExt.find? env n
      if let Option.none := r then
        println! "!!! Cannot find pos for {n}\n"
      else
      let i := env.getModuleIdxFor? n
      if let Option.none := i then
        println! "!!! Cannot find module index for {n}\n"
      else
      let m := env.header.moduleNames.get? (← i)
      if let Option.none := m then
        println! "!!! Cannot find module name for {n}\n"
      else
      println! "{← m}::{(← r).range.pos.1}"
      println! "#align {missers.find! k} {n}"
      println! ""
