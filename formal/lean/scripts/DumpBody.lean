open Lean Meta

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

def flat (f : Format) : String :=
  ((f.pretty 1000000).replace "\n" " ").replace "\t" " "

-- One line per constant declared in the imported module `DUMPMOD`:
--   name, kind, #universe params, type (pp.all), value (pp.all, definitions only).
-- If the environment variable DUMP_ONLY names a file with one constant name per line, only those constants
-- get the full type/value; every other constant of the module still gets a row if it is an axiom/opaque/quot.
#eval show MetaM Unit from do
  let env ← getEnv
  let some idx := env.getModuleIdx? `DUMPMOD | throwError "module DUMPMOD not imported"
  let only? : Option (List String) ← do
    match ← IO.getEnv "DUMP_ONLY" with
    | some p => pure (some (((← IO.FS.readFile p).splitOn "\n").filter (· ≠ "")))
    | none => pure none
  let mut rows : Array String := #[]
  for (n, ci) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some idx then
      let k := kindOf ci
      if only?.all (fun l => l.contains n.toString) then
        let opts := fun (o : Options) => (o.setBool `pp.all true).setBool `pp.universes true
        let ty ← withOptions opts (ppExpr ci.type)
        let va : String ← match ci with
          | .defnInfo v => do pure (flat (← withOptions opts (ppExpr v.value)))
          | _ => pure "-"
        rows := rows.push s!"{n}\t{k}\t{ci.levelParams.length}\t{flat ty}\t{va}"
      else if k == "axiom" || k == "opaque" || k == "quot" then
        rows := rows.push s!"{n}\t{k}\t{ci.levelParams.length}\t\t"
  IO.FS.writeFile "OUTFILE" ("\n".intercalate (rows.qsort (· < ·)).toList ++ "\n")
