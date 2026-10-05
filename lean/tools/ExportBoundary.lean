import QuaternionicSymmetry
import Lean

/-! Export the meaning of the publication boundary from the compiled environment.
Follow declaration types and definition bodies, including structure constructors.
Do not follow theorem proof bodies. External-library references are recorded as
leaves; all project definitions reachable by this rule are traversed. -/
open Lean Meta in
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
run_cmd do
  let env ← getEnv
  let source := ``QuaternionicSymmetry.Stage2IntrinsicSources.Sources
  let some fields := getStructureInfo? env source | throwError "Missing source record"
  let mut roots : Array (Name × String × String) := #[]
  for field in fields.fieldNames do
    let ci ← getConstInfo (source ++ Name.mkSimple field.getString!)
    let .forallE _ _ body _ := ci.type | throwError "Unexpected projection type"
    let some target := body.getAppFn.constName? | throwError "Source field is not a named predicate"
    roots := roots.push (target,"literature",field.getString!)
  roots := roots ++ #[
    (``QuaternionicSymmetry.ManifoldFourDerdzinskiIntrinsicSymmetry.DerdzinskiFourSymmetrySource,"additional","derdzinski"),
    (``QuaternionicSymmetry.Stage2IntrinsicSources.AmannInput,"additional","amann"),
    (``QuaternionicSymmetry.Stage2IntrinsicClassification.intrinsicSymmetric_c12,"target","c12"),
    (``QuaternionicSymmetry.Stage2IntrinsicClassification.intrinsicSymmetric_e14,"target","e14"),
    (``QuaternionicSymmetry.Stage2IntrinsicClassification.exists_generated_ample_contact_c12,"target","contact_c12"),
    (``QuaternionicSymmetry.Stage2IntrinsicClassification.exists_generated_ample_contact_e14,"target","contact_e14"),
    (source,"boundary","sources")]
  let mut todo := roots.map (·.1)
  let mut visited : NameHashSet := {}
  let mut nodes : Array Json := #[]
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if visited.contains name then continue
    visited := visited.insert name
    let some ci := env.find? name | throwError "Missing declaration {name}"
    let some idx := env.getModuleIdxFor? name | continue
    let moduleName := env.allImportedModuleNames[idx.toNat]!
    if !(`QuaternionicSymmetry).isPrefixOf moduleName then continue
    let mut refs := ci.type.getUsedConstants
    let kind := match ci with
      | .defnInfo _ => "definition"
      | .thmInfo _ => "theorem"
      | .inductInfo _ => if (getStructureInfo? env name).isSome then "structure" else "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom"
      | .quotInfo _ => "quotient"
    match ci with
    | .defnInfo v => refs := refs ++ v.value.getUsedConstants
    | .opaqueInfo v => refs := refs ++ v.value.getUsedConstants
    | .inductInfo v => refs := refs ++ v.ctors.toArray
    | _ => pure ()
    let deps := (refs.toList.eraseDups.toArray).qsort Name.quickLt
    todo := todo ++ deps
    let ranges ← findDeclarationRanges? name
    let doc ← findDocString? env name
    let typ ← Elab.Command.liftTermElabM do
      return (← ppExpr ci.type).pretty 100
    let location := match ranges with
      | none => Json.null
      | some r => Json.mkObj [
          ("startLine",toJson r.range.pos.line),("startColumn",toJson r.range.pos.column),
          ("endLine",toJson r.range.endPos.line),("endColumn",toJson r.range.endPos.column)]
    nodes := nodes.push <| Json.mkObj [
      ("name",toJson name.toString),("module",toJson moduleName.toString),
      ("kind",toJson kind),("location",location),("doc",toJson (doc.getD "")),
      ("type",toJson typ),("dependencies",toJson (deps.map Name.toString))]
  let rootsJson := roots.map fun (name,role,key) => Json.mkObj [
    ("name",toJson name.toString),("role",toJson role),("key",toJson key)]
  let output := Json.mkObj [("schema",toJson (1 : Nat)),("roots",toJson rootsJson),
    ("sourceFieldCount",toJson fields.fieldNames.size),("nodes",toJson nodes)]
  let path := (← IO.getEnv "BOUNDARY_OUTPUT").getD "../site-data/kernel.json"
  IO.FS.writeFile path (output.compress ++ "\n")
  logInfo m!"Exported {nodes.size} project declarations; {fields.fieldNames.size} source fields; {roots.size} roots."
