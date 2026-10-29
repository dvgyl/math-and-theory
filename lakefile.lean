import Lake
import Lean.Elab.ParseImportsFast

open Lake DSL System
open Lean hiding Module

package asymmetricTutteBridge where
  moreLeanArgs := #["-j1", "-M4096", "--trust=0", "-Dcompiler.postponeCompile=false"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "56a005855ea17e0b0958f73ec801ae140b0a1679"

require «tutte-threshold» from git
  "https://github.com/michaeliu4/tutte-threshold.git" @
  "636352f0fef47b19d7d5de364858ccee2317fd66"

def isUpstreamModule (name : Name) : Bool :=
  name.toString.startsWith "TutteSource.TutteThreshold."

def sourceName (name : Name) : Name := name.replacePrefix `TutteSource `Results

def sourceFile (mod : Module) : FilePath :=
  Lean.modToFilePath mod.lib.srcDir (sourceName mod.name) "lean"

def configFile (mod : Module) : FilePath := mod.pkg.dir / "bridge-config.json"

def transformImport (imp : Import) : Import :=
  let upstream := imp.module.toString.startsWith "Results.TutteThreshold."
  {imp with
    module := if upstream then imp.module.replacePrefix `Results `TutteSource else imp.module
    importAll := upstream
    isExported := false}

def checkSource (mod : Module) : IO String := do
  let text ← IO.FS.readFile (configFile mod)
  let data ← IO.ofExcept (Json.parse text)
  let approved ← IO.ofExcept do
    let sources ← data.getObjVal? "approved_sources"
    sources.getObjValAs? (Array String) (sourceName mod.name).toString
  let digest ← IO.Process.output {
    cmd := "/usr/bin/shasum", args := #["-a", "256", (sourceFile mod).toString]
  }
  unless digest.exitCode == 0 do
    throw <| IO.userError "The source hash command failed."
  let actual := (digest.stdout.splitOn " ").head!
  unless approved.contains actual do
    throw <| IO.userError s!"Source hash rejected for {mod.name}: {actual}"
  return text

@[«module_facet»] def bridgeInput : ModuleFacetDecl :=
  .mk Module.inputFacet <| mkFacetJobConfig (buildable := false) fun mod => do
    if !isUpstreamModule mod.name then return ← Module.inputFacetConfig.run mod
    return ← Job.async do
      let path := sourceFile mod
      let contents ← IO.FS.readFile path
      let configText ← checkSource mod
      let originalHeader ← Lean.parseImports' contents path.toString
      let header := {originalHeader with
        isModule := true
        imports := originalHeader.imports.map transformImport}
      let imports ← header.imports.mapM fun imp => do
        return {toImport := imp, module? := ← findModule? imp.module : ModuleImport}
      let trace : BuildTrace := {
        caption := path.toString
        mtime := ← getMTime path
        hash := (Hash.ofText contents).mix (Hash.ofText configText)}
      setTrace trace
      return {path, imports, header, trace}

def outputArtifacts (mod : Module) : JobM ModuleOutputArtifacts := do
  return {
    isModule := true
    olean := ← computeArtifact mod.oleanFile "olean"
    oleanServer? := some (← computeArtifact mod.oleanServerFile "olean.server")
    oleanPrivate? := some (← computeArtifact mod.oleanPrivateFile "olean.private")
    ilean := ← computeArtifact mod.ileanFile "ilean"
    irSig? := some (← computeArtifact mod.irSigFile "ir.sig")
    ir? := some (← computeArtifact mod.irFile "ir")
    c := ← computeArtifact mod.cFile "c"
    bc? := ← mod.bcFile?.mapM (fun path => computeArtifact path "bc")}

def compileLegacy (mod : Module) (input : ModuleInput)
    (presetup : ModulePreSetup) (baseSetup : ModuleSetup) : JobM ModuleOutputArtifacts := do
  let setup := {baseSetup with isModule := true, imports? := some input.header.imports}
  let arts : ModuleArtifacts := {
    lean? := some presetup.srcFile
    olean? := some mod.oleanFile
    oleanServer? := some mod.oleanServerFile
    oleanPrivate? := some mod.oleanPrivateFile
    ilean? := some mod.ileanFile
    irSig? := some mod.irSigFile
    ir? := some mod.irFile
    c? := some mod.cFile
    bc? := mod.bcFile?}
  mod.clearOutputArtifacts
  mod.clearOutputHashes
  compileLeanModule presetup.srcFile (relPathFrom mod.pkg.dir presetup.srcFile) setup mod.setupFile arts
    (mod.weakLeanArgs ++ mod.leanArgs) (← getLeanPath) (← getLean) (← getLeanir)
  outputArtifacts mod

@[«module_facet»] def bridgeLeanArts : ModuleFacetDecl :=
  .mk Module.leanArtsFacet <| mkFacetJobConfig fun mod => do
    if !isUpstreamModule mod.name then return ← Module.leanArtsFacetConfig.run mod
    let inputJob ← mod.input.fetch
    let presetupJob ← mod.presetup.fetch
    let setupJob ← Module.setupFacetConfig.run mod
    return ← (inputJob.zipWith Prod.mk presetupJob |>.zipWith (fun pair setup => (pair, setup)) setupJob).mapM fun ((input, presetup), setup) => do
      setTrace presetup.trace
      let saved ← readTraceFile mod.traceFile
      let allArtifactsPresent ← Module.checkArtifactsExist mod true
      if allArtifactsPresent && (← saved.replayCachedIfUpToDate presetup.trace.hash) then
        outputArtifacts mod
      else
        buildAction presetup.trace mod.traceFile (compileLegacy mod input presetup setup)

lean_lib TutteSource where
  srcDir := ".lake/packages/tutte-threshold/lean"
  moreLeanArgs := #["-Dbackward.isDefEq.respectTransparency=false"]

@[default_target] lean_lib AsymmetricTutte
lean_lib Challenge
lean_lib Solution
lean_lib Audit where
  moreLeanArgs := #["-DwarningAsError=true"]
