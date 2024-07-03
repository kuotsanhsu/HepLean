/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Lean
import Mathlib.Tactic.Linter.TextBased
/-!

# Double line Lint

This linter double empty lines in files.

## Note

Parts of this file are adapted from `Mathlib.Tactic.Linter.TextBased`,
  authored by Michael Rothgang.
-/
open Lean System Meta

/-- Given a list of lines, outputs an error message and a line number. -/
def HepLeanTextLinter : Type := Array String → Array (String × ℕ)

/-- Checks if there are two consecutive empty lines. -/
def doubleEmptyLineLinter : HepLeanTextLinter := fun lines ↦ Id.run do
  let enumLines := (lines.toList.enumFrom 1)
  let pairLines := List.zip enumLines (List.tail! enumLines)
  let errors := pairLines.filterMap (fun ((lno1, l1), _, l2) ↦
    if l1.length == 0 && l2.length == 0  then
      some (s!" Double empty line. ", lno1)
    else none)
  errors.toArray

structure HepLeanErrorContext where
  /-- The underlying `message`. -/
  error : String
  /-- The line number -/
  lineNumber : ℕ
  /-- The file path -/
  path : FilePath

def printErrors (errors : Array HepLeanErrorContext) : IO Unit := do
  for e in errors do
    IO.println (s!"error: {e.path}:{e.lineNumber}: {e.error}")

def hepLeanLintFile (path : FilePath) : IO Bool := do
  let lines ← IO.FS.lines path
  let allOutput := (Array.map (fun lint ↦
    (Array.map (fun (e, n) ↦ HepLeanErrorContext.mk e n path)) (lint lines)))
    #[doubleEmptyLineLinter]
  let errors := allOutput.flatten
  printErrors errors
  return errors.size > 0

def main (_ : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mods : Name :=  `HepLean
  let imp :  Import := {module := mods}
  let mFile ← findOLean imp.module
  unless (← mFile.pathExists) do
        throw <| IO.userError s!"object file '{mFile}' of module {imp.module} does not exist"
  let (hepLeanMod, _) ← readModuleData mFile
  let mut warned := false
  for imp in hepLeanMod.imports do
    if imp.module == `Init then continue
    let filePath := (mkFilePath (imp.module.toString.split (· == '.'))).addExtension "lean"
    if ← hepLeanLintFile filePath  then
      warned := true
  if warned then
    throw <| IO.userError s!"Errors found."
  return 0
