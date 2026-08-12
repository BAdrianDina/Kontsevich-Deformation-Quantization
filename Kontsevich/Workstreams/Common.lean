/-
Copyright (c) 2026 Adrian Dina.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Dina
-/

/-!
# Common workstream metadata

This file contains only the project skeleton. It records the six parts
of the Kontsevich formalization path as Lean data, so each workstream
can build without importing the global module.
-/

namespace Kontsevich

/-- The six workstreams in the Kontsevich formalization path. -/
inductive WorkstreamId where
  | A
  | B
  | C
  | D
  | E
  | F
  deriving DecidableEq, Repr

/-- Minimal metadata attached to one workstream. -/
structure Workstream where
  id : WorkstreamId
  title : String
  goal : String
  dependsOn : List WorkstreamId
  deriving Repr

/-- A workstream has no formal prerequisites inside this scaffold. -/
def Workstream.hasNoDependencies (w : Workstream) : Prop :=
  w.dependsOn = []

end Kontsevich
