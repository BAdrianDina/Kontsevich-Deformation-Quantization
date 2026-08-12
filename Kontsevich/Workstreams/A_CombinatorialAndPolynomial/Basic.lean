import Kontsevich.Workstreams.Common

/-!
# Workstream A: combinatorial and polynomial scaffolding

This module is intentionally independent of the other workstreams.
It is the entry point for admissible graphs, polynomial polyvector
fields, polynomial polydifferential operators, the operator `B_Gamma`,
and axiomatised graph weights.
-/

namespace Kontsevich.Workstreams.A

/-- Workstream A metadata. -/
def plan : Workstream where
  id := .A
  title := "Combinatorial and polynomial scaffolding"
  goal := "Admissible graphs, polynomial objects on R^d, B_Gamma, and graph weights."
  dependsOn := []

theorem noDependencies : plan.hasNoDependencies := rfl

end Kontsevich.Workstreams.A
