import Kontsevich.Workstreams.Common

/-!
# Workstream B: graded and Lie infrastructure

This module records the algebraic layer around graded Poisson
structures, the Schouten-Nijenhuis bracket, the Gerstenhaber bracket,
the Hochschild differential, and the two dg Lie algebras.
-/

namespace Kontsevich.Workstreams.B

/-- Workstream B metadata. -/
def plan : Workstream where
  id := .B
  title := "Graded and Lie infrastructure"
  goal := "Schouten-Nijenhuis, Gerstenhaber, Hochschild differential, and dg Lie instances."
  dependsOn := [.A]

theorem dependsOnA : plan.dependsOn = [.A] := rfl

end Kontsevich.Workstreams.B
