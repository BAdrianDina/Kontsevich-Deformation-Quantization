import Kontsevich.Workstreams.Common

/-!
# Workstream F: analytic input

This module records the deferred analytic layer: configuration
spaces, compactifications, angle forms, Stokes' theorem with corners,
and Kontsevich weight integrals.
-/

namespace Kontsevich.Workstreams.F

/-- Workstream F metadata. -/
def plan : Workstream where
  id := .F
  title := "Analytic input"
  goal := "Configuration spaces, compactifications, angle forms, Stokes with corners, and weights."
  dependsOn := [.E]

theorem dependsOnFormulaLayer : plan.dependsOn = [.E] := rfl

end Kontsevich.Workstreams.F
