import Kontsevich.Workstreams.Common

/-!
# Workstream D: L-infinity and Maurer-Cartan

This module records the homotopical algebra layer: `L_infinity`
algebras, `L_infinity` morphisms, Maurer-Cartan elements, gauge
equivalence, and transport of Maurer-Cartan elements.
-/

namespace Kontsevich.Workstreams.D

/-- Workstream D metadata. -/
def plan : Workstream where
  id := .D
  title := "L-infinity and Maurer-Cartan"
  goal := "L-infinity structures, morphisms, MC elements, gauge equivalence, and MC transport."
  dependsOn := [.B]

theorem dependsOnB : plan.dependsOn = [.B] := rfl

end Kontsevich.Workstreams.D
