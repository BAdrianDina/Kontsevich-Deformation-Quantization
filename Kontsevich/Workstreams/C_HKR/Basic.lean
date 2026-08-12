import Kontsevich.Workstreams.Common

/-!
# Workstream C: Hochschild-Kostant-Rosenberg

This module records the HKR layer: the map `U_HKR`, its chain-map
property, and the quasi-isomorphism statement in the polynomial
setting.
-/

namespace Kontsevich.Workstreams.C

/-- Workstream C metadata. -/
def plan : Workstream where
  id := .C
  title := "Hochschild-Kostant-Rosenberg"
  goal := "Define U_HKR and prove its chain-map and quasi-isomorphism statements."
  dependsOn := [.B]

theorem dependsOnB : plan.dependsOn = [.B] := rfl

end Kontsevich.Workstreams.C
