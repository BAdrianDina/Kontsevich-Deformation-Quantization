import Kontsevich.Workstreams.Common

/-!
# Workstream E: Kontsevich formula on R^d

This module records the formula layer: the maps `U_n`, the Moyal
test case, the `L_infinity` identities modulo the boundary identities,
and the star-product corollary.
-/

namespace Kontsevich.Workstreams.E

/-- Workstream E metadata. -/
def plan : Workstream where
  id := .E
  title := "Kontsevich formula on R^d"
  goal := "Define U_n, verify the Moyal case, and prove the star-product corollary modulo boundary identities."
  dependsOn := [.A, .B, .C, .D]

theorem dependsOnAlgebraicLayer : plan.dependsOn = [.A, .B, .C, .D] := rfl

end Kontsevich.Workstreams.E
