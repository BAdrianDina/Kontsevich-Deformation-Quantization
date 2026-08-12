import Kontsevich.Workstreams.A_CombinatorialAndPolynomial.Basic
import Kontsevich.Workstreams.B_GradedAndLie.Basic
import Kontsevich.Workstreams.C_HKR.Basic
import Kontsevich.Workstreams.D_LInfinityMC.Basic
import Kontsevich.Workstreams.E_KontsevichFormula.Basic
import Kontsevich.Workstreams.F_AnalyticInput.Basic

/-!
# Global Kontsevich implementation path

This module connects the six independent workstreams into the project
path. It does not contain mathematics yet. It is the place where later
global theorems will import the data produced by each workstream.
-/

namespace Kontsevich.Global

/-- The ordered implementation path for the first Kontsevich formalization pass. -/
def implementationPath : List Workstream :=
  [ Workstreams.A.plan
  , Workstreams.B.plan
  , Workstreams.C.plan
  , Workstreams.D.plan
  , Workstreams.E.plan
  , Workstreams.F.plan
  ]

theorem implementationPath_length : implementationPath.length = 6 := rfl

end Kontsevich.Global
