import Mathlib

namespace Kontsevich

/-- A multi-index in `d` coordinate directions. -/
abbrev MultiIndex (d : Nat) := Finsupp (Fin d) Nat

end Kontsevich
