import Kontsevich.Polynomial.Basic

/-!
# Polynomial polydifferential operators
-/

namespace Kontsevich

open scoped BigOperators

/--
One normal-form term for an `m`-ary polynomial polydifferential operator.

It consists of a polynomial coefficient and one multi-index for each input.
-/
abbrev DPolyTerm (d m : Nat) :=
  RdPoly d × (Fin m → MultiIndex d)

/-- Evaluate one normal-form term on its polynomial inputs. -/
noncomputable def evalDPolyTerm
    (term : DPolyTerm d m) (f : Fin m → RdPoly d) : RdPoly d :=
  term.1 * ∏ j : Fin m, RdPoly.pderivMulti (term.2 j) (f j)

/--
`m`-ary polynomial polydifferential operators on `ℝ^d`.

The field `normalForm` records a finite expansion in iterated partial
derivatives.
-/
structure DPoly (d m : Nat) where
  toMultilinearMap :
    MultilinearMap ℝ (fun _ : Fin m => RdPoly d) (RdPoly d)

  normalForm :
    ∃ terms : Multiset (DPolyTerm d m), ∀ f,
      toMultilinearMap f =
        (terms.map (fun term => evalDPolyTerm term f)).sum

end Kontsevich
