import Kontsevich.Polynomial.Basic
set_option linter.style.whitespace false
/-!
# Polynomial bivectors

This module defines polynomial bivectors as antisymmetric coefficient families.
-/

namespace Kontsevich

/-- Polynomial bivectors on `ℝ^d`. -/
def Bivector (d : Nat) :
    Submodule ℝ (Fin d → Fin d → RdPoly d) where
  carrier := {γ | ∀ i j, γ i j = -γ j i}

  zero_mem' := by
    intro i j
    simp

  add_mem' := by
    intro γ η hγ hη i j
    calc
      (γ + η) i j = γ i j + η i j := rfl
      _ = (-γ j i) + (-η j i) := by
        rw [hγ i j, hη i j]
      _ = -(γ j i + η j i) := by
        rw [neg_add]

  smul_mem' := by
    intro c γ hγ i j
    calc
      (c • γ) i j = c • γ i j := rfl
      _ = c • (-γ j i) := by
        rw [hγ i j]
      _ = -(c • γ j i) := by
        rw [smul_neg]

namespace Bivector

variable {d : Nat}

/-- The `(i,j)` coefficient of a polynomial bivector. -/
def coeff (γ : Bivector d) (i j : Fin d) : RdPoly d :=
  γ.1 i j

theorem coeff_antisymm (γ : Bivector d) (i j : Fin d) :
    coeff γ i j = -coeff γ j i := by
  simpa [coeff] using γ.2 i j

@[simp]
theorem coeff_add (γ η : Bivector d) (i j : Fin d) :
    coeff (γ + η) i j = coeff γ i j + coeff η i j := by
  simp [coeff]
@[simp]
theorem coeff_smul (c : ℝ) (γ : Bivector d) (i j : Fin d) :
    coeff (c • γ) i j = c • coeff γ i j := by
  simp [coeff]
/-
extracting a fixed coefficientis a ℝ linear map
-/

def coeffLinearMap(i j : Fin d):
  Bivector d →ₗ[ℝ] RdPoly d where
  toFun :=fun γ => coeff γ i j

  map_add':= by
    intro γ η
    exact coeff_add γ η i j

  map_smul' := by
    intro c γ
    exact coeff_smul c γ i j

end Bivector
end Kontsevich
