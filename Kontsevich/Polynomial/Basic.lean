import Mathlib
import Kontsevich.Basic.MultiIndex
noncomputable section
namespace Kontsevich
open scoped BigOperators
open MvPolynomial

/- Polynomial functions on `ℝ^d`, represented as multivariate polynomials
in variables indexed by `Fin d`. -/
abbrev RdPoly (d : ℕ):= MvPolynomial (Fin d) ℝ

namespace RdPoly
variable {d : ℕ}
--The coordinate polynomial x_i.
def coord (i : Fin d) : Kontsevich.RdPoly d:= X i
--The partial derivative ∂ / ∂ x_i viewed as a derivation
def pderiv (i : Fin d) :
Derivation ℝ (Kontsevich.RdPoly d) (Kontsevich.RdPoly d) :=
 MvPolynomial.pderiv i

--The Partial derivative ∂ / ∂ x_i viewed as a  linear endomorphism
def pderivEnd (i : Fin d) : Module.End ℝ (Kontsevich.RdPoly d):=
 (pderiv i).toLinearMap

-- Mixed partial derivatives comute
/- theorem pderivative_comm (i j : Fin d) :
    pderivEnd i * pderivEnd j = pderivEnd j * pderivEnd i := by
    apply LinearMap.ext
    intro f
    simp [pderivEnd, pderiv, Finsupp.add_apply,
     add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]

-/
-- The r-fold partial derivative with respect to x_i.
def pderivIter (i : Fin d) (r : ℕ) : Module.End ℝ (RdPoly d) :=
(pderivEnd i)^r

-- The derivative associated to a multi-index, using the standard order on coordinate indices.
def pderivMulti (α : MultiIndex d) : Module.End ℝ (RdPoly d)
:= (List.ofFn (fun i : Fin d => (pderivEnd i)^ α i)).prod


/-
If exactly one exponent is `1` and all others are `0`, the ordered product is
the corresponding single factor:
\[
  \prod_{j=0}^{d-1} a_j^{\delta_i(j)} = a_i.
\]
-/
private theorem prod_ofFn_pow_single
    {M : Type*} [Monoid M] (a : Fin d → M) (i : Fin d) :
    (List.ofFn (fun j : Fin d =>
      (a j) ^ (Finsupp.single i 1 j))).prod = a i := by
  induction d with
  | zero =>
      exact Fin.elim0 i
  | succ d ih =>
      refine Fin.cases ?_ (fun i => ?_) i
      · rw [List.ofFn_succ]
        simp only [List.prod_cons]
        have htail :
            (List.ofFn (fun j : Fin d =>
              (a (Fin.succ j)) ^
                (Finsupp.single (0 : Fin (d + 1)) 1 (Fin.succ j)))).prod =
              1 := by
          have hfun :
              (fun j : Fin d =>
                (a (Fin.succ j)) ^
                  (Finsupp.single (0 : Fin (d + 1)) 1 (Fin.succ j))) =
                fun _ => (1 : M) := by
            funext j
            have hne : (0 : Fin (d + 1)) ≠ Fin.succ j :=
              Ne.symm (Fin.succ_ne_zero j)
            simp
          rw [hfun]
          simp
        have hhead :
            Finsupp.single (0 : Fin (d + 1)) 1 (0 : Fin (d + 1)) = 1 := by
          simp
        rw [hhead, pow_one, htail, mul_one]
      · rw [List.ofFn_succ]
        have htail :
            (fun j : Fin d =>
              (a (Fin.succ j)) ^
                (Finsupp.single (Fin.succ i) 1 (Fin.succ j))) =
              (fun j : Fin d =>
                (a (Fin.succ j)) ^ (Finsupp.single i 1 j)) := by
          funext j
          simp [Finsupp.single_apply]
        rw [htail]
        have hhead :
            Finsupp.single (Fin.succ i) 1 (0 : Fin (d + 1)) = 0 := by
          simp
        rw [hhead, pow_zero]
        simp only [List.prod_cons, one_mul]
        exact ih (fun j : Fin d => a (Fin.succ j)) i


/-
The mixed derivative with multi-index \(\delta_i\) is the ordinary partial
derivative:
\[
  \partial^{\delta_i} f = \partial_i f.
\]
-/
@[simp]
theorem pderivMulti_single_one_apply
    (i : Fin d) (f : RdPoly d) :
    pderivMulti (Finsupp.single i 1) f = pderiv i f := by
  change
    (List.ofFn (fun j : Fin d =>
      (pderivEnd j) ^ (Finsupp.single i 1 j))).prod f =
        pderivEnd i f
  rw [prod_ofFn_pow_single]


@[simp]
theorem pderivMulti_zero :
  pderivMulti (0: MultiIndex d) = 1 := by
  simp[pderivMulti]


@[simp]
theorem pderivIter_zero (i : Fin d) :
    pderivIter i 0 = 1 := by
    simp[pderivIter]

@[simp]
theorem pderivIter_one (i : Fin d) :
    pderivIter i 1 = pderivEnd i := by
    simp[pderivIter]

theorem pdervIter_succ (i : Fin d) (r : ℕ) :
pderivIter i (r+1) = pderivIter i  r * pderivEnd i := by
    simp[pderivIter, pow_succ]

@[simp]
theorem pderiv_coord_self (i : Fin d) :
    pderiv i (coord i)= 1 := by
    simp[pderiv, coord]

@[simp]
theorem pderiv_coord_of_ne {i j : Fin d} (h : j ≠ i) :
    pderiv i (coord j) = 0 :=by
    simp[pderiv, coord, h]

@[simp]
theorem pderivEnd_coord_self (i : Fin d) :
    pderivEnd i (coord i)= 1 := by
    simp[pderivEnd]

@[simp]
theorem pderivEnd_coord_of_ne {i j : Fin d} (h : j ≠ i) :
    pderivEnd i (coord j) = 0 := by
    simp[pderivEnd, h]

end RdPoly
end Kontsevich
end
