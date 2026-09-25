import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-!
# `L∞`-algebras with Koszul signs

An `L∞`-algebra on a `ℤ`-graded `K`-module `L` is a family of
graded skew-symmetric multilinear maps `Qₙ : L^{⊗n} → L` of degree `2 - n` (`n ≥ 1`)
satisfying the generalized Jacobi identities
```
∑_{i+j=n+1} ∑_{σ ∈ Sh(i,n-i)} ± Q_j(Q_i(x_{σ(1)}, …, x_{σ(i)}), x_{σ(i+1)}, …, x_{σ(n)}) = 0.
```

## Representation of graded modules

A graded `K`-module is a `K`-module `V` together with an internal direct-sum decomposition
`𝒜 : ℤ → Submodule K V`, `[DirectSum.Decomposition 𝒜]`, just how Mathlib's `GradedRing`
and `GradedAlgebra` are set up. Every `Qₙ` is a multilinear map on all of `V`
(`MultilinearMap K (fun _ : Fin n => V) V`). Degrees enter only through membership
`x i ∈ 𝒜 (d i)`. Graded antisymmetry and the Jacobi identities are required for tuples of
homogeneous elements, which determine them by multilinearity. This avoids all dependent-type
casts between `𝒜 i` and `𝒜 j`. (Mathlib's `AlternatingMap` is not suitable, since graded
antisymmetry carries Koszul signs, so the `Qₙ` are not alternating on `V`.)

The definitions only assume that `K` is a commutative ring. Over a ring in which `2` is
invertible (in particular, over the characteristic-zero fields used for deformation quantization),
these graded skew-symmetric maps have the expected interpretation as maps out of the graded
exterior power. Over a general commutative ring, permutation skew-symmetry need not force the
additional alternating relations in characteristic two; the multilinear-map formulation below is
the structure that is meant in that generality.

## Assumptions and convention

* **(S1) Koszul sign.** Degrees are integers. For `σ ∈ Sₙ` and homogeneous `x₁, …, xₙ` of
  degrees `d = (d₁, …, dₙ)`, write `x ∘ σ` for the tuple `(x_{σ(1)}, …, x_{σ(n)})`. The
  Koszul sign is
  `ε(σ; d) = ∏_{a < b, σ(a) > σ(b)} (-1)^{d_{σ(a)} d_{σ(b)}}` (`koszulSign`),
  i.e. the sign by which `x_{σ(1)} ⊙ ⋯ ⊙ x_{σ(n)}` differs from `x₁ ⊙ ⋯ ⊙ xₙ` in the free
  graded-commutative algebra.
* **(S2) Antisymmetric Koszul sign.** `χ(σ; d) = sgn(σ) ε(σ; d)` (`antisymmKoszulSign`).
  Graded antisymmetry of `Qₙ` is `Qₙ(x ∘ σ) = χ(σ; d) Qₙ(x)`.
* **(S3) Shuffles.** `Sh(i, n-i)` is the set of `σ ∈ Sₙ` with `σ(1) < ⋯ < σ(i)` and
  `σ(i+1) < ⋯ < σ(n)` (`shuffles n i`).
* **(S4) Jacobi sign.** The `(i, j, σ)`-term of the generalized Jacobi identity carries the
  sign `(-1)^{i(j-1)} χ(σ; d)` (`jacobiSign`), so the identity used in this file is
  ```
  ∑_{i+j=n+1} ∑_{σ ∈ Sh(i,n-i)} (-1)^{i(j-1)} χ(σ; x)
      Q_j(Q_i(x_{σ(1)}, …, x_{σ(i)}), x_{σ(i+1)}, …, x_{σ(n)}) = 0.
  ```
  This is the cohomological version of Lada–Markl [LM95, Definition 2.1]. Lada–Markl use
  operations of degree `n - 2`; reversing the grading gives degree `2 - n` and leaves all parity
  signs unchanged. It is the antisymmetric (décalage) form of Kontsevich's definition
  [K03, Definition 4.3] by a degree-one square-zero coderivation on the symmetric coalgebra of
  `L[1]`. The displayed generalized Jacobi identity in the project formalization note omits the
  factor `(-1)^{i(j-1)}`; that factor is necessary for the `n = 2` identity to be the usual
  dg-Lie Leibniz rule with `Q₁ = d` and `Q₂ = [·,·]`.
* **(S5) Consequence (Example 3.2).** A dg Lie algebra `(L, d, [·,·])` is an `L∞`-algebra
  with `Q₁ = d`, `Q₂ = [·,·]`, `Qₙ = 0` for `n ≥ 3`, with no further signs: the `n = 1, 2, 3`
  identities are `d² = 0`, the graded Leibniz rule `d[x,y] = [dx,y] + (-1)^{|x|}[x,dy]`, and
  the graded Jacobi identity `[x,[y,z]] = [[x,y],z] + (-1)^{|x||y|}[y,[x,z]]`. This is proved
  below in both directions (`LInftyAlgebra.d_comp_d`, `LInftyAlgebra.d_bracket`,
  `LInftyAlgebra.bracket_bracket_of_Q_three_eq_zero`, and the converse
  `LInftyAlgebra.ofDifferentialBracket`).

## Main definitions

* `Kontsevich.LInfty.koszulSign`, `Kontsevich.LInfty.antisymmKoszulSign`,
  `Kontsevich.LInfty.jacobiSign`: the signs (S1), (S2), (S4).
* `Kontsevich.LInfty.shuffles`: the finite set `Sh(i, n-i)` of `(i, n-i)`-shuffles (S3).
* `Kontsevich.LInfty.jacobiTerm`, `Kontsevich.LInfty.jacobiSum`: the terms and the left-hand
  side of the generalized Jacobi identity for an arbitrary family of operations.
* `Kontsevich.LInftyAlgebra K 𝒜`: the `L∞`-algebra structure on the graded module `𝒜`, with
  the differential `LInftyAlgebra.d` and the bracket `LInftyAlgebra.bracket` as (bi)linear maps.
* `Kontsevich.LInftyAlgebra.ofDifferentialBracket`: a dg Lie algebra is an `L∞`-algebra.

## Main results

* `jacobiSum_one`, `jacobiSum_two`, `jacobiSum_three`: explicit expansions of the `n = 1, 2, 3`
  Jacobi sums (the shuffles of `Fin n`, `n ≤ 3`, are enumerated by `decide`), and
  `jacobiSum_eq_zero_of_le_two`. For `n ≥ 4` the identity is vacuous when `Qₘ = 0` for
  `m ≥ 3`.
* `koszulSign_eq_of_even_sub`, `antisymmKoszulSign_eq_of_even_sub`, and
  `jacobiSign_eq_of_even_sub`: all three signs depend only on degree parity.
* `LInftyAlgebra.antisymm_comp`, `LInftyAlgebra.antisymm_cocycle_smul`, and
  `LInftyAlgebra.antisymm_inv`: composition, cocycle, and inverse reindexing rules for arbitrary
  permutations of homogeneous arguments.
* `LInftyAlgebra.jacobi_one`, `LInftyAlgebra.d_comp_d` (`Q₁² = 0`),
  `LInftyAlgebra.jacobi_two`, `LInftyAlgebra.leibniz`, `LInftyAlgebra.d_bracket` (graded
  Leibniz rule), `LInftyAlgebra.jacobi_three`, `LInftyAlgebra.jacobiator_eq_Q_three` (graded
  Jacobi up to the homotopy `Q₃`), `LInftyAlgebra.jacobi_of_Q_three_eq_zero`, and
  `LInftyAlgebra.bracket_bracket_of_Q_three_eq_zero` (graded Jacobi when `Q₃ = 0`),
  `LInftyAlgebra.antisymm_two`, `LInftyAlgebra.bracket_antisymm`.

## References

* [K03] M. Kontsevich, *Deformation quantization of Poisson manifolds*, Lett. Math. Phys.
  66 (2003), §§3–4.
* [LM95] T. Lada, M. Markl, *Strongly homotopy Lie algebras*, Comm. Algebra 23 (1995),
  Definition 2.1.
-/

namespace Kontsevich

namespace LInfty

open Equiv Finset

/-! ### Koszul signs -/

/-- The Koszul sign `ε(σ; d)` of the permutation `σ` acting on a tuple of homogeneous
elements of degrees `d 0, …, d (n-1)`: the product of `(-1)^{d (σ a) * d (σ b)}` over the
inversions `a < b`, `σ b < σ a` of `σ`. -/
def koszulSign {n : ℕ} (σ : Perm (Fin n)) (d : Fin n → ℤ) : ℤˣ :=
  Int.negOnePow (∑ a : Fin n, ∑ b : Fin n, if a < b ∧ σ b < σ a then d (σ a) * d (σ b) else 0)

/-- The antisymmetric Koszul sign `χ(σ; d) = sgn(σ) ε(σ; d)`. -/
def antisymmKoszulSign {n : ℕ} (σ : Perm (Fin n)) (d : Fin n → ℤ) : ℤˣ :=
  Perm.sign σ * koszulSign σ d

/-- The sign `(-1)^{i(j-1)} χ(σ; d)` of the `(i, j, σ)`-term of the generalized Jacobi
identity. -/
def jacobiSign (i j : ℕ) {n : ℕ} (σ : Perm (Fin n)) (d : Fin n → ℤ) : ℤˣ :=
  Int.negOnePow ((i : ℤ) * ((j : ℤ) - 1)) * antisymmKoszulSign σ d

@[simp] lemma negOnePow_two : Int.negOnePow 2 = 1 := Int.negOnePow_even 2 even_two

@[simp] lemma koszulSign_one {n : ℕ} (d : Fin n → ℤ) : koszulSign (1 : Perm (Fin n)) d = 1 := by
  have : ∀ a b : Fin n, (a < b ∧ b < a) = False := fun a b =>
    eq_false fun ⟨h₁, h₂⟩ => absurd (h₁.trans h₂) (lt_irrefl _)
  simp [koszulSign, this]

@[simp] lemma antisymmKoszulSign_one {n : ℕ} (d : Fin n → ℤ) :
    antisymmKoszulSign (1 : Perm (Fin n)) d = 1 := by
  simp [antisymmKoszulSign]

/-- Koszul signs depend only on the degree function, not on its presentation. -/
lemma koszulSign_congr {n : ℕ} (σ : Perm (Fin n)) {d e : Fin n → ℤ}
    (h : ∀ i, d i = e i) :
    koszulSign σ d = koszulSign σ e := by
  congr 2
  funext i
  exact h i

/-- Antisymmetric Koszul signs depend only on the degree function, not on its presentation. -/
lemma antisymmKoszulSign_congr {n : ℕ} (σ : Perm (Fin n)) {d e : Fin n → ℤ}
    (h : ∀ i, d i = e i) :
    antisymmKoszulSign σ d = antisymmKoszulSign σ e := by
  rw [antisymmKoszulSign, antisymmKoszulSign, koszulSign_congr σ h]

/-- `Int.negOnePow` takes finite sums to products. -/
lemma negOnePow_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    Int.negOnePow (∑ i ∈ s, f i) = ∏ i ∈ s, Int.negOnePow (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih => simp [hi, Int.negOnePow_add, ih]

/-- Products of degrees have the same parity when the individual degrees do. -/
lemma even_degree_mul_sub {p q p' q' : ℤ} (hp : Even (p - p')) (hq : Even (q - q')) :
    Even (p * q - p' * q') := by
  rcases hp with ⟨u, hu⟩
  rcases hq with ⟨v, hv⟩
  refine ⟨u * q + p' * v, ?_⟩
  calc
    p * q - p' * q' = (p - p') * q + p' * (q - q') := by ring
    _ = (u + u) * q + p' * (v + v) := by rw [hu, hv]
    _ = (u * q + p' * v) + (u * q + p' * v) := by ring

/-- Koszul signs only depend on the parities of the degrees. -/
lemma koszulSign_eq_of_even_sub {n : ℕ} (σ : Perm (Fin n)) {d e : Fin n → ℤ}
    (h : ∀ i, Even (d i - e i)) : koszulSign σ d = koszulSign σ e := by
  classical
  let term (d' : Fin n → ℤ) (a b : Fin n) :=
    if a < b ∧ σ b < σ a then d' (σ a) * d' (σ b) else 0
  have hterm : ∀ a b, Int.negOnePow (term d a b) = Int.negOnePow (term e a b) := by
    intro a b
    by_cases hab : a < b ∧ σ b < σ a
    · simp only [term, if_pos hab]
      rw [Int.negOnePow_eq_iff]
      exact even_degree_mul_sub (h (σ a)) (h (σ b))
    · simp [term, hab]
  unfold koszulSign
  change Int.negOnePow (∑ a, ∑ b, term d a b) =
    Int.negOnePow (∑ a, ∑ b, term e a b)
  calc
    Int.negOnePow (∑ a, ∑ b, term d a b) =
        ∏ a, ∏ b, Int.negOnePow (term d a b) := by
      rw [negOnePow_sum]
      apply Finset.prod_congr rfl
      intro a _
      rw [negOnePow_sum]
    _ = ∏ a, ∏ b, Int.negOnePow (term e a b) := by
      apply Finset.prod_congr rfl
      intro a _
      apply Finset.prod_congr rfl
      intro b _
      exact hterm a b
    _ = Int.negOnePow (∑ a, ∑ b, term e a b) := by
      rw [negOnePow_sum]
      apply Eq.symm
      apply Finset.prod_congr rfl
      intro a _
      rw [negOnePow_sum]

/-- Antisymmetric Koszul signs only depend on the parities of the degrees. -/
lemma antisymmKoszulSign_eq_of_even_sub {n : ℕ} (σ : Perm (Fin n)) {d e : Fin n → ℤ}
    (h : ∀ i, Even (d i - e i)) : antisymmKoszulSign σ d = antisymmKoszulSign σ e := by
  simp only [antisymmKoszulSign, koszulSign_eq_of_even_sub σ h]

/-- Adding an arbitrary even integer to every degree does not change a Koszul sign. -/
lemma koszulSign_add_two_mul {n : ℕ} (σ : Perm (Fin n)) (d k : Fin n → ℤ) :
    koszulSign σ (fun i ↦ d i + 2 * k i) = koszulSign σ d := by
  apply koszulSign_eq_of_even_sub
  intro i
  exact ⟨k i, by ring⟩

/-- Adding an arbitrary even integer to every degree does not change an antisymmetric Koszul
sign. -/
lemma antisymmKoszulSign_add_two_mul {n : ℕ} (σ : Perm (Fin n)) (d k : Fin n → ℤ) :
    antisymmKoszulSign σ (fun i ↦ d i + 2 * k i) = antisymmKoszulSign σ d := by
  apply antisymmKoszulSign_eq_of_even_sub
  intro i
  exact ⟨k i, by ring⟩

/-- Reversing every grading degree does not change a Koszul sign. This records that all signs
only depend on products of pairs of degrees. -/
@[simp] lemma koszulSign_neg {n : ℕ} (σ : Perm (Fin n)) (d : Fin n → ℤ) :
    koszulSign σ (-d) = koszulSign σ d := by
  simp only [koszulSign, Pi.neg_apply, neg_mul_neg]

/-- Reversing every grading degree does not change an antisymmetric Koszul sign. -/
@[simp] lemma antisymmKoszulSign_neg {n : ℕ} (σ : Perm (Fin n)) (d : Fin n → ℤ) :
    antisymmKoszulSign σ (-d) = antisymmKoszulSign σ d := by
  simp [antisymmKoszulSign]

/-- For a tuple concentrated in even degree zero, the antisymmetric Koszul sign is the ordinary
signature of the permutation. -/
@[simp] lemma koszulSign_zero {n : ℕ} (σ : Perm (Fin n)) :
    koszulSign σ (0 : Fin n → ℤ) = 1 := by
  simp [koszulSign]

@[simp] lemma antisymmKoszulSign_zero {n : ℕ} (σ : Perm (Fin n)) :
    antisymmKoszulSign σ (0 : Fin n → ℤ) = Perm.sign σ := by
  simp [antisymmKoszulSign]

/-- Reversing every grading degree does not change a generalized-Jacobi sign. -/
@[simp] lemma jacobiSign_neg (i j : ℕ) {n : ℕ} (σ : Perm (Fin n)) (d : Fin n → ℤ) :
    jacobiSign i j σ (-d) = jacobiSign i j σ d := by
  simp [jacobiSign]

/-- Generalized-Jacobi signs only depend on the parities of the input degrees. -/
lemma jacobiSign_eq_of_even_sub (i j : ℕ) {n : ℕ} (σ : Perm (Fin n))
    {d e : Fin n → ℤ} (h : ∀ k, Even (d k - e k)) :
    jacobiSign i j σ d = jacobiSign i j σ e := by
  simp only [jacobiSign, antisymmKoszulSign_eq_of_even_sub σ h]

lemma koszulSign_swap_two (d : Fin 2 → ℤ) :
    koszulSign (swap 0 1) d = Int.negOnePow (d 0 * d 1) := by
  simp [koszulSign, Fin.sum_univ_two, mul_comm]

lemma antisymmKoszulSign_swap_two (d : Fin 2 → ℤ) :
    antisymmKoszulSign (swap 0 1) d = -Int.negOnePow (d 0 * d 1) := by
  simp [antisymmKoszulSign, koszulSign_swap_two]

/-! Signs of the four non-identity shuffles of `Fin 3` occurring in the `n = 3` Jacobi
identity: `swap 0 1`, `swap 1 2 * swap 0 1` (the shuffles `(2,1,3)`, `(3,1,2)` of `Sh(1,2)`)
and `swap 1 2`, `swap 0 1 * swap 1 2` (the shuffles `(1,3,2)`, `(2,3,1)` of `Sh(2,1)`). -/

lemma koszulSign_swap₀₁_three (d : Fin 3 → ℤ) :
    koszulSign (swap 0 1) d = Int.negOnePow (d 0 * d 1) := by
  simp +decide [koszulSign, Fin.sum_univ_three, swap_apply_def, mul_comm]

lemma koszulSign_swap₁₂_three (d : Fin 3 → ℤ) :
    koszulSign (swap 1 2) d = Int.negOnePow (d 1 * d 2) := by
  simp +decide [koszulSign, Fin.sum_univ_three, swap_apply_def, mul_comm]

lemma koszulSign_cycle_left_three (d : Fin 3 → ℤ) :
    koszulSign (swap 1 2 * swap 0 1) d = Int.negOnePow (d 2 * d 0 + d 2 * d 1) := by
  simp +decide [koszulSign, Fin.sum_univ_three, swap_apply_def]

lemma koszulSign_cycle_right_three (d : Fin 3 → ℤ) :
    koszulSign (swap 0 1 * swap 1 2) d = Int.negOnePow (d 1 * d 0 + d 2 * d 0) := by
  simp +decide [koszulSign, Fin.sum_univ_three, swap_apply_def]

lemma antisymmKoszulSign_swap₀₁_three (d : Fin 3 → ℤ) :
    antisymmKoszulSign (swap 0 1) d = -Int.negOnePow (d 0 * d 1) := by
  rw [antisymmKoszulSign, koszulSign_swap₀₁_three, Perm.sign_swap (by decide)]; simp

lemma antisymmKoszulSign_swap₁₂_three (d : Fin 3 → ℤ) :
    antisymmKoszulSign (swap 1 2) d = -Int.negOnePow (d 1 * d 2) := by
  rw [antisymmKoszulSign, koszulSign_swap₁₂_three, Perm.sign_swap (by decide)]; simp

lemma antisymmKoszulSign_cycle_left_three (d : Fin 3 → ℤ) :
    antisymmKoszulSign (swap 1 2 * swap 0 1) d = Int.negOnePow (d 2 * d 0 + d 2 * d 1) := by
  rw [antisymmKoszulSign, koszulSign_cycle_left_three,
    show Perm.sign (swap 1 2 * swap 0 1 : Perm (Fin 3)) = 1 by decide, one_mul]

lemma antisymmKoszulSign_cycle_right_three (d : Fin 3 → ℤ) :
    antisymmKoszulSign (swap 0 1 * swap 1 2) d = Int.negOnePow (d 1 * d 0 + d 2 * d 0) := by
  rw [antisymmKoszulSign, koszulSign_cycle_right_three,
    show Perm.sign (swap 0 1 * swap 1 2 : Perm (Fin 3)) = 1 by decide, one_mul]

/-! ### Shuffles -/

/-- `IsShuffle i σ` says that `σ` is an `(i, n - i)`-shuffle: `σ` is strictly increasing on
the positions `0, …, i - 1` and on the positions `i, …, n - 1`. -/
def IsShuffle {n : ℕ} (i : ℕ) (σ : Perm (Fin n)) : Prop :=
  ∀ a b : Fin n, a < b → ((b : ℕ) < i ∨ i ≤ (a : ℕ)) → σ a < σ b

instance {n i : ℕ} : DecidablePred (IsShuffle (n := n) i) := fun _ => by
  unfold IsShuffle; infer_instance

/-- The finite set `Sh(i, n - i)` of `(i, n - i)`-shuffles. -/
def shuffles (n i : ℕ) : Finset (Perm (Fin n)) := univ.filter (IsShuffle i)

lemma mem_shuffles {n i : ℕ} {σ : Perm (Fin n)} : σ ∈ shuffles n i ↔ IsShuffle i σ := by
  simp [shuffles]

lemma shuffles_one_one : shuffles 1 1 = {1} := by decide
lemma shuffles_two_one : shuffles 2 1 = {1, swap 0 1} := by decide
lemma shuffles_two_two : shuffles 2 2 = {1} := by decide
lemma shuffles_three_one : shuffles 3 1 = {1, swap 0 1, swap 1 2 * swap 0 1} := by decide
lemma shuffles_three_two : shuffles 3 2 = {1, swap 1 2, swap 0 1 * swap 1 2} := by decide
lemma shuffles_three_three : shuffles 3 3 = {1} := by decide

/-- Precomposition with the transposition of `Fin 2` swaps the two entries. -/
lemma comp_swap_two {α : Type*} (x : Fin 2 → α) : x ∘ swap 0 1 = ![x 1, x 0] := by
  funext k; fin_cases k <;> simp

/-- Successive reindexing by `σ` and then `τ` is reindexing by the product `σ * τ`.
This fixes the order convention used by all permutation-sign lemmas below. -/
lemma comp_perm_mul {α : Type*} {n : ℕ} (x : Fin n → α) (σ τ : Perm (Fin n)) :
    x ∘ ⇑(σ * τ) = (x ∘ σ) ∘ τ := by
  funext i
  rfl

/-! ### The generalized Jacobi sum -/

variable {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V]

/-- A family of `n`-ary multilinear operations on `V`, one for each arity `n : ℕ`. -/
abbrev OpFamily (K V : Type*) [CommRing K] [AddCommGroup V] [Module K V] :=
  (n : ℕ) → MultilinearMap K (fun _ : Fin n => V) V

/-- The `(i, σ)`-term `Q_{n+1-i}(Q_{i+1}(x_{σ 0}, …, x_{σ i}), x_{σ (i+1)}, …, x_{σ n})` of the
generalized Jacobi identity of arity `n + 1`. -/
def jacobiTerm (Q : OpFamily K V) {n : ℕ} (x : Fin (n + 1) → V) (σ : Perm (Fin (n + 1)))
    (i : Fin (n + 1)) : V :=
  Q (n - i + 1) <| Fin.cons (Q (i + 1) fun l => x (σ (Fin.castLE i.isLt l)))
    fun k : Fin (n - i) => x (σ ⟨i + 1 + k, by omega⟩)

/-- The left-hand side of the generalized Jacobi identity of arity `n + 1`. -/
def jacobiSum (Q : OpFamily K V) {n : ℕ} (d : Fin (n + 1) → ℤ) (x : Fin (n + 1) → V) : V :=
  ∑ i : Fin (n + 1), ∑ σ ∈ shuffles (n + 1) (i + 1),
    jacobiSign (i + 1) (n - i + 1) σ d • jacobiTerm Q x σ i

section expansions

variable (Q : OpFamily K V)

lemma jacobiTerm_one_zero (x : Fin 1 → V) (σ : Perm (Fin 1)) :
    jacobiTerm Q x σ 0 = Q 1 ![Q 1 ![x (σ 0)]] := by
  unfold jacobiTerm
  refine congrArg _ (funext fun k => ?_)
  fin_cases k
  simp only [Fin.zero_eta, Fin.isValue, Fin.cons_zero, Matrix.cons_val_zero]
  refine congrArg _ (funext fun l => ?_)
  fin_cases l
  rfl

lemma jacobiTerm_two_zero (x : Fin 2 → V) (σ : Perm (Fin 2)) :
    jacobiTerm Q x σ 0 = Q 2 ![Q 1 ![x (σ 0)], x (σ 1)] := by
  unfold jacobiTerm
  refine congrArg _ (funext fun k => ?_)
  fin_cases k
  · simp only [Fin.zero_eta, Fin.isValue, Fin.cons_zero, Matrix.cons_val_zero]
    refine congrArg _ (funext fun l => ?_)
    fin_cases l
    rfl
  · rfl

lemma jacobiTerm_two_one (x : Fin 2 → V) (σ : Perm (Fin 2)) :
    jacobiTerm Q x σ 1 = Q 1 ![Q 2 ![x (σ 0), x (σ 1)]] := by
  unfold jacobiTerm
  refine congrArg _ (funext fun k => ?_)
  fin_cases k
  simp only [Fin.zero_eta, Fin.isValue, Fin.cons_zero]
  refine congrArg _ (funext fun l => ?_)
  fin_cases l <;> rfl

lemma jacobiTerm_three_zero (x : Fin 3 → V) (σ : Perm (Fin 3)) :
    jacobiTerm Q x σ 0 = Q 3 ![Q 1 ![x (σ 0)], x (σ 1), x (σ 2)] := by
  unfold jacobiTerm
  refine congrArg _ (funext fun k => ?_)
  fin_cases k
  · simp only [Fin.zero_eta, Fin.isValue, Fin.cons_zero, Matrix.cons_val_zero]
    refine congrArg _ (funext fun l => ?_)
    fin_cases l
    rfl
  · rfl
  · rfl

lemma jacobiTerm_three_one (x : Fin 3 → V) (σ : Perm (Fin 3)) :
    jacobiTerm Q x σ 1 = Q 2 ![Q 2 ![x (σ 0), x (σ 1)], x (σ 2)] := by
  unfold jacobiTerm
  refine congrArg _ (funext fun k => ?_)
  fin_cases k
  · simp only [Fin.zero_eta, Fin.isValue, Fin.cons_zero]
    refine congrArg _ (funext fun l => ?_)
    fin_cases l <;> rfl
  · rfl

lemma jacobiTerm_three_two (x : Fin 3 → V) (σ : Perm (Fin 3)) :
    jacobiTerm Q x σ 2 = Q 1 ![Q 3 ![x (σ 0), x (σ 1), x (σ 2)]] := by
  unfold jacobiTerm
  refine congrArg _ (funext fun k => ?_)
  fin_cases k
  simp only [Fin.zero_eta, Fin.isValue, Fin.cons_zero]
  refine congrArg _ (funext fun l => ?_)
  fin_cases l <;> rfl

lemma jacobiSum_one (d : Fin 1 → ℤ) (x : Fin 1 → V) :
    jacobiSum Q d x = Q 1 ![Q 1 ![x 0]] := by
  simp [jacobiSum, shuffles_one_one, jacobiSign, jacobiTerm_one_zero, Int.negOnePow_zero]

lemma jacobiSum_two (d : Fin 2 → ℤ) (x : Fin 2 → V) :
    jacobiSum Q d x =
      -Q 2 ![Q 1 ![x 0], x 1] + Int.negOnePow (d 0 * d 1) • Q 2 ![Q 1 ![x 1], x 0]
        + Q 1 ![Q 2 ![x 0, x 1]] := by
  simp +decide [jacobiSum, Fin.sum_univ_two, shuffles_two_one, shuffles_two_two, jacobiSign,
    jacobiTerm_two_zero, jacobiTerm_two_one, antisymmKoszulSign_swap_two, Int.negOnePow_zero,
    Int.negOnePow_one, Units.neg_smul]
  abel

lemma jacobiSum_three (d : Fin 3 → ℤ) (x : Fin 3 → V) :
    jacobiSum Q d x =
      Q 3 ![Q 1 ![x 0], x 1, x 2]
      - Int.negOnePow (d 0 * d 1) • Q 3 ![Q 1 ![x 1], x 0, x 2]
      + Int.negOnePow (d 2 * d 0 + d 2 * d 1) • Q 3 ![Q 1 ![x 2], x 0, x 1]
      + Q 2 ![Q 2 ![x 0, x 1], x 2]
      - Int.negOnePow (d 1 * d 2) • Q 2 ![Q 2 ![x 0, x 2], x 1]
      + Int.negOnePow (d 1 * d 0 + d 2 * d 0) • Q 2 ![Q 2 ![x 1, x 2], x 0]
      + Q 1 ![Q 3 ![x 0, x 1, x 2]] := by
  simp +decide [jacobiSum, Fin.sum_univ_three, shuffles_three_one, shuffles_three_two,
    shuffles_three_three, Finset.sum_insert, jacobiSign, jacobiTerm_three_zero,
    jacobiTerm_three_one, jacobiTerm_three_two, antisymmKoszulSign_swap₀₁_three,
    antisymmKoszulSign_swap₁₂_three, antisymmKoszulSign_cycle_left_three,
    antisymmKoszulSign_cycle_right_three, Perm.mul_apply, swap_apply_def, Int.negOnePow_zero,
    Units.neg_smul]
  abel

/-- If all operations of arity `≥ 3` vanish, every Jacobi identity of arity `n + 1 ≥ 4` holds
trivially, since each term contains a vanishing operation. -/
lemma jacobiSum_eq_zero_of_le_two (hQ : ∀ m, 3 ≤ m → Q m = 0) {n : ℕ} (hn : 3 ≤ n)
    (d : Fin (n + 1) → ℤ) (x : Fin (n + 1) → V) : jacobiSum Q d x = 0 := by
  unfold jacobiSum
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun σ _ => ?_
  unfold jacobiTerm
  rcases le_or_gt 3 ((i : ℕ) + 1) with h | h
  · simp only [hQ _ h, zero_apply]
    rw [MultilinearMap.map_coord_zero _ 0 (Fin.cons_zero _ _), smul_zero]
  · have h3 : 3 ≤ n - i + 1 := by omega
    simp [hQ _ h3]

end expansions

end LInfty

open LInfty

/-- An `L∞`-algebra structure on the `ℤ`-graded `K`-module `V = ⨁ i, 𝒜 i`: operations
`Qₙ : V^n → V` of degree `2 - n`, graded skew-symmetric, satisfying the generalized Jacobi
identities, with the sign conventions (S1)–(S4) of the module docstring.

Over an arbitrary `CommRing K`, "graded skew-symmetric" means precisely the permutation law in
the `antisymm` field. Its identification with a map from a graded exterior power requires the
usual extra hypotheses excluding the characteristic-two distinction between skew-symmetric and
alternating maps. -/
@[ext]
structure LInftyAlgebra (K : Type*) [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
    (𝒜 : ℤ → Submodule K V) [DirectSum.Decomposition 𝒜] where
  /-- The operations `Q n : V^n → V`. Only `n ≥ 1` carries data. -/
  Q : OpFamily K V
  /-- There is no `0`-ary operation (no curvature). -/
  Q_zero : Q 0 = 0
  /-- `Q n` has degree `2 - n`. -/
  Q_mem : ∀ {n : ℕ} {d : Fin n → ℤ} {x : Fin n → V}, (∀ i, x i ∈ 𝒜 (d i)) →
    Q n x ∈ 𝒜 (∑ i, d i + (2 - n))
  /-- Graded antisymmetry with the antisymmetric Koszul sign `χ(σ; d)`. -/
  antisymm : ∀ {n : ℕ} {d : Fin n → ℤ} {x : Fin n → V}, (∀ i, x i ∈ 𝒜 (d i)) →
    ∀ σ : Equiv.Perm (Fin n), Q n (x ∘ σ) = antisymmKoszulSign σ d • Q n x
  /-- The generalized Jacobi identity of arity `n + 1`, for every `n`. -/
  jacobi : ∀ {n : ℕ} {d : Fin (n + 1) → ℤ} {x : Fin (n + 1) → V}, (∀ i, x i ∈ 𝒜 (d i)) →
    jacobiSum Q d x = 0

namespace LInftyAlgebra

variable {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V]
  {𝒜 : ℤ → Submodule K V} [DirectSum.Decomposition 𝒜] (L : LInftyAlgebra K 𝒜)
  {a b c : ℤ} {x y z : V}

/-- The trivial `L∞`-algebra structure, `Qₙ = 0` for all `n`. -/
def trivial : LInftyAlgebra K 𝒜 where
  Q _ := 0
  Q_zero := rfl
  Q_mem _ := by simp
  antisymm _ _ := by simp
  jacobi _ := by simp [jacobiSum, jacobiTerm]

instance : Inhabited (LInftyAlgebra K 𝒜) := ⟨trivial⟩

/-! ### Reindexing homogeneous arguments -/

/-- Applying graded antisymmetry successively first by `σ` and then by `τ`. Besides being a
convenient reindexing rule, this theorem records which transformed degree function occurs in the
Koszul sign for the second permutation. -/
theorem antisymm_comp {n : ℕ} {dg : Fin n → ℤ} {v : Fin n → V}
    (hv : ∀ i, v i ∈ 𝒜 (dg i)) (σ τ : Equiv.Perm (Fin n)) :
    L.Q n (v ∘ ⇑(σ * τ)) =
      antisymmKoszulSign τ (dg ∘ σ) • (antisymmKoszulSign σ dg • L.Q n v) := by
  rw [comp_perm_mul]
  rw [L.antisymm (d := dg ∘ σ) (x := v ∘ σ) (fun i ↦ hv (σ i)) τ,
    L.antisymm hv σ]

/-- The combined scalar in `antisymm_comp`, useful when comparing a composite permutation with a
single permutation. -/
theorem antisymm_comp' {n : ℕ} {dg : Fin n → ℤ} {v : Fin n → V}
    (hv : ∀ i, v i ∈ 𝒜 (dg i)) (σ τ : Equiv.Perm (Fin n)) :
    L.Q n (v ∘ ⇑(σ * τ)) =
      (antisymmKoszulSign τ (dg ∘ σ) * antisymmKoszulSign σ dg) • L.Q n v := by
  simpa only [mul_smul] using L.antisymm_comp hv σ τ

/-- The cocycle law for permutation signs, stated at exactly the level needed by an
`LInftyAlgebra`: the sign of the composite and the product of the two successive signs have the
same action on the value of every homogeneous operation. This formulation remains valid over an
arbitrary commutative base ring, where scalar actions need not be cancellable. -/
theorem antisymm_cocycle_smul {n : ℕ} {dg : Fin n → ℤ} {v : Fin n → V}
    (hv : ∀ i, v i ∈ 𝒜 (dg i)) (σ τ : Equiv.Perm (Fin n)) :
    antisymmKoszulSign (σ * τ) dg • L.Q n v =
      (antisymmKoszulSign τ (dg ∘ σ) * antisymmKoszulSign σ dg) • L.Q n v := by
  rw [← L.antisymm hv (σ * τ)]
  exact L.antisymm_comp' hv σ τ

/-- The inverse form of graded antisymmetry. The degrees on the permuted tuple are `dg ∘ σ`. -/
theorem antisymm_inv {n : ℕ} {dg : Fin n → ℤ} {v : Fin n → V}
    (hv : ∀ i, v i ∈ 𝒜 (dg i)) (σ : Equiv.Perm (Fin n)) :
    L.Q n v = antisymmKoszulSign σ⁻¹ (dg ∘ σ) • L.Q n (v ∘ σ) := by
  have h := L.antisymm (d := dg ∘ σ) (x := v ∘ σ) (fun i ↦ hv (σ i)) σ⁻¹
  have heq : (v ∘ σ) ∘ ⇑(σ⁻¹) = v := by
    funext i
    simp
  simpa only [heq] using h

/-! ### The differential and the bracket as (bi)linear maps -/

/-- The differential `Q₁` as a linear map. -/
def d : V →ₗ[K] V := (MultilinearMap.ofSubsingleton K V V (0 : Fin 1)).symm (L.Q 1)

@[simp] lemma d_apply (x : V) : L.d x = L.Q 1 ![x] := by
  change L.Q 1 (fun _ => x) = L.Q 1 ![x]
  congr 1
  funext i; fin_cases i; rfl

/-- The binary operation `Q₂` as a bilinear map. -/
def bracket : V →ₗ[K] V →ₗ[K] V :=
  (MultilinearMap.ofSubsingletonₗ K K V V (0 : Fin 1)).symm.toLinearMap ∘ₗ (L.Q 2).curryLeft

@[simp] lemma bracket_apply (x y : V) : L.bracket x y = L.Q 2 ![x, y] := by
  change L.Q 2 (Fin.cons x fun _ => y) = L.Q 2 ![x, y]
  congr 1
  funext i; fin_cases i <;> rfl

/-! ### Degrees of the low-arity operations -/

lemma Q_one_mem (hx : x ∈ 𝒜 a) : L.Q 1 ![x] ∈ 𝒜 (a + 1) := by
  simpa using L.Q_mem (d := ![a]) (x := ![x]) (by simp [hx])

lemma Q_two_mem (hx : x ∈ 𝒜 a) (hy : y ∈ 𝒜 b) : L.Q 2 ![x, y] ∈ 𝒜 (a + b) := by
  simpa using L.Q_mem (d := ![a, b]) (x := ![x, y]) (by simp [Fin.forall_fin_two, hx, hy])

lemma Q_three_mem (hx : x ∈ 𝒜 a) (hy : y ∈ 𝒜 b) (hz : z ∈ 𝒜 c) :
    L.Q 3 ![x, y, z] ∈ 𝒜 (a + b + c - 1) := by
  have := L.Q_mem (d := ![a, b, c]) (x := ![x, y, z]) (by simp [Fin.forall_fin_succ, hx, hy, hz])
  simpa [Fin.sum_univ_three, sub_eq_add_neg] using this

lemma d_mem (hx : x ∈ 𝒜 a) : L.d x ∈ 𝒜 (a + 1) := by
  simpa using L.Q_one_mem hx

lemma bracket_mem (hx : x ∈ 𝒜 a) (hy : y ∈ 𝒜 b) : L.bracket x y ∈ 𝒜 (a + b) := by
  simpa using L.Q_two_mem hx hy

/-! ### Antisymmetry in low arities -/

theorem antisymm_two (hx : x ∈ 𝒜 a) (hy : y ∈ 𝒜 b) :
    L.Q 2 ![y, x] = -(Int.negOnePow (a * b) • L.Q 2 ![x, y]) := by
  have := L.antisymm (d := ![a, b]) (x := ![x, y]) (by simp [Fin.forall_fin_two, hx, hy])
    (Equiv.swap 0 1)
  rw [comp_swap_two, antisymmKoszulSign_swap_two] at this
  simpa [Units.neg_smul] using this

theorem bracket_antisymm (hx : x ∈ 𝒜 a) (hy : y ∈ 𝒜 b) :
    L.bracket y x = -(Int.negOnePow (a * b) • L.bracket x y) := by
  simpa using L.antisymm_two hx hy

/-- Swapping the first two arguments of `Q₃`. -/
theorem antisymm_three_swap₀₁ (hx : x ∈ 𝒜 a) (hy : y ∈ 𝒜 b) (hz : z ∈ 𝒜 c) :
    L.Q 3 ![y, x, z] = -(Int.negOnePow (a * b) • L.Q 3 ![x, y, z]) := by
  have h := L.antisymm (d := ![a, b, c]) (x := ![x, y, z])
    (by simp [Fin.forall_fin_succ, hx, hy, hz]) (Equiv.swap 0 1)
  rw [show ![x, y, z] ∘ Equiv.swap 0 1 = ![y, x, z] by
      funext k; fin_cases k <;> simp +decide [Equiv.swap_apply_def],
    antisymmKoszulSign_swap₀₁_three] at h
  simpa [Units.neg_smul] using h

/-- Swapping the last two arguments of `Q₃`. -/
theorem antisymm_three_swap₁₂ (hx : x ∈ 𝒜 a) (hy : y ∈ 𝒜 b) (hz : z ∈ 𝒜 c) :
    L.Q 3 ![x, z, y] = -(Int.negOnePow (b * c) • L.Q 3 ![x, y, z]) := by
  have h := L.antisymm (d := ![a, b, c]) (x := ![x, y, z])
    (by simp [Fin.forall_fin_succ, hx, hy, hz]) (Equiv.swap 1 2)
  rw [show ![x, y, z] ∘ Equiv.swap 1 2 = ![x, z, y] by
      funext k; fin_cases k <;> simp +decide [Equiv.swap_apply_def],
    antisymmKoszulSign_swap₁₂_three] at h
  simpa [Units.neg_smul] using h

/-- Moving the last argument of `Q₃` to the front. This even permutation has only its Koszul
sign. -/
theorem antisymm_three_cycle_left (hx : x ∈ 𝒜 a) (hy : y ∈ 𝒜 b) (hz : z ∈ 𝒜 c) :
    L.Q 3 ![z, x, y] = Int.negOnePow (c * (a + b)) • L.Q 3 ![x, y, z] := by
  have h := L.antisymm (d := ![a, b, c]) (x := ![x, y, z])
    (by simp [Fin.forall_fin_succ, hx, hy, hz]) (Equiv.swap 1 2 * Equiv.swap 0 1)
  rw [show ![x, y, z] ∘
      ⇑(Equiv.swap 1 2 * Equiv.swap 0 1 : Equiv.Perm (Fin 3)) = ![z, x, y] by
      funext k; fin_cases k <;> simp +decide [Equiv.swap_apply_def],
    antisymmKoszulSign_cycle_left_three] at h
  simpa [mul_add] using h

/-! ### The `n = 1` identity: `Q₁² = 0` -/

theorem jacobi_one (hx : x ∈ 𝒜 a) : L.Q 1 ![L.Q 1 ![x]] = 0 := by
  simpa [jacobiSum_one] using L.jacobi (d := ![a]) (x := ![x]) (by simp [hx])

/-- `Q₁ ∘ Q₁ = 0` on all of `V` (not only on homogeneous elements). -/
theorem d_comp_d : L.d ∘ₗ L.d = 0 := by
  ext x
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  induction x using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp only [map_zero]
  | homogeneous m => simpa using L.jacobi_one m.2
  | add m m' hm hm' => simp only [map_add, hm, hm', add_zero]

theorem d_d_apply (x : V) : L.d (L.d x) = 0 := LinearMap.congr_fun L.d_comp_d x

/-! ### The `n = 2` identity: `Q₁` is a derivation of `Q₂` -/

/-- The `n = 2` Jacobi identity, as it comes out of the shuffle sum. -/
theorem jacobi_two (hx : x ∈ 𝒜 a) (hy : y ∈ 𝒜 b) :
    L.Q 1 ![L.Q 2 ![x, y]] =
      L.Q 2 ![L.Q 1 ![x], y] - Int.negOnePow (a * b) • L.Q 2 ![L.Q 1 ![y], x] := by
  have := L.jacobi (d := ![a, b]) (x := ![x, y]) (by simp [Fin.forall_fin_two, hx, hy])
  rw [jacobiSum_two] at this
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
  rw [eq_sub_iff_add_eq, ← sub_eq_zero, ← this]
  abel

/-- The graded Leibniz rule `Q₁[x, y] = [Q₁ x, y] + (-1)^{|x|} [x, Q₁ y]`. -/
theorem leibniz (hx : x ∈ 𝒜 a) (hy : y ∈ 𝒜 b) :
    L.Q 1 ![L.Q 2 ![x, y]] =
      L.Q 2 ![L.Q 1 ![x], y] + Int.negOnePow a • L.Q 2 ![x, L.Q 1 ![y]] := by
  rw [L.jacobi_two hx hy, L.antisymm_two hx (L.Q_one_mem hy), smul_neg, smul_smul, sub_neg_eq_add,
    ← Int.negOnePow_add]
  congr 2
  rw [Int.negOnePow_eq_iff]
  exact ⟨a * b, by ring⟩

/-- The graded Leibniz rule in terms of `d` and `bracket`. -/
theorem d_bracket (hx : x ∈ 𝒜 a) (hy : y ∈ 𝒜 b) :
    L.d (L.bracket x y) = L.bracket (L.d x) y + Int.negOnePow a • L.bracket x (L.d y) := by
  simpa using L.leibniz hx hy

/-! ### The `n = 3` identity: graded Jacobi up to the homotopy `Q₃` -/

/-- The `n = 3` Jacobi identity, as it comes out of the shuffle sum. -/
theorem jacobi_three (hx : x ∈ 𝒜 a) (hy : y ∈ 𝒜 b) (hz : z ∈ 𝒜 c) :
    L.Q 3 ![L.Q 1 ![x], y, z]
      - Int.negOnePow (a * b) • L.Q 3 ![L.Q 1 ![y], x, z]
      + Int.negOnePow (c * (a + b)) • L.Q 3 ![L.Q 1 ![z], x, y]
      + L.Q 2 ![L.Q 2 ![x, y], z]
      - Int.negOnePow (b * c) • L.Q 2 ![L.Q 2 ![x, z], y]
      + Int.negOnePow (a * (b + c)) • L.Q 2 ![L.Q 2 ![y, z], x]
      + L.Q 1 ![L.Q 3 ![x, y, z]] = 0 := by
  have := L.jacobi (d := ![a, b, c]) (x := ![x, y, z])
    (by simp [Fin.forall_fin_succ, hx, hy, hz])
  rw [jacobiSum_three] at this
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at this
  rw [show c * (a + b) = c * a + c * b by ring, show a * (b + c) = b * a + c * a by ring]
  exact this

/-- The conventional form of the `n = 3` identity: the graded Jacobiator of `Q₂` is the
chain-homotopy supplied by `Q₃`. All occurrences of a differentiated argument have been moved
back to its original position, so the four signs on the right are the standard cochain signs. -/
theorem jacobiator_eq_Q_three (hx : x ∈ 𝒜 a) (hy : y ∈ 𝒜 b) (hz : z ∈ 𝒜 c) :
    L.bracket x (L.bracket y z) - L.bracket (L.bracket x y) z
        - Int.negOnePow (a * b) • L.bracket y (L.bracket x z) =
      L.d (L.Q 3 ![x, y, z]) + L.Q 3 ![L.d x, y, z]
        + Int.negOnePow a • L.Q 3 ![x, L.d y, z]
        + Int.negOnePow (a + b) • L.Q 3 ![x, y, L.d z] := by
  have h := L.jacobi_three hx hy hz
  rw [L.antisymm_two hy (L.Q_two_mem hx hz), L.antisymm_two hx (L.Q_two_mem hy hz),
    smul_neg, smul_neg, smul_smul, smul_smul, ← Int.negOnePow_add, ← Int.negOnePow_add] at h
  have e₁ : Int.negOnePow (b * c + b * (a + c)) = Int.negOnePow (a * b) := by
    rw [Int.negOnePow_eq_iff]
    exact ⟨b * c, by ring⟩
  have e₂ : Int.negOnePow (a * (b + c) + a * (b + c)) = 1 := by
    rw [Int.negOnePow_eq_one_iff]
    exact ⟨a * (b + c), by ring⟩
  rw [e₁, e₂, one_smul] at h
  rw [L.antisymm_three_swap₀₁ hx (L.Q_one_mem hy) hz,
    L.antisymm_three_cycle_left hx hy (L.Q_one_mem hz), smul_neg, smul_smul, smul_smul] at h
  simp only [sub_neg_eq_add] at h
  have e₃ : Int.negOnePow (a * b) * Int.negOnePow (a * (b + 1)) = Int.negOnePow a := by
    rw [← Int.negOnePow_add, Int.negOnePow_eq_iff]
    exact ⟨a * b, by ring⟩
  have e₄ : Int.negOnePow (c * (a + b)) * Int.negOnePow ((c + 1) * (a + b)) =
      Int.negOnePow (a + b) := by
    rw [← Int.negOnePow_add, Int.negOnePow_eq_iff]
    exact ⟨c * (a + b), by ring⟩
  rw [e₃, e₄] at h
  simp only [d_apply, bracket_apply]
  rw [eq_comm, ← sub_eq_zero]
  abel_nf at h ⊢
  exact h

/-- When `Q₃ = 0` (for instance for a dg Lie algebra), the `n = 3` identity is the graded
Jacobi identity `[x, [y, z]] = [[x, y], z] + (-1)^{|x||y|} [y, [x, z]]`. -/
theorem jacobi_of_Q_three_eq_zero (h₃ : L.Q 3 = 0) (hx : x ∈ 𝒜 a) (hy : y ∈ 𝒜 b)
    (hz : z ∈ 𝒜 c) :
    L.Q 2 ![x, L.Q 2 ![y, z]] =
      L.Q 2 ![L.Q 2 ![x, y], z] + Int.negOnePow (a * b) • L.Q 2 ![y, L.Q 2 ![x, z]] := by
  have h := L.jacobiator_eq_Q_three hx hy hz
  simp only [h₃, zero_apply, map_zero, smul_zero, add_zero] at h
  simp only [bracket_apply] at h ⊢
  rw [← sub_eq_zero]
  abel_nf at h ⊢
  exact h

/-- The graded Jacobi identity in terms of `bracket`, when `Q₃ = 0`. -/
theorem bracket_bracket_of_Q_three_eq_zero (h₃ : L.Q 3 = 0) (hx : x ∈ 𝒜 a) (hy : y ∈ 𝒜 b)
    (hz : z ∈ 𝒜 c) :
    L.bracket x (L.bracket y z) =
      L.bracket (L.bracket x y) z + Int.negOnePow (a * b) • L.bracket y (L.bracket x z) := by
  simpa using L.jacobi_of_Q_three_eq_zero h₃ hx hy hz

/-! ### dg Lie algebras are `L∞`-algebras -/

section ofDifferentialBracket

variable (d : V →ₗ[K] V) (bracket : V →ₗ[K] V →ₗ[K] V)

/-- The operations `Q₁ = d`, `Q₂ = bracket`, `Qₙ = 0` (`n ≠ 1, 2`) of a dg Lie algebra. -/
def dglaOps : OpFamily K V
  | 1 => MultilinearMap.ofSubsingleton K V V (0 : Fin 1) d
  | 2 => LinearMap.uncurryLeft
      ((MultilinearMap.ofSubsingletonₗ K K V V (0 : Fin 1)).toLinearMap ∘ₗ bracket)
  | _ => 0

@[simp] lemma dglaOps_zero : dglaOps d bracket 0 = 0 := rfl

@[simp] lemma dglaOps_one_apply (x : Fin 1 → V) : dglaOps d bracket 1 x = d (x 0) := rfl

@[simp] lemma dglaOps_two_apply (x : Fin 2 → V) :
    dglaOps d bracket 2 x = bracket (x 0) (x 1) := rfl

lemma dglaOps_of_three_le {n : ℕ} (hn : 3 ≤ n) : dglaOps d bracket n = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rfl

/-- A dg Lie algebra structure on the graded module `𝒜` — a differential `d` of degree `1`
and a bracket of degree `0`, graded antisymmetric, with `d² = 0`, the graded Leibniz rule and
the graded Jacobi identity — is an `L∞`-algebra with `Q₁ = d`, `Q₂ = bracket` and `Qₙ = 0` for
`n ≥ 3`, with no further signs. -/
def ofDifferentialBracket
    (d_mem : ∀ {a : ℤ} {x : V}, x ∈ 𝒜 a → d x ∈ 𝒜 (a + 1))
    (bracket_mem : ∀ {a b : ℤ} {x y : V}, x ∈ 𝒜 a → y ∈ 𝒜 b → bracket x y ∈ 𝒜 (a + b))
    (bracket_antisymm : ∀ {a b : ℤ} {x y : V}, x ∈ 𝒜 a → y ∈ 𝒜 b →
      bracket y x = -(Int.negOnePow (a * b) • bracket x y))
    (d_comp_d : d ∘ₗ d = 0)
    (leibniz : ∀ {a b : ℤ} {x y : V}, x ∈ 𝒜 a → y ∈ 𝒜 b →
      d (bracket x y) = bracket (d x) y + Int.negOnePow a • bracket x (d y))
    (jacobi : ∀ {a b c : ℤ} {x y z : V}, x ∈ 𝒜 a → y ∈ 𝒜 b → z ∈ 𝒜 c →
      bracket x (bracket y z) =
        bracket (bracket x y) z + Int.negOnePow (a * b) • bracket y (bracket x z)) :
    LInftyAlgebra K 𝒜 where
  Q := dglaOps d bracket
  Q_zero := rfl
  Q_mem {n dg x} hx := by
    rcases Nat.lt_or_ge n 3 with hn | hn
    · interval_cases n
      · simp
      · simpa using d_mem (hx 0)
      · simpa using bracket_mem (hx 0) (hx 1)
    · simp [dglaOps_of_three_le d bracket hn]
  antisymm {n dg x} hx σ := by
    rcases Nat.lt_or_ge n 3 with hn | hn
    · interval_cases n
      · simp
      · rw [Subsingleton.elim σ 1]; simp
      · have hσ : σ = 1 ∨ σ = Equiv.swap 0 1 := by revert σ; decide
        rcases hσ with rfl | rfl
        · simp
        · rw [comp_swap_two, antisymmKoszulSign_swap_two, Units.neg_smul]
          simpa using bracket_antisymm (hx 0) (hx 1)
    · simp [dglaOps_of_three_le d bracket hn]
  jacobi {n dg x} hx := by
    rcases Nat.lt_or_ge n 3 with hn | hn
    · interval_cases n
      · rw [jacobiSum_one]
        simpa using LinearMap.congr_fun d_comp_d (x 0)
      · rw [jacobiSum_two]
        simp only [dglaOps_one_apply, dglaOps_two_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one]
        rw [leibniz (hx 0) (hx 1), bracket_antisymm (hx 0) (d_mem (hx 1)), smul_neg, smul_smul,
          ← Int.negOnePow_add]
        have e : Int.negOnePow (dg 0 * dg 1 + dg 0 * (dg 1 + 1)) = Int.negOnePow (dg 0) := by
          rw [Int.negOnePow_eq_iff]; exact ⟨dg 0 * dg 1, by ring⟩
        rw [e]
        abel
      · rw [jacobiSum_three]
        have h3 : dglaOps d bracket 3 = 0 := rfl
        simp only [h3, dglaOps_one_apply, dglaOps_two_apply, zero_apply, smul_zero, sub_zero,
          zero_add, add_zero, map_zero, Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [bracket_antisymm (hx 1) (bracket_mem (hx 0) (hx 2)),
          bracket_antisymm (hx 0) (bracket_mem (hx 1) (hx 2)),
          smul_neg, smul_neg, smul_smul, smul_smul, ← Int.negOnePow_add, ← Int.negOnePow_add]
        have e₁ : Int.negOnePow (dg 1 * dg 2 + dg 1 * (dg 0 + dg 2)) =
            Int.negOnePow (dg 0 * dg 1) := by
          rw [Int.negOnePow_eq_iff]; exact ⟨dg 1 * dg 2, by ring⟩
        have e₂ : Int.negOnePow (dg 1 * dg 0 + dg 2 * dg 0 + dg 0 * (dg 1 + dg 2)) = 1 := by
          rw [Int.negOnePow_eq_one_iff]; exact ⟨dg 0 * (dg 1 + dg 2), by ring⟩
        rw [e₁, e₂, one_smul, jacobi (hx 0) (hx 1) (hx 2)]
        abel
    · exact jacobiSum_eq_zero_of_le_two _ (fun m hm => dglaOps_of_three_le d bracket hm) hn dg x

variable {d bracket}

@[simp] lemma ofDifferentialBracket_Q (d_mem bracket_mem bracket_antisymm d_comp_d leibniz
    jacobi) :
    (ofDifferentialBracket (𝒜 := 𝒜) d bracket d_mem bracket_mem bracket_antisymm d_comp_d
      leibniz jacobi).Q = dglaOps d bracket := rfl

@[simp] lemma ofDifferentialBracket_d (d_mem bracket_mem bracket_antisymm d_comp_d leibniz
    jacobi) :
    (ofDifferentialBracket (𝒜 := 𝒜) d bracket d_mem bracket_mem bracket_antisymm d_comp_d
      leibniz jacobi).d = d := by
  ext x; simp

@[simp] lemma ofDifferentialBracket_bracket (d_mem bracket_mem bracket_antisymm d_comp_d leibniz
    jacobi) :
    (ofDifferentialBracket (𝒜 := 𝒜) d bracket d_mem bracket_mem bracket_antisymm d_comp_d
      leibniz jacobi).bracket = bracket := by
  ext x y; simp

end ofDifferentialBracket

end LInftyAlgebra

end Kontsevich
