import Kontsevich.Polynomial.BGamma

/-!
# Basic Kontsevich graph examples
-/

namespace Kontsevich

/--
The graph with one aerial vertex and two ground vertices:
the first edge goes to `\bar 1`, and the second goes to `\bar 2`.
-/
def poissonGraph : KontsevichGraph 1 2 where
  target := fun e => Sum.inr e.2

  no_loop := by
    intro e h
    cases h

open scoped BigOperators

variable {d : Nat}

@[simp]
theorem poissonGraph_target (e : Edge 1) :
    poissonGraph.target e = Sum.inr e.2 := rfl

@[simp]
theorem inEdges_poissonGraph_aerial (k : Aerial 1) :
    inEdges poissonGraph (Sum.inl k) = ∅ := by
  ext e
  simp [inEdges]


@[simp]
theorem inEdges_poissonGraph_ground (j : Ground 2) :
    inEdges poissonGraph (Sum.inr j) =
      {((0 : Aerial 1), j)} := by
  ext e
  rcases e with ⟨k, s⟩
  have hk : k = 0 := Fin.eq_zero k
  subst k
  simp [inEdges]

@[simp]
theorem inMulti_poissonGraph_aerial
    (I : Labelling 1 d) (k : Aerial 1) :
    inMulti poissonGraph I (Sum.inl k) = 0 := by
  exact inMulti_eq_zero_of_inEdges_eq_empty
    poissonGraph I (Sum.inl k) (inEdges_poissonGraph_aerial k)

@[simp]
theorem inMulti_poissonGraph_ground
    (I : Labelling 1 d) (j : Ground 2) :
    inMulti poissonGraph I (Sum.inr j) =
      Finsupp.single (I ((0 : Aerial 1), j)) 1 := by
  simp [inMulti]

@[simp]
theorem vertexFactor_poissonGraph
    (γ : Fin 1 → Bivector d) (I : Labelling 1 d)
    (k : Aerial 1) :
    vertexFactor poissonGraph γ I k =
      Bivector.coeff (γ k) (I (k, 0)) (I (k, 1)) := by
  exact vertexFactor_eq_coeff_of_inEdges_eq_empty
    poissonGraph γ I k (inEdges_poissonGraph_aerial k)
@[simp]
theorem groundFactor_poissonGraph
    (f : Fin 2 → RdPoly d) (I : Labelling 1 d)
    (j : Ground 2) :
    groundFactor poissonGraph f I j =
      RdPoly.pderivMulti
        (Finsupp.single (I ((0 : Aerial 1), j)) 1) (f j) := by
    change RdPoly.pderivMulti (inMulti poissonGraph I (Sum.inr j)) (f j) =
      RdPoly.pderivMulti (Finsupp.single (I ((0 : Aerial 1), j)) 1) (f j)
    rw[inMulti_poissonGraph_ground]


/-
For the Poisson graph, the unique edge entering ground vertex \(\bar j\) gives
one ordinary partial derivative:
\[
  \operatorname{groundFactor}_{\Gamma}(f,I,j)
  =
  \partial_{I((0,j))}(f_j).
\]
-/
@[simp]
theorem groundFactor_poissonGraph_eq_pderiv
    (f : Fin 2 → RdPoly d) (I : Labelling 1 d)
    (j : Ground 2) :
    groundFactor poissonGraph f I j =
      RdPoly.pderiv (I ((0 : Aerial 1), j)) (f j) := by
  rw [groundFactor_poissonGraph]
  exact RdPoly.pderivMulti_single_one_apply _ _


/-
A labelling of the two edges of `poissonGraph` is exactly a pair of coordinate
indices:
\[
  I \longleftrightarrow
  \bigl(I(e_0^1), I(e_0^2)\bigr).
\]
-/
def poissonLabellingOfPair
    (p : Fin d × Fin d) : Labelling 1 d :=
  fun e => if e.2 = 0 then p.1 else p.2

@[simp]
theorem poissonLabellingOfPair_left
    (p : Fin d × Fin d) :
    poissonLabellingOfPair p ((0 : Aerial 1), 0) = p.1 := by
  simp [poissonLabellingOfPair]

@[simp]
theorem poissonLabellingOfPair_right
    (p : Fin d × Fin d) :
    poissonLabellingOfPair p ((0 : Aerial 1), 1) = p.2 := by
  simp [poissonLabellingOfPair]

/-
The two descriptions of a Poisson-graph labelling are equivalent:
\[
  \operatorname{Labelling}(1,d) \simeq
  (\operatorname{Fin}d) \times (\operatorname{Fin}d).
\]
-/
def poissonLabellingEquiv :
    Labelling 1 d ≃ Fin d × Fin d where
  toFun I :=
    (I ((0 : Aerial 1), 0), I ((0 : Aerial 1), 1))

  invFun p :=
    poissonLabellingOfPair p

  left_inv I := by
    funext e
    rcases e with ⟨k, s⟩
    have hk : k = 0 := Fin.eq_zero k
    subst k
    fin_cases s <;> simp [poissonLabellingOfPair]

  right_inv p := by
    rcases p with ⟨i, j⟩
    simp [poissonLabellingOfPair]

/-
For a label pair \((i,j)\), the corresponding Poisson-graph summand is
\[
  \gamma^{ij}\,(\partial_i f)\,(\partial_j g).
\]
-/
@[simp]
theorem poissonGraph_summand_ofPair
    (γ : Bivector d) (f g : RdPoly d)
    (p : Fin d × Fin d) :
    (∏ k : Aerial 1,
      vertexFactor poissonGraph (fun _ => γ)
        (poissonLabellingOfPair p) k) *
      (∏ j : Ground 2,
        groundFactor poissonGraph ![f, g]
          (poissonLabellingOfPair p) j) =
        (Bivector.coeff γ p.1 p.2 * RdPoly.pderiv p.1 f) *
          RdPoly.pderiv p.2 g := by
  classical
  simp only [
    Fin.prod_univ_succ,
    Fin.prod_univ_zero,
    mul_one]
  rw [
    groundFactor_poissonGraph_eq_pderiv,
    groundFactor_poissonGraph_eq_pderiv
  ]
  simp [poissonLabellingOfPair, mul_assoc]

 /-
The bracket determined by an antisymmetric polynomial bivector.

If `γ` later satisfies the Jacobi identity, this is its Poisson bracket.
-/
noncomputable def bivectorBracket
    (γ : Bivector d) (f g : RdPoly d) : RdPoly d :=
  ∑ i : Fin d, ∑ j : Fin d,
    (Bivector.coeff γ i j * RdPoly.pderiv i f) *
      RdPoly.pderiv j g

/-
For `poissonGraph`, the sum over all edge-labellings is the sum over all pairs
of coordinate indices:
\[
  B_\Gamma(\gamma)(f,g)
  =
  \sum_{i,j}
    \gamma^{ij}(\partial_i f)(\partial_j g),
\]
written first as a sum over `Fin d × Fin d`.
-/
theorem BGamma_poissonGraph_pair_sum
    (γ : Bivector d) (f g : RdPoly d) :
    BGamma poissonGraph (fun _ => γ) ![f, g] =
      ∑ p : Fin d × Fin d,
        (Bivector.coeff γ p.1 p.2 * RdPoly.pderiv p.1 f) *
          RdPoly.pderiv p.2 g := by
  classical
  let e : Labelling 1 d ≃ Fin d × Fin d :=
    poissonLabellingEquiv
  let S : Labelling 1 d → RdPoly d :=
    fun I =>
      (∏ k : Aerial 1,
        vertexFactor poissonGraph (fun _ => γ) I k) *
        ∏ j : Ground 2,
          groundFactor poissonGraph ![f, g] I j
  let P : Fin d × Fin d → RdPoly d :=
    fun p =>
      (Bivector.coeff γ p.1 p.2 * RdPoly.pderiv p.1 f) *
        RdPoly.pderiv p.2 g
  calc
    BGamma poissonGraph (fun _ => γ) ![f, g] =
        ∑ I : Labelling 1 d, S I := by
          rfl
    _ = ∑ I : Labelling 1 d, P (e I) := by
          apply Finset.sum_congr rfl
          intro I _
          calc
            S I = S (e.symm (e I)) := by
              apply congrArg S
              exact (e.symm_apply_apply I).symm
            _ = P (e I) := by
              change S (poissonLabellingOfPair (e I)) = P (e I)
              simpa [S, P] using
                poissonGraph_summand_ofPair γ f g (e I)
    _ = ∑ p : Fin d × Fin d, P p := by
          exact Equiv.sum_comp e P
    _ = ∑ p : Fin d × Fin d,
        (Bivector.coeff γ p.1 p.2 * RdPoly.pderiv p.1 f) *
          RdPoly.pderiv p.2 g := by
          rfl

/-
The Kontsevich operator of the one-vertex Poisson graph is the bracket defined
by the bivector:
\[
  B_{\Gamma_{\mathrm{Pois}}}(\gamma)(f,g)
  =
  \sum_{i,j}\gamma^{ij}\,\partial_i f\,\partial_j g.
\]
-/
theorem BGamma_poissonGraph_eq_bivectorBracket
    (γ : Bivector d) (f g : RdPoly d) :
    BGamma poissonGraph (fun _ => γ) ![f, g] =
      bivectorBracket γ f g := by
  rw [BGamma_poissonGraph_pair_sum]
  unfold bivectorBracket
  rw [Fintype.sum_prod_type]

/-
The two-aerial-vertex graph from the worked example:
\[
  e_0^1\to\bar 0,\qquad e_0^2\to 1,\qquad
  e_1^1\to\bar 0,\qquad e_1^2\to\bar 1.
\]

In particular, the edge `((0, 1))` enters aerial vertex `1`, so its label will
differentiate the coefficient of the second bivector.
-/
def derivativeGraph : KontsevichGraph 2 2 where
  target := fun
    | (0, 0) => Sum.inr 0
    | (0, 1) => Sum.inl 1
    | (1, 0) => Sum.inr 0
    | (1, 1) => Sum.inr 1

  no_loop := by
    intro e h
    rcases e with ⟨k, s⟩
    fin_cases k <;> fin_cases s <;> simp at h


/-
The only edge entering aerial vertex `1` is the second edge from aerial vertex
`0`:
\[
  \operatorname{In}(1)=\{e_0^2\}.
\]
-/
@[simp]
theorem inEdges_derivativeGraph_aerial_one :
    inEdges derivativeGraph (Sum.inl (1 : Aerial 2)) =
      {((0 : Aerial 2), (1 : Fin 2))} := by
  ext e
  rcases e with ⟨k, s⟩
  fin_cases k <;> fin_cases s <;> simp [inEdges, derivativeGraph]

@[simp]
theorem inMulti_derivativeGraph_aerial_one
    (I : Labelling 2 d) :
    inMulti derivativeGraph I (Sum.inl (1 : Aerial 2)) =
      Finsupp.single (I ((0 : Aerial 2), (1 : Fin 2))) 1 := by
  simp [inMulti, inEdges_derivativeGraph_aerial_one]

/-
Consequently, the label on `e_0^2` differentiates the coefficient belonging to
the second bivector:
\[
  \partial_{I(e_0^2)}
    \bigl(\gamma_1^{\,I(e_1^1)\,I(e_1^2)}\bigr).
\]
-/
@[simp]
theorem vertexFactor_derivativeGraph_one
    (γ : Fin 2 → Bivector d) (I : Labelling 2 d) :
    vertexFactor derivativeGraph γ I (1 : Aerial 2) =
      RdPoly.pderiv (I ((0 : Aerial 2), (1 : Fin 2)))
        (Bivector.coeff (γ (1 : Aerial 2))
          (I ((1 : Aerial 2), (0 : Fin 2)))
          (I ((1 : Aerial 2), (1 : Fin 2)))) := by
  unfold vertexFactor
  rw [inMulti_derivativeGraph_aerial_one]
  exact RdPoly.pderivMulti_single_one_apply _ _

/-
For `derivativeGraph`,
\[
  \operatorname{In}(0)=\varnothing,\qquad
  \operatorname{In}(\bar 0)=\{e_0^1,e_1^1\},\qquad
  \operatorname{In}(\bar 1)=\{e_1^2\}.
\]
-/
@[simp]
theorem inEdges_derivativeGraph_aerial_zero :
    inEdges derivativeGraph (Sum.inl (0 : Aerial 2)) = ∅ := by
  ext e
  rcases e with ⟨k, s⟩
  fin_cases k <;> fin_cases s <;> simp [inEdges, derivativeGraph]

@[simp]
theorem inEdges_derivativeGraph_ground_zero :
    inEdges derivativeGraph (Sum.inr (0 : Ground 2)) =
      {((0 : Aerial 2), (0 : Fin 2)),
       ((1 : Aerial 2), (0 : Fin 2))} := by
  ext e
  rcases e with ⟨k, s⟩
  fin_cases k <;> fin_cases s <;> simp [inEdges, derivativeGraph]

@[simp]
theorem inEdges_derivativeGraph_ground_one :
    inEdges derivativeGraph (Sum.inr (1 : Ground 2)) =
      {((1 : Aerial 2), (1 : Fin 2))} := by
  ext e
  rcases e with ⟨k, s⟩
  fin_cases k <;> fin_cases s <;> simp [inEdges, derivativeGraph]

/-
The remaining incoming multi-indices are
\[
  \alpha(0)=0,\qquad
  \alpha(\bar 0)=\delta_{I(e_0^1)}+\delta_{I(e_1^1)},\qquad
  \alpha(\bar 1)=\delta_{I(e_1^2)}.
\]
-/
@[simp]
theorem inMulti_derivativeGraph_aerial_zero
    (I : Labelling 2 d) :
    inMulti derivativeGraph I (Sum.inl (0 : Aerial 2)) = 0 := by
  exact inMulti_eq_zero_of_inEdges_eq_empty
    derivativeGraph I (Sum.inl (0 : Aerial 2))
      inEdges_derivativeGraph_aerial_zero

@[simp]
theorem inMulti_derivativeGraph_ground_zero
    (I : Labelling 2 d) :
    inMulti derivativeGraph I (Sum.inr (0 : Ground 2)) =
      Finsupp.single (I ((0 : Aerial 2), (0 : Fin 2))) 1 +
        Finsupp.single (I ((1 : Aerial 2), (0 : Fin 2))) 1 := by
  simp [inMulti, inEdges_derivativeGraph_ground_zero]

@[simp]
theorem inMulti_derivativeGraph_ground_one
    (I : Labelling 2 d) :
    inMulti derivativeGraph I (Sum.inr (1 : Ground 2)) =
      Finsupp.single (I ((1 : Aerial 2), (1 : Fin 2))) 1 := by
  simp [inMulti, inEdges_derivativeGraph_ground_one]


/-
No edge enters aerial vertex `0`, so its coefficient is undifferentiated.
-/
@[simp]
theorem vertexFactor_derivativeGraph_zero
    (γ : Fin 2 → Bivector d) (I : Labelling 2 d) :
    vertexFactor derivativeGraph γ I (0 : Aerial 2) =
      Bivector.coeff (γ (0 : Aerial 2))
        (I ((0 : Aerial 2), (0 : Fin 2)))
        (I ((0 : Aerial 2), (1 : Fin 2))) := by
  exact vertexFactor_eq_coeff_of_inEdges_eq_empty
    derivativeGraph γ I (0 : Aerial 2)
      inEdges_derivativeGraph_aerial_zero


/-
The first ground argument receives two derivatives, one for each edge entering
\(\bar 0\).
-/
@[simp]
theorem groundFactor_derivativeGraph_zero
    (f : Fin 2 → RdPoly d) (I : Labelling 2 d) :
    groundFactor derivativeGraph f I (0 : Ground 2) =
      RdPoly.pderivMulti
        (Finsupp.single (I ((0 : Aerial 2), (0 : Fin 2))) 1 +
          Finsupp.single (I ((1 : Aerial 2), (0 : Fin 2))) 1)
        (f (0 : Ground 2)) := by
  change
    RdPoly.pderivMulti
      (inMulti derivativeGraph I (Sum.inr (0 : Ground 2)))
      (f (0 : Ground 2)) =
        RdPoly.pderivMulti
          (Finsupp.single (I ((0 : Aerial 2), (0 : Fin 2))) 1 +
            Finsupp.single (I ((1 : Aerial 2), (0 : Fin 2))) 1)
          (f (0 : Ground 2))
  rw [inMulti_derivativeGraph_ground_zero]


/-
The second ground argument receives the derivative attached to \(e_1^2\).
-/
@[simp]
theorem groundFactor_derivativeGraph_one
    (f : Fin 2 → RdPoly d) (I : Labelling 2 d) :
    groundFactor derivativeGraph f I (1 : Ground 2) =
      RdPoly.pderiv (I ((1 : Aerial 2), (1 : Fin 2)))
        (f (1 : Ground 2)) := by
  change
    RdPoly.pderivMulti
      (inMulti derivativeGraph I (Sum.inr (1 : Ground 2)))
      (f (1 : Ground 2)) =
        RdPoly.pderiv (I ((1 : Aerial 2), (1 : Fin 2)))
          (f (1 : Ground 2))
  rw [inMulti_derivativeGraph_ground_one]
  exact RdPoly.pderivMulti_single_one_apply _ _

/-
For a labelling `I`, write
\[
  a=I(e_0^1),\quad b=I(e_0^2),\quad
  c=I(e_1^1),\quad e=I(e_1^2).
\]
The `derivativeGraph` summand is
\[
  \gamma_0^{ab}\,
  (\partial_b\gamma_1^{ce})\,
  \partial^{\delta_a+\delta_c}f_0\,
  (\partial_e f_1).
\]
-/
theorem derivativeGraph_summand
    (γ : Fin 2 → Bivector d) (f : Fin 2 → RdPoly d)
    (I : Labelling 2 d) :
    (∏ k : Aerial 2, vertexFactor derivativeGraph γ I k) *
      (∏ j : Ground 2, groundFactor derivativeGraph f I j) =
        Bivector.coeff (γ (0 : Aerial 2))
          (I ((0 : Aerial 2), (0 : Fin 2)))
          (I ((0 : Aerial 2), (1 : Fin 2))) *
        RdPoly.pderiv (I ((0 : Aerial 2), (1 : Fin 2)))
          (Bivector.coeff (γ (1 : Aerial 2))
            (I ((1 : Aerial 2), (0 : Fin 2)))
            (I ((1 : Aerial 2), (1 : Fin 2)))) *
        RdPoly.pderivMulti
          (Finsupp.single (I ((0 : Aerial 2), (0 : Fin 2))) 1 +
            Finsupp.single (I ((1 : Aerial 2), (0 : Fin 2))) 1)
          (f (0 : Ground 2)) *
        RdPoly.pderiv (I ((1 : Aerial 2), (1 : Fin 2)))
          (f (1 : Ground 2)) := by
  classical
  simp only [
    Fin.prod_univ_succ,
    Fin.prod_univ_zero,
    mul_one,
    Fin.succ_zero_eq_one
  ]
  rw [
    vertexFactor_derivativeGraph_zero,
    vertexFactor_derivativeGraph_one,
    groundFactor_derivativeGraph_zero,
    groundFactor_derivativeGraph_one
  ]
  ring
/-
The full operator for `derivativeGraph` is the sum of the worked-example
summands:
\[
  \sum_I
    \gamma_0^{ab}\,
    (\partial_b\gamma_1^{ce})\,
    \partial^{\delta_a+\delta_c}f_0\,
    (\partial_e f_1).
\]
-/
theorem BGamma_derivativeGraph_expansion
    (γ : Fin 2 → Bivector d) (f : Fin 2 → RdPoly d) :
    BGamma derivativeGraph γ f =
      ∑ I : Labelling 2 d,
        Bivector.coeff (γ (0 : Aerial 2))
          (I ((0 : Aerial 2), (0 : Fin 2)))
          (I ((0 : Aerial 2), (1 : Fin 2))) *
        RdPoly.pderiv (I ((0 : Aerial 2), (1 : Fin 2)))
          (Bivector.coeff (γ (1 : Aerial 2))
            (I ((1 : Aerial 2), (0 : Fin 2)))
            (I ((1 : Aerial 2), (1 : Fin 2)))) *
        RdPoly.pderivMulti
          (Finsupp.single (I ((0 : Aerial 2), (0 : Fin 2))) 1 +
            Finsupp.single (I ((1 : Aerial 2), (0 : Fin 2))) 1)
          (f (0 : Ground 2)) *
        RdPoly.pderiv (I ((1 : Aerial 2), (1 : Fin 2)))
          (f (1 : Ground 2)) := by
  unfold BGamma
  apply Finset.sum_congr rfl
  intro I _
  exact derivativeGraph_summand γ f I

/-
The two-aerial-vertex graph with no aerial edge:
\[
  e_0^1,e_1^1\to\bar 0,
  \qquad
  e_0^2,e_1^2\to\bar 1.
\]

Thus no edge enters either aerial vertex.
-/
def moyalGraph : KontsevichGraph 2 2 where
  target := fun
    | (0, 0) => Sum.inr 0
    | (0, 1) => Sum.inr 1
    | (1, 0) => Sum.inr 0
    | (1, 1) => Sum.inr 1

  no_loop := by
    intro e h
    rcases e with ⟨k, s⟩
    fin_cases k <;> fin_cases s <;> simp at h


/-
No edge enters an aerial vertex of `moyalGraph`:
\[
  \operatorname{In}(0)=\operatorname{In}(1)=\varnothing.
\]
-/
@[simp]
theorem inEdges_moyalGraph_aerial
    (k : Aerial 2) :
    inEdges moyalGraph (Sum.inl k) = ∅ := by
  ext e
  rcases e with ⟨l, s⟩
  fin_cases l <;> fin_cases s <;> simp [inEdges, moyalGraph]

/-
Consequently, neither bivector coefficient is differentiated.
-/
@[simp]
theorem vertexFactor_moyalGraph
    (γ : Fin 2 → Bivector d) (I : Labelling 2 d)
    (k : Aerial 2) :
    vertexFactor moyalGraph γ I k =
      Bivector.coeff (γ k) (I (k, 0)) (I (k, 1)) := by
  exact vertexFactor_eq_coeff_of_inEdges_eq_empty
    moyalGraph γ I k (inEdges_moyalGraph_aerial k)

/-
For `moyalGraph`,
\[
  \operatorname{In}(\bar 0)=\{e_0^1,e_1^1\},
  \qquad
  \operatorname{In}(\bar 1)=\{e_0^2,e_1^2\}.
\]
-/
@[simp]
theorem inEdges_moyalGraph_ground_zero :
    inEdges moyalGraph (Sum.inr (0 : Ground 2)) =
      {((0 : Aerial 2), (0 : Fin 2)),
       ((1 : Aerial 2), (0 : Fin 2))} := by
  ext e
  rcases e with ⟨k, s⟩
  fin_cases k <;> fin_cases s <;> simp [inEdges, moyalGraph]

@[simp]
theorem inEdges_moyalGraph_ground_one :
    inEdges moyalGraph (Sum.inr (1 : Ground 2)) =
      {((0 : Aerial 2), (1 : Fin 2)),
       ((1 : Aerial 2), (1 : Fin 2))} := by
  ext e
  rcases e with ⟨k, s⟩
  fin_cases k <;> fin_cases s <;> simp [inEdges, moyalGraph]

/-
The ground-vertex multi-indices are
\[
  \alpha(\bar 0)=\delta_{I(e_0^1)}+\delta_{I(e_1^1)},
  \qquad
  \alpha(\bar 1)=\delta_{I(e_0^2)}+\delta_{I(e_1^2)}.
\]
-/
@[simp]
theorem inMulti_moyalGraph_ground_zero
    (I : Labelling 2 d) :
    inMulti moyalGraph I (Sum.inr (0 : Ground 2)) =
      Finsupp.single (I ((0 : Aerial 2), (0 : Fin 2))) 1 +
        Finsupp.single (I ((1 : Aerial 2), (0 : Fin 2))) 1 := by
  simp [inMulti, inEdges_moyalGraph_ground_zero]

@[simp]
theorem inMulti_moyalGraph_ground_one
    (I : Labelling 2 d) :
    inMulti moyalGraph I (Sum.inr (1 : Ground 2)) =
      Finsupp.single (I ((0 : Aerial 2), (1 : Fin 2))) 1 +
        Finsupp.single (I ((1 : Aerial 2), (1 : Fin 2))) 1 := by
  simp [inMulti, inEdges_moyalGraph_ground_one]

@[simp]
theorem groundFactor_moyalGraph_zero
    (f : Fin 2 → RdPoly d) (I : Labelling 2 d) :
    groundFactor moyalGraph f I (0 : Ground 2) =
      RdPoly.pderivMulti
        (Finsupp.single (I ((0 : Aerial 2), (0 : Fin 2))) 1 +
          Finsupp.single (I ((1 : Aerial 2), (0 : Fin 2))) 1)
        (f (0 : Ground 2)) := by
  change
    RdPoly.pderivMulti
      (inMulti moyalGraph I (Sum.inr (0 : Ground 2)))
      (f (0 : Ground 2)) =
        RdPoly.pderivMulti
          (Finsupp.single (I ((0 : Aerial 2), (0 : Fin 2))) 1 +
            Finsupp.single (I ((1 : Aerial 2), (0 : Fin 2))) 1)
          (f (0 : Ground 2))
  rw [inMulti_moyalGraph_ground_zero]

@[simp]
theorem groundFactor_moyalGraph_one
    (f : Fin 2 → RdPoly d) (I : Labelling 2 d) :
    groundFactor moyalGraph f I (1 : Ground 2) =
      RdPoly.pderivMulti
        (Finsupp.single (I ((0 : Aerial 2), (1 : Fin 2))) 1 +
          Finsupp.single (I ((1 : Aerial 2), (1 : Fin 2))) 1)
        (f (1 : Ground 2)) := by
  change
    RdPoly.pderivMulti
      (inMulti moyalGraph I (Sum.inr (1 : Ground 2)))
      (f (1 : Ground 2)) =
        RdPoly.pderivMulti
          (Finsupp.single (I ((0 : Aerial 2), (1 : Fin 2))) 1 +
            Finsupp.single (I ((1 : Aerial 2), (1 : Fin 2))) 1)
          (f (1 : Ground 2))
  rw [inMulti_moyalGraph_ground_one]

/-
For a labelling `I`, the `moyalGraph` summand is
\[
  \gamma_0^{ab}\gamma_1^{ce}\,
  \partial^{\delta_a+\delta_c}f_0\,
  \partial^{\delta_b+\delta_e}f_1.
\]
No derivative acts on a bivector coefficient.
-/
theorem moyalGraph_summand
    (γ : Fin 2 → Bivector d) (f : Fin 2 → RdPoly d)
    (I : Labelling 2 d) :
    (∏ k : Aerial 2, vertexFactor moyalGraph γ I k) *
      (∏ j : Ground 2, groundFactor moyalGraph f I j) =
        Bivector.coeff (γ (0 : Aerial 2))
          (I ((0 : Aerial 2), (0 : Fin 2)))
          (I ((0 : Aerial 2), (1 : Fin 2))) *
        Bivector.coeff (γ (1 : Aerial 2))
          (I ((1 : Aerial 2), (0 : Fin 2)))
          (I ((1 : Aerial 2), (1 : Fin 2))) *
        RdPoly.pderivMulti
          (Finsupp.single (I ((0 : Aerial 2), (0 : Fin 2))) 1 +
            Finsupp.single (I ((1 : Aerial 2), (0 : Fin 2))) 1)
          (f (0 : Ground 2)) *
        RdPoly.pderivMulti
          (Finsupp.single (I ((0 : Aerial 2), (1 : Fin 2))) 1 +
            Finsupp.single (I ((1 : Aerial 2), (1 : Fin 2))) 1)
          (f (1 : Ground 2)) := by
  classical
  simp only [
    Fin.prod_univ_succ,
    Fin.prod_univ_zero,
    mul_one,
    Fin.succ_zero_eq_one
  ]
  rw [
    vertexFactor_moyalGraph,
    vertexFactor_moyalGraph,
    groundFactor_moyalGraph_zero,
    groundFactor_moyalGraph_one
  ]
  ring

/-
The complete operator for `moyalGraph` is the finite sum of its Moyal-type
summands.
-/
theorem BGamma_moyalGraph_expansion
    (γ : Fin 2 → Bivector d) (f : Fin 2 → RdPoly d) :
    BGamma moyalGraph γ f =
      ∑ I : Labelling 2 d,
        Bivector.coeff (γ (0 : Aerial 2))
          (I ((0 : Aerial 2), (0 : Fin 2)))
          (I ((0 : Aerial 2), (1 : Fin 2))) *
        Bivector.coeff (γ (1 : Aerial 2))
          (I ((1 : Aerial 2), (0 : Fin 2)))
          (I ((1 : Aerial 2), (1 : Fin 2))) *
        RdPoly.pderivMulti
          (Finsupp.single (I ((0 : Aerial 2), (0 : Fin 2))) 1 +
            Finsupp.single (I ((1 : Aerial 2), (0 : Fin 2))) 1)
          (f (0 : Ground 2)) *
        RdPoly.pderivMulti
          (Finsupp.single (I ((0 : Aerial 2), (1 : Fin 2))) 1 +
            Finsupp.single (I ((1 : Aerial 2), (1 : Fin 2))) 1)
          (f (1 : Ground 2)) := by
  unfold BGamma
  apply Finset.sum_congr rfl
  intro I _
  exact moyalGraph_summand γ f I

/-
Both worked graphs have distinct targets for the two outgoing edges at each
aerial vertex, so they are admissible Kontsevich graphs.
-/
def derivativeGraphAdmissible : AdmissibleGraph 2 2 where
  toKontsevichGraph := derivativeGraph

  no_double := by
    intro k h
    fin_cases k <;> simp [derivativeGraph] at h


def moyalGraphAdmissible : AdmissibleGraph 2 2 where
  toKontsevichGraph := moyalGraph

  no_double := by
    intro k h
    fin_cases k <;> simp [moyalGraph] at h

/-
A non-admissible graph with a double edge: both outgoing edges from the unique
aerial vertex land at the same ground vertex.
-/
def doubleEdgeGraph : KontsevichGraph 1 1 where
  target := fun _ => Sum.inr 0

  no_loop := by
    intro e h
    cases h

@[simp]
theorem hasDoubleEdge_doubleEdgeGraph :
    hasDoubleEdge doubleEdgeGraph := by
  refine ⟨0, ?_⟩
  rfl

/-
The antisymmetry of the bivector forces cancellation under the swap of the two
edge labels:
\[
  B_{\Gamma_{\mathrm{double}}}=0.
\]
-/
theorem BGamma_doubleEdgeGraph_eq_zero
    (γ : Fin 1 → Bivector d) (f : Fin 1 → RdPoly d) :
    BGamma doubleEdgeGraph γ f = 0 := by
  exact BGamma_eq_zero_of_hasDoubleEdge
    doubleEdgeGraph γ f hasDoubleEdge_doubleEdgeGraph

theorem poissonGraph_swap_eq_neg_bracket
    (γ : Bivector d) (f g : RdPoly d) :
    BGamma (swapOutgoingEdges poissonGraph (0 : Aerial 1))
      (fun _ => γ) ![f, g] =
        -bivectorBracket γ f g := by
  rw [BGamma_swapOutgoingEdges]
  rw [BGamma_poissonGraph_eq_bivectorBracket]

end Kontsevich
