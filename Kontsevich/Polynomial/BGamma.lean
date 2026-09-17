import Kontsevich.Polynomial.Basic
import Kontsevich.Polynomial.Bivector
import Kontsevich.Combinatorics.AdmissibleGraph
import Kontsevich.Polynomial.DPoly
set_option linter.style.header false -- Module header linting is intentionally disabled.
/-!
# Polynomial Kontsevich graph operators
This module defines the polynomial-coefficient operator
`BGamma` attached toan admissible Kontsevich graph.
-/

namespace Kontsevich

open scoped BigOperators

variable {n m d : Nat}

/-- The factor contributed by aerial vertex `k`. -/
noncomputable def vertexFactor
    (G : KontsevichGraph n m) (γ : Fin n → Bivector d)
    (I : Labelling n d) (k : Aerial n) : RdPoly d :=
  RdPoly.pderivMulti (inMulti G I (Sum.inl k))
    (Bivector.coeff (γ k) (I (k, 0)) (I (k, 1)))

@[simp]
theorem vertexFactor_eq_coeff_of_inEdges_eq_empty
    (G : KontsevichGraph n m) (γ : Fin n → Bivector d)
    (I : Labelling n d) (k : Aerial n)
    (h : inEdges G (Sum.inl k) = ∅) :
    vertexFactor G γ I k =
      Bivector.coeff (γ k) (I (k, 0)) (I (k, 1)) := by
  calc
    vertexFactor G γ I k =
        RdPoly.pderivMulti (0 : MultiIndex d)
          (Bivector.coeff (γ k) (I (k, 0)) (I (k, 1))) := by
      rw [vertexFactor,
        inMulti_eq_zero_of_inEdges_eq_empty G I (Sum.inl k) h]
    _ = Bivector.coeff (γ k) (I (k, 0)) (I (k, 1)) := by
      simp

/-- The aerial factor at `k`, viewed as a linear map in its bivector. -/
noncomputable def vertexFactorLinear
    (G : KontsevichGraph n m) (I : Labelling n d)
    (k : Aerial n) : Bivector d →ₗ[ℝ] RdPoly d :=
  (RdPoly.pderivMulti (inMulti G I (Sum.inl k))).comp
    (Bivector.coeffLinearMap (I (k, 0)) (I (k, 1)))

@[simp]
theorem vertexFactor_eq_vertexFactorLinear
    (G : KontsevichGraph n m) (γ : Fin n → Bivector d)
    (I : Labelling n d) (k : Aerial n) :
    vertexFactor G γ I k =
      vertexFactorLinear G I k (γ k) := rfl



/-- The factor contributed by ground vertex `j`. -/
noncomputable def groundFactor
    (G : KontsevichGraph n m) (f : Fin m → RdPoly d)
    (I : Labelling n d) (j : Ground m) : RdPoly d :=
  RdPoly.pderivMulti (inMulti G I (Sum.inr j)) (f j)


  /- The ground factor at `j`, viewed as a linear
  map in its polynomial input. -/

noncomputable def groundFactorLinear
    (G : KontsevichGraph n m) (I : Labelling n d)
    (j : Ground m) : RdPoly d →ₗ[ℝ] RdPoly d :=
  RdPoly.pderivMulti (inMulti G I (Sum.inr j))

@[simp]
theorem groundFactor_eq_groundFactorLinear
    (G : KontsevichGraph n m) (f : Fin m → RdPoly d)
    (I : Labelling n d) (j : Ground m) :
    groundFactor G f I j =
      groundFactorLinear G I j (f j) := rfl

-- ∂^α(p + q) = ∂^αp + ∂^αq
theorem groundFactor_update_add
    (G : KontsevichGraph n m) (f : Fin m → RdPoly d)
    (I : Labelling n d) (j : Ground m)
    (p q : RdPoly d) :
    groundFactor G (Function.update f j (p + q)) I j =
      groundFactor G (Function.update f j p) I j +
        groundFactor G (Function.update f j q) I j := by
  simp [groundFactor_eq_groundFactorLinear]

-- ∂^α(c • p) = c • ∂^αp
theorem groundFactor_update_smul
    (G : KontsevichGraph n m) (f : Fin m → RdPoly d)
    (I : Labelling n d) (j : Ground m)
    (c : ℝ) (p : RdPoly d) :
    groundFactor G (Function.update f j (c • p)) I j =
      c • groundFactor G (Function.update f j p) I j := by
  simp [groundFactor_eq_groundFactorLinear]

@[simp]
theorem groundFactor_eq_of_inEdges_eq_empty
    (G : KontsevichGraph n m) (f : Fin m → RdPoly d)
    (I : Labelling n d) (j : Ground m)
    (h : inEdges G (Sum.inr j) = ∅) :
    groundFactor G f I j = f j := by
  calc
    groundFactor G f I j =
        RdPoly.pderivMulti (0 : MultiIndex d) (f j) := by
      rw [groundFactor,
        inMulti_eq_zero_of_inEdges_eq_empty G I (Sum.inr j) h]
    _ = f j := by
      simp

/-- The coefficient of the normal-form term indexed by a graph labelling. -/
noncomputable def graphCoefficient
    (G : KontsevichGraph n m) (γ : Fin n → Bivector d)
    (I : Labelling n d) : RdPoly d :=
  ∏ k : Aerial n, vertexFactor G γ I k

/-- The family of ground-vertex multi-indices for a graph labelling. -/
noncomputable def graphMultiIndex
    (G : KontsevichGraph n m) (I : Labelling n d) :
    Fin m → MultiIndex d :=
  fun j => inMulti G I (Sum.inr j)

/-- The polydifferential normal-form term indexed by a graph labelling. -/
noncomputable def graphTerm
    (G : KontsevichGraph n m) (γ : Fin n → Bivector d)
    (I : Labelling n d) : DPolyTerm d m :=
  (graphCoefficient G γ I, graphMultiIndex G I)


/-- The polynomial operator associated to an admissible graph. -/
noncomputable def BGamma
    (G : KontsevichGraph n m) (γ : Fin n → Bivector d)
    (f : Fin m → RdPoly d) : RdPoly d :=
  ∑ I : Labelling n d,
    (∏ k : Aerial n, vertexFactor G γ I k) *
      ∏ j : Ground m, groundFactor G f I j


/-- If one aerial bivector input is zero, the graph operator vanishes. -/
theorem BGamma_eq_zero_of_gamma_eq_zero
    (G : KontsevichGraph n m) (γ : Fin n → Bivector d)
    (f : Fin m → RdPoly d) (k : Aerial n)
    (h : γ k = 0) :
    BGamma G γ f = 0 := by
  unfold BGamma
  apply Finset.sum_eq_zero
  intro I _
  have hkI : vertexFactor G γ I k = 0 := by
    simp [vertexFactor_eq_vertexFactorLinear, h]
  have hprod :
      ∏ a : Aerial n, vertexFactor G γ I a = 0 := by
    exact Finset.prod_eq_zero (Finset.mem_univ k) hkI
  rw[hprod]
  simp



/-- If one ground polynomial input is zero, the graph operator vanishes. -/
theorem BGamma_eq_zero_of_arg_eq_zero
    (G : KontsevichGraph n m) (γ : Fin n → Bivector d)
    (f : Fin m → RdPoly d) (j : Ground m)
    (h : f j = 0) :
    BGamma G γ f = 0 := by
  unfold BGamma
  apply Finset.sum_eq_zero
  intro I _
  have hjI : groundFactor G f I j = 0 := by
    simp [groundFactor_eq_groundFactorLinear, h]
  have hprod :
      ∏ b : Ground m, groundFactor G f I b = 0 := by
    exact Finset.prod_eq_zero (Finset.mem_univ j) hjI
  rw [hprod]
  simp


@[simp]
theorem BGamma_empty
    (G : KontsevichGraph 0 m) (γ : Fin 0 → Bivector d)
    (f : Fin m → RdPoly d) :
    BGamma G γ f = ∏ j : Ground m, f j := by
  simp [BGamma, vertexFactor, groundFactor, inMulti, inEdges]

@[simp]
theorem evalDPolyTerm_graphTerm
    (G : KontsevichGraph n m) (γ : Fin n → Bivector d)
    (f : Fin m → RdPoly d) (I : Labelling n d) :
    evalDPolyTerm (graphTerm G γ I) f =
      (∏ k : Aerial n, vertexFactor G γ I k) *
        ∏ j : Ground m, groundFactor G f I j := rfl

theorem BGamma_eq_sum_evalDPolyTerm
    (G : KontsevichGraph n m) (γ : Fin n → Bivector d)
    (f : Fin m → RdPoly d) :
    BGamma G γ f =
      ∑ I : Labelling n d, evalDPolyTerm (graphTerm G γ I) f := rfl

/-- The finite family of normal-form terms occurring in `BGamma`. -/
noncomputable def BGammaTerms
    (G : KontsevichGraph n m) (γ : Fin n → Bivector d) :
    Multiset (DPolyTerm d m) :=
  (Finset.univ : Finset (Labelling n d)).1.map (graphTerm G γ)

theorem BGamma_eq_sum_BGammaTerms
    (G : KontsevichGraph n m) (γ : Fin n → Bivector d)
    (f : Fin m → RdPoly d) :
    BGamma G γ f =
      ((BGammaTerms G γ).map
        (fun term => evalDPolyTerm term f)).sum := by
  rw [BGamma_eq_sum_evalDPolyTerm]
  simp [BGammaTerms]

theorem groundFactor_update_ne
    (G : KontsevichGraph n m) (f : Fin m → RdPoly d)
    (I : Labelling n d) (j j' : Ground m)
    (p : RdPoly d) (h : j' ≠ j) :
    groundFactor G (Function.update f j p) I j' =
      groundFactor G f I j' := by
  simp [groundFactor_eq_groundFactorLinear, h]

/--
Fix a graph `G` and a labelling `I`. Define
`P_I(f) = ∏ b, groundFactor G f I b`.
For a chosen ground vertex `j`, replacing the `j`-th polynomial input by
`p + q` gives
`P_I(f[j ↦ p + q]) = P_I(f[j ↦ p]) + P_I(f[j ↦ q])`.
All factors at vertices `b ≠ j` are unchanged; the factor at `j` is linear
because it is an iterated partial derivative.
-/
theorem groundProduct_update_add
    (G : KontsevichGraph n m) (f : Fin m → RdPoly d)
    (I : Labelling n d) (j : Ground m)
    (p q : RdPoly d) :
    (∏ b : Ground m,
      groundFactor G (Function.update f j (p + q)) I b) =
      (∏ b : Ground m,
        groundFactor G (Function.update f j p) I b) +
        ∏ b : Ground m,
          groundFactor G (Function.update f j q) I b := by
  have hErase (r : RdPoly d) :
      (∏ b ∈ (Finset.univ : Finset (Ground m)).erase j,
        groundFactor G (Function.update f j r) I b) =
        ∏ b ∈ (Finset.univ : Finset (Ground m)).erase j,
          groundFactor G f I b := by
    apply Finset.prod_congr rfl
    intro b hb
    exact groundFactor_update_ne G f I j b r
      (Finset.ne_of_mem_erase hb)
  calc
    (∏ b : Ground m,
      groundFactor G (Function.update f j (p + q)) I b) =
        groundFactor G (Function.update f j (p + q)) I j *
          ∏ b ∈ (Finset.univ : Finset (Ground m)).erase j,
            groundFactor G (Function.update f j (p + q)) I b := by
          symm
          exact Finset.mul_prod_erase Finset.univ
            (fun b => groundFactor G (Function.update f j (p + q)) I b)
            (Finset.mem_univ j)
    _ = (groundFactor G (Function.update f j p) I j +
          groundFactor G (Function.update f j q) I j) *
          ∏ b ∈ (Finset.univ : Finset (Ground m)).erase j,
            groundFactor G f I b := by
          rw [groundFactor_update_add, hErase]
    _ = groundFactor G (Function.update f j p) I j *
          (∏ b ∈ (Finset.univ : Finset (Ground m)).erase j,
            groundFactor G f I b) +
        groundFactor G (Function.update f j q) I j *
          (∏ b ∈ (Finset.univ : Finset (Ground m)).erase j,
            groundFactor G f I b) := by
          rw [add_mul]
    _ = (∏ b : Ground m,
          groundFactor G (Function.update f j p) I b) +
        ∏ b : Ground m,
          groundFactor G (Function.update f j q) I b := by
          have hp :
              groundFactor G (Function.update f j p) I j *
                  (∏ b ∈ (Finset.univ : Finset (Ground m)).erase j,
                    groundFactor G f I b) =
                ∏ b : Ground m,
                  groundFactor G (Function.update f j p) I b := by
            rw [← hErase p]
            exact Finset.mul_prod_erase Finset.univ
              (fun b => groundFactor G (Function.update f j p) I b)
              (Finset.mem_univ j)
          have hq :
              groundFactor G (Function.update f j q) I j *
                  (∏ b ∈ (Finset.univ : Finset (Ground m)).erase j,
                    groundFactor G f I b) =
                ∏ b : Ground m,
                  groundFactor G (Function.update f j q) I b := by
            rw [← hErase q]
            exact Finset.mul_prod_erase Finset.univ
              (fun b => groundFactor G (Function.update f j q) I b)
              (Finset.mem_univ j)
          rw [hp, hq]


/--
Fix a graph `G` and a labelling `I`. Define
`P_I(f) = ∏ b, groundFactor G f I b`.
For a chosen ground vertex `j`, replacing the `j`-th polynomial input by
`c • p` gives
`P_I(f[j ↦ c • p]) = c • P_I(f[j ↦ p])`.
All factors at vertices `b ≠ j` are unchanged; the factor at `j` is
`ℝ`-linear because it is an iterated partial derivative.
-/
theorem groundProduct_update_smul
    (G : KontsevichGraph n m) (f : Fin m → RdPoly d)
    (I : Labelling n d) (j : Ground m)
    (c : ℝ) (p : RdPoly d) :
    (∏ b : Ground m,
      groundFactor G (Function.update f j (c • p)) I b) =
      c • (∏ b : Ground m,
        groundFactor G (Function.update f j p) I b) := by
  have hErase (r : RdPoly d) :
      (∏ b ∈ (Finset.univ : Finset (Ground m)).erase j,
        groundFactor G (Function.update f j r) I b) =
        ∏ b ∈ (Finset.univ : Finset (Ground m)).erase j,
          groundFactor G f I b := by
    apply Finset.prod_congr rfl
    intro b hb
    exact groundFactor_update_ne G f I j b r
      (Finset.ne_of_mem_erase hb)
  calc
    (∏ b : Ground m,
      groundFactor G (Function.update f j (c • p)) I b) =
        groundFactor G (Function.update f j (c • p)) I j *
          ∏ b ∈ (Finset.univ : Finset (Ground m)).erase j,
            groundFactor G (Function.update f j (c • p)) I b := by
          symm
          exact Finset.mul_prod_erase Finset.univ
            (fun b => groundFactor G (Function.update f j (c • p)) I b)
            (Finset.mem_univ j)
    _ = (c • groundFactor G (Function.update f j p) I j) *
          ∏ b ∈ (Finset.univ : Finset (Ground m)).erase j,
            groundFactor G f I b := by
          rw [groundFactor_update_smul, hErase]
    _ = c • (groundFactor G (Function.update f j p) I j *
          ∏ b ∈ (Finset.univ : Finset (Ground m)).erase j,
            groundFactor G f I b) := by
          rw [smul_mul_assoc]
    _ = c • (∏ b : Ground m,
          groundFactor G (Function.update f j p) I b) := by
          congr 1
          rw [← hErase p]
          exact Finset.mul_prod_erase Finset.univ
            (fun b => groundFactor G (Function.update f j p) I b)
            (Finset.mem_univ j)



/--
`BGamma` is additive in its `j`-th polynomial argument:
`BGamma G γ (f[j ↦ p + q]) =
  BGamma G γ (f[j ↦ p]) + BGamma G γ (f[j ↦ q])`.
-/
theorem BGamma_update_add
    (G : KontsevichGraph n m) (γ : Fin n → Bivector d)
    (f : Fin m → RdPoly d) (j : Ground m)
    (p q : RdPoly d) :
    BGamma G γ (Function.update f j (p + q)) =
      BGamma G γ (Function.update f j p) +
        BGamma G γ (Function.update f j q) := by
  unfold BGamma
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro I _
  rw [groundProduct_update_add, mul_add]

/--
`BGamma` is ℝ-linear in its `j`-th polynomial argument:

`BGamma G γ (f[j ↦ c • p]) =
  c • BGamma G γ (f[j ↦ p])`.
-/
theorem BGamma_update_smul
    (G : KontsevichGraph n m) (γ : Fin n → Bivector d)
    (f : Fin m → RdPoly d) (j : Ground m)
    (c : ℝ) (p : RdPoly d) :
    BGamma G γ (Function.update f j (c • p)) =
      c • BGamma G γ (Function.update f j p) := by
  unfold BGamma
  calc
    ∑ I, (∏ k : Aerial n, vertexFactor G γ I k) *
        (∏ b : Ground m,
          groundFactor G (Function.update f j (c • p)) I b) =
        ∑ I, c • ((∏ k : Aerial n, vertexFactor G γ I k) *
          (∏ b : Ground m,
            groundFactor G (Function.update f j p) I b)) := by
      apply Finset.sum_congr rfl
      intro I _
      rw [groundProduct_update_smul]
      rw [mul_smul_comm]
    _ = c • ∑ I, (∏ k : Aerial n, vertexFactor G γ I k) *
          (∏ b : Ground m,
            groundFactor G (Function.update f j p) I b) := by
      rw [Finset.smul_sum]
    _ = c • BGamma G γ (Function.update f j p) := by
      rfl


/--
For fixed `G` and `γ`, the graph operator is ℝ-multilinear in its `m`
polynomial arguments.
-/
noncomputable def BGammaMultilinear
    (G : KontsevichGraph n m) (γ : Fin n → Bivector d) :
    MultilinearMap ℝ (fun _ : Fin m => RdPoly d) (RdPoly d) where
  toFun := fun f => BGamma G γ f

  map_update_add' := by
    intro decEq f j p q
    have hupdate (r : RdPoly d) :
        @Function.update (Fin m) (fun _ : Fin m => RdPoly d)
            decEq f j r =
          @Function.update (Fin m) (fun _ : Fin m => RdPoly d)
            (instDecidableEqFin m) f j r := by
      funext b
      by_cases h : b = j
      · subst b
        simp
      · simp [h]
    rw [hupdate (p + q), hupdate p, hupdate q]
    exact BGamma_update_add G γ f j p q

  map_update_smul' := by
    intro decEq f j c p
    have hupdate (r : RdPoly d) :
        @Function.update (Fin m) (fun _ : Fin m => RdPoly d)
            decEq f j r =
          @Function.update (Fin m) (fun _ : Fin m => RdPoly d)
            (instDecidableEqFin m) f j r := by
      funext b
      by_cases h : b = j
      · subst b
        simp
      · simp [h]
    rw [hupdate (c • p), hupdate p]
    exact BGamma_update_smul G γ f j c p

/--
For fixed `G` and `γ`, `BGammaD G γ` is the corresponding `m`-ary
polynomial polydifferential operator.
-/
noncomputable def BGammaD
    (G : KontsevichGraph n m) (γ : Fin n → Bivector d) :
    DPoly d m where
  toMultilinearMap := BGammaMultilinear G γ
  normalForm := by
    refine ⟨BGammaTerms G γ, ?_⟩
    intro f
    change BGamma G γ f =
      ((BGammaTerms G γ).map
        (fun term => evalDPolyTerm term f)).sum
    exact BGamma_eq_sum_BGammaTerms G γ f

/--
For every admissible graph `G`, every collection of bivectors `γ`, and every
tuple of polynomial arguments `f`, the multilinear map underlying `BGammaD G γ`
evaluates to the original graph operator:
\[
  \bigl(B_\Gamma(\gamma_\bullet)\bigr)(f_\bullet)
  =
  B_\Gamma(\gamma_\bullet)(f_\bullet).
\]
In other words, `BGammaD G γ` is the bundled polydifferential operator whose
underlying function is `BGamma G γ`.
-/
@[simp]
theorem BGammaD_apply
    (G : KontsevichGraph n m) (γ : Fin n → Bivector d)
    (f : Fin m → RdPoly d) :
    (BGammaD G γ).toMultilinearMap f = BGamma G γ f := rfl

/--
Let `G` be an admissible graph with no aerial vertices (`n = 0`). Then for
every `m`-tuple of polynomials \(f=(f_0,\ldots,f_{m-1})\),
\[
  B_G(f_0,\ldots,f_{m-1})
  =
  \prod_{j=0}^{m-1} f_j.
\]
Thus the empty graph represents ordinary multiplication of the input
polynomials.
-/
@[simp]
theorem BGammaD_empty_apply
    (G : KontsevichGraph 0 m) (γ : Fin 0 → Bivector d)
    (f : Fin m → RdPoly d) :
    (BGammaD G γ).toMultilinearMap f = ∏ j : Ground m, f j := by
  rw [BGammaD_apply, BGamma_empty]

/--
For fixed `G` and `γ`, the graph operator has the finite normal form
\[
  B_\Gamma(\gamma_\bullet)(f_\bullet)
  =
  \sum_{I \in \mathrm{Labelling}(n,d)}
    c_I \prod_{j=0}^{m-1}
      \partial^{\alpha_{\Gamma,I}(\bar j)}f_j,
\]
where `graphTerm G γ I` stores the coefficient \(c_I\) and the `m` incoming
multi-indices associated to the labelling \(I\).
-/
theorem BGammaD_normal_form
    (G : KontsevichGraph n m) (γ : Fin n → Bivector d)
    (f : Fin m → RdPoly d) :
    (BGammaD G γ).toMultilinearMap f =
      ((BGammaTerms G γ).map
        (fun term => evalDPolyTerm term f)).sum := by
  rw [BGammaD_apply]
  exact BGamma_eq_sum_BGammaTerms G γ f


/--
Fix a graph `G`, an edge-labelling `I`, and an aerial vertex `k`. Then the
factor contributed by vertex `k` is additive in the bivector placed at `k`:
\[
  V_k(\ldots,\pi+\eta,\ldots)
  =
  V_k(\ldots,\pi,\ldots)+V_k(\ldots,\eta,\ldots).
\]
-/
theorem vertexFactor_update_add
    (G : KontsevichGraph n m) (γ : Fin n → Bivector d)
    (I : Labelling n d) (k : Aerial n)
    (π η : Bivector d) :
    vertexFactor G (Function.update γ k (π + η)) I k =
      vertexFactor G (Function.update γ k π) I k +
        vertexFactor G (Function.update γ k η) I k := by
  rw [vertexFactor_eq_vertexFactorLinear,
    vertexFactor_eq_vertexFactorLinear,
    vertexFactor_eq_vertexFactorLinear]
  simp



/--
Fix a graph `G`, an edge-labelling `I`, and an aerial vertex `k`. Then the
factor contributed by vertex `k` is ℝ-linear in the bivector placed at `k`:
\[
  V_k(\ldots,c\pi,\ldots)
  =
  c\,V_k(\ldots,\pi,\ldots).
\]
-/
theorem vertexFactor_update_smul
    (G : KontsevichGraph n m) (γ : Fin n → Bivector d)
    (I : Labelling n d) (k : Aerial n)
    (c : ℝ) (π : Bivector d) :
    vertexFactor G (Function.update γ k (c • π)) I k =
      c • vertexFactor G (Function.update γ k π) I k := by
  rw [vertexFactor_eq_vertexFactorLinear,
    vertexFactor_eq_vertexFactorLinear]
  simp

/--
If `k' ≠ k`, replacing the bivector at aerial vertex `k` does not affect the
factor belonging to aerial vertex `k'`:
\[
  V_{k'}(\ldots,\pi\text{ at }k,\ldots)=V_{k'}(\gamma_\bullet).
\]
-/
theorem vertexFactor_update_ne
    (G : KontsevichGraph n m) (γ : Fin n → Bivector d)
    (I : Labelling n d) (k k' : Aerial n)
    (π : Bivector d) (h : k' ≠ k) :
    vertexFactor G (Function.update γ k π) I k' =
      vertexFactor G γ I k' := by
  simp [vertexFactor_eq_vertexFactorLinear, h]


/--
For a fixed edge-labelling `I`, the product of all aerial-vertex factors is
additive in the bivector at any chosen aerial vertex `k`:
\[
 \prod_a V_a(\gamma[k\mapsto \pi+\eta])
 =
 \prod_a V_a(\gamma[k\mapsto \pi])
 +
 \prod_a V_a(\gamma[k\mapsto \eta]).
\]
-/
theorem vertexProduct_update_add
    (G : KontsevichGraph n m) (γ : Fin n → Bivector d)
    (I : Labelling n d) (k : Aerial n)
    (π η : Bivector d) :
    (∏ a : Aerial n,
      vertexFactor G (Function.update γ k (π + η)) I a) =
      (∏ a : Aerial n,
        vertexFactor G (Function.update γ k π) I a) +
        ∏ a : Aerial n,
          vertexFactor G (Function.update γ k η) I a := by
  have hErase (r : Bivector d) :
      (∏ a ∈ (Finset.univ : Finset (Aerial n)).erase k,
        vertexFactor G (Function.update γ k r) I a) =
        ∏ a ∈ (Finset.univ : Finset (Aerial n)).erase k,
          vertexFactor G γ I a := by
    apply Finset.prod_congr rfl
    intro a ha
    exact vertexFactor_update_ne G γ I k a r
      (Finset.ne_of_mem_erase ha)
  calc
    (∏ a : Aerial n,
      vertexFactor G (Function.update γ k (π + η)) I a) =
        vertexFactor G (Function.update γ k (π + η)) I k *
          ∏ a ∈ (Finset.univ : Finset (Aerial n)).erase k,
            vertexFactor G (Function.update γ k (π + η)) I a := by
          symm
          exact Finset.mul_prod_erase Finset.univ
            (fun a => vertexFactor G (Function.update γ k (π + η)) I a)
            (Finset.mem_univ k)
    _ = (vertexFactor G (Function.update γ k π) I k +
          vertexFactor G (Function.update γ k η) I k) *
          ∏ a ∈ (Finset.univ : Finset (Aerial n)).erase k,
            vertexFactor G γ I a := by
          rw [vertexFactor_update_add, hErase]
    _ = vertexFactor G (Function.update γ k π) I k *
          (∏ a ∈ (Finset.univ : Finset (Aerial n)).erase k,
            vertexFactor G γ I a) +
        vertexFactor G (Function.update γ k η) I k *
          (∏ a ∈ (Finset.univ : Finset (Aerial n)).erase k,
            vertexFactor G γ I a) := by
          rw [add_mul]
    _ = (∏ a : Aerial n,
          vertexFactor G (Function.update γ k π) I a) +
        ∏ a : Aerial n,
          vertexFactor G (Function.update γ k η) I a := by
          have hπ :
              vertexFactor G (Function.update γ k π) I k *
                  (∏ a ∈ (Finset.univ : Finset (Aerial n)).erase k,
                    vertexFactor G γ I a) =
                ∏ a : Aerial n,
                  vertexFactor G (Function.update γ k π) I a := by
            rw [← hErase π]
            exact Finset.mul_prod_erase Finset.univ
              (fun a => vertexFactor G (Function.update γ k π) I a)
              (Finset.mem_univ k)
          have hη :
              vertexFactor G (Function.update γ k η) I k *
                  (∏ a ∈ (Finset.univ : Finset (Aerial n)).erase k,
                    vertexFactor G γ I a) =
                ∏ a : Aerial n,
                  vertexFactor G (Function.update γ k η) I a := by
            rw [← hErase η]
            exact Finset.mul_prod_erase Finset.univ
              (fun a => vertexFactor G (Function.update γ k η) I a)
              (Finset.mem_univ k)
          rw [hπ, hη]

/--
For a fixed edge-labelling `I`, the product of all aerial-vertex factors is
ℝ-linear in the bivector at a chosen aerial vertex `k`:
\[
 \prod_a V_a(\gamma[k\mapsto c\pi])
 =
 c\prod_a V_a(\gamma[k\mapsto \pi]).
\]
-/
theorem vertexProduct_update_smul
    (G : KontsevichGraph n m) (γ : Fin n → Bivector d)
    (I : Labelling n d) (k : Aerial n)
    (c : ℝ) (π : Bivector d) :
    (∏ a : Aerial n,
      vertexFactor G (Function.update γ k (c • π)) I a) =
      c • (∏ a : Aerial n,
        vertexFactor G (Function.update γ k π) I a) := by
  have hErase (r : Bivector d) :
      (∏ a ∈ (Finset.univ : Finset (Aerial n)).erase k,
        vertexFactor G (Function.update γ k r) I a) =
        ∏ a ∈ (Finset.univ : Finset (Aerial n)).erase k,
          vertexFactor G γ I a := by
    apply Finset.prod_congr rfl
    intro a ha
    exact vertexFactor_update_ne G γ I k a r
      (Finset.ne_of_mem_erase ha)
  calc
    (∏ a : Aerial n,
      vertexFactor G (Function.update γ k (c • π)) I a) =
        vertexFactor G (Function.update γ k (c • π)) I k *
          ∏ a ∈ (Finset.univ : Finset (Aerial n)).erase k,
            vertexFactor G (Function.update γ k (c • π)) I a := by
          symm
          exact Finset.mul_prod_erase Finset.univ
            (fun a => vertexFactor G (Function.update γ k (c • π)) I a)
            (Finset.mem_univ k)
    _ = (c • vertexFactor G (Function.update γ k π) I k) *
          ∏ a ∈ (Finset.univ : Finset (Aerial n)).erase k,
            vertexFactor G γ I a := by
          rw [vertexFactor_update_smul, hErase]
    _ = c • (vertexFactor G (Function.update γ k π) I k *
          ∏ a ∈ (Finset.univ : Finset (Aerial n)).erase k,
            vertexFactor G γ I a) := by
          rw [smul_mul_assoc]
    _ = c • (∏ a : Aerial n,
          vertexFactor G (Function.update γ k π) I a) := by
          congr 1
          rw [← hErase π]
          exact Finset.mul_prod_erase Finset.univ
            (fun a => vertexFactor G (Function.update γ k π) I a)
            (Finset.mem_univ k)


/--
The Kontsevich graph operator is additive in its `k`-th bivector input:
\[
  B_\Gamma(\gamma[k\mapsto \pi+\eta])(f_\bullet)
  =
  B_\Gamma(\gamma[k\mapsto \pi])(f_\bullet)
  +
  B_\Gamma(\gamma[k\mapsto \eta])(f_\bullet).
\]
-/
theorem BGamma_update_bivector_add
    (G : KontsevichGraph n m) (γ : Fin n → Bivector d)
    (f : Fin m → RdPoly d) (k : Aerial n)
    (π η : Bivector d) :
    BGamma G (Function.update γ k (π + η)) f =
      BGamma G (Function.update γ k π) f +
        BGamma G (Function.update γ k η) f := by
  unfold BGamma
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro I _
  rw [vertexProduct_update_add, add_mul]

/--
The Kontsevich graph operator is ℝ-linear in its `k`-th bivector input:
\[
  B_\Gamma(\gamma[k\mapsto c\pi])(f_\bullet)
  =
  c\,B_\Gamma(\gamma[k\mapsto \pi])(f_\bullet).
\]
-/
theorem BGamma_update_bivector_smul
    (G : KontsevichGraph n m) (γ : Fin n → Bivector d)
    (f : Fin m → RdPoly d) (k : Aerial n)
    (c : ℝ) (π : Bivector d) :
    BGamma G (Function.update γ k (c • π)) f =
      c • BGamma G (Function.update γ k π) f := by
  unfold BGamma
  calc
    ∑ I, (∏ a : Aerial n,
      vertexFactor G (Function.update γ k (c • π)) I a) *
        ∏ j : Ground m, groundFactor G f I j =
      ∑ I, c • ((∏ a : Aerial n,
        vertexFactor G (Function.update γ k π) I a) *
          ∏ j : Ground m, groundFactor G f I j) := by
        apply Finset.sum_congr rfl
        intro I _
        rw [vertexProduct_update_smul, smul_mul_assoc]
    _ = c • ∑ I, (∏ a : Aerial n,
        vertexFactor G (Function.update γ k π) I a) *
          ∏ j : Ground m, groundFactor G f I j := by
        rw [Finset.smul_sum]
    _ = c • BGamma G (Function.update γ k π) f := by
        rfl

/--
For fixed `G` and fixed polynomial arguments `f`, the map
\[
  (\gamma_0,\ldots,\gamma_{n-1})
  \longmapsto B_\Gamma(\gamma_0,\ldots,\gamma_{n-1})(f)
\]
is ℝ-multilinear in the `n` bivector inputs.
-/
noncomputable def BGammaBivectorMultilinear
    (G : KontsevichGraph n m) (f : Fin m → RdPoly d) :
    MultilinearMap ℝ (fun _ : Fin n => Bivector d) (RdPoly d) where
  toFun := fun γ => BGamma G γ f

  map_update_add' := by
    intro decEq γ k π η
    have hupdate (r : Bivector d) :
        @Function.update (Fin n) (fun _ : Fin n => Bivector d)
            decEq γ k r =
          @Function.update (Fin n) (fun _ : Fin n => Bivector d)
            (instDecidableEqFin n) γ k r := by
      funext a
      by_cases h : a = k
      · subst a
        simp
      · simp [h]
    rw [hupdate (π + η), hupdate π, hupdate η]
    exact BGamma_update_bivector_add G γ f k π η

  map_update_smul' := by
    intro decEq γ k c π
    have hupdate (r : Bivector d) :
        @Function.update (Fin n) (fun _ : Fin n => Bivector d)
            decEq γ k r =
          @Function.update (Fin n) (fun _ : Fin n => Bivector d)
            (instDecidableEqFin n) γ k r := by
      funext a
      by_cases h : a = k
      · subst a
        simp
      · simp [h]
    rw [hupdate (c • π), hupdate π]
    exact BGamma_update_bivector_smul G γ f k c π

/--
Evaluating the bundled multilinear map in the bivector inputs recovers the
original graph operator:
\[
  \operatorname{BGammaBivectorMultilinear}_{G,f}(\gamma_\bullet)
  =
  B_\Gamma(\gamma_\bullet)(f_\bullet).
\]
-/
@[simp]
theorem BGammaBivectorMultilinear_apply
    (G : KontsevichGraph n m) (f : Fin m → RdPoly d)
    (γ : Fin n → Bivector d) :
    BGammaBivectorMultilinear G f γ = BGamma G γ f := rfl

/-
Suppose `k` has a double edge. For every other aerial vertex `a ≠ k`, swapping
the labels of the two edges leaving `k` does not change the factor at `a`:
\[
  a\neq k
  \quad\Longrightarrow\quad
  V_a(\operatorname{swap}_k(I))=V_a(I).
\]
-/
theorem vertexFactor_swapLabelsAt_of_ne
    (G : KontsevichGraph n m) (γ : Fin n → Bivector d)
    (I : Labelling n d) (k a : Aerial n)
    (hdouble : G.target (k, 0) = G.target (k, 1))
    (ha : a ≠ k) :
    vertexFactor G γ (swapLabelsAt I k) a =
      vertexFactor G γ I a := by
  unfold vertexFactor
  rw [inMulti_swapLabelsAt_of_double G I k hdouble (Sum.inl a)]
  rw [swapLabelsAt_of_source_ne I k (a, 0) ha,
    swapLabelsAt_of_source_ne I k (a, 1) ha]

/-
Suppose `k` has a double edge. Then swapping the labels on the two edges
leaving `k` leaves every ground-vertex factor unchanged:
\[
  W_j(\operatorname{swap}_k(I))=W_j(I).
\]
-/
theorem groundFactor_swapLabelsAt_of_double
    (G : KontsevichGraph n m) (f : Fin m → RdPoly d)
    (I : Labelling n d) (k : Aerial n)
    (hdouble : G.target (k, 0) = G.target (k, 1))
    (j : Ground m) :
    groundFactor G f (swapLabelsAt I k) j =
      groundFactor G f I j := by
  unfold groundFactor
  rw [inMulti_swapLabelsAt_of_double G I k hdouble (Sum.inr j)]

/-
Suppose `k` has a double edge. Swapping the labels on its two outgoing edges
negates the factor at `k`:
\[
  V_k(\operatorname{swap}_k(I))=-V_k(I).
\]
The sign comes from the antisymmetry
\(\gamma_k^{ji}=-\gamma_k^{ij}\); the incoming derivative multi-index is
unchanged.
-/
theorem vertexFactor_swapLabelsAt_self
    (G : KontsevichGraph n m) (γ : Fin n → Bivector d)
    (I : Labelling n d) (k : Aerial n)
    (hdouble : G.target (k, 0) = G.target (k, 1)) :
    vertexFactor G γ (swapLabelsAt I k) k =
      -vertexFactor G γ I k := by
  unfold vertexFactor
  rw [inMulti_swapLabelsAt_of_double G I k hdouble (Sum.inl k)]
  rw [swapLabelsAt_left, swapLabelsAt_right]
  rw [Bivector.coeff_antisymm]
  simp


/-
If `k` has a double edge, then swapping its two labels negates the product of
all aerial-vertex factors:
\[
  \prod_a V_a(\operatorname{swap}_k(I))
  =
  -\prod_a V_a(I).
\]
-/
theorem vertexProduct_swapLabelsAt_of_double
    (G : KontsevichGraph n m) (γ : Fin n → Bivector d)
    (I : Labelling n d) (k : Aerial n)
    (hdouble : G.target (k, 0) = G.target (k, 1)) :
    (∏ a : Aerial n, vertexFactor G γ (swapLabelsAt I k) a) =
      -(∏ a : Aerial n, vertexFactor G γ I a) := by
  have hErase :
      (∏ a ∈ (Finset.univ : Finset (Aerial n)).erase k,
        vertexFactor G γ (swapLabelsAt I k) a) =
        ∏ a ∈ (Finset.univ : Finset (Aerial n)).erase k,
          vertexFactor G γ I a := by
    apply Finset.prod_congr rfl
    intro a ha
    exact vertexFactor_swapLabelsAt_of_ne G γ I k a hdouble
      (Finset.ne_of_mem_erase ha)
  calc
    (∏ a : Aerial n, vertexFactor G γ (swapLabelsAt I k) a) =
        vertexFactor G γ (swapLabelsAt I k) k *
          ∏ a ∈ (Finset.univ : Finset (Aerial n)).erase k,
            vertexFactor G γ (swapLabelsAt I k) a := by
          symm
          exact Finset.mul_prod_erase Finset.univ
            (fun a => vertexFactor G γ (swapLabelsAt I k) a)
            (Finset.mem_univ k)
    _ = (-vertexFactor G γ I k) *
          ∏ a ∈ (Finset.univ : Finset (Aerial n)).erase k,
            vertexFactor G γ I a := by
          rw [vertexFactor_swapLabelsAt_self G γ I k hdouble, hErase]
    _ = -(vertexFactor G γ I k *
          ∏ a ∈ (Finset.univ : Finset (Aerial n)).erase k,
            vertexFactor G γ I a) := by
          rw [neg_mul]
    _ = -(∏ a : Aerial n, vertexFactor G γ I a) := by
          rw [← Finset.mul_prod_erase Finset.univ
            (fun a => vertexFactor G γ I a) (Finset.mem_univ k)]

/-
If `k` has a double edge, then swapping its two labels leaves the product of
all ground-vertex factors unchanged:
\[
  \prod_j W_j(\operatorname{swap}_k(I))
  =
  \prod_j W_j(I).
\]
-/
theorem groundProduct_swapLabelsAt_of_double
    (G : KontsevichGraph n m) (f : Fin m → RdPoly d)
    (I : Labelling n d) (k : Aerial n)
    (hdouble : G.target (k, 0) = G.target (k, 1)) :
    (∏ j : Ground m, groundFactor G f (swapLabelsAt I k) j) =
      ∏ j : Ground m, groundFactor G f I j := by
  apply Finset.prod_congr rfl
  intro j _
  exact groundFactor_swapLabelsAt_of_double G f I k hdouble j

/-
If `k` has a double edge, the complete summand associated to the swapped
labelling is the negative of the original summand:
\[
 \left(\prod_a V_a(\operatorname{swap}_k(I))\right)
 \left(\prod_j W_j(\operatorname{swap}_k(I))\right)
 =
 -
 \left[
   \left(\prod_a V_a(I)\right)
   \left(\prod_j W_j(I)\right)
 \right].
\]
-/
theorem BGamma_summand_swapLabelsAt_of_double
    (G : KontsevichGraph n m) (γ : Fin n → Bivector d)
    (f : Fin m → RdPoly d) (I : Labelling n d)
    (k : Aerial n)
    (hdouble : G.target (k, 0) = G.target (k, 1)) :
    (∏ a : Aerial n, vertexFactor G γ (swapLabelsAt I k) a) *
        (∏ j : Ground m, groundFactor G f (swapLabelsAt I k) j) =
      -((∏ a : Aerial n, vertexFactor G γ I a) *
        ∏ j : Ground m, groundFactor G f I j) := by
  rw [vertexProduct_swapLabelsAt_of_double G γ I k hdouble,
    groundProduct_swapLabelsAt_of_double G f I k hdouble]
  rw [neg_mul]

/-
A loop-free Kontsevich graph with a double edge has zero graph operator:
\[
  \operatorname{hasDoubleEdge}(\Gamma)
  \quad\Longrightarrow\quad
  B_\Gamma(\gamma_\bullet)(f_\bullet)=0.
\]

Indeed, swapping the two labels on the double edge is a bijection on
labellings, and it negates every summand.
-/
theorem BGamma_eq_zero_of_hasDoubleEdge
    (G : KontsevichGraph n m) (γ : Fin n → Bivector d)
    (f : Fin m → RdPoly d)
    (h : hasDoubleEdge G) :
    BGamma G γ f = 0 := by
  rcases h with ⟨k, hdouble⟩
  unfold BGamma
  let F : Labelling n d → RdPoly d :=
    fun I =>
      (∏ a : Aerial n, vertexFactor G γ I a) *
        ∏ j : Ground m, groundFactor G f I j
  change (∑ I : Labelling n d, F I) = 0
  have hneg :
      (∑ I : Labelling n d, F (swapLabelsAt I k)) =
        -(∑ I : Labelling n d, F I) := by
    calc
      (∑ I : Labelling n d, F (swapLabelsAt I k)) =
          ∑ I : Labelling n d, -F I := by
        apply Finset.sum_congr rfl
        intro I _
        simpa [F] using
          BGamma_summand_swapLabelsAt_of_double G γ f I k hdouble
      _ = -(∑ I : Labelling n d, F I) := by
        rw [Finset.sum_neg_distrib]
  have hsum :
      (∑ I : Labelling n d, F I) =
        -(∑ I : Labelling n d, F I) := by
    calc
      (∑ I : Labelling n d, F I) =
          ∑ I : Labelling n d, F (swapLabelsAt I k) := by
        exact (sum_swapLabelsAt F k).symm
      _ = -(∑ I : Labelling n d, F I) := hneg
  have htwo : (2 : ℝ) • (∑ I : Labelling n d, F I) = 0 := by
    calc
      (2 : ℝ) • (∑ I : Labelling n d, F I) =
          (∑ I : Labelling n d, F I) +
            (∑ I : Labelling n d, F I) := by
          rw [two_smul]
      _ = -(∑ I : Labelling n d, F I) +
            (∑ I : Labelling n d, F I) := by
          exact congrArg
            (fun x : RdPoly d =>
              x + ∑ I : Labelling n d, F I) hsum
      _ = 0 := by
          simp
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

/-
For an aerial vertex \(a\neq k\), swapping the ordered outgoing edges in the
graph has the same effect as swapping the labels at `k` in the original graph:
\[
  V_a^{\operatorname{swap}_k(G)}(I)
  =
  V_a^G(\operatorname{swap}_k(I)).
\]
-/
theorem vertexFactor_swapOutgoingEdges_of_ne
    (G : KontsevichGraph n m) (γ : Fin n → Bivector d)
    (I : Labelling n d) (k a : Aerial n)
    (ha : a ≠ k) :
    vertexFactor (swapOutgoingEdges G k) γ I a =
      vertexFactor G γ (swapLabelsAt I k) a := by
  unfold vertexFactor
  rw [inMulti_swapOutgoingEdges G I k (Sum.inl a)]
  rw [swapLabelsAt_of_source_ne I k (a, 0) ha,
    swapLabelsAt_of_source_ne I k (a, 1) ha]

/-
At the swapped aerial vertex `k`, graph-swapping gives the negative of
label-swapping:
\[
  V_k^{\operatorname{swap}_k(G)}(I)
  =
  -V_k^G(\operatorname{swap}_k(I)).
\]
-/
theorem vertexFactor_swapOutgoingEdges_self
    (G : KontsevichGraph n m) (γ : Fin n → Bivector d)
    (I : Labelling n d) (k : Aerial n) :
    vertexFactor (swapOutgoingEdges G k) γ I k =
      -vertexFactor G γ (swapLabelsAt I k) k := by
  unfold vertexFactor
  rw [inMulti_swapOutgoingEdges G I k (Sum.inl k)]
  rw [swapLabelsAt_left, swapLabelsAt_right]
  have hanti :
      Bivector.coeff (γ k) (I (k, 1)) (I (k, 0)) =
        -Bivector.coeff (γ k) (I (k, 0)) (I (k, 1)) :=
    Bivector.coeff_antisymm (γ k) (I (k, 1)) (I (k, 0))
  rw [hanti]
  simp

/-
For every ground vertex `j`, graph-swapping agrees with label-swapping:
\[
  W_j^{\operatorname{swap}_k(G)}(I)
  =
  W_j^G(\operatorname{swap}_k(I)).
\]
-/
theorem groundFactor_swapOutgoingEdges
    (G : KontsevichGraph n m) (f : Fin m → RdPoly d)
    (I : Labelling n d) (k : Aerial n) (j : Ground m) :
    groundFactor (swapOutgoingEdges G k) f I j =
      groundFactor G f (swapLabelsAt I k) j := by
  unfold groundFactor
  rw [inMulti_swapOutgoingEdges G I k (Sum.inr j)]


/-
Exchanging the two ordered outgoing edges at `k` negates the total aerial
factor product:
\[
 \prod_a V_a^{\operatorname{swap}_k(G)}(I)
 =
 -\prod_a V_a^G(\operatorname{swap}_k(I)).
\]
-/
theorem vertexProduct_swapOutgoingEdges
    (G : KontsevichGraph n m) (γ : Fin n → Bivector d)
    (I : Labelling n d) (k : Aerial n) :
    (∏ a : Aerial n,
      vertexFactor (swapOutgoingEdges G k) γ I a) =
      -(∏ a : Aerial n,
        vertexFactor G γ (swapLabelsAt I k) a) := by
  have hErase :
      (∏ a ∈ (Finset.univ : Finset (Aerial n)).erase k,
        vertexFactor (swapOutgoingEdges G k) γ I a) =
        ∏ a ∈ (Finset.univ : Finset (Aerial n)).erase k,
          vertexFactor G γ (swapLabelsAt I k) a := by
    apply Finset.prod_congr rfl
    intro a ha
    exact vertexFactor_swapOutgoingEdges_of_ne G γ I k a
      (Finset.ne_of_mem_erase ha)
  calc
    (∏ a : Aerial n,
      vertexFactor (swapOutgoingEdges G k) γ I a) =
        vertexFactor (swapOutgoingEdges G k) γ I k *
          ∏ a ∈ (Finset.univ : Finset (Aerial n)).erase k,
            vertexFactor (swapOutgoingEdges G k) γ I a := by
          symm
          exact Finset.mul_prod_erase Finset.univ
            (fun a => vertexFactor (swapOutgoingEdges G k) γ I a)
            (Finset.mem_univ k)
    _ = (-vertexFactor G γ (swapLabelsAt I k) k) *
          ∏ a ∈ (Finset.univ : Finset (Aerial n)).erase k,
            vertexFactor G γ (swapLabelsAt I k) a := by
          rw [vertexFactor_swapOutgoingEdges_self G γ I k, hErase]
    _ = -(vertexFactor G γ (swapLabelsAt I k) k *
          ∏ a ∈ (Finset.univ : Finset (Aerial n)).erase k,
            vertexFactor G γ (swapLabelsAt I k) a) := by
          rw [neg_mul]
    _ = -(∏ a : Aerial n,
          vertexFactor G γ (swapLabelsAt I k) a) := by
          rw [← Finset.mul_prod_erase Finset.univ
            (fun a => vertexFactor G γ (swapLabelsAt I k) a)
            (Finset.mem_univ k)]

/-
The product of ground factors satisfies
\[
 \prod_j W_j^{\operatorname{swap}_k(G)}(I)
 =
 \prod_j W_j^G(\operatorname{swap}_k(I)).
\]
-/
theorem groundProduct_swapOutgoingEdges
    (G : KontsevichGraph n m) (f : Fin m → RdPoly d)
    (I : Labelling n d) (k : Aerial n) :
    (∏ j : Ground m,
      groundFactor (swapOutgoingEdges G k) f I j) =
      ∏ j : Ground m,
        groundFactor G f (swapLabelsAt I k) j := by
  apply Finset.prod_congr rfl
  intro j _
  exact groundFactor_swapOutgoingEdges G f I k j

/-
For every labelling `I`, the summand in the swapped graph is the negative of
the summand for the swapped labelling in the original graph:
\[
  S_{\operatorname{swap}_k(G)}(I)
  =
  -S_G(\operatorname{swap}_k(I)).
\]
-/
theorem BGamma_summand_swapOutgoingEdges
    (G : KontsevichGraph n m) (γ : Fin n → Bivector d)
    (f : Fin m → RdPoly d) (I : Labelling n d)
    (k : Aerial n) :
    (∏ a : Aerial n,
      vertexFactor (swapOutgoingEdges G k) γ I a) *
        (∏ j : Ground m,
          groundFactor (swapOutgoingEdges G k) f I j) =
      -((∏ a : Aerial n,
        vertexFactor G γ (swapLabelsAt I k) a) *
          ∏ j : Ground m,
            groundFactor G f (swapLabelsAt I k) j) := by
  rw [vertexProduct_swapOutgoingEdges G γ I k,
    groundProduct_swapOutgoingEdges G f I k]
  rw [neg_mul]


/-
Let \(\operatorname{swap}_k(G)\) be obtained from `G` by exchanging the ordered
outgoing edges at aerial vertex `k`. Then
\[
  B_{\operatorname{swap}_k(G)}(\gamma_\bullet)(f_\bullet)
  =
  -B_G(\gamma_\bullet)(f_\bullet).
\]

The sign is caused by reversing the two upper indices of the bivector at `k`.
-/
theorem BGamma_swapOutgoingEdges
    (G : KontsevichGraph n m) (γ : Fin n → Bivector d)
    (f : Fin m → RdPoly d) (k : Aerial n) :
    BGamma (swapOutgoingEdges G k) γ f =
      -BGamma G γ f := by
  unfold BGamma
  let F : Labelling n d → RdPoly d :=
    fun I =>
      (∏ a : Aerial n, vertexFactor G γ I a) *
        ∏ j : Ground m, groundFactor G f I j
  calc
    (∑ I : Labelling n d,
      (∏ a : Aerial n,
        vertexFactor (swapOutgoingEdges G k) γ I a) *
          ∏ j : Ground m,
            groundFactor (swapOutgoingEdges G k) f I j) =
        ∑ I : Labelling n d, -F (swapLabelsAt I k) := by
          apply Finset.sum_congr rfl
          intro I _
          simpa [F] using
            BGamma_summand_swapOutgoingEdges G γ f I k
    _ = -(∑ I : Labelling n d, F (swapLabelsAt I k)) := by
          rw [Finset.sum_neg_distrib]
    _ = -(∑ I : Labelling n d, F I) := by
          rw [sum_swapLabelsAt F k]

/-
If `G` is admissible, then exchanging the two ordered outgoing edges at `k`
produces another admissible graph and negates its graph operator:
\[
  B_{\operatorname{swap}_k(G)}=-B_G.
\]
-/
theorem BGamma_swapOutgoingEdgesAdmissible
    (G : AdmissibleGraph n m) (γ : Fin n → Bivector d)
    (f : Fin m → RdPoly d) (k : Aerial n) :
    BGamma (swapOutgoingEdgesAdmissible G k) γ f =
      -BGamma (G : KontsevichGraph n m) γ f := by
  exact BGamma_swapOutgoingEdges
    (G : KontsevichGraph n m) γ f k
end Kontsevich
