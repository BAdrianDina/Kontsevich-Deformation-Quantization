import Mathlib
import Kontsevich.Basic.MultiIndex
namespace Kontsevich

/-- Aerial vertices, numbered `0, ..., n - 1`. -/
abbrev Aerial (n : ℕ) := Fin n

/-- Ground vertices, numbered `0, ..., m - 1`. -/
abbrev Ground (m : ℕ) := Fin m

/-- A vertex is either aerial (`Sum.inl`) or ground (`Sum.inr`). -/
abbrev Vertex (n m : ℕ) := Aerial n ⊕ Ground m

/-- An edge is specified by its aerial source and one of its two ordered slots. -/
abbrev Edge (n : ℕ) := Aerial n × Fin 2

/--
A loop-free Kontsevich graph in the bivector case. At this level, double edges
are allowed.
-/
structure KontsevichGraph (n m : ℕ) where
  target : Edge n → Vertex n m
  no_loop : ∀ e : Edge n, target e ≠ Sum.inl e.1

/--
Admissible Kontsevich graphs are loop-free graphs with no double edges.
-/
structure AdmissibleGraph (n m : ℕ) extends KontsevichGraph n m where
  no_double : ∀ k : Aerial n, target (k, 0) ≠ target (k, 1)

/-- Forget the no-double-edge condition. -/
instance (n m : ℕ) :
    Coe (AdmissibleGraph n m) (KontsevichGraph n m) where
  coe := AdmissibleGraph.toKontsevichGraph

/-- The edges of `Γ` whose target is `v`. -/
def inEdges (Γ : KontsevichGraph n m) (v : Vertex n m) :
    Finset (Edge n) :=
  Finset.univ.filter (fun e => Γ.target e = v)

--A labelling of the edges by coordinate indices 0, .., d-1
abbrev Labelling (n d : ℕ):= Edge n → Fin d

/--
Swap the two coordinate labels on the two ordered outgoing edges of aerial
vertex `k`, leaving every other edge-label unchanged.
-/
def swapLabelsAt (I : Labelling n d) (k : Aerial n) : Labelling n d :=
  fun e =>
    if e = (k, 0) then I (k, 1)
    else if e = (k, 1) then I (k, 0)
    else I e

@[simp]
theorem swapLabelsAt_left
    (I : Labelling n d) (k : Aerial n) :
    swapLabelsAt I k (k, 0) = I (k, 1) := by
  simp [swapLabelsAt]

@[simp]
theorem swapLabelsAt_right
    (I : Labelling n d) (k : Aerial n) :
    swapLabelsAt I k (k, 1) = I (k, 0) := by
  simp [swapLabelsAt]

@[simp]
theorem swapLabelsAt_of_ne
    (I : Labelling n d) (k : Aerial n) (e : Edge n)
    (h₀ : e ≠ (k, 0)) (h₁ : e ≠ (k, 1)) :
    swapLabelsAt I k e = I e := by
  simp [swapLabelsAt, h₀, h₁]


/-
If an edge `e` does not leave aerial vertex `k`, swapping the labels on the two
outgoing edges of `k` leaves the label of `e` unchanged:
\[
  s(e)\neq k
  \quad\Longrightarrow\quad
  \operatorname{swap}_k(I)(e)=I(e).
\]
-/
theorem swapLabelsAt_of_source_ne
    (I : Labelling n d) (k : Aerial n) (e : Edge n)
    (h : e.1 ≠ k) :
    swapLabelsAt I k e = I e := by
  apply swapLabelsAt_of_ne
  · intro h₀
    exact h (congrArg Prod.fst h₀)
  · intro h₁
    exact h (congrArg Prod.fst h₁)


/--
Swapping the labels on the two outgoing edges of `k` twice is the identity:
\[
  \operatorname{swap}_k(\operatorname{swap}_k(I))=I.
\]
Hence \(\operatorname{swap}_k\) is a bijection on the finite set of labellings.
-/
theorem swapLabelsAt_involutive
    (I : Labelling n d) (k : Aerial n) :
    swapLabelsAt (swapLabelsAt I k) k = I := by
  funext e
  by_cases h₀ : e = (k, 0)
  · subst e
    simp [swapLabelsAt]
  by_cases h₁ : e = (k, 1)
  · subst e
    simp [swapLabelsAt]
  · simp [swapLabelsAt, h₀, h₁]

/-- The multi-index formed from the labels of edges entering `v`. -/
noncomputable def inMulti
    (Γ : KontsevichGraph n m) (I : Labelling n d)
    (v : Vertex n m) : MultiIndex d :=
  (inEdges Γ v).sum (fun e => Finsupp.single (I e) 1)

@[simp]
theorem mem_inEdges
    (Γ : KontsevichGraph n m) (v : Vertex n m) (e : Edge n) :
    e ∈ inEdges Γ v ↔ Γ.target e = v := by
  simp [inEdges]

theorem inMulti_eq_zero_of_inEdges_eq_empty
    (Γ : KontsevichGraph n m) (I : Labelling n d)
    (v : Vertex n m) (h : inEdges Γ v = ∅) :
    inMulti Γ I v = 0 := by
  simp [inMulti, h]

theorem not_mem_inEdges_source
    (Γ : KontsevichGraph n m) (_ : Vertex n m) (e : Edge n) :
    e ∉ inEdges Γ (Sum.inl e.1) := by
  simpa using Γ.no_loop e

  /-
`G` has a double edge when the two ordered outgoing edges of some aerial vertex
have the same target.
-/
def hasDoubleEdge (G : KontsevichGraph n m) : Prop :=
  ∃ k : Aerial n, G.target (k, 0) = G.target (k, 1)

/-
An admissible graph has no double edge:
\[
  G\in G_{n,m}\quad\Longrightarrow\quad\neg\operatorname{hasDoubleEdge}(G).
\]
-/
theorem AdmissibleGraph.not_hasDoubleEdge
    (Γ : AdmissibleGraph n m) :
    ¬ hasDoubleEdge (Γ : KontsevichGraph n m) := by
  rintro ⟨k, hk⟩
  exact Γ.no_double k hk
/--
The equivalence of edge-labellings obtained by swapping the labels on the two
outgoing edges of aerial vertex `k`.
-/
def swapLabelsAtEquiv (k : Aerial n) :
    Equiv (Labelling n d) (Labelling n d) where
  toFun I := swapLabelsAt I k
  invFun I := swapLabelsAt I k
  left_inv I := swapLabelsAt_involutive I k
  right_inv I := swapLabelsAt_involutive I k
@[simp]
theorem swapLabelsAtEquiv_apply
    (I : Labelling n d) (k : Aerial n) :
    swapLabelsAtEquiv k I = swapLabelsAt I k := rfl

/-
For every function \(F\) of an edge-labelling, swapping the two labels at
vertex `k` merely reorders the finite sum over all labellings:
\[
  \sum_I F(\operatorname{swap}_k(I))
  =
  \sum_I F(I).
\]
-/
theorem sum_swapLabelsAt
    {A : Type*} [AddCommMonoid A]
    (F : Labelling n d → A) (k : Aerial n) :
    (∑ I : Labelling n d, F (swapLabelsAt I k)) =
      ∑ I : Labelling n d, F I := by
  simpa [swapLabelsAtEquiv_apply] using
    (Equiv.sum_comp (swapLabelsAtEquiv k) F)


/-
Suppose neither outgoing edge of `k` targets `v`. Then swapping their labels
does not change the incoming multi-index at `v`:
\[
  t(e_k^1)\neq v,\quad t(e_k^2)\neq v
  \quad\Longrightarrow\quad
  \alpha_{\Gamma,\operatorname{swap}_k(I)}(v)
  =
  \alpha_{\Gamma,I}(v).
\]
-/
theorem inMulti_swapLabelsAt_of_targets_ne
    (G : KontsevichGraph n m) (I : Labelling n d)
    (k : Aerial n) (v : Vertex n m)
    (h₀ : G.target (k, 0) ≠ v)
    (h₁ : G.target (k, 1) ≠ v) :
    inMulti G (swapLabelsAt I k) v = inMulti G I v := by
  unfold inMulti
  apply Finset.sum_congr rfl
  intro e he
  have htarget : G.target e = v :=
    (mem_inEdges G v e).mp he
  have hk₀ : e ≠ (k, 0) := by
    intro h
    apply h₀
    rw [← h]
    exact htarget
  have hk₁ : e ≠ (k, 1) := by
    intro h
    apply h₁
    rw [← h]
    exact htarget
  rw [swapLabelsAt_of_ne I k e hk₀ hk₁]

/--
Swap the two ordered outgoing edges of aerial vertex `k`, leaving every other
edge unchanged.
-/
def swapEdgesAt (k : Aerial n) : Edge n → Edge n :=
  fun e =>
    if e = (k, 0) then (k, 1)
    else if e = (k, 1) then (k, 0)
    else e

@[simp]
 theorem swapEdgesAt_left
    (k : Aerial n) :
    swapEdgesAt k (k, 0) = (k, 1) := by
  simp [swapEdgesAt]
@[simp]
theorem swapEdgesAt_right
    (k : Aerial n) :
    swapEdgesAt k (k, 1) = (k, 0) := by
  simp [swapEdgesAt]
@[simp]
theorem swapEdgesAt_of_ne
    (k : Aerial n) (e : Edge n)
    (h₀ : e ≠ (k, 0)) (h₁ : e ≠ (k, 1)) :
    swapEdgesAt k e = e := by
  simp [swapEdgesAt, h₀, h₁]

/-
The swapped labelling is obtained by evaluating the original labelling on the
swapped edge:
\[
  \operatorname{swapLabelsAt}(I,k)(e)
  =
  I\bigl(\operatorname{swapEdgesAt}(k,e)\bigr).
\]
-/

theorem swapLabelsAt_apply_eq_apply_swapEdgesAt
    (I : Labelling n d) (k : Aerial n) (e : Edge n) :
    swapLabelsAt I k e = I (swapEdgesAt k e) := by
  by_cases h₀ : e = (k, 0)
  · subst e
    simp [swapLabelsAt, swapEdgesAt]
  by_cases h₁ : e = (k, 1)
  · subst e
    simp [swapLabelsAt, swapEdgesAt]
  · simp [swapLabelsAt, swapEdgesAt, h₀, h₁]

/-
Suppose the two outgoing edges of `k` have the same target:
\[
  t(e_k^1)=t(e_k^2).
\]
Then swapping those edges preserves the target of every edge:
\[
  t(\operatorname{swapEdgesAt}(k,e))=t(e).
\]
-/
theorem target_swapEdgesAt_eq
    (G : KontsevichGraph n m) (k : Aerial n)
    (hdouble : G.target (k, 0) = G.target (k, 1))
    (e : Edge n) :
    G.target (swapEdgesAt k e) = G.target e := by
  by_cases h₀ : e = (k, 0)
  · subst e
    simpa [swapEdgesAt] using hdouble.symm
  by_cases h₁ : e = (k, 1)
  · subst e
    simpa [swapEdgesAt] using hdouble
  · simp [swapEdgesAt, h₀, h₁]

/-
If `k` has a double edge, then an edge enters `v` exactly when its swapped edge
enters `v`:
\[
  \operatorname{swapEdgesAt}(k,e)\in\operatorname{In}_G(v)
  \iff
  e\in\operatorname{In}_G(v).
\]
-/
theorem mem_inEdges_swapEdgesAt_iff
    (G : KontsevichGraph n m) (k : Aerial n)
    (hdouble : G.target (k, 0) = G.target (k, 1))
    (v : Vertex n m) (e : Edge n) :
    swapEdgesAt k e ∈ inEdges G v ↔ e ∈ inEdges G v := by
  simp only [mem_inEdges]
  rw [target_swapEdgesAt_eq G k hdouble e]

/-
Swapping the two outgoing edges of `k` twice is the identity:
\[
  \operatorname{swapEdgesAt}(k,
    \operatorname{swapEdgesAt}(k,e))=e.
\]
-/
theorem swapEdgesAt_involutive
    (k : Aerial n) (e : Edge n) :
    swapEdgesAt k (swapEdgesAt k e) = e := by
  by_cases h₀ : e = (k, 0)
  · subst e
    simp [swapEdgesAt]
  by_cases h₁ : e = (k, 1)
  · subst e
    simp [swapEdgesAt]
  · simp [swapEdgesAt, h₀, h₁]

/--
The equivalence of edges obtained by exchanging the two outgoing edges of
aerial vertex `k`.
-/
def swapEdgesAtEquiv (k : Aerial n) :
    Equiv (Edge n) (Edge n) where
  toFun e := swapEdgesAt k e
  invFun e := swapEdgesAt k e
  left_inv e := swapEdgesAt_involutive k e
  right_inv e := swapEdgesAt_involutive k e

@[simp]
theorem swapEdgesAtEquiv_apply
    (k : Aerial n) (e : Edge n) :
    swapEdgesAtEquiv k e = swapEdgesAt k e := rfl

/-
If the two outgoing edges of `k` have the same target, then swapping those
edges restricts to a bijection
\[
  \operatorname{In}_G(v)\simeq\operatorname{In}_G(v)
\]
for every vertex `v`.
-/
def swapEdgesAtInEdgesEquiv
    (G : KontsevichGraph n m) (k : Aerial n)
    (hdouble : G.target (k, 0) = G.target (k, 1))
    (v : Vertex n m) :
    {e : Edge n // e ∈ inEdges G v} ≃
      {e : Edge n // e ∈ inEdges G v} where
  toFun e :=
    ⟨swapEdgesAt k e.1,
      (mem_inEdges_swapEdgesAt_iff G k hdouble v e.1).2 e.2⟩
  invFun e :=
    ⟨swapEdgesAt k e.1,
      (mem_inEdges_swapEdgesAt_iff G k hdouble v e.1).2 e.2⟩
  left_inv e := by
    apply Subtype.ext
    exact swapEdgesAt_involutive k e.1
  right_inv e := by
    apply Subtype.ext
    exact swapEdgesAt_involutive k e.1

/-
If the two outgoing edges of `k` have the same target, then swapping their
labels preserves the incoming multi-index at every vertex:
\[
  t(e_k^1)=t(e_k^2)
  \quad\Longrightarrow\quad
  \alpha_{\Gamma,\operatorname{swap}_k(I)}(v)
  =
  \alpha_{\Gamma,I}(v).
\]
-/
theorem inMulti_swapLabelsAt_of_double
    (G : KontsevichGraph n m) (I : Labelling n d)
    (k : Aerial n)
    (hdouble : G.target (k, 0) = G.target (k, 1))
    (v : Vertex n m) :
    inMulti G (swapLabelsAt I k) v = inMulti G I v := by
  unfold inMulti
  refine Finset.sum_equiv (swapEdgesAtEquiv k) ?_ ?_
  · intro e
    simpa [swapEdgesAtEquiv_apply] using
      (mem_inEdges_swapEdgesAt_iff G k hdouble v e).symm
  · intro e he
    simp only [swapEdgesAtEquiv_apply]
    rw [swapLabelsAt_apply_eq_apply_swapEdgesAt]

/-
Swapping the two outgoing edges of `k` changes only their ordered slot; it
never changes an edge’s aerial source:
\[
  s(\operatorname{swapEdgesAt}(k,e))=s(e).
\]
-/
theorem swapEdgesAt_fst
    (k : Aerial n) (e : Edge n) :
    (swapEdgesAt k e).1 = e.1 := by
  by_cases h₀ : e = (k, 0)
  · subst e
    simp [swapEdgesAt]
  by_cases h₁ : e = (k, 1)
  · subst e
    simp [swapEdgesAt]
  · simp [swapEdgesAt, h₀, h₁]


/--
Exchange the two ordered outgoing edges of aerial vertex `k`.

The new graph has target function
\[
  t_{\operatorname{swap}_k(G)}(e)
  =
  t_G(\operatorname{swapEdgesAt}(k,e)).
\]
-/
def swapOutgoingEdges
    (G : KontsevichGraph n m) (k : Aerial n) :
    KontsevichGraph n m where
  target e := G.target (swapEdgesAt k e)
  no_loop := by
    intro e h
    apply G.no_loop (swapEdgesAt k e)
    rw [swapEdgesAt_fst k e]
    exact h

@[simp]
theorem swapOutgoingEdges_target
    (G : KontsevichGraph n m) (k : Aerial n) (e : Edge n) :
    (swapOutgoingEdges G k).target e =
      G.target (swapEdgesAt k e) := rfl
/-
The first and second outgoing targets at `k` are exchanged:
\[
  t_{\operatorname{swap}_k(G)}(e_k^1)=t_G(e_k^2),
  \qquad
  t_{\operatorname{swap}_k(G)}(e_k^2)=t_G(e_k^1).
\]
-/
@[simp]
theorem swapOutgoingEdges_target_left
    (G : KontsevichGraph n m) (k : Aerial n) :
    (swapOutgoingEdges G k).target (k, 0) = G.target (k, 1) := by
  simp [swapOutgoingEdges]

@[simp]
theorem swapOutgoingEdges_target_right
    (G : KontsevichGraph n m) (k : Aerial n) :
    (swapOutgoingEdges G k).target (k, 1) = G.target (k, 0) := by
  simp [swapOutgoingEdges]


/-
If an edge does not leave aerial vertex `k`, swapping the two outgoing edges
of `k` leaves that edge unchanged:
\[
  s(e)\neq k
  \quad\Longrightarrow\quad
  \operatorname{swapEdgesAt}(k,e)=e.
\]
-/
theorem swapEdgesAt_of_source_ne
  (k : Aerial n) (e : Edge n) (h : e.1 ≠ k) :
  swapEdgesAt k e = e := by
  apply swapEdgesAt_of_ne
  · intro h₀
    exact h (congrArg Prod.fst h₀)
  · intro h₁
    exact h (congrArg Prod.fst h₁)

/-
Exchange the two ordered outgoing edges at `k` in an admissible graph.

The result is again admissible: at `k` the two distinct targets are merely
exchanged, and at every other aerial vertex the targets are unchanged.
-/
def swapOutgoingEdgesAdmissible
    (G : AdmissibleGraph n m) (k : Aerial n) :
    AdmissibleGraph n m where
  toKontsevichGraph :=
    swapOutgoingEdges (G : KontsevichGraph n m) k
  no_double := by
    intro a
    by_cases h : a = k
    · subst a
      simpa only [swapOutgoingEdges_target_left,
        swapOutgoingEdges_target_right] using (G.no_double k).symm
    · change
        G.target (swapEdgesAt k (a, 0)) ≠
          G.target (swapEdgesAt k (a, 1))
      rw [swapEdgesAt_of_source_ne k (a, 0) h,
        swapEdgesAt_of_source_ne k (a, 1) h]
      exact G.no_double a
/-
An edge enters `v` in the graph with its outgoing edges swapped at `k` exactly
when its swapped edge enters `v` in the original graph:
\[
  e\in\operatorname{In}_{\operatorname{swap}_k(G)}(v)
  \iff
  \operatorname{swapEdgesAt}(k,e)\in\operatorname{In}_G(v).
\]
-/
theorem mem_inEdges_swapOutgoingEdges_iff
    (G : KontsevichGraph n m) (k : Aerial n)
    (v : Vertex n m) (e : Edge n) :
    e ∈ inEdges (swapOutgoingEdges G k) v ↔
      swapEdgesAt k e ∈ inEdges G v := by
  simp only [mem_inEdges, swapOutgoingEdges_target]

/--
**Mathematical statement.**
Swapping the ordered outgoing edges in the graph is equivalent, at the level of
incoming multi-indices, to keeping the graph fixed and swapping the labels:
\[
  \alpha_{\operatorname{swap}_k(G),I}(v)
  =
  \alpha_{G,\operatorname{swap}_k(I)}(v).
\]
-/
theorem inMulti_swapOutgoingEdges
    (G : KontsevichGraph n m) (I : Labelling n d)
    (k : Aerial n) (v : Vertex n m) :
    inMulti (swapOutgoingEdges G k) I v =
      inMulti G (swapLabelsAt I k) v := by
  unfold inMulti
  refine Finset.sum_equiv (swapEdgesAtEquiv k) ?_ ?_
  · intro e
    simp [swapEdgesAtEquiv_apply]
  · intro e he
    simp only [swapEdgesAtEquiv_apply]
    rw [swapLabelsAt_apply_eq_apply_swapEdgesAt,
      swapEdgesAt_involutive]
end Kontsevich
