import GeneralizedBulk.Graph.BoundaryExterior
import GeneralizedBulk.Graph.UniformSwitching
import GeneralizedBulk.Exterior.Equivariance

/-!
# Joint finite exterior equivariance under the actual graph switch

The scalar coordinate and the whole boundary self-energy are computed from
the literal graph resolvent. Accepted switches preserve the outside principal
minor and permute the coupling, giving their joint exterior equivariance.
-/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical
namespace GeneralizedBulk.Graph
open Exterior
attribute [local instance] outsideFintype

abbrev GraphNonreal := {z : ℂ // z.im ≠ 0}
abbrev GraphExteriorState := (GraphNonreal → ℂ) × (GraphNonreal → Mat)

variable {V : Type*} [Fintype V] [DecidableEq V]

def graphResolvent (G : SimpleGraph V) (z : ℂ) : Matrix V V ℂ :=
  (G.adjMatrix ℂ - z • 1)⁻¹

def graphBoundary (G : SimpleGraph V) (e : Fin 4 → V) (z : ℂ) : Mat :=
  (graphResolvent G z).submatrix e e

def graphBoundaryDerivative (G : SimpleGraph V) (e : Fin 4 → V) (z : ℂ) : Mat :=
  (graphResolvent G z * graphResolvent G z).submatrix e e

def graphExteriorScalar (G : SimpleGraph V) (e : Fin 4 → V) (z : ℂ) : ℂ :=
  rawExteriorScalar (Matrix.trace (graphResolvent G z)) (graphBoundary G e z)
    (graphBoundaryDerivative G e z)

def graphExteriorMatrix (G : SimpleGraph V) (e : Fin 4 → V) (z : ℂ) : Mat :=
  rawExterior (graphBoundary G e z)

def graphExterior (G : SimpleGraph V) (e : Fin 4 → V) : GraphExteriorState :=
  (fun z => graphExteriorScalar G e z.1, fun z => graphExteriorMatrix G e z.1)

theorem graphAdjacency_isHermitian (G : SimpleGraph V) : (G.adjMatrix ℂ).IsHermitian := by
  ext v w
  simp [Matrix.conjTranspose_apply, SimpleGraph.adjMatrix_apply, G.adj_comm]

theorem endpointPermutation_left_apply {W : Type*} (B : Matrix (Fin 4) W ℂ)
    (i : Fin 4) (j : W) :
    ((GeneralizedSwitching.endpointPermutation : Mat) * B) i j = B (swapPartners i) j := by
  fin_cases i <;>
    simp [GeneralizedSwitching.endpointPermutation, Matrix.mul_apply, Fin.sum_univ_succ,
      swapPartners, Equiv.swap_apply_def]

theorem endpointPermutation_right_apply {W : Type*} (B : Matrix W (Fin 4) ℂ)
    (i : W) (j : Fin 4) :
    (B * (GeneralizedSwitching.endpointPermutation : Mat)) i j = B i (swapPartners j) := by
  fin_cases j <;>
    simp [GeneralizedSwitching.endpointPermutation, Matrix.mul_apply, Fin.sum_univ_succ,
      swapPartners, Equiv.swap_apply_def]

theorem endpointPermutation_conjugate_submatrix (M : Mat) :
    GeneralizedSwitching.endpointPermutation * M *
      (GeneralizedSwitching.endpointPermutation : Mat).transpose =
        M.submatrix swapPartners swapPartners := by
  rw [endpointPermutation_transpose]
  ext i j
  rw [endpointPermutation_right_apply, endpointPermutation_left_apply]
  rfl

theorem endpointPermutation_orthogonal :
    (GeneralizedSwitching.endpointPermutation : Mat) *
      (GeneralizedSwitching.endpointPermutation : Mat).transpose = 1 := by
  rw [endpointPermutation_transpose, endpointPermutation_sq]

theorem switchIncrement_conjugate :
    (GeneralizedSwitching.endpointPermutation : Mat) * GeneralizedSwitching.switchIncrement *
      GeneralizedSwitching.endpointPermutation = -GeneralizedSwitching.switchIncrement := by
  simp only [GeneralizedSwitching.switchIncrement, Matrix.mul_sub, Matrix.sub_mul]
  have h : (GeneralizedSwitching.endpointPermutation : Mat) *
      (GeneralizedSwitching.endpointPermutation * GeneralizedSwitching.edgeMatrix *
        GeneralizedSwitching.endpointPermutation) * GeneralizedSwitching.endpointPermutation =
      GeneralizedSwitching.edgeMatrix := by
    calc
      _ = (GeneralizedSwitching.endpointPermutation * GeneralizedSwitching.endpointPermutation) *
          GeneralizedSwitching.edgeMatrix *
          (GeneralizedSwitching.endpointPermutation * GeneralizedSwitching.endpointPermutation) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [endpointPermutation_sq]; simp
  rw [h]
  abel

theorem switchGraph_outside_adjacency (G : SimpleGraph V) (e : Fin 4 → V)
    (v : Outside e) (w : V) :
    (switchGraph G e).adjMatrix ℂ v w = G.adjMatrix ℂ v w := by
  have hv : ∀ i, (v : V) ≠ e i := by
    intro i hi
    exact v.property ⟨i, hi.symm⟩
  simp only [SimpleGraph.adjMatrix_apply, switchGraph_adj, cycleMask_outside e v w hv,
    not_false_eq_true, and_true, false_and, or_false]

theorem switchGraph_outsideMinor (G : SimpleGraph V) (e : Fin 4 → V) :
    ((switchGraph G e).adjMatrix ℂ).submatrix (fun v : Outside e => (v : V))
      (fun v : Outside e => (v : V)) =
      (G.adjMatrix ℂ).submatrix (fun v : Outside e => (v : V)) (fun v : Outside e => (v : V)) := by
  ext v w
  exact switchGraph_outside_adjacency G e v w

theorem switchGraph_coupling_outside (G : SimpleGraph V) (e : Fin 4 → V) :
    ((switchGraph G e).adjMatrix ℂ).submatrix (fun v : Outside e => (v : V)) e =
      (G.adjMatrix ℂ).submatrix (fun v : Outside e => (v : V)) e := by
  ext v i
  exact switchGraph_outside_adjacency G e v (e i)

theorem switchGraph_coupling_boundary (G : SimpleGraph V) (e : Fin 4 → V) :
    ((switchGraph G e).adjMatrix ℂ).submatrix e (fun v : Outside e => (v : V)) =
      (G.adjMatrix ℂ).submatrix e (fun v : Outside e => (v : V)) := by
  ext i v
  simpa only [Matrix.submatrix_apply, SimpleGraph.adjMatrix_apply, (switchGraph G e).adj_comm (e i) v,
    G.adj_comm (e i) v] using switchGraph_outside_adjacency G e v (e i)

theorem switchGraph_boundary_adjacency (G : SimpleGraph V) (e : Fin 4 → V)
    (he : Function.Injective e) (h : Alternating G e) :
    ((switchGraph G e).adjMatrix ℂ).submatrix e e =
      (G.adjMatrix ℂ).submatrix e e + (GeneralizedSwitching.switchIncrement : Mat) := by
  have h10 := G.symm h.1
  have h32 := G.symm h.2.1
  have h30 : ¬G.Adj (e 3) (e 0) := fun hn => h.2.2.1 (G.symm hn)
  have h12 : ¬G.Adj (e 1) (e 2) := fun hn => h.2.2.2 (G.symm hn)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.submatrix_apply, SimpleGraph.adjMatrix_apply, switchGraph_adj,
      cycleMask_endpoint e he, he.eq_iff, oldPartner, newPartner, h.1, h.2.1,
      h.2.2.1, h.2.2.2, h10, h32, h30, h12, Matrix.add_apply,
      GeneralizedSwitching.switchIncrement, GeneralizedSwitching.endpointPermutation,
      GeneralizedSwitching.edgeMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

theorem graphBoundary_swap (G : SimpleGraph V) (e : Fin 4 → V) (z : ℂ) :
    graphBoundary G (e ∘ swapPartners) z = GeneralizedSwitching.endpointPermutation *
      graphBoundary G e z * (GeneralizedSwitching.endpointPermutation : Mat).transpose := by
  rw [endpointPermutation_conjugate_submatrix]
  rfl

theorem graphBoundaryDerivative_swap (G : SimpleGraph V) (e : Fin 4 → V) (z : ℂ) :
    graphBoundaryDerivative G (e ∘ swapPartners) z = GeneralizedSwitching.endpointPermutation *
      graphBoundaryDerivative G e z * (GeneralizedSwitching.endpointPermutation : Mat).transpose := by
  rw [endpointPermutation_conjugate_submatrix]
  rfl

theorem graphExteriorScalar_swap (G : SimpleGraph V) (e : Fin 4 → V) (z : ℂ) :
    graphExteriorScalar G (e ∘ swapPartners) z = graphExteriorScalar G e z := by
  simp only [graphExteriorScalar, graphBoundary_swap, graphBoundaryDerivative_swap]
  exact rawExteriorScalar_conjugate _ _ _ _ endpointPermutation_orthogonal

theorem graphExteriorMatrix_swap (G : SimpleGraph V) (e : Fin 4 → V) (z : ℂ) :
    graphExteriorMatrix G (e ∘ swapPartners) z =
      GeneralizedSwitching.endpointPermutation * graphExteriorMatrix G e z *
        (GeneralizedSwitching.endpointPermutation : Mat).transpose - GeneralizedSwitching.switchIncrement := by
  change rawExterior (graphBoundary G (e ∘ swapPartners) z) = _
  rw [graphBoundary_swap, rawExterior, inverse_conjugate _ _ endpointPermutation_orthogonal]
  simp only [graphExteriorMatrix, rawExterior, GeneralizedSwitching.switchIncrement,
    Matrix.mul_sub, Matrix.sub_mul, endpointPermutation_transpose]
  abel

/-- The actual finite scalar exterior equals the trace of the deleted
outside resolvent, jointly with its boundary self-energy. -/
theorem graphExteriorScalar_eq_minor (G : SimpleGraph V) (e : Fin 4 → V)
    (he : Function.Injective e) (z : ℂ) (hz : z.im ≠ 0) :
    graphExteriorScalar G e z = Matrix.trace
      (((G.adjMatrix ℂ).submatrix (fun v : Outside e => (v : V))
        (fun v : Outside e => (v : V)) - z • 1)⁻¹) := by
  exact boundary_exterior_trace_identity (G.adjMatrix ℂ) (graphAdjacency_isHermitian G) e he z hz

/-- The actual finite boundary self-energy equals its outside Schur formula. -/
theorem graphExteriorMatrix_eq_minor (G : SimpleGraph V) (e : Fin 4 → V)
    (he : Function.Injective e) (z : ℂ) (hz : z.im ≠ 0) :
    graphExteriorMatrix G e z =
      GeneralizedSwitching.edgeMatrix - ((G.adjMatrix ℂ).submatrix e e - z • 1) +
        (G.adjMatrix ℂ).submatrix e (fun v : Outside e => (v : V)) *
          (((G.adjMatrix ℂ).submatrix (fun v : Outside e => (v : V))
            (fun v : Outside e => (v : V)) - z • 1)⁻¹) *
              (G.adjMatrix ℂ).submatrix (fun v : Outside e => (v : V)) e := by
  exact boundary_exterior_selfEnergy (G.adjMatrix ℂ) (graphAdjacency_isHermitian G) e he
    GeneralizedSwitching.edgeMatrix z hz

/-- Switching changes no outside vertex or outside edge. -/
theorem graphExteriorScalar_switch (G : SimpleGraph V) (e : Fin 4 → V)
    (he : Function.Injective e) (z : ℂ) (hz : z.im ≠ 0) :
    graphExteriorScalar (switchGraph G e) e z = graphExteriorScalar G e z := by
  rw [graphExteriorScalar_eq_minor (switchGraph G e) e he z hz,
    graphExteriorScalar_eq_minor G e he z hz, switchGraph_outsideMinor]

/-- Before endpoint relabeling, the finite exterior matrix changes by the
literal deterministic switching increment. -/
theorem graphExteriorMatrix_switch (G : SimpleGraph V) (e : Fin 4 → V)
    (he : Function.Injective e) (h : Alternating G e) (z : ℂ) (hz : z.im ≠ 0) :
    graphExteriorMatrix (switchGraph G e) e z = graphExteriorMatrix G e z -
      GeneralizedSwitching.switchIncrement := by
  rw [graphExteriorMatrix_eq_minor (switchGraph G e) e he z hz,
    graphExteriorMatrix_eq_minor G e he z hz, switchGraph_boundary_adjacency G e he h,
    switchGraph_coupling_boundary, switchGraph_coupling_outside, switchGraph_outsideMinor]
  abel

/-- The scalar and every exterior spectral matrix transform jointly under
the accepted finite graph switch, with the same endpoint permutation. -/
theorem graphExterior_switchedPair (G : SimpleGraph V) (e : Fin 4 → V)
    (he : Function.Injective e) (h : Alternating G e) :
    graphExterior (switchGraph G e) (e ∘ swapPartners) =
      action (GeneralizedSwitching.endpointPermutation : Mat) (graphExterior G e) := by
  apply Prod.ext
  · funext z
    exact (graphExteriorScalar_swap (switchGraph G e) e z.1).trans
      (graphExteriorScalar_switch G e he z.1 z.2)
  · funext z
    change graphExteriorMatrix (switchGraph G e) (e ∘ swapPartners) z.1 =
      GeneralizedSwitching.endpointPermutation * graphExteriorMatrix G e z.1 *
        (GeneralizedSwitching.endpointPermutation : Mat).transpose
    rw [graphExteriorMatrix_swap, graphExteriorMatrix_switch G e he h z.1 z.2]
    simp only [Matrix.mul_sub, Matrix.sub_mul, endpointPermutation_transpose,
      switchIncrement_conjugate]
    abel

/-- Actual exterior field of the uniformly sampled regular graph and two
oriented edges. -/
def edgePairExterior {N d : ℕ} (s : EdgePairState N d) : GraphExteriorState :=
  graphExterior s.val.1 s.val.2

/-- Exact accepted-switch equivariance of the actual joint finite exterior. -/
theorem edgePairExterior_proposalSwitch {N d : ℕ} (s : EdgePairState N d)
    (hs : Accepted s) :
    edgePairExterior (proposalSwitch s) =
      action (GeneralizedSwitching.endpointPermutation : Mat) (edgePairExterior s) := by
  rw [proposalSwitch, dif_pos hs]
  exact graphExterior_switchedPair s.val.1 s.val.2 hs.1 (accepted_alternating s hs)

/-- Every scalar observable is integrable on the actual finite uniform model. -/
theorem integrable_finiteUniform_real {A : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] (f : A → ℝ) :
    Integrable f (finiteUniform A) := by
  apply (integrable_finset_sum_measure.mpr (fun _ _ => integrable_dirac)).smul_measure
  exact ENNReal.inv_ne_top.mpr (by exact_mod_cast (Fintype.card_ne_zero : Fintype.card A ≠ 0))

theorem integral_finiteUniform_real {A : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] (f : A → ℝ) :
    (∫ a, f a ∂finiteUniform A) = (Fintype.card A : ℝ)⁻¹ * ∑ a, f a := by
  rw [finiteUniform, integral_smul_measure,
    integral_finset_sum_measure (fun _ _ => integrable_dirac)]
  simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]

/-- Rejection is the only error in finite joint exterior invariance. This
bound holds for every bounded test of the entire exterior field. -/
theorem edgePairExterior_approximate_switch_invariance
    {N d : ℕ} [Nonempty (EdgePairState N d)]
    (F : GraphExteriorState → ℝ) (B : ℝ) (hF : ∀ x, ‖F x‖ ≤ B) :
    ‖(∫ s, F (action (GeneralizedSwitching.endpointPermutation : Mat) (edgePairExterior s))
        ∂edgePairLaw N d) -
      (∫ s, F (edgePairExterior s) ∂edgePairLaw N d)‖ ≤
      2 * B * (edgePairLaw N d {s | ¬Accepted s}).toReal := by
  let μ := edgePairLaw N d
  let T : EdgePairState N d → EdgePairState N d := proposalSwitch
  let bad : Set (EdgePairState N d) := {s | ¬Accepted s}
  let f : EdgePairState N d → ℝ := fun s =>
    F (action (GeneralizedSwitching.endpointPermutation : Mat) (edgePairExterior s))
  let g : EdgePairState N d → ℝ := fun s => F (edgePairExterior (T s))
  have hcomp : (∫ s, g s ∂μ) = ∫ s, F (edgePairExterior s) ∂μ := by
    change (∫ s, g s ∂finiteUniform (EdgePairState N d)) =
      ∫ s, F (edgePairExterior s) ∂finiteUniform (EdgePairState N d)
    rw [integral_finiteUniform_real, integral_finiteUniform_real]
    congr 1
    exact Equiv.sum_comp (proposalSwitchEquiv N d) (fun s => F (edgePairExterior s))
  have hbad : MeasurableSet bad := bad.toFinite.measurableSet
  have hi : Integrable (bad.indicator (fun _ => (2 * B : ℝ))) μ :=
    integrable_finiteUniform_real _
  have hb := norm_integral_le_of_norm_le hi (Eventually.of_forall (fun s => by
    change ‖f s - g s‖ ≤ bad.indicator (fun _ => (2 * B : ℝ)) s
    by_cases hs : Accepted s
    · have he := edgePairExterior_proposalSwitch s hs
      have hnbad : s ∉ bad := by simpa only [bad, Set.mem_setOf_eq] using not_not.mpr hs
      simp only [f, g, T, he, sub_self, norm_zero, Set.indicator_of_not_mem hnbad, le_refl]
    · rw [Set.indicator_of_mem hs]
      exact (norm_sub_le _ _).trans ((add_le_add (hF _) (hF _)).trans_eq (by ring))))
  have hfi : Integrable f μ := integrable_finiteUniform_real f
  have hgi : Integrable g μ := integrable_finiteUniform_real g
  rw [integral_sub hfi hgi, hcomp, integral_indicator_const _ hbad] at hb
  simpa only [Measure.real, smul_eq_mul, mul_comm] using hb

end GeneralizedBulk.Graph
