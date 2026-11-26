import GeneralizedBulk.Graph.RankTrace
import GeneralizedBulk.Graph.SwitchRank
import GeneralizedBulk.Graph.MicroscopicExterior

/-!
# Uniform scalar change under the genuine finite switching involution

The matrix perturbation has rank at most two, so the raw trace changes by at
most `4/|Im z|`. Literal microscopic scaling cancels the spectral height and
gives `4/|Im w|`, the deterministic shift needed by reversible tail recursion.
-/
noncomputable section
open scoped Topology Classical
namespace GeneralizedBulk.Graph
open Exterior

/-- Rank-two switching gives a size-independent raw trace bound. -/
theorem graphResolvent_trace_switch_bound
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (e : Fin 4 → V)
    (he : Function.Injective e) (h : Alternating G e) (z : ℂ) (hz : z.im ≠ 0) :
    ‖Matrix.trace (graphResolvent (switchGraph G e) z) - Matrix.trace (graphResolvent G z)‖ ≤
      4 / |z.im| := by
  have ht := norm_hermitian_resolvent_trace_sub_le (G.adjMatrix ℂ) ((switchGraph G e).adjMatrix ℂ)
    (graphAdjacency_isHermitian G) (graphAdjacency_isHermitian (switchGraph G e)) z hz
  rw [norm_sub_rev] at ht
  have hr : ((((switchGraph G e).adjMatrix ℂ) - G.adjMatrix ℂ).rank : ℝ) ≤ 2 :=
    Nat.cast_le.mpr (switchGraph_adjacency_rank_le_two G e he h)
  have hb := ht.trans (mul_le_mul_of_nonneg_right hr (by positivity : 0 ≤ 2 / |z.im|))
  convert hb using 1 <;> ring

/-- Rejected proposals are self-loops, so the same trace bound holds at every
sample of the actual accepted/rejected finite involution. -/
theorem proposalSwitch_trace_bound {N d : ℕ} (s : EdgePairState N d)
    (z : ℂ) (hz : z.im ≠ 0) :
    ‖Matrix.trace (graphResolvent (proposalSwitch s).val.1 z) -
      Matrix.trace (graphResolvent s.val.1 z)‖ ≤ 4 / |z.im| := by
  by_cases hs : Accepted s
  · rw [proposalSwitch, dif_pos hs]
    exact graphResolvent_trace_switch_bound s.val.1 s.val.2 hs.1 (accepted_alternating s hs) z hz
  · simp only [proposalSwitch, hs, ↓reduceDIte, sub_self, norm_zero]
    positivity

/-- The literal normalized finite microscopic Stieltjes transform. -/
def microscopicScalar {N : ℕ} (G : SimpleGraph (Fin N)) (hN : 0 < N)
    (E sigma a : ℝ) (hsigma : 0 < sigma) (w : GraphNonreal) : ℂ :=
  (((N : ℂ)⁻¹ * Matrix.trace (graphResolvent G (microscopicParameter N hN E sigma hsigma w).1) -
    (a : ℂ)) / (sigma : ℂ))

theorem microscopicScalar_eq {N : ℕ} (G : SimpleGraph (Fin N)) (hN : 0 < N)
    (E sigma a : ℝ) (hsigma : 0 < sigma) (w : GraphNonreal) :
    microscopicScalar G hN E sigma a hsigma w =
      (microscopicStep N sigma : ℂ) * Matrix.trace
        (graphResolvent G (microscopicParameter N hN E sigma hsigma w).1) - ((a / sigma : ℝ) : ℂ) := by
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hsc : (sigma : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hsigma)
  simp only [microscopicScalar, microscopicStep, Complex.ofReal_inv, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_natCast]
  field_simp
  ring

/-- The normalized scalar moves by a fixed amount independent of graph size,
including on rejected proposals. This closes the finite tail-shift obligation. -/
theorem microscopicScalar_proposalSwitch_bound {N d : ℕ} (s : EdgePairState N d) (hN : 0 < N)
    (E sigma a : ℝ) (hsigma : 0 < sigma) (w : GraphNonreal) :
    ‖microscopicScalar (proposalSwitch s).val.1 hN E sigma a hsigma w -
      microscopicScalar s.val.1 hN E sigma a hsigma w‖ ≤ 4 / |w.1.im| := by
  let c := microscopicStep N sigma
  let z := microscopicParameter N hN E sigma hsigma w
  have hc : 0 < c := microscopicStep_pos N hN sigma hsigma
  have hzi : z.1.im = c * w.1.im := by
    simp only [z, microscopicParameter, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, zero_mul, add_zero, zero_add]
    rfl
  rw [microscopicScalar_eq, microscopicScalar_eq]
  have he : (microscopicStep N sigma : ℂ) * Matrix.trace (graphResolvent (proposalSwitch s).val.1 z.1) -
      ((a / sigma : ℝ) : ℂ) -
      ((microscopicStep N sigma : ℂ) * Matrix.trace (graphResolvent s.val.1 z.1) - ((a / sigma : ℝ) : ℂ)) =
    (c : ℂ) * (Matrix.trace (graphResolvent (proposalSwitch s).val.1 z.1) -
      Matrix.trace (graphResolvent s.val.1 z.1)) := by dsimp only [c]; ring
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  calc
    _ ≤ c * (4 / |z.1.im|) := mul_le_mul_of_nonneg_left (proposalSwitch_trace_bound s z.1 z.2) hc.le
    _ = 4 / |w.1.im| := by
      rw [hzi, abs_mul, abs_of_pos hc]
      field_simp [ne_of_gt hc, abs_ne_zero.mpr w.2]
      ring

/-- The corresponding scalar height shift used in a reversible tail bound. -/
theorem microscopicScalar_norm_proposalSwitch_bound {N d : ℕ} (s : EdgePairState N d) (hN : 0 < N)
    (E sigma a : ℝ) (hsigma : 0 < sigma) (w : GraphNonreal) :
    |‖microscopicScalar (proposalSwitch s).val.1 hN E sigma a hsigma w‖ -
      ‖microscopicScalar s.val.1 hN E sigma a hsigma w‖| ≤ 4 / |w.1.im| :=
  (abs_norm_sub_norm_le _ _).trans (microscopicScalar_proposalSwitch_bound s hN E sigma a hsigma w)

end GeneralizedBulk.Graph
