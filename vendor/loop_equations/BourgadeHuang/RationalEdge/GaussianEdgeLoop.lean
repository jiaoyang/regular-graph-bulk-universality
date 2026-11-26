import BourgadeHuang.RationalEdge.GaussianEdgeScale

/-! Exact finite soft-edge loop identity for actual Gaussian beta particles. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalEdge
open RationalBulk

/-- The full finite Gaussian edge hierarchy, with no local-law hypothesis. -/
theorem gaussianBeta_finite_edge_loop (β : ℝ) (hβ : 0<β)
    (N n : ℕ) {t : ℝ} (ht : t≠0) (hcube : t^3=(N+1:ℝ))
    (w : ℂ) (hw : w.im≠0) (aux : Fin n → ℂ) (ha : ∀a,(aux a).im≠0) :
    (∫ x, RationalEdge.loopIntegrand β (finiteEdgeState t x) w aux
      ∂gaussianBetaMeasure β (N+1)) =
      -(w/(t:ℂ)) * ∫ x,resolventMonomial (finiteEdgeState t x) w aux
        ∂gaussianBetaMeasure β (N+1) := by
  letI := gaussianBetaMeasure_probability hβ (show 0<N+1 by omega)
  have hL := RationalEdge.integrable_loop_comp (gaussianBetaMeasure β (N+1))
    (finiteEdgeState t) (measurable_finiteEdgeState (N+1) t)
    (finiteEdgeState_moment (gaussianBetaMeasure β (N+1)) t) β hw ha
  have hM := integrable_resolventMonomial_comp (gaussianBetaMeasure β (N+1))
    (finiteEdgeState t) (measurable_finiteEdgeState (N+1) t)
    (finiteEdgeState_moment (gaussianBetaMeasure β (N+1)) t) hw ha
  have hEq := congrArg
    (fun f : (Fin (N+1) → ℝ) → ℂ => ∫ x,f x ∂gaussianBetaMeasure β (N+1))
    (funext fun x => edge_loop_scale_identity β hβ.ne' ht (by exact_mod_cast hcube) x hw ha)
  simp only [integral_add hL (hM.const_mul _),integral_const_mul] at hEq
  rw [gaussianBeta_centered_finite_loop β hβ N n (-1) (edgeParameter (N+1) t w)
    (edgeParameter_offReal (N+1) ht hw) (fun a=>edgeParameter (N+1) t (aux a))
    (fun a=>edgeParameter_offReal (N+1) ht (ha a)),mul_zero] at hEq
  linear_combination hEq

end BourgadeHuang.RationalEdge
