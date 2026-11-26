import GaussianWave.BS.ColoredFisherMonotonicity
import GaussianWave.BS.ScoreRigidity

/-!
# Zero joint Fisher defect gives all whole-edge score constraints

Every conditional expectation retains the full 2r-dimensional edge. Thus
the conclusion constrains genuine joint channels, rather than only scalar
channel combinations. Positive bulk weights force every residual to vanish.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianWave.BS

theorem colored_star_heatFrameFisherDefect_eq_zero_scores_fixed
    (d r : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (μ : Measure ((Fin r × Fin d) → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t)
    (hrev : ∀ i, Measure.map (edgeFlipLinear r)
      (Measure.map (fun x => (coloredStarEdgeProjection d r c i).mulVec x) μ) =
        Measure.map (fun x => (coloredStarEdgeProjection d r c i).mulVec x) μ)
    (hzero : heatFrameFisherDefect μ (coloredStarEdgeProjection d r c) t = 0) :
    ∀ (i : Fin d) (p : Bool × Fin r),
      heatDirectionalScoreL2 μ ht (coloredStarEdgeProjection d r c i p) =
        conditionalScore (heatedLaw μ t)
          (MeasurableSpace.comap
            (fun x : (Fin r × Fin d) → ℝ => (coloredStarEdgeProjection d r c i).mulVec x) inferInstance)
          (measurable_finiteMatrixAction (coloredStarEdgeProjection d r c i)).comap_le
          (heatDirectionalScoreL2 μ ht (coloredStarEdgeProjection d r c i p)) := by
  classical
  have hc := (bulk_rho_lower d hd c hbulk).1
  have hw := bulk_weights_pos d hd c hbulk
  let O := coloredStarEdgeProjection d r c
  let U := fun i p => heatDirectionalScoreL2 μ ht (O i p)
  let C := fun i p => conditionalScore (heatedLaw μ t)
    (MeasurableSpace.comap (fun x : (Fin r × Fin d) → ℝ => (O i).mulVec x) inferInstance)
    (measurable_finiteMatrixAction (O i)).comap_le (U i p)
  let term := fun i q =>
    weightA d c * (‖U i (false, q)‖ ^ 2 - ‖C i (false, q)‖ ^ 2) +
      weightB d c * (‖U i (true, q)‖ ^ 2 - ‖C i (true, q)‖ ^ 2)
  have hres (i : Fin d) (p : Bool × Fin r) :
      ‖U i p - C i p‖ ^ 2 = ‖U i p‖ ^ 2 - ‖C i p‖ ^ 2 :=
    conditionalScore_residual_norm_sq (heatedLaw μ t)
      (MeasurableSpace.comap (fun x : (Fin r × Fin d) → ℝ => (O i).mulVec x) inferInstance)
      (measurable_finiteMatrixAction (O i)).comap_le (U i p)
  have hdiff (i : Fin d) (p : Bool × Fin r) : 0 ≤ ‖U i p‖ ^ 2 - ‖C i p‖ ^ 2 := by
    rw [← hres]
    exact sq_nonneg _
  have hn (i : Fin d) (q : Fin r) : 0 ≤ term i q :=
    add_nonneg (mul_nonneg hw.1.le (hdiff i (false, q)))
      (mul_nonneg hw.2.le (hdiff i (true, q)))
  letI : ∀ i, IsProbabilityMeasure (Measure.map (fun x => (O i).mulVec x) μ) :=
    fun i => isProbabilityMeasure_map (measurable_finiteMatrixAction (O i)).aemeasurable
  have hcond (i : Fin d) :
      (∑ q, (weightA d c * ‖C i (false, q)‖ ^ 2 + weightB d c * ‖C i (true, q)‖ ^ 2)) =
        (1 / 2 : ℝ) * heatFisherInformation (Measure.map (fun x => (O i).mulVec x) μ) t := by
    simp only [C, U]
    simp_rw [conditionalScore_heatDirectionalScore_norm_sq μ ht (O i)
      (coloredStarEdgeProjection_mul_transpose d r (by omega) c hc i)]
    exact colored_weighted_heatFisher_eq_half r _ (hrev i) ht (weightA d c) (weightB d c) (weight_sum d c hc)
  have hsum : (∑ i, ∑ q, term i q) = 0 := by
    have heach (i : Fin d) : (∑ q, term i q) =
        (∑ q, (weightA d c * ‖U i (false, q)‖ ^ 2 + weightB d c * ‖U i (true, q)‖ ^ 2)) -
          (1 / 2 : ℝ) * heatFisherInformation (Measure.map (fun x => (O i).mulVec x) μ) t := by
      rw [← hcond i]
      simp only [term, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      ring
    simp_rw [heach]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    dsimp only [U]
    rw [colored_heatDirectionalScoreL2_weighted_frame r μ ht O (weightA d c) (weightB d c)
      (coloredStarEdgeProjection_weighted_energy d r (by omega) c hc)]
    exact hzero
  intro i p
  have houter : (∑ q, term i q) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg (fun q _ => hn i q))).mp hsum i (Finset.mem_univ i)
  have hterm : term i p.2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun q _ => hn i q)).mp houter p.2 (Finset.mem_univ p.2)
  have hA : weightA d c * (‖U i (false, p.2)‖ ^ 2 - ‖C i (false, p.2)‖ ^ 2) = 0 := by
    have ha := mul_nonneg hw.1.le (hdiff i (false, p.2))
    have hb := mul_nonneg hw.2.le (hdiff i (true, p.2))
    dsimp [term] at hterm
    linarith
  have hB : weightB d c * (‖U i (true, p.2)‖ ^ 2 - ‖C i (true, p.2)‖ ^ 2) = 0 := by
    have ha := mul_nonneg hw.1.le (hdiff i (false, p.2))
    have hb := mul_nonneg hw.2.le (hdiff i (true, p.2))
    dsimp [term] at hterm
    linarith
  have hp : ‖U i p‖ ^ 2 - ‖C i p‖ ^ 2 = 0 := by
    rcases p with ⟨b, q⟩
    cases b
    · exact (mul_eq_zero.mp hA).resolve_left hw.1.ne'
    · exact (mul_eq_zero.mp hB).resolve_left hw.2.ne'
  rw [← hres] at hp
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hp))

/-- Genuine joint mixed-Hessian rigidity from zero actual colored Fisher
defect, with no score or Hessian premise left over. -/
theorem colored_star_log_heatDensity_hessian_mixed_of_fisherDefect_zero
    (d r : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (μ : Measure ((Fin r × Fin d) → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t)
    (hrev : ∀ i, Measure.map (edgeFlipLinear r)
      (Measure.map (fun x => (coloredStarEdgeProjection d r c i).mulVec x) μ) =
        Measure.map (fun x => (coloredStarEdgeProjection d r c i).mulVec x) μ)
    (hzero : heatFrameFisherDefect μ (coloredStarEdgeProjection d r c) t = 0)
    (x : (Fin r × Fin d) → ℝ) (i : Fin d) (u v : (Fin r × Fin d) → ℝ) :
    let O := coloredStarEdgeProjection d r c i
    fderiv ℝ (fderiv ℝ (fun y => Real.log (heatDensity μ t y))) x
      (u - O.transpose.mulVec (O.mulVec u)) (O.transpose.mulVec (O.mulVec v)) = 0 := by
  exact log_heatDensity_hessian_projection_mixed_of_scores_fixed μ ht (coloredStarEdgeProjection d r c i)
    (coloredStarEdgeProjection_mul_transpose d r (by omega) c (bulk_rho_lower d hd c hbulk).1 i)
    (colored_star_heatFrameFisherDefect_eq_zero_scores_fixed d r hd c hbulk μ ht hrev hzero i) x u v

end GaussianWave.BS
