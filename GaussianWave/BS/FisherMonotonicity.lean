import GaussianWave.BS.FrameFisher
import GaussianWave.BS.ScoreRotation
import GaussianWave.BS.BinaryReversal

/-!
# The actual Fisher inequality for a reversible weighted frame

The marginal score is proved to be an L2 conditional expectation in
ScoreRotation. This file integrates that identity and applies the actual
projection contraction. No Fisher inequality or score identity is assumed.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianWave.BS

/-- The conditional full-law score energy is exactly the literal marginal
coordinate Fisher integral, for any actual orthonormal-row observation. -/
theorem conditionalScore_heatDirectionalScore_norm_sq
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t)
    (O : Matrix J I ℝ) (hO : O * O.transpose = 1) (j : J) :
    ‖conditionalScore (heatedLaw μ t)
      (MeasurableSpace.comap (fun x : I → ℝ => O.mulVec x) inferInstance)
      (measurable_finiteMatrixAction O).comap_le (heatDirectionalScoreL2 μ ht (O j))‖ ^ 2 =
        ∫ x, heatFisherCoordinate (Measure.map (fun y : I → ℝ => O.mulVec y) μ) t j x := by
  let ν := Measure.map (fun y : I → ℝ => O.mulVec y) μ
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_map (measurable_finiteMatrixAction O).aemeasurable
  rw [score_norm_sq_eq_integral]
  have hscore := conditionalScore_heatDirectionalScore_orthonormal_rows μ ht O hO j
  calc
    _ = ∫ x, heatDirectionalScore ν t (Pi.single j 1) (O.mulVec x) ^ 2 ∂heatedLaw μ t :=
      integral_congr_ae (hscore.mono (fun _ h => congrArg (fun s : ℝ => s ^ 2) h))
    _ = ∫ x, heatDirectionalScore ν t (Pi.single j 1) x ^ 2 ∂heatedLaw ν t := by
      have hm : AEStronglyMeasurable (fun x => heatDirectionalScore ν t (Pi.single j 1) x ^ 2)
          (Measure.map (fun x : I → ℝ => O.mulVec x) (heatedLaw μ t)) :=
        ((measurable_heatDirectionalScore ν t (Pi.single j 1)).pow_const 2).aestronglyMeasurable
      rw [← integral_map (measurable_finiteMatrixAction O).aemeasurable hm,
        heatedLaw_map_orthonormal_rows μ O hO]
    _ = ∫ x, heatFisherCoordinate ν t j x := by
      rw [heatedLaw_eq_withDensity ν ht,
        integral_withDensity_eq_integral_toReal_smul (measurable_heatDensity ν t).ennreal_ofReal
          (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [heatDirectionalScore_coordinate]
      simp only [ENNReal.toReal_ofReal (heatDensity_nonneg _ _ _), smul_eq_mul]
      unfold heatFisherCoordinate
      field_simp [(heatDensity_pos ν ht x).ne']
      ring

/-- Actual Fisher contraction under an orthonormal-row observation follows
from the proved score identity and orthogonal projection contraction. -/
theorem marginal_heatFisherCoordinate_le_full_score
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t)
    (O : Matrix J I ℝ) (hO : O * O.transpose = 1) (j : J) :
    (∫ x, heatFisherCoordinate (Measure.map (fun y : I → ℝ => O.mulVec y) μ) t j x) ≤
      ‖heatDirectionalScoreL2 μ ht (O j)‖ ^ 2 := by
  rw [← conditionalScore_heatDirectionalScore_norm_sq μ ht O hO j]
  have h := norm_condExpL2_coe_le (𝕜 := ℝ) (E := ℝ)
    (measurable_finiteMatrixAction O).comap_le (heatDirectionalScoreL2 μ ht (O j))
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-- The full actual Fisher inequality for a reversible binary weighted
tight frame. The only law symmetry is reversal of each actual edge marginal.
All score identities and contractions are derived in the preceding layers. -/
theorem heatFrameFisherDefect_nonneg
    {I K : Type*} [Fintype I] [Fintype K] [DecidableEq I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t)
    (O : K → Matrix Bool I ℝ) (hO : ∀ i, O i * (O i).transpose = 1)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hframe : ∀ z : I → ℝ,
      (∑ i, (a * ((O i).mulVec z false) ^ 2 + b * ((O i).mulVec z true) ^ 2)) = squareRadius z)
    (hrev : ∀ i, Measure.map binarySwap (Measure.map (fun x => (O i).mulVec x) μ) =
      Measure.map (fun x => (O i).mulVec x) μ) :
    0 ≤ heatFrameFisherDefect μ O t := by
  classical
  letI : ∀ i, IsProbabilityMeasure (Measure.map (fun x => (O i).mulVec x) μ) :=
    fun i => isProbabilityMeasure_map (measurable_finiteMatrixAction (O i)).aemeasurable
  have hlocal (i : K) :
      (1 / 2 : ℝ) * heatFisherInformation (Measure.map (fun x => (O i).mulVec x) μ) t ≤
        a * ‖heatDirectionalScoreL2 μ ht (O i false)‖ ^ 2 +
          b * ‖heatDirectionalScoreL2 μ ht (O i true)‖ ^ 2 := by
    rw [← weighted_binary_heatFisher_eq_half _ (hrev i) ht a b hab]
    exact add_le_add
      (mul_le_mul_of_nonneg_left (marginal_heatFisherCoordinate_le_full_score μ ht (O i) (hO i) false) ha)
      (mul_le_mul_of_nonneg_left (marginal_heatFisherCoordinate_le_full_score μ ht (O i) (hO i) true) hb)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset K)) => hlocal i)
  rw [← Finset.mul_sum, heatDirectionalScoreL2_weighted_frame μ ht O a b hframe] at hsum
  exact sub_nonneg.mpr hsum

/-- BS's actual scalar root/simplex Fisher inequality in the strict bulk.
No geometric tight-frame, score-projection, Fisher, or entropy premise is
left over: the hypotheses are the probability law and actual edge reversal. -/
theorem star_heatFrameFisherDefect_nonneg
    (d : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t)
    (hrev : ∀ i, Measure.map binarySwap
      (Measure.map (fun x => (starEdgeProjection d c i).mulVec x) μ) =
        Measure.map (fun x => (starEdgeProjection d c i).mulVec x) μ) :
    0 ≤ heatFrameFisherDefect μ (starEdgeProjection d c) t := by
  have hc := (bulk_rho_lower d hd c hbulk).1
  exact heatFrameFisherDefect_nonneg μ ht (starEdgeProjection d c)
    (starEdgeProjection_mul_transpose d (by omega) c hc)
    (weightA d c) (weightB d c) (bulk_weights_pos d hd c hbulk).1.le
    (bulk_weights_pos d hd c hbulk).2.le (weight_sum d c hc)
    (starEdgeProjection_weighted_energy d (by omega) c hc) hrev

/-- The literal sum of actual conditional-score residual squares for a
binary frame. -/
def heatFrameResidualEnergy
    {I K : Type*} [Fintype I] [Fintype K]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t)
    (O : K → Matrix Bool I ℝ) (a b : ℝ) : ℝ :=
  ∑ i,
    (a * ‖heatDirectionalScoreL2 μ ht (O i false) -
      conditionalScore (heatedLaw μ t)
        (MeasurableSpace.comap (fun x : I → ℝ => (O i).mulVec x) inferInstance)
        (measurable_finiteMatrixAction (O i)).comap_le (heatDirectionalScoreL2 μ ht (O i false))‖ ^ 2 +
    b * ‖heatDirectionalScoreL2 μ ht (O i true) -
      conditionalScore (heatedLaw μ t)
        (MeasurableSpace.comap (fun x : I → ℝ => (O i).mulVec x) inferInstance)
        (measurable_finiteMatrixAction (O i)).comap_le (heatDirectionalScoreL2 μ ht (O i true))‖ ^ 2)

/-- Exact, actual Fisher defect identity. This is the equality-strength
version of the upper Fisher inequality, with every directional score and
conditional expectation constructed from the actual law. -/
theorem heatFrameFisherDefect_eq_residualEnergy
    {I K : Type*} [Fintype I] [Fintype K] [DecidableEq I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t)
    (O : K → Matrix Bool I ℝ) (hO : ∀ i, O i * (O i).transpose = 1)
    (a b : ℝ) (hab : a + b = 1)
    (hframe : ∀ z : I → ℝ,
      (∑ i, (a * ((O i).mulVec z false) ^ 2 + b * ((O i).mulVec z true) ^ 2)) = squareRadius z)
    (hrev : ∀ i, Measure.map binarySwap (Measure.map (fun x => (O i).mulVec x) μ) =
      Measure.map (fun x => (O i).mulVec x) μ) :
    heatFrameFisherDefect μ O t = heatFrameResidualEnergy μ ht O a b := by
  classical
  letI : ∀ i, IsProbabilityMeasure (Measure.map (fun x => (O i).mulVec x) μ) :=
    fun i => isProbabilityMeasure_map (measurable_finiteMatrixAction (O i)).aemeasurable
  have hlocal (i : K) :
      a * ‖conditionalScore (heatedLaw μ t)
        (MeasurableSpace.comap (fun x : I → ℝ => (O i).mulVec x) inferInstance)
        (measurable_finiteMatrixAction (O i)).comap_le (heatDirectionalScoreL2 μ ht (O i false))‖ ^ 2 +
      b * ‖conditionalScore (heatedLaw μ t)
        (MeasurableSpace.comap (fun x : I → ℝ => (O i).mulVec x) inferInstance)
        (measurable_finiteMatrixAction (O i)).comap_le (heatDirectionalScoreL2 μ ht (O i true))‖ ^ 2 =
      (1 / 2 : ℝ) * heatFisherInformation (Measure.map (fun x => (O i).mulVec x) μ) t := by
    rw [conditionalScore_heatDirectionalScore_norm_sq μ ht (O i) (hO i) false,
      conditionalScore_heatDirectionalScore_norm_sq μ ht (O i) (hO i) true]
    exact weighted_binary_heatFisher_eq_half _ (hrev i) ht a b hab
  symm
  calc
    heatFrameResidualEnergy μ ht O a b =
        ∑ i, ((a * ‖heatDirectionalScoreL2 μ ht (O i false)‖ ^ 2 +
          b * ‖heatDirectionalScoreL2 μ ht (O i true)‖ ^ 2) -
            (1 / 2 : ℝ) * heatFisherInformation (Measure.map (fun x => (O i).mulVec x) μ) t) := by
      unfold heatFrameResidualEnergy
      apply Finset.sum_congr rfl
      intro i _
      rw [conditionalScore_residual_norm_sq, conditionalScore_residual_norm_sq, ← hlocal i]
      ring
    _ = heatFrameFisherDefect μ O t := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
        heatDirectionalScoreL2_weighted_frame μ ht O a b hframe]
      rfl

/-- In the strict bulk, zero actual Fisher defect forces every full
directional score in BS's frame to be fixed by its actual edge observation.
This is the input for smooth log-density rigidity. -/
theorem star_heatFrameFisherDefect_eq_zero_scores_fixed
    (d : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t)
    (hrev : ∀ i, Measure.map binarySwap
      (Measure.map (fun x => (starEdgeProjection d c i).mulVec x) μ) =
        Measure.map (fun x => (starEdgeProjection d c i).mulVec x) μ)
    (hzero : heatFrameFisherDefect μ (starEdgeProjection d c) t = 0) :
    ∀ (i : Fin d) (j : Bool),
      heatDirectionalScoreL2 μ ht (starEdgeProjection d c i j) =
        conditionalScore (heatedLaw μ t)
          (MeasurableSpace.comap (fun x : Fin d → ℝ => (starEdgeProjection d c i).mulVec x) inferInstance)
          (measurable_finiteMatrixAction (starEdgeProjection d c i)).comap_le
          (heatDirectionalScoreL2 μ ht (starEdgeProjection d c i j)) := by
  classical
  have hc := (bulk_rho_lower d hd c hbulk).1
  have hw := bulk_weights_pos d hd c hbulk
  let O := starEdgeProjection d c
  let U := fun i j => heatDirectionalScoreL2 μ ht (O i j)
  let C := fun i j => conditionalScore (heatedLaw μ t)
    (MeasurableSpace.comap (fun x : Fin d → ℝ => (O i).mulVec x) inferInstance)
    (measurable_finiteMatrixAction (O i)).comap_le (U i j)
  let term := fun i => weightA d c * ‖U i false - C i false‖ ^ 2 +
    weightB d c * ‖U i true - C i true‖ ^ 2
  have hnonneg (i : Fin d) : 0 ≤ term i :=
    add_nonneg (mul_nonneg hw.1.le (sq_nonneg _)) (mul_nonneg hw.2.le (sq_nonneg _))
  have hsum : (∑ i, term i) = 0 := by
    change heatFrameResidualEnergy μ ht O (weightA d c) (weightB d c) = 0
    rw [← heatFrameFisherDefect_eq_residualEnergy μ ht O
      (starEdgeProjection_mul_transpose d (by omega) c hc) (weightA d c) (weightB d c)
      (weight_sum d c hc) (starEdgeProjection_weighted_energy d (by omega) c hc) hrev]
    exact hzero
  intro i j
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnonneg i)).mp hsum i (Finset.mem_univ i)
  have hA : weightA d c * ‖U i false - C i false‖ ^ 2 = 0 := by
    have hna := mul_nonneg hw.1.le (sq_nonneg ‖U i false - C i false‖)
    have hnb := mul_nonneg hw.2.le (sq_nonneg ‖U i true - C i true‖)
    dsimp [term] at hterm
    linarith
  have hB : weightB d c * ‖U i true - C i true‖ ^ 2 = 0 := by
    dsimp [term] at hterm
    linarith
  have hnorm : ‖U i j - C i j‖ ^ 2 = 0 := by
    cases j
    · exact (mul_eq_zero.mp hA).resolve_left hw.1.ne'
    · exact (mul_eq_zero.mp hB).resolve_left hw.2.ne'
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm))

end GaussianWave.BS
