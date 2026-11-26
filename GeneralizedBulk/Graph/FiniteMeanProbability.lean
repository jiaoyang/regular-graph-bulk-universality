import GeneralizedBulk.Graph.FiniteMeanCalibration
import GeneralizedBulk.Graph.MicroscopicScalarState
import GeneralizedBulk.Analysis.VanishingAffineError

/-! The actual finite physical proposal mean is asymptotic in probability
to the calibrated marked mean at every fixed nonreal microscopic point. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped Topology
namespace GeneralizedBulk.External.RegularSpectralData
open Graph GeneralizedBulk.Analysis GeneralizedBulk.Gaussian GeneralizedSwitching Exterior
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

theorem microscopic_proposalMean_calibration_eq (n : ℕ) (ω : Ω)
    (E : ℝ) (hd : 3 ≤ (d : ℝ)) (hbulk : E^2 < 4*((d : ℝ)-1)) (w : GraphNonreal) :
    let parameters := Parameters.regular d E hd hbulk
    let z := (microscopicParameter (N n) (D.size_pos n) E parameters.scale parameters.scale_pos w).val
    D.proposalMean n ω z-
      Marked.mean parameters (fun ω => D.microscopicCountingState n ω E parameters.scale parameters.center) w.val ω =
      finiteMeanCalibrationError (N n) d z E parameters.center parameters.scale
        (anchoredNevanlinna (D.microscopicCountingState n ω E parameters.scale parameters.center) w.val) := by
  intro parameters z
  let s := anchoredNevanlinna (D.microscopicCountingState n ω E parameters.scale parameters.center) w.val
  have hscalar := D.microscopicCountingState_scalar n ω E parameters.scale parameters.center parameters.scale_pos w
  have hsigma : (parameters.scale : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr parameters.scale_pos.ne'
  have hlin : s*(parameters.scale : ℂ)=D.scalarResolvent n ω z-(parameters.center : ℂ) := by
    apply (eq_div_iff hsigma).mp
    exact hscalar
  have hm : (parameters.center : ℂ)+(parameters.scale : ℂ)*s=D.scalarResolvent n ω z := by
    calc
      _ = (parameters.center : ℂ)+s*(parameters.scale : ℂ) := by ring
      _ = _ := by rw [hlin]; ring
  unfold finiteMeanCalibrationError
  apply congrArg₂ (fun A B : Mat => A-B)
  · exact (D.proposalMean_eq_finiteMean n ω (by exact_mod_cast (show (0 : ℝ) < d by linarith)) z (microscopicParameter (N n) (D.size_pos n) E parameters.scale parameters.scale_pos w).property).trans
      (congrArg (finiteMean (N n) d z) hm.symm)
  · exact (limitingMean_regular d E hd hbulk s).symm

set_option maxHeartbeats 2000000 in
theorem microscopic_proposalMean_calibration_probability
    (P : Measure Ω) [IsProbabilityMeasure P]
    (E : ℝ) (hd : 3 ≤ (d : ℝ)) (hbulk : E^2 < 4*((d : ℝ)-1))
    (r : ℕ → ℕ) (hr : StrictMono r) (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hweak : let parameters := Parameters.regular d E hd hbulk
      WeakLawConverges
        (fun n => P.map (fun ω => D.microscopicCountingState (r n) ω E parameters.scale parameters.center)) ν)
    (w : GraphNonreal) :
    let parameters := Parameters.regular d E hd hbulk
    ∀ ε : ℝ,0 < ε → Tendsto (fun n => P.real {ω | ε < entryEnvelope
      (D.proposalMean (r n) ω
        (microscopicParameter (N (r n)) (D.size_pos (r n)) E parameters.scale parameters.scale_pos w).val-
        Marked.mean parameters (fun ω => D.microscopicCountingState (r n) ω E parameters.scale parameters.center) w.val ω)})
      atTop (nhds 0) := by
  intro parameters
  let X := fun n ω => D.microscopicCountingState (r n) ω E parameters.scale parameters.center
  let z := fun n => (microscopicParameter (N (r n)) (D.size_pos (r n)) E parameters.scale parameters.scale_pos w).val
  let c := fun n => 16*finiteMeanCalibrationCoefficient (N (r n)) d (z n) E parameters.center parameters.scale
  let e := fun n ω => entryEnvelope (D.proposalMean (r n) ω (z n)-Marked.mean parameters (X n) w.val ω)
  change ∀ ε : ℝ,0 < ε → Tendsto (fun n => P.real {ω | ε < e n ω}) atTop (nhds 0)
  apply vanishing_affine_error_probability_of_weakLaw_observation (fun _ : ℕ => P) X
    (fun n => D.measurable_microscopicCountingState (r n) E parameters.scale parameters.center) ν hweak
    (fun s : AnchoredCountingState => anchoredNevanlinna s w.val) (continuous_anchoredNevanlinna w.property) c e
  · exact Eventually.of_forall (fun n => mul_nonneg (by norm_num) (finiteMeanCalibrationCoefficient_nonneg _ _ _ _ _ _))
  · exact (microscopicMeanCalibrationCoefficient_tendsto_zero N D.size_pos D.size_tendsto d E hd hbulk w).comp hr.tendsto_atTop
  · apply Eventually.of_forall
    intro n ω
    dsimp only [e]
    rw [D.microscopic_proposalMean_calibration_eq (r n) ω E hd hbulk w]
    exact finiteMeanCalibrationError_envelope _ _ _ _ _ _ _

end GeneralizedBulk.External.RegularSpectralData
