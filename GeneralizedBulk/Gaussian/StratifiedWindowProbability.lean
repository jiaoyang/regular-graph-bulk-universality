import GeneralizedBulk.Gaussian.StratifiedWindow
import GeneralizedBulk.Analysis.TruncationProbability

/-! Actual mixed Gaussian window tails vanish in probability before normalization. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped Topology
namespace GeneralizedBulk.Gaussian
variable (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
variable (hm : Integrable (fun s : AnchoredCountingState => ‖s.val.2‖) ν)

theorem massWindow_entry_probability_tendsto_zero (parameters : Parameters)
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) (v : ℂ × Bool) (i j : Fin 4) :
    ∀ ε δ : ℝ,0 < ε → 0 < δ → ∀ᶠ n in atTop,
      (massMarkedLaw ν parameters).real {z | ε <
        ‖massWindowField ν parameters (R n) v z i j - massCenteredField ν hm parameters v z i j‖} ≤ δ := by
  have hEval : Measurable (fun M : EndpointMatrix => M i j) :=
    (show Continuous (fun M : EndpointMatrix => M i j) from
      (continuous_apply j).comp (continuous_apply i)).measurable
  have hdist (n : ℕ) (z : MassMarkedSample ν) :
      dist (massWindowField ν parameters (R n) v z i j)
        (massCenteredField ν hm parameters v z i j)^2 =
      ‖massCenteredField ν hm parameters v z i j - massWindowField ν parameters (R n) v z i j‖^2 := by
    rw [dist_eq_norm,norm_sub_rev]
  have hi (n) : Integrable (fun z => dist (massWindowField ν parameters (R n) v z i j)
      (massCenteredField ν hm parameters v z i j)^2) (massMarkedLaw ν parameters) := by
    simpa only [hdist] using massWindow_errors_integrable ν hm parameters R v i j n
  have ht : Tendsto (fun n => ∫ z,dist (massWindowField ν parameters (R n) v z i j)
      (massCenteredField ν hm parameters v z i j)^2 ∂massMarkedLaw ν parameters) atTop (𝓝 0) := by
    simpa only [hdist] using massWindow_joint_second_moment_tendsto_zero ν hm parameters R hR v i j
  have hprob := Analysis.target_probability_of_second_tendsto_zero (massMarkedLaw ν parameters)
    (fun n z => massWindowField ν parameters (R n) v z i j)
    (fun z => massCenteredField ν hm parameters v z i j)
    (fun n => hEval.comp (measurable_massWindowField ν parameters (R n) v))
    (hEval.comp (measurable_massCenteredField ν hm parameters v)) hi ht
  simpa only [dist_eq_norm] using hprob

end GeneralizedBulk.Gaussian
