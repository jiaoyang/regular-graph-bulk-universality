import GaussianWave.BS.InvariantProcessMoments
import GaussianWave.GaussianNormalization

/-! Positivity of actual finite-L2 mixed-second-moment matrices, without
fourth moments, Gaussianity, or a supplied covariance witness. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GaussianWave.BS

def actualSecondMomentMatrix {I : Type*} [Fintype I] (μ : Measure (I → ℝ)) : Matrix I I ℝ :=
  fun i j => ∫ x,x i*x j ∂μ

theorem actualSecondMomentMatrix_posSemidef {I : Type*} [Fintype I] [DecidableEq I]
    (μ : Measure (I → ℝ)) (hi : ∀ i j,Integrable (fun x => x i*x j) μ) :
    (actualSecondMomentMatrix μ).PosSemidef := by
  constructor
  · ext i j
    simp only [Matrix.conjTranspose_apply,star_trivial,actualSecondMomentMatrix,mul_comm]
  · intro t
    have h := integral_finiteLinearForm_sq μ t hi
    have hn : 0 ≤ ∑ i,∑ j,t i*(∫ x,x i*x j ∂μ)*t j := by
      rw [← h]
      exact integral_nonneg (fun _ => sq_nonneg _)
    simpa only [actualSecondMomentMatrix,Matrix.mulVec,dotProduct,Pi.star_apply,star_trivial,
      Finset.mul_sum,mul_assoc] using hn

def rootChannelLaw {r d : ℕ} (μ : Measure ((Fin r × RegularTreeVertex d) → ℝ)) : Measure (Fin r → ℝ) :=
  Measure.map (fun x : (Fin r × RegularTreeVertex d) → ℝ => fun a => x (a,none)) μ

theorem measurable_rootChannel {r d : ℕ} :
    Measurable (fun x : (Fin r × RegularTreeVertex d) → ℝ => fun a => x (a,none)) :=
  measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

instance rootChannelLaw_probability {r d : ℕ} (μ : Measure ((Fin r × RegularTreeVertex d) → ℝ))
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (rootChannelLaw μ) :=
  isProbabilityMeasure_map measurable_rootChannel.aemeasurable

theorem rootChannelLaw_integral_product {r d : ℕ} (μ : Measure ((Fin r × RegularTreeVertex d) → ℝ))
    (a b : Fin r) : (∫ y,y a*y b ∂rootChannelLaw μ)=treeMixedMoment μ a b none none :=
  integral_map measurable_rootChannel.aemeasurable
    (((measurable_pi_apply a).mul (measurable_pi_apply b)).aestronglyMeasurable)

theorem rootChannelLaw_integrable_product {r d : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex d) → ℝ))
    (hi : ∀ av,Integrable (fun x => x av^2) μ) (a b : Fin r) :
    Integrable (fun y => y a*y b) (rootChannelLaw μ) := by
  apply (integrable_map_measure
    (((measurable_pi_apply a).mul (measurable_pi_apply b)).aestronglyMeasurable)
    measurable_rootChannel.aemeasurable).mpr
  exact integrable_treeCoordinate_product_of_second μ hi (a,none) (b,none)

def treeRootCovariance {r d : ℕ} (μ : Measure ((Fin r × RegularTreeVertex d) → ℝ)) :
    Matrix (Fin r) (Fin r) ℝ := fun a b => treeMixedMoment μ a b none none

theorem treeRootCovariance_posSemidef {r d : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex d) → ℝ))
    (hi : ∀ av,Integrable (fun x => x av^2) μ) : (treeRootCovariance μ).PosSemidef := by
  have h : actualSecondMomentMatrix (rootChannelLaw μ)=treeRootCovariance μ := by
    ext a b
    exact rootChannelLaw_integral_product μ a b
  rw [← h]
  exact actualSecondMomentMatrix_posSemidef _ (rootChannelLaw_integrable_product μ hi)

theorem rootChannelLaw_integrable_squareRadius {r d : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex d) → ℝ))
    (hi : ∀ av,Integrable (fun x => x av^2) μ) :
    Integrable (squareRadius (I := Fin r)) (rootChannelLaw μ) := by
  unfold squareRadius
  apply integrable_finset_sum
  intro a _
  simpa only [pow_two] using rootChannelLaw_integrable_product μ hi a a

end GaussianWave.BS
