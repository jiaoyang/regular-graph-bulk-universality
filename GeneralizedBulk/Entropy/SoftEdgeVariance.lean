import GeneralizedBulk.Entropy.SoftEdgeGradient
import GeneralizedBulk.Entropy.CorrelatedGaussianPoincare

/-! The actual soft-edge concentration input for arbitrary correlated
Gaussian vertex noise, including singular covariance. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Matrix.L2OpNorm

namespace GeneralizedBulk.Entropy
open Hermite

variable {k N d : ℕ} {B J₀ : Type*} [Fintype B] [DecidableEq B]
  [MeasurableSpace B] [MeasurableSingletonClass B] [Fintype J₀] [DecidableEq J₀]

theorem quantizedSoftEdgeAverage_correlated_variance
    (A : Matrix (Fin k × Fin N) J₀ ℝ) (nb : Fin N → Fin d → Fin N)
    (hnb : ∀ f : Fin N → ℝ,(∑ u,∑ j,f (nb u j)) = (d : ℝ)*∑ v,f v)
    (hN : 0 < N) (hd : 0 < d) (J : ℝ → B) (hJ : Measurable J) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (a : Fin k × Fin N → ℝ) (word : Fin k × Fin 2 → B) :
    (∫ x,(quantizedSoftEdgeAverage nb J ℓ a word x-
      ∫ y,quantizedSoftEdgeAverage nb J ℓ a word y ∂GeneralizedBulk.Gaussian.linearImageGaussian A)^2
      ∂GeneralizedBulk.Gaussian.linearImageGaussian A) ≤
        ‖A*A.transpose‖*((k : ℝ)/((N : ℝ)*ℓ^2)) := by
  apply correlated_gaussian_variance_le_energy_constant A (quantizedSoftEdgeAverage nb J ℓ a word)
    (contDiff_one_quantizedSoftEdgeAverage nb J hJ ℓ hℓ a word) 1
    (fun x => quantizedSoftEdgeAverage_abs_le_one nb hN hd J hJ ℓ hℓ a x word)
    (fun _ => ((N : ℝ)*ℓ)⁻¹)
    (fun i x => quantizedSoftEdgeAverage_coordinate_bound nb hnb hN hd J hJ ℓ hℓ a x word i)
  intro x
  exact quantizedSoftEdgeAverage_gradient_energy nb hnb hN hd J hJ ℓ hℓ a x word

end GeneralizedBulk.Entropy
