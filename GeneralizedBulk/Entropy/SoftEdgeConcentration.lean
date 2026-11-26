import GeneralizedBulk.Entropy.SoftEdgeVariance
import GeneralizedBulk.Entropy.SoftEdgeProfile
import GeneralizedBulk.Entropy.ProfileConcentration

/-! Actual correlated soft-profile concentration and the hard-profile
expectation triangle, with no independent-vertex-noise hypothesis. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical Matrix.L2OpNorm

namespace GeneralizedBulk.Entropy

variable {k N d : ℕ} {B J₀ : Type*} [Fintype B] [DecidableEq B]
  [MeasurableSpace B] [MeasurableSingletonClass B] [Fintype J₀] [DecidableEq J₀]

theorem quantizedSoftEdgeAverage_memLp (A : Matrix (Fin k × Fin N) J₀ ℝ)
    (nb : Fin N → Fin d → Fin N) (hN : 0 < N) (hd : 0 < d)
    (J : ℝ → B) (hJ : Measurable J) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (a : Fin k × Fin N → ℝ) (word : Fin k × Fin 2 → B) :
    MemLp (quantizedSoftEdgeAverage nb J ℓ a word) 2 (GeneralizedBulk.Gaussian.linearImageGaussian A) := by
  apply MemLp.of_bound (contDiff_one_quantizedSoftEdgeAverage nb J hJ ℓ hℓ a word).continuous.aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun x => quantizedSoftEdgeAverage_abs_le_one nb hN hd J hJ ℓ hℓ a x word)

theorem quantizedSoftEdgeAverage_mean_l1_le (A : Matrix (Fin k × Fin N) J₀ ℝ)
    (nb : Fin N → Fin d → Fin N)
    (hnb : ∀ f : Fin N → ℝ,(∑ u,∑ j,f (nb u j)) = (d : ℝ)*∑ v,f v)
    (hN : 0 < N) (hd : 0 < d) (J : ℝ → B) (hJ : Measurable J) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (a : Fin k × Fin N → ℝ) :
    (∫ x,profileL1 (fun word => quantizedSoftEdgeAverage nb J ℓ a word x)
      (meanProfile (GeneralizedBulk.Gaussian.linearImageGaussian A)
        (fun y word => quantizedSoftEdgeAverage nb J ℓ a word y))
      ∂GeneralizedBulk.Gaussian.linearImageGaussian A) ≤
        (Fintype.card B : ℝ)^(2*k)*Real.sqrt (‖A*A.transpose‖*((k : ℝ)/((N : ℝ)*ℓ^2))) := by
  have h := integral_profileL1_mean_le_variance (GeneralizedBulk.Gaussian.linearImageGaussian A)
    (fun x word => quantizedSoftEdgeAverage nb J ℓ a word x)
    (fun word => quantizedSoftEdgeAverage_memLp A nb hN hd J hJ ℓ hℓ a word)
    (‖A*A.transpose‖*((k : ℝ)/((N : ℝ)*ℓ^2)))
    (fun word => quantizedSoftEdgeAverage_correlated_variance A nb hnb hN hd J hJ ℓ hℓ a word)
  simpa only [Fintype.card_fun,Fintype.card_prod,Fintype.card_fin,Nat.cast_pow,Nat.mul_comm k 2] using h

theorem measurable_quantizedHardEdgeAverage (nb : Fin N → Fin d → Fin N)
    (J : ℝ → B) (hJ : Measurable J) (a : Fin k × Fin N → ℝ) (word : Fin k × Fin 2 → B) :
    Measurable (quantizedHardEdgeAverage nb J a word) := by
  unfold quantizedHardEdgeAverage softEdgeAverage edgeLabelProduct
  apply Measurable.mul measurable_const
  apply Finset.measurable_sum
  intro u hu
  apply Finset.measurable_sum
  intro j hj
  apply Finset.measurable_prod
  intro i hi
  apply (measurable_hardLabel J hJ (word i)).comp
  fun_prop

theorem quantizedHardEdgeAverage_abs_le_one (nb : Fin N → Fin d → Fin N) (hN : 0 < N) (hd : 0 < d)
    (J : ℝ → B) (a x : Fin k × Fin N → ℝ) (word : Fin k × Fin 2 → B) :
    |quantizedHardEdgeAverage nb J a word x| ≤ 1 := by
  unfold quantizedHardEdgeAverage
  rw [abs_of_nonneg (softEdgeAverage_nonneg nb _ (fun i => hardLabel_nonneg J (word i)) a x)]
  exact softEdgeAverage_le_one nb hN hd _ (fun i => hardLabel_nonneg J (word i))
    (fun i => hardLabel_le_one J (word i)) a x

theorem quantizedHardEdgeAverage_memLp (A : Matrix (Fin k × Fin N) J₀ ℝ)
    (nb : Fin N → Fin d → Fin N) (hN : 0 < N) (hd : 0 < d)
    (J : ℝ → B) (hJ : Measurable J) (a : Fin k × Fin N → ℝ) (word : Fin k × Fin 2 → B) :
    MemLp (quantizedHardEdgeAverage nb J a word) 2 (GeneralizedBulk.Gaussian.linearImageGaussian A) := by
  apply MemLp.of_bound (measurable_quantizedHardEdgeAverage nb J hJ a word).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun x => quantizedHardEdgeAverage_abs_le_one nb hN hd J a x word)

set_option maxHeartbeats 1000000 in
theorem quantizedHardEdgeAverage_mean_l1_le (A : Matrix (Fin k × Fin N) J₀ ℝ)
    (nb : Fin N → Fin d → Fin N)
    (hnb : ∀ f : Fin N → ℝ,(∑ u,∑ j,f (nb u j)) = (d : ℝ)*∑ v,f v)
    (hN : 0 < N) (hd : 0 < d) (J : ℝ → B) (hJ : Measurable J) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (a : Fin k × Fin N → ℝ) :
    (∫ x,profileL1 (fun word => quantizedHardEdgeAverage nb J a word x)
      (meanProfile (GeneralizedBulk.Gaussian.linearImageGaussian A)
        (fun y word => quantizedHardEdgeAverage nb J a word y))
      ∂GeneralizedBulk.Gaussian.linearImageGaussian A) ≤
      2*(∫ x,profileL1 (fun word => quantizedHardEdgeAverage nb J a word x)
        (fun word => quantizedSoftEdgeAverage nb J ℓ a word x) ∂GeneralizedBulk.Gaussian.linearImageGaussian A)+
          (Fintype.card B : ℝ)^(2*k)*Real.sqrt (‖A*A.transpose‖*((k : ℝ)/((N : ℝ)*ℓ^2))) := by
  have h := integral_profileL1_mean_triangle (GeneralizedBulk.Gaussian.linearImageGaussian A)
    (fun x word => quantizedHardEdgeAverage nb J a word x)
    (fun x word => quantizedSoftEdgeAverage nb J ℓ a word x)
    (fun word => (quantizedHardEdgeAverage_memLp A nb hN hd J hJ a word).integrable (by norm_num))
    (fun word => (quantizedSoftEdgeAverage_memLp A nb hN hd J hJ ℓ hℓ a word).integrable (by norm_num))
  exact h.trans (add_le_add_left (quantizedSoftEdgeAverage_mean_l1_le A nb hnb hN hd J hJ ℓ hℓ a) _)

end GeneralizedBulk.Entropy
