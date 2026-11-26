import GeneralizedBulk.Entropy.SoftEdgeConcentration
import GeneralizedBulk.Entropy.CorrelatedTransition
import GeneralizedBulk.Entropy.QuantizerBoundaries

/-! The actual integrated hard/soft profile error and full hard-profile
concentration for arbitrary correlated Gaussian noise. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical Matrix.L2OpNorm

namespace GeneralizedBulk.Entropy
open GeneralizedBulk.Gaussian

variable {k N d : ℕ} {B J₀ : Type*} [Fintype B] [DecidableEq B]
  [MeasurableSpace B] [MeasurableSingletonClass B] [Fintype J₀] [DecidableEq J₀]

set_option maxHeartbeats 1000000 in
theorem quantizedHardSoftEdge_expected_l1_le (A : Matrix (Fin k × Fin N) J₀ ℝ)
    (nb : Fin N → Fin d → Fin N)
    (hnb : ∀ f : Fin N → ℝ,(∑ u,∑ j,f (nb u j)) = (d : ℝ)*∑ v,f v)
    (hN : 0 < N) (hd : 0 < d) (J : ℝ → B) (hJ : Measurable J)
    (F : Finset ℝ) (hF : HasQuantizerBoundaries J F) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (a : Fin k × Fin N → ℝ) (v₀ : ℝ) (hv₀ : 0 < v₀)
    (hvar : ∀ i,v₀ ≤ coordinateVariance A i) :
    (∫ x,profileL1 (fun word => quantizedHardEdgeAverage nb J a word x)
      (fun word => quantizedSoftEdgeAverage nb J ℓ a word x) ∂linearImageGaussian A) ≤
        16*k*(F.card : ℝ)*ℓ/Real.sqrt (2*Real.pi*v₀) := by
  let μ := linearImageGaussian A
  let T := transitionIntervals F ℓ
  have hm (i : Fin k × Fin N) : MeasurableSet {x : Fin k × Fin N → ℝ | a i+x i ∈ T} :=
    (measurableSet_transitionIntervals F ℓ).preimage (by fun_prop)
  have hi (i : Fin k × Fin N) : Integrable
      (fun x : Fin k × Fin N → ℝ => if a i+x i ∈ T then (1 : ℝ) else 0) μ := by
    simpa only [Set.indicator,Set.mem_setOf_eq,Pi.one_apply] using
      (integrable_const (1 : ℝ)).indicator (hm i)
  have hpoint (x : Fin k × Fin N → ℝ) :
      profileL1 (fun word => quantizedHardEdgeAverage nb J a word x)
        (fun word => quantizedSoftEdgeAverage nb J ℓ a word x) ≤
          (4/(N : ℝ))*∑ i : Fin k × Fin N,if a i+x i ∈ T then (1 : ℝ) else 0 := by
    apply (quantizedHardSoftEdge_l1_le_transitions nb hnb hN hd J hJ ℓ hℓ a x).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Finset.sum_le_sum (fun i hi => transition_indicator_le_boundary_indicator J F hF ℓ ((a+x) i))
  have hleft : Integrable (fun x => profileL1 (fun word => quantizedHardEdgeAverage nb J a word x)
      (fun word => quantizedSoftEdgeAverage nb J ℓ a word x)) μ :=
    integrable_profileL1 μ _ _
      (fun word => (quantizedHardEdgeAverage_memLp A nb hN hd J hJ a word).integrable (by norm_num))
      (fun word => (quantizedSoftEdgeAverage_memLp A nb hN hd J hJ ℓ hℓ a word).integrable (by norm_num))
  apply (integral_mono hleft ((integrable_finset_sum _ (fun i hi' => hi i)).const_mul (4/(N : ℝ))) hpoint).trans
  rw [integral_const_mul,integral_finset_sum _ (fun i hi' => hi i)]
  have he (i : Fin k × Fin N) :
      (∫ x,if a i+x i ∈ T then (1 : ℝ) else 0 ∂μ) = μ.real {x | a i+x i ∈ T} := by
    simpa only [Set.indicator,Set.mem_setOf_eq,Pi.one_apply] using (integral_indicator_one (μ := μ) (hm i))
  simp_rw [he]
  calc
    _ ≤ (4/(N : ℝ))*∑ _i : Fin k × Fin N,(F.card : ℝ)*(4*ℓ)/Real.sqrt (2*Real.pi*v₀) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun i hi => correlated_coordinate_transition_probability_le A a i v₀ hv₀ (hvar i) F ℓ hℓ.le)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul]
      field_simp
      ring

set_option maxHeartbeats 1000000 in
theorem quantizedHardEdge_correlated_mean_l1_le (A : Matrix (Fin k × Fin N) J₀ ℝ)
    (nb : Fin N → Fin d → Fin N)
    (hnb : ∀ f : Fin N → ℝ,(∑ u,∑ j,f (nb u j)) = (d : ℝ)*∑ v,f v)
    (hN : 0 < N) (hd : 0 < d) (J : ℝ → B) (hJ : Measurable J)
    (F : Finset ℝ) (hF : HasQuantizerBoundaries J F) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (a : Fin k × Fin N → ℝ) (v₀ : ℝ) (hv₀ : 0 < v₀)
    (hvar : ∀ i,v₀ ≤ coordinateVariance A i) :
    (∫ x,profileL1 (fun word => quantizedHardEdgeAverage nb J a word x)
      (meanProfile (linearImageGaussian A) (fun y word => quantizedHardEdgeAverage nb J a word y))
      ∂linearImageGaussian A) ≤
        32*k*(F.card : ℝ)*ℓ/Real.sqrt (2*Real.pi*v₀)+
          (Fintype.card B : ℝ)^(2*k)*Real.sqrt (‖A*A.transpose‖*((k : ℝ)/((N : ℝ)*ℓ^2))) := by
  have h := quantizedHardEdgeAverage_mean_l1_le A nb hnb hN hd J hJ ℓ hℓ a
  have he := quantizedHardSoftEdge_expected_l1_le A nb hnb hN hd J hJ F hF ℓ hℓ a v₀ hv₀ hvar
  apply h.trans
  convert add_le_add_right (mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 2))
    ((Fintype.card B : ℝ)^(2*k)*Real.sqrt (‖A*A.transpose‖*((k : ℝ)/((N : ℝ)*ℓ^2)))) using 1 <;> ring

end GeneralizedBulk.Entropy
