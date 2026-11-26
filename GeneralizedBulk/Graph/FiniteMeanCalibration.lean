import GeneralizedBulk.Graph.FinitePolynomial
import GeneralizedBulk.Graph.MicroscopicOuter
import GeneralizedBulk.Matrix.MeanBounds
import GeneralizedBulk.Gaussian.StratifiedNormalization

/-! The literal finite proposal mean converges uniformly on bounded scalar
sets to the calibrated mean; the constant-eigenvector correction is retained. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace GeneralizedBulk.Graph
open Exterior GeneralizedSwitching

def limitingMean (d : ℕ) (E m : ℂ) : Mat := meanMatrix m ((E*m+1)/(d:ℂ)) 0

theorem continuous_meanMatrix : Continuous (fun p : ℂ × (ℂ × ℂ) => meanMatrix p.1 p.2.1 p.2.2) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;> norm_num [meanMatrix] <;> fun_prop

theorem finiteMean_tendsto (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (d : ℕ) (z m : ℕ → ℂ) (E M : ℂ)
    (hz : Tendsto z atTop (𝓝 E)) (hm : Tendsto m atTop (𝓝 M))
    (hE : (d:ℂ)-E ≠ 0) :
    Tendsto (fun n => finiteMean (N n) d (z n) (m n)) atTop (𝓝 (limitingMean d E M)) := by
  have hq := constantMode_tendsto_zero N hN d z E hz hE
  have hi : Tendsto (fun n => (N n : ℂ)⁻¹) atTop (𝓝 0) := by
    have hr : Tendsto (fun n => (N n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hN)
    simpa only [Function.comp_def,Complex.ofReal_inv,Complex.ofReal_natCast,
      Complex.ofReal_zero] using Complex.continuous_ofReal.continuousAt.tendsto.comp hr
  have ha := hm.sub hq
  have hb := (((hz.mul ha).add_const 1).sub hi).div_const (d:ℂ)
  have ht := continuous_meanMatrix.continuousAt.tendsto.comp (ha.prodMk_nhds (hb.prodMk_nhds hq))
  simpa only [sub_zero,finiteMean,limitingMean] using ht

def finiteMeanCalibrationError (N d : ℕ) (z E a sigma s : ℂ) : Mat :=
  finiteMean N d z (a+sigma*s)-limitingMean d E (a+sigma*s)

theorem finiteMeanCalibrationError_affine (N d : ℕ) (z E a sigma s : ℂ) :
    finiteMeanCalibrationError N d z E a sigma s =
      finiteMeanCalibrationError N d z E a sigma 0 + s •
        (finiteMeanCalibrationError N d z E a sigma 1-
          finiteMeanCalibrationError N d z E a sigma 0) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [finiteMeanCalibrationError,finiteMean,limitingMean,meanMatrix,Matrix.smul_apply,
      Matrix.add_apply,Matrix.sub_apply,smul_eq_mul,div_eq_mul_inv] <;> ring

def finiteMeanCalibrationCoefficient (N d : ℕ) (z E a sigma : ℂ) : ℝ :=
  entryEnvelope (finiteMeanCalibrationError N d z E a sigma 0) +
    entryEnvelope (finiteMeanCalibrationError N d z E a sigma 1-
      finiteMeanCalibrationError N d z E a sigma 0)

theorem finiteMeanCalibrationCoefficient_nonneg (N d : ℕ) (z E a sigma : ℂ) :
    0 ≤ finiteMeanCalibrationCoefficient N d z E a sigma :=
  add_nonneg (entryEnvelope_nonneg _) (entryEnvelope_nonneg _)

theorem finiteMeanCalibrationError_entryBound (N d : ℕ) (z E a sigma s : ℂ) :
    EntryBound (finiteMeanCalibrationError N d z E a sigma s)
      (finiteMeanCalibrationCoefficient N d z E a sigma * (1+‖s‖)) := by
  rw [finiteMeanCalibrationError_affine]
  intro i j
  have h0 := entryEnvelope_bound (finiteMeanCalibrationError N d z E a sigma 0) i j
  have h1 := entryEnvelope_bound (finiteMeanCalibrationError N d z E a sigma 1-
    finiteMeanCalibrationError N d z E a sigma 0) i j
  have hb := (norm_add_le _ _).trans (add_le_add h0
    (show ‖(s • (finiteMeanCalibrationError N d z E a sigma 1-
      finiteMeanCalibrationError N d z E a sigma 0)) i j‖ ≤
      ‖s‖*entryEnvelope (finiteMeanCalibrationError N d z E a sigma 1-
        finiteMeanCalibrationError N d z E a sigma 0) from by
      simpa only [Matrix.smul_apply,norm_smul] using mul_le_mul_of_nonneg_left h1 (norm_nonneg s)))
  refine hb.trans ?_
  dsimp [finiteMeanCalibrationCoefficient]
  nlinarith [entryEnvelope_nonneg (finiteMeanCalibrationError N d z E a sigma 0),
    entryEnvelope_nonneg (finiteMeanCalibrationError N d z E a sigma 1-
      finiteMeanCalibrationError N d z E a sigma 0),norm_nonneg s]

theorem finiteMeanCalibrationError_envelope (N d : ℕ) (z E a sigma s : ℂ) :
    entryEnvelope (finiteMeanCalibrationError N d z E a sigma s) ≤
      (16*finiteMeanCalibrationCoefficient N d z E a sigma)*(1+‖s‖) := by
  have hb := finiteMeanCalibrationError_entryBound N d z E a sigma s
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) =>
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 4))) => hb i j))
  calc
    _ ≤ 4*(4*(finiteMeanCalibrationCoefficient N d z E a sigma*(1+‖s‖))) := by
      simpa only [entryEnvelope,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
        nsmul_eq_mul,Nat.cast_ofNat] using hs
    _ = _ := by ring

theorem finiteMeanCalibrationCoefficient_tendsto_zero
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (d : ℕ) (z : ℕ → ℂ) (E a sigma : ℂ)
    (hz : Tendsto z atTop (𝓝 E)) (hE : (d:ℂ)-E ≠ 0) :
    Tendsto (fun n => finiteMeanCalibrationCoefficient (N n) d (z n) E a sigma) atTop (𝓝 0) := by
  have ht (s : ℂ) : Tendsto (fun n => finiteMeanCalibrationError (N n) d (z n) E a sigma s)
      atTop (𝓝 (0 : Mat)) := by
    have hh := (finiteMean_tendsto N hN d z (fun _ => a+sigma*s) E (a+sigma*s) hz
      tendsto_const_nhds hE).sub_const (limitingMean d E (a+sigma*s))
    simpa only [finiteMeanCalibrationError,sub_self] using hh
  have h0 := continuous_entryEnvelope.continuousAt.tendsto.comp (ht 0)
  have h1 := continuous_entryEnvelope.continuousAt.tendsto.comp ((ht 1).sub (ht 0))
  simpa only [finiteMeanCalibrationCoefficient,sub_zero,Function.comp_def,
    (entryEnvelope_eq_zero_iff (0 : Mat)).mpr rfl,add_zero] using h0.add h1

theorem limitingMean_regular (d : ℕ) (E : ℝ) (hd : 3 ≤ (d:ℝ))
    (hbulk : E^2 < 4*((d:ℝ)-1)) (s : ℂ) :
    limitingMean d E (((Parameters.regular d E hd hbulk).center : ℂ)+
      ((Parameters.regular d E hd hbulk).scale : ℂ)*s) =
      calibratedMean (Parameters.regular d E hd hbulk) s := by
  simp only [limitingMean,calibratedMean,Parameters.regular_p,Parameters.regular_r,
    Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_natCast]
  congr 1
  ring

theorem regular_degree_sub_energy_ne_zero (d : ℕ) (E : ℝ)
    (hbulk : E^2 < 4*((d:ℝ)-1)) : (d:ℂ)-(E:ℂ) ≠ 0 := by
  have hp := Parameters.regular_denominator_pos (d:ℝ) E hbulk
  intro hz
  have he : (d:ℝ) = E := by
    exact_mod_cast (sub_eq_zero.mp hz)
  rw [he] at hp
  linarith

theorem microscopicMeanCalibrationCoefficient_tendsto_zero
    (N : ℕ → ℕ) (hNpos : ∀ n,0 < N n) (hN : Tendsto N atTop atTop)
    (d : ℕ) (E : ℝ) (hd : 3 ≤ (d:ℝ)) (hbulk : E^2 < 4*((d:ℝ)-1))
    (w : GraphNonreal) :
    Tendsto (fun n => 16*finiteMeanCalibrationCoefficient (N n) d
      (microscopicParameter (N n) (hNpos n) E (Parameters.regular d E hd hbulk).scale
        (Parameters.regular d E hd hbulk).scale_pos w).val E
      (Parameters.regular d E hd hbulk).center (Parameters.regular d E hd hbulk).scale)
      atTop (𝓝 0) := by
  have ht := finiteMeanCalibrationCoefficient_tendsto_zero N hN d _ E
    (Parameters.regular d E hd hbulk).center (Parameters.regular d E hd hbulk).scale
    (microscopicParameter_tendsto_center N hNpos hN E _
      (Parameters.regular d E hd hbulk).scale_pos w)
    (regular_degree_sub_energy_ne_zero d E hbulk)
  simpa only [mul_zero] using ht.const_mul 16

end GeneralizedBulk.Graph
