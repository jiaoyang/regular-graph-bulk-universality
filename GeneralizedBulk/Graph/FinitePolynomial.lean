import GeneralizedBulk.Graph.ResolventMean
import GeneralizedBulk.Parameters
import GeneralizedBulk.Graph.ExteriorSwitching

/-!
# The genuine finite switching polynomial and its scalar limit

The constant eigenvector correction is retained in the mean matrix. It drops
out of the common switching residual algebraically, before taking a limit.
-/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology Classical
namespace GeneralizedBulk.Graph
open GeneralizedSwitching
open Exterior

def constantMode (N d : ℕ) (z : ℂ) : ℂ := ((N : ℂ) * ((d : ℂ) - z))⁻¹

def finiteMean (N d : ℕ) (z m : ℂ) : Mat :=
  meanMatrix (m - constantMode N d z)
    ((z * (m - constantMode N d z) + 1 - (N : ℂ)⁻¹) / (d : ℂ)) (constantMode N d z)

def finiteSwitchingPolynomial (N d : ℕ) (z h : ℂ) : ℂ :=
  h ^ 2 - ((z * h + 1 - (N : ℂ)⁻¹) / (d : ℂ)) ^ 2 +
    ((z * h + 1 - (N : ℂ)⁻¹) / (d : ℂ))

def switchingResidual (H : Mat) : Mat :=
  (1 + H * switchIncrement) * endpointPermutation * H * endpointPermutation - H

/-- The exact finite mean is governed by the same polynomial as the limiting
matrix. The rank-one constant-mode contribution cancels identically. -/
theorem finiteMean_residual (N d : ℕ) (z m : ℂ) :
    switchingResidual (finiteMean N d z m) =
      finiteSwitchingPolynomial N d z (m - constantMode N d z) • (switchIncrement : Mat) :=
  common_switching_polynomial _ _ _

/-- A single literal residual entry has absolute value equal to the scalar
polynomial, so no choice of a matrix norm is needed for the obstruction. -/
theorem norm_finiteMean_residual_entry (N d : ℕ) (z m : ℂ) :
    ‖switchingResidual (finiteMean N d z m) 0 1‖ =
      ‖finiteSwitchingPolynomial N d z (m - constantMode N d z)‖ := by
  rw [finiteMean_residual, switchIncrement_eq]
  simp [Matrix.smul_apply]

theorem finiteSwitchingPolynomial_expand (N d : ℕ) (z h : ℂ) :
    finiteSwitchingPolynomial N d z h =
      (1 - (z / (d : ℂ)) ^ 2) * h ^ 2 +
        ((z / (d : ℂ)) * (1 - 2 * ((1 - (N : ℂ)⁻¹) / (d : ℂ)))) * h +
          ((1 - (N : ℂ)⁻¹) / (d : ℂ)) * (1 - ((1 - (N : ℂ)⁻¹) / (d : ℂ))) := by
  dsimp [finiteSwitchingPolynomial]
  ring

/-- Coefficientwise convergence of the actual finite polynomial. -/
theorem finiteSwitchingPolynomial_tendsto
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (d : ℕ)
    (z h : ℕ → ℂ) (E v : ℂ)
    (hz : Tendsto z atTop (𝓝 E)) (hh : Tendsto h atTop (𝓝 v)) :
    Tendsto (fun n => finiteSwitchingPolynomial (N n) d (z n) (h n)) atTop
      (𝓝 (v ^ 2 - ((E * v + 1) / (d : ℂ)) ^ 2 + ((E * v + 1) / (d : ℂ)))) := by
  have hInv : Tendsto (fun n => (N n : ℂ)⁻¹) atTop (𝓝 0) := by
    have hreal : Tendsto (fun n => (N n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hN)
    simpa only [Function.comp_def, Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  have hb := (((hz.mul hh).add_const 1).sub hInv).div_const (d : ℂ)
  have hp := ((hh.pow 2).sub (hb.pow 2)).add hb
  simpa only [sub_zero] using hp

/-- The distinguished constant-mode term really vanishes under microscopic
or macroscopic limits with limiting energy different from `d`. -/
theorem constantMode_tendsto_zero (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (d : ℕ) (z : ℕ → ℂ) (E : ℂ) (hz : Tendsto z atTop (𝓝 E))
    (hE : (d : ℂ) - E ≠ 0) :
    Tendsto (fun n => constantMode (N n) d (z n)) atTop (𝓝 0) := by
  have hInv : Tendsto (fun n => (N n : ℂ)⁻¹) atTop (𝓝 0) := by
    have hreal : Tendsto (fun n => (N n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hN)
    simpa only [Function.comp_def, Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  have h := hInv.mul ((tendsto_const_nhds.sub hz).inv₀ hE)
  simpa only [constantMode, mul_inv_rev, mul_comm, zero_mul, mul_zero] using h

/-- An ordered residual expansion. Its hypothesis is the exact finite
compression shift equation, and its conclusion is proved by ring expansion. -/
theorem switchingResidual_perturbation_identity (H X Y : Mat)
    (hshift : (1 + (H + X) * switchIncrement) *
      (endpointPermutation * H * endpointPermutation + Y) = H + X) :
    switchingResidual H + (1 + H * switchIncrement) * Y +
      X * switchIncrement * endpointPermutation * H * endpointPermutation +
        X * switchIncrement * Y - X = 0 := by
  have heq : switchingResidual H + (1 + H * switchIncrement) * Y +
      X * switchIncrement * endpointPermutation * H * endpointPermutation +
        X * switchIncrement * Y - X =
      (1 + (H + X) * switchIncrement) *
        (endpointPermutation * H * endpointPermutation + Y) - (H + X) := by
    dsimp [switchingResidual]
    noncomm_ring
  rw [heq, hshift, sub_self]

end GeneralizedBulk.Graph

namespace GeneralizedBulk.External.RegularSpectralData
open Graph
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

/-- The exact proposal mean in the polynomial's literal finite coordinates. -/
theorem proposalMean_eq_finiteMean (hd : 0 < d) (z : ℂ) (hz : z.im ≠ 0) :
    D.proposalMean n ω z = finiteMean (N n) d z (D.scalarResolvent n ω z) := by
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  have hN0 : (N n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (D.size_pos n))
  have hdz : (d : ℂ) - z ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.natCast_im, Complex.zero_im, zero_sub, neg_eq_zero] at hi
    exact hz hi
  rw [D.proposalMean_eq_meanMatrix n ω hd z hz]
  have hb : ((z * D.scalarResolvent n ω z + 1) / (d : ℂ) -
      ((N n : ℂ) * ((d : ℂ) - z))⁻¹) =
      (z * (D.scalarResolvent n ω z - ((N n : ℂ) * ((d : ℂ) - z))⁻¹) +
        1 - (N n : ℂ)⁻¹) / (d : ℂ) := by
    field_simp
    ring
  exact congrArg (fun b : ℂ => GeneralizedSwitching.meanMatrix
    (D.scalarResolvent n ω z - ((N n : ℂ) * ((d : ℂ) - z))⁻¹) b
      (((N n : ℂ) * ((d : ℂ) - z))⁻¹)) hb

/-- The common polynomial is an exact identity for the genuine conditional
mean of the compressed graph resolvent. -/
theorem proposalMean_residual (hd : 0 < d) (z : ℂ) (hz : z.im ≠ 0) :
    switchingResidual (D.proposalMean n ω z) =
      finiteSwitchingPolynomial (N n) d z (D.scalarResolvent n ω z - constantMode (N n) d z) •
        (GeneralizedSwitching.switchIncrement : Exterior.Mat) := by
  rw [D.proposalMean_eq_finiteMean n ω hd z hz]
  exact finiteMean_residual _ _ _ _

end GeneralizedBulk.External.RegularSpectralData
