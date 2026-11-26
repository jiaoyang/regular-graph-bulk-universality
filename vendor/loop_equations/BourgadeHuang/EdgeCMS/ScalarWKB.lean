import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! The actual scalar WKB gauge for the Airy equation.  Its residual is
proved explicitly; it is not postulated to solve the Airy equation. -/
noncomputable section
open Filter
open scoped Topology

namespace BourgadeHuang.EdgeCMS

/-- Principal square root, specified by the principal logarithm. -/
def root (z : ℂ) : ℂ := Complex.exp (Complex.log z / 2)

theorem root_ne_zero (z : ℂ) : root z ≠ 0 := Complex.exp_ne_zero _

theorem root_sq {z : ℂ} (hz : z ≠ 0) : root z ^ 2 = z := by
  rw [root, pow_two, ← Complex.exp_add]
  rw [show Complex.log z / 2 + Complex.log z / 2 = Complex.log z by ring]
  exact Complex.exp_log hz

theorem analyticAt_root {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    AnalyticAt ℂ root z :=
  ((analyticAt_clog hz).div analyticAt_const (by norm_num)).cexp

theorem hasDerivAt_root {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    HasDerivAt root (1 / (2 * root z)) z := by
  have h := (((hasDerivAt_id z).clog hz).div_const 2).cexp
  convert h using 1
  have hz0 := Complex.slitPlane_ne_zero hz
  have hs := root_sq hz0
  change 1 / (2 * root z) = Complex.exp (Complex.log z / 2) * ((1 / z) / 2)
  change 1 / (2 * root z) = root z * ((1 / z) / 2)
  have hr := root_ne_zero z
  generalize he : root z = r at hs hr ⊢
  rw [← hs]
  field_simp [hr]
  ring

/-- The leading logarithmic phase; `a` is a signed square root of the
coefficient of the linear potential. -/
def scalarWKBLog (a z : ℂ) : ℂ := (2 / 3 : ℂ) * a * z * root z - Complex.log z / 4

def scalarWKB (a z : ℂ) : ℂ := Complex.exp (scalarWKBLog a z)

def scalarWKBLogDerivative (a z : ℂ) : ℂ := a * root z - 1 / (4 * z)

theorem scalarWKB_ne_zero (a z : ℂ) : scalarWKB a z ≠ 0 := Complex.exp_ne_zero _

theorem analyticAt_scalarWKBLog (a : ℂ) {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    AnalyticAt ℂ (scalarWKBLog a) z := by
  exact (((analyticAt_const.mul analyticAt_id).mul (analyticAt_root hz)).sub
    ((analyticAt_clog hz).div analyticAt_const (by norm_num)))

theorem analyticAt_scalarWKB (a : ℂ) {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    AnalyticAt ℂ (scalarWKB a) z := (analyticAt_scalarWKBLog a hz).cexp

theorem hasDerivAt_scalarWKBLog (a : ℂ) {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    HasDerivAt (scalarWKBLog a) (scalarWKBLogDerivative a z) z := by
  have h := (((hasDerivAt_id z).mul (hasDerivAt_root hz)).const_mul ((2 / 3 : ℂ) * a)).sub
    (((hasDerivAt_id z).clog hz).div_const 4)
  convert h using 1
  · funext w
    simp only [scalarWKBLog, id_eq]
    ring
  · have hz0 := Complex.slitPlane_ne_zero hz
    have hs := root_sq hz0
    unfold scalarWKBLogDerivative
    simp only [id_eq, one_mul]
    have hr := root_ne_zero z
    generalize he : root z = r at hs hr ⊢
    rw [← hs]
    field_simp [hr]
    ring

theorem hasDerivAt_scalarWKB (a : ℂ) {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    HasDerivAt (scalarWKB a) (scalarWKBLogDerivative a z * scalarWKB a z) z := by
  simpa only [scalarWKB, mul_comm] using (hasDerivAt_scalarWKBLog a hz).cexp

theorem hasDerivAt_scalarWKBLogDerivative (a : ℂ) {z : ℂ}
    (hz : z ∈ Complex.slitPlane) :
    HasDerivAt (scalarWKBLogDerivative a)
      (a / (2 * root z) + 1 / (4 * z ^ 2)) z := by
  have h := ((hasDerivAt_root hz).const_mul a).sub
    (((hasDerivAt_id z).inv (Complex.slitPlane_ne_zero hz)).const_mul (1 / 4 : ℂ))
  convert h using 1
  · funext w
    simp only [scalarWKBLogDerivative, id_eq]
    ring
  · simp only [id_eq]
    ring

/-- Exact scalar residual: after WKB conjugation, the Airy potential
cancels and leaves the inverse-square term `5/(16z²)`. -/
theorem scalarWKB_riccati_residual (a : ℂ) {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    deriv (scalarWKBLogDerivative a) z + scalarWKBLogDerivative a z ^ 2 - a ^ 2 * z =
      5 / (16 * z ^ 2) := by
  rw [(hasDerivAt_scalarWKBLogDerivative a hz).deriv]
  unfold scalarWKBLogDerivative
  have hz0 := Complex.slitPlane_ne_zero hz
  have hs := root_sq hz0
  have hr := root_ne_zero z
  generalize he : root z = r at hs hr ⊢
  rw [← hs]
  field_simp [hr]
  ring

end BourgadeHuang.EdgeCMS
