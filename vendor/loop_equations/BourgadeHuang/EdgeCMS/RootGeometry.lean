import BourgadeHuang.EdgeCMS.ScalarWKB
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-! Principal-root geometry in a fixed sector containing the edge comparison
angle π/3.  This supplies uniform local-law constants without introducing an
abstract branch or assuming the required estimates. -/
noncomputable section
open scoped Topology
namespace BourgadeHuang.EdgeCMS

theorem arg_pos_of_im_pos {z : ℂ} (hz : 0<z.im) : 0<z.arg := by
  have hn : 0≤z.arg := Complex.arg_nonneg_iff.mpr hz.le
  refine lt_of_le_of_ne hn ?_
  intro he
  have hi := (Complex.arg_eq_zero_iff.mp he.symm).2
  linarith

theorem root_im_pos {z : ℂ} (hz : 0<z.im) : 0<(root z).im := by
  have ha := arg_pos_of_im_pos hz
  have hb := Complex.arg_le_pi z
  have hsin : 0<Real.sin (z.arg/2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  simpa [root,Complex.exp_im,Complex.div_ofNat_im,Complex.log_im] using
    mul_pos (Real.exp_pos ((Complex.log z/2).re)) hsin

theorem root_re_pos {z : ℂ} (hz : 0<z.im) : 0<(root z).re := by
  have ha := arg_pos_of_im_pos hz
  have hb : z.arg<Real.pi := Complex.arg_lt_pi_iff.mpr (Or.inr hz.ne')
  have hcos : 0<Real.cos (z.arg/2) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],by linarith⟩
  simpa [root,Complex.exp_re,Complex.div_ofNat_im,Complex.log_im] using
    mul_pos (Real.exp_pos ((Complex.log z/2).re)) hcos

/-- On the simple sector `0 < Im z` and `Re z ≤ Im z`, the root-to-imaginary
part ratio is uniformly bounded by four. -/
theorem root_norm_le_four_im {z : ℂ} (hz : 0<z.im) (hsector : z.re≤z.im) :
    ‖root z‖≤4*(root z).im := by
  have hx := root_re_pos hz
  have hy := root_im_pos hz
  have hz0 : z≠0 := by intro h; simpa [h] using hz
  have hs := root_sq hz0
  have hsre := congrArg Complex.re hs
  have hsim := congrArg Complex.im hs
  simp only [pow_two,Complex.mul_re,Complex.mul_im] at hsre hsim
  have hxy : (root z).re≤3*(root z).im := by
    by_contra h
    have hlt := lt_of_not_ge h
    have hp := mul_pos (sub_pos.mpr hlt) (add_pos hx hy)
    nlinarith
  calc
    _≤|(root z).re|+|(root z).im| := Complex.norm_le_abs_re_add_abs_im _
    _=(root z).re+(root z).im := by rw [abs_of_pos hx,abs_of_pos hy]
    _≤4*(root z).im := by linarith

/-- The deterministic edge primitive, whose derivative is the principal root. -/
def edgePrimitive (z : ℂ) : ℂ := (2/3:ℂ)*z*root z

theorem hasDerivAt_edgePrimitive {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    HasDerivAt edgePrimitive (root z) z := by
  have h := ((hasDerivAt_id z).mul (hasDerivAt_root hz)).const_mul (2/3:ℂ)
  convert h using 1
  · funext w
    simp only [edgePrimitive,id_eq]
    ring
  · simp only [id_eq,one_mul]
    have hs := root_sq (Complex.slitPlane_ne_zero hz)
    have hr := root_ne_zero z
    generalize he : root z=r at hs hr ⊢
    rw [←hs]
    field_simp [hr]
    ring

theorem analyticAt_edgePrimitive {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    AnalyticAt ℂ edgePrimitive z :=
  (analyticAt_const.mul analyticAt_id).mul (analyticAt_root hz)

theorem root_conj {z : ℂ} (hz : z.im≠0) :
    root (starRingEnd ℂ z)=starRingEnd ℂ (root z) := by
  have ha : z.arg≠Real.pi := (Complex.arg_lt_pi_iff.mpr (Or.inr hz)).ne
  unfold root
  rw [Complex.log_conj z ha, ← Complex.exp_conj]
  congr 1
  rw [map_div₀]
  norm_num only [Complex.conj_ofNat]

theorem edgePrimitive_conj {z : ℂ} (hz : z.im≠0) :
    edgePrimitive (starRingEnd ℂ z)=starRingEnd ℂ (edgePrimitive z) := by
  unfold edgePrimitive
  rw [root_conj hz]
  simp only [map_mul,map_div₀,Complex.conj_ofNat]

end BourgadeHuang.EdgeCMS
