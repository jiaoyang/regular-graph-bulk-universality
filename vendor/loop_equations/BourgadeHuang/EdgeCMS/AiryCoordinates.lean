import BourgadeHuang.EdgeCMS.ScalarWKB
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Complex.CauchyIntegral

/-! The genuine Airy change of coordinate and its analytic local inverse.
The derivative and second derivative formulas here concern actual functions,
not a formal substitution of differential operators. -/
noncomputable section
open Filter Set
open scoped Topology
namespace BourgadeHuang.EdgeCMS

def airyCoordinate (z : ℂ) : ℂ := (2 / 3 : ℂ) * z * root z

theorem analyticAt_airyCoordinate {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    AnalyticAt ℂ airyCoordinate z :=
  (analyticAt_const.mul analyticAt_id).mul (analyticAt_root hz)

theorem hasStrictDerivAt_root {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    HasStrictDerivAt root (1 / (2 * root z)) z := by
  have h := (((hasStrictDerivAt_id z).clog hz).div_const 2).cexp
  convert h using 1
  have hz0 := Complex.slitPlane_ne_zero hz
  have hs := root_sq hz0
  change 1 / (2 * root z) = root z * ((1 / z) / 2)
  field_simp [hz0, root_ne_zero z]
  linear_combination -2 * hs

theorem hasStrictDerivAt_airyCoordinate {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    HasStrictDerivAt airyCoordinate (root z) z := by
  have h := (((hasStrictDerivAt_id z).const_mul (2 / 3 : ℂ)).mul
    (hasStrictDerivAt_root hz))
  convert h using 1
  have hs := root_sq (Complex.slitPlane_ne_zero hz)
  field_simp [root_ne_zero z]
  linear_combination 6 * hs

theorem hasDerivAt_airyCoordinate {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    HasDerivAt airyCoordinate (root z) z :=
  (hasStrictDerivAt_airyCoordinate hz).hasDerivAt

/-- The inverse function theorem supplies a genuine local inverse; the branch
is specified by the base point, and no global injectivity is asserted. -/
def airyCoordinateInverse {z : ℂ} (hz : z ∈ Complex.slitPlane) : ℂ → ℂ :=
  (hasStrictDerivAt_airyCoordinate hz).localInverse airyCoordinate (root z) z
    (root_ne_zero z)

theorem airyCoordinateInverse_left {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    ∀ᶠ w in 𝓝 z, airyCoordinateInverse hz (airyCoordinate w) = w :=
  ((hasStrictDerivAt_airyCoordinate hz).hasStrictFDerivAt_equiv
    (root_ne_zero z)).eventually_left_inverse

@[simp] theorem airyCoordinateInverse_base {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    airyCoordinateInverse hz (airyCoordinate z) = z :=
  (airyCoordinateInverse_left hz).self_of_nhds

theorem airyCoordinateInverse_right {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    ∀ᶠ y in 𝓝 (airyCoordinate z), airyCoordinate (airyCoordinateInverse hz y) = y :=
  ((hasStrictDerivAt_airyCoordinate hz).hasStrictFDerivAt_equiv
    (root_ne_zero z)).eventually_right_inverse

theorem hasStrictDerivAt_airyCoordinateInverse {z : ℂ}
    (hz : z ∈ Complex.slitPlane) :
    HasStrictDerivAt (airyCoordinateInverse hz) (root z)⁻¹ (airyCoordinate z) :=
  (hasStrictDerivAt_airyCoordinate hz).to_localInverse (root_ne_zero z)

theorem analyticAt_airyCoordinateInverse {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    AnalyticAt ℂ (airyCoordinateInverse hz) (airyCoordinate z) := by
  let h := (hasStrictDerivAt_airyCoordinate hz).hasStrictFDerivAt_equiv (root_ne_zero z)
  let e := h.toPartialHomeomorph airyCoordinate
  have htarget : airyCoordinate z ∈ e.target := h.image_mem_toPartialHomeomorph_target
  have hbase : e.symm (airyCoordinate z) = z := airyCoordinateInverse_base hz
  let S : Set ℂ := {y | y ∈ e.target ∧ e.symm y ∈ Complex.slitPlane}
  have hS : S ∈ 𝓝 (airyCoordinate z) := by
    apply inter_mem (e.open_target.mem_nhds htarget)
    have hc := (e.symm.continuousAt htarget).preimage_mem_nhds
      (Complex.isOpen_slitPlane.mem_nhds (show e.symm (airyCoordinate z) ∈
        Complex.slitPlane by rw [hbase]; exact hz))
    exact hc
  have hd : DifferentiableOn ℂ e.symm S := by
    intro y hy
    exact (e.hasDerivAt_symm hy.1 (root_ne_zero (e.symm y))
      (hasDerivAt_airyCoordinate hy.2)).differentiableAt.differentiableWithinAt
  exact hd.analyticAt hS

theorem airyCoordinate_first_chain {f : ℂ → ℂ} {z : ℂ}
    (hz : z ∈ Complex.slitPlane) (hf : DifferentiableAt ℂ f (airyCoordinate z)) :
    deriv (fun w => f (airyCoordinate w)) z = root z * deriv f (airyCoordinate z) := by
  simpa only [Function.comp_apply, mul_comm] using
    (hf.hasDerivAt.comp z (hasDerivAt_airyCoordinate hz)).deriv

theorem airyCoordinate_second_chain {f : ℂ → ℂ} {z : ℂ}
    (hz : z ∈ Complex.slitPlane) (hf : AnalyticAt ℂ f (airyCoordinate z)) :
    deriv (deriv (fun w => f (airyCoordinate w))) z =
      z * deriv (deriv f) (airyCoordinate z) + deriv f (airyCoordinate z) / (2 * root z) := by
  have he : (deriv (fun w => f (airyCoordinate w))) =ᶠ[𝓝 z]
      (fun w => root w * deriv f (airyCoordinate w)) := by
    filter_upwards [Complex.isOpen_slitPlane.mem_nhds hz,
      (analyticAt_airyCoordinate hz).continuousAt.tendsto.eventually hf.eventually_analyticAt]
      with w hw hfw
    exact airyCoordinate_first_chain hw hfw.differentiableAt
  rw [he.deriv_eq]
  have hd := (hasDerivAt_root hz).mul
    (hf.deriv.differentiableAt.hasDerivAt.comp z (hasDerivAt_airyCoordinate hz))
  have hd' : deriv (fun w => root w * deriv f (airyCoordinate w)) z =
      1 / (2 * root z) * deriv f (airyCoordinate z) +
        root z * (deriv (deriv f) (airyCoordinate z) * root z) := by
    simpa only [Function.comp_apply] using hd.deriv
  rw [hd']
  have hs := root_sq (Complex.slitPlane_ne_zero hz)
  calc
    1 / (2 * root z) * deriv f (airyCoordinate z) +
        root z * (deriv (deriv f) (airyCoordinate z) * root z) =
      root z ^ 2 * deriv (deriv f) (airyCoordinate z) +
        deriv f (airyCoordinate z) / (2 * root z) := by ring
    _ = _ := by rw [hs]

/-- Positive real scaling preserves the chosen square-root branch. -/
theorem root_ofReal_sq_mul {u : ℝ} (hu : 0 < u) {z : ℂ} (hz : z ≠ 0) :
    root ((u : ℂ) ^ 2 * z) = (u : ℂ) * root z := by
  have hlog : Complex.log ((u : ℂ) ^ 2 * z) =
      2 * (Real.log u : ℂ) + Complex.log z := by
    rw [← Complex.ofReal_pow, Complex.log_ofReal_mul (sq_pos_of_pos hu) hz,
      Real.log_pow]
    push_cast
    rfl
  unfold root
  rw [hlog, show (2 * (Real.log u : ℂ) + Complex.log z) / 2 =
    (Real.log u : ℂ) + Complex.log z / 2 by ring, Complex.exp_add]
  rw [← Complex.ofReal_exp, Real.exp_log hu]

/-- The Airy coordinate is homogeneous of degree three under root scaling,
equivalently degree three-halves in the original spectral parameter. -/
theorem airyCoordinate_ofReal_sq_mul {u : ℝ} (hu : 0 < u) {z : ℂ} (hz : z ≠ 0) :
    airyCoordinate ((u : ℂ) ^ 2 * z) = (u : ℂ) ^ 3 * airyCoordinate z := by
  unfold airyCoordinate
  rw [root_ofReal_sq_mul hu hz]
  ring

/-- The analytic inverse has the corresponding homogeneity locally around
its base point. This follows from the actual inverse identities. -/
theorem airyCoordinateInverse_scale_local {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    ∀ᶠ u : ℝ in 𝓝 1,
      airyCoordinateInverse hz ((u : ℂ) ^ 3 * airyCoordinate z) = (u : ℂ) ^ 2 * z := by
  have hc : Tendsto (fun u : ℝ => (u : ℂ) ^ 2 * z) (𝓝 1) (𝓝 z) := by
    have hc0 : Continuous (fun u : ℝ => (u : ℂ) ^ 2 * z) :=
      (Complex.continuous_ofReal.pow 2).mul continuous_const
    simpa using (hc0.continuousAt (x := 1)).tendsto
  filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num),
    hc.eventually (airyCoordinateInverse_left hz)] with u hu hi
  rw [← airyCoordinate_ofReal_sq_mul hu (Complex.slitPlane_ne_zero hz)]
  exact hi

end BourgadeHuang.EdgeCMS
