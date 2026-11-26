import BourgadeHuang.EdgeCMS.AiryCoordinates
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

/-! A global analytic inverse branch for the Airy coordinate on the slit plane,
with exact identities and positive-real homogeneity. -/
noncomputable section
open Filter Set
open scoped Topology
namespace BourgadeHuang.EdgeCMS

def airyInverse (y : ℂ) : ℂ := Complex.exp ((2 / 3 : ℂ) * Complex.log ((3 / 2 : ℂ) * y))

theorem airyInverse_ne_zero (y : ℂ) : airyInverse y ≠ 0 := Complex.exp_ne_zero _

theorem positive_real_mul_mem_slitPlane {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∈ Complex.slitPlane) : (t : ℂ) * z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff] at hz ⊢
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, add_zero]
  exact hz.elim (fun h => Or.inl (mul_pos ht h))
    (fun h => Or.inr (mul_ne_zero ht.ne' h))

theorem analyticAt_airyInverse {y : ℂ} (hy : y ∈ Complex.slitPlane) :
    AnalyticAt ℂ airyInverse y := by
  have hs : (3 / 2 : ℂ) * y ∈ Complex.slitPlane := by
    simpa using positive_real_mul_mem_slitPlane (by norm_num : (0 : ℝ) < 3 / 2) hy
  exact (analyticAt_const.mul
    ((analyticAt_clog hs).comp (analyticAt_const.mul analyticAt_id))).cexp

theorem log_airyInverse (y : ℂ) :
    Complex.log (airyInverse y) = (2 / 3 : ℂ) * Complex.log ((3 / 2 : ℂ) * y) := by
  apply Complex.log_exp
  · have h := Complex.neg_pi_lt_log_im ((3 / 2 : ℂ) * y)
    norm_num [Complex.mul_im] at *
    linarith [Real.pi_pos]
  · have h := Complex.log_im_le_pi ((3 / 2 : ℂ) * y)
    norm_num [Complex.mul_im] at *
    linarith [Real.pi_pos]

theorem airyInverse_mem_slitPlane (y : ℂ) : airyInverse y ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff_arg.mpr
  refine ⟨?_, airyInverse_ne_zero y⟩
  have h := congrArg Complex.im (log_airyInverse y)
  have hbound := Complex.log_im_le_pi ((3 / 2 : ℂ) * y)
  simp only [Complex.log_im] at h
  norm_num [Complex.mul_im] at h
  intro he
  rw [he] at h
  linarith [Real.pi_pos]

theorem root_airyInverse (y : ℂ) :
    root (airyInverse y) = Complex.exp ((1 / 3 : ℂ) * Complex.log ((3 / 2 : ℂ) * y)) := by
  unfold root
  rw [log_airyInverse]
  congr 1
  ring

theorem root_airyInverse_re_pos (y : ℂ) : 0 < (root (airyInverse y)).re := by
  rw [root_airyInverse, Complex.exp_re]
  apply mul_pos (Real.exp_pos _)
  apply Real.cos_pos_of_mem_Ioo
  have hlo := Complex.neg_pi_lt_log_im ((3 / 2 : ℂ) * y)
  have hhi := Complex.log_im_le_pi ((3 / 2 : ℂ) * y)
  norm_num [Complex.mul_im]
  constructor <;> linarith [Real.pi_pos]

theorem airyCoordinate_airyInverse {y : ℂ} (hy : y ≠ 0) :
    airyCoordinate (airyInverse y) = y := by
  unfold airyCoordinate
  rw [root_airyInverse]
  unfold airyInverse
  rw [mul_assoc, ← Complex.exp_add]
  rw [show (2 / 3 : ℂ) * Complex.log ((3 / 2 : ℂ) * y) +
    (1 / 3 : ℂ) * Complex.log ((3 / 2 : ℂ) * y) =
      Complex.log ((3 / 2 : ℂ) * y) by ring]
  rw [Complex.exp_log (mul_ne_zero (by norm_num) hy)]
  ring

theorem airyInverse_injectiveOn : Set.InjOn airyInverse ({0}ᶜ : Set ℂ) := by
  intro x hx y hy h
  have he := congrArg airyCoordinate h
  simpa only [airyCoordinate_airyInverse (show x ≠ 0 from hx),
    airyCoordinate_airyInverse (show y ≠ 0 from hy)] using he

/-- On the right half-plane the forward Airy coordinate stays within the
principal logarithm branch, so the inverse is also a left inverse. -/
theorem airyInverse_airyCoordinate {z : ℂ} (hz : 0 < z.re) :
    airyInverse (airyCoordinate z) = z := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hb := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz))
  have hlo : -Real.pi < ((3 / 2 : ℂ) * Complex.log z).im := by
    norm_num [Complex.mul_im, Complex.log_im]
    linarith [Real.pi_pos]
  have hhi : ((3 / 2 : ℂ) * Complex.log z).im ≤ Real.pi := by
    norm_num [Complex.mul_im, Complex.log_im]
    linarith [Real.pi_pos]
  have he : (3 / 2 : ℂ) * airyCoordinate z =
      Complex.exp ((3 / 2 : ℂ) * Complex.log z) := by
    calc
      (3 / 2 : ℂ) * airyCoordinate z =
          Complex.exp (Complex.log z) * Complex.exp (Complex.log z / 2) := by
        rw [Complex.exp_log hz0]
        unfold airyCoordinate root
        ring
      _ = _ := by rw [← Complex.exp_add]; congr 1; ring
  unfold airyInverse
  rw [he, Complex.log_exp hlo hhi]
  rw [show (2 / 3 : ℂ) * ((3 / 2 : ℂ) * Complex.log z) = Complex.log z by ring]
  exact Complex.exp_log hz0

theorem airyInverse_ofReal_cube_mul {u : ℝ} (hu : 0 < u) {y : ℂ} (hy : y ≠ 0) :
    airyInverse ((u : ℂ) ^ 3 * y) = (u : ℂ) ^ 2 * airyInverse y := by
  have hn : (3 / 2 : ℂ) * y ≠ 0 := mul_ne_zero (by norm_num) hy
  have hlog : Complex.log ((3 / 2 : ℂ) * ((u : ℂ) ^ 3 * y)) =
      3 * (Real.log u : ℂ) + Complex.log ((3 / 2 : ℂ) * y) := by
    rw [show (3 / 2 : ℂ) * ((u : ℂ) ^ 3 * y) =
      ((u ^ 3 : ℝ) : ℂ) * ((3 / 2 : ℂ) * y) by push_cast; ring]
    rw [Complex.log_ofReal_mul (pow_pos hu 3) hn, Real.log_pow]
    push_cast
    rfl
  unfold airyInverse
  rw [hlog, show (2 / 3 : ℂ) * (3 * (Real.log u : ℂ) +
    Complex.log ((3 / 2 : ℂ) * y)) =
      (Real.log u : ℂ) + (Real.log u : ℂ) +
        (2 / 3 : ℂ) * Complex.log ((3 / 2 : ℂ) * y) by ring,
    Complex.exp_add, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hu]
  ring

theorem exists_positive_cube_root {t : ℝ} (ht : 0 < t) :
    ∃ u : ℝ, 0 < u ∧ u ^ 3 = t := by
  refine ⟨t ^ (1 / 3 : ℝ), Real.rpow_pos_of_pos ht _, ?_⟩
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
  norm_num

theorem airyInverse_im_pos {y : ℂ} (hy : 0 < y.im) : 0 < (airyInverse y).im := by
  have him : 0 < ((3 / 2 : ℂ) * y).im := by
    norm_num [Complex.mul_im]
    linarith
  have harg : 0 < Complex.arg ((3 / 2 : ℂ) * y) := by
    have hn := Complex.arg_nonneg_iff.mpr him.le
    have hne : Complex.arg ((3 / 2 : ℂ) * y) ≠ 0 :=
      fun h => him.ne' (Complex.arg_eq_zero_iff.mp h).2
    exact lt_of_le_of_ne hn hne.symm
  unfold airyInverse
  rw [Complex.exp_im]
  apply mul_pos (Real.exp_pos _)
  apply Real.sin_pos_of_pos_of_lt_pi
  · norm_num [Complex.mul_im, Complex.log_im]
    linarith
  · have hu := Complex.arg_le_pi ((3 / 2 : ℂ) * y)
    norm_num [Complex.mul_im, Complex.log_im]
    linarith [Real.pi_pos]

theorem airyInverse_im_neg {y : ℂ} (hy : y.im < 0) : (airyInverse y).im < 0 := by
  have him : ((3 / 2 : ℂ) * y).im < 0 := by
    norm_num [Complex.mul_im]
    linarith
  have harg := Complex.arg_neg_iff.mpr him
  unfold airyInverse
  rw [Complex.exp_im]
  apply mul_neg_of_pos_of_neg (Real.exp_pos _)
  apply Real.sin_neg_of_neg_of_neg_pi_lt
  · norm_num [Complex.mul_im, Complex.log_im]
    linarith
  · have hl := Complex.neg_pi_lt_arg ((3 / 2 : ℂ) * y)
    norm_num [Complex.mul_im, Complex.log_im]
    linarith [Real.pi_pos]

end BourgadeHuang.EdgeCMS
