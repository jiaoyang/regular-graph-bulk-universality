import BourgadeHuang.NevanlinnaAnalytic

/-!
# Reflection and positivity of the reconstructed Nevanlinna function

The anchor inequality supplies a nonnegative linear coefficient. Subtracting
the real regularization from each reciprocal leaves a kernel whose imaginary
part is the positive Poisson kernel. This proves the actual half-plane mapping
property of every anchored counting state.
-/
noncomputable section
open scoped Topology ComplexConjugate
open MeasureTheory Filter
namespace BourgadeHuang

/-- The decaying anchored kernel respects complex conjugation. -/
theorem anchoredResolventKernel_conj (z : ℂ) (a : ℝ) :
    anchoredResolventKernel (conj z) a = conj (anchoredResolventKernel z a) := by
  simp [anchoredResolventKernel]

/-- Reflection holds for the reconstructed function, including the real axis
where its Bochner integral is interpreted by the usual total convention. -/
theorem anchoredNevanlinna_conj (s : AnchoredCountingState) (z : ℂ) :
    anchoredNevanlinna s (conj z) = conj (anchoredNevanlinna s z) := by
  simp only [anchoredNevanlinna, anchoredResolventKernel_conj, integral_conj,
    map_add, map_mul, map_pow, map_one, Complex.conj_ofReal]

/-- The nonnegative coefficient of the possible linear term at infinity. -/
def anchoredLinearCoefficient (s : AnchoredCountingState) : ℝ :=
  s.val.2.im - ∫ a, nevanlinnaWeight a ∂s.val.1.measure

theorem anchoredLinearCoefficient_nonneg (s : AnchoredCountingState) :
    0 ≤ anchoredLinearCoefficient s := sub_nonneg.mpr s.integral_weight_le_im

/-- Real regularization leaves the imaginary part of the reciprocal unchanged. -/
def regularizedResolventKernel (z : ℂ) (a : ℝ) : ℂ :=
  ((a : ℂ) - z)⁻¹ - (a * nevanlinnaWeight a : ℝ)

theorem regularizedResolventKernel_eq (a : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    regularizedResolventKernel z a = z * (nevanlinnaWeight a : ℂ) +
      (1 + z ^ 2) * anchoredResolventKernel z a := by
  rw [regularizedResolventKernel, reciprocal_anchor_decomposition a hz]
  ring

theorem integrable_regularizedResolventKernel (s : AnchoredCountingState)
    {z : ℂ} (hz : z.im ≠ 0) : Integrable (regularizedResolventKernel z) s.val.1.measure := by
  have he : regularizedResolventKernel z = fun a => z * (nevanlinnaWeight a : ℂ) +
      (1 + z ^ 2) * anchoredResolventKernel z a := funext (fun a => regularizedResolventKernel_eq a hz)
  rw [he]
  exact (s.integrable_weight.ofReal.const_mul z).add
    ((integrable_anchoredResolventKernel s.val.1.measure s.integrable_weight hz).const_mul (1 + z ^ 2))

/-- The classical regularized integral representation with a nonnegative linear term. -/
theorem anchoredNevanlinna_eq_regularized (s : AnchoredCountingState)
    {z : ℂ} (hz : z.im ≠ 0) :
    anchoredNevanlinna s z = (s.val.2.re : ℂ) + z * (anchoredLinearCoefficient s : ℂ) +
      ∫ a, regularizedResolventKernel z a ∂s.val.1.measure := by
  have he : regularizedResolventKernel z = fun a => z * (nevanlinnaWeight a : ℂ) +
      (1 + z ^ 2) * anchoredResolventKernel z a := funext (fun a => regularizedResolventKernel_eq a hz)
  have h1 : Integrable (fun a : ℝ => z * (nevanlinnaWeight a : ℂ)) s.val.1.measure :=
    s.integrable_weight.ofReal.const_mul z
  have h2 : Integrable (fun a : ℝ => (1 + z ^ 2) * anchoredResolventKernel z a) s.val.1.measure :=
    (integrable_anchoredResolventKernel s.val.1.measure s.integrable_weight hz).const_mul (1 + z ^ 2)
  have hi : (∫ a, regularizedResolventKernel z a ∂s.val.1.measure) =
      z * (∫ a, nevanlinnaWeight a ∂s.val.1.measure : ℝ) +
        (1 + z ^ 2) * ∫ a, anchoredResolventKernel z a ∂s.val.1.measure := by
    calc
      _ = (∫ a, z * (nevanlinnaWeight a : ℂ) ∂s.val.1.measure) +
          ∫ a, (1 + z ^ 2) * anchoredResolventKernel z a ∂s.val.1.measure := by
        rw [he]
        exact integral_add h1 h2
      _ = _ := by rw [integral_const_mul, integral_const_mul, integral_complex_ofReal]
  rw [hi]
  simp only [anchoredNevanlinna, anchoredLinearCoefficient, Complex.ofReal_sub]
  ring

/-- The regularized kernel has exactly the Poisson imaginary part. -/
theorem regularizedResolventKernel_im (z : ℂ) (a : ℝ) :
    (regularizedResolventKernel z a).im = z.im / Complex.normSq ((a : ℂ) - z) := by
  simp [regularizedResolventKernel, Complex.inv_im]

/-- Explicit positive representation of the imaginary part. -/
theorem anchoredNevanlinna_im_eq (s : AnchoredCountingState)
    {z : ℂ} (hz : z.im ≠ 0) :
    (anchoredNevanlinna s z).im = z.im * anchoredLinearCoefficient s +
      ∫ a, z.im / Complex.normSq ((a : ℂ) - z) ∂s.val.1.measure := by
  rw [anchoredNevanlinna_eq_regularized s hz]
  simp only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_im,
    Complex.ofReal_re, mul_zero]
  have he := integral_im (integrable_regularizedResolventKernel s hz)
  change (∫ a, (regularizedResolventKernel z a).im ∂s.val.1.measure) =
    (∫ a, regularizedResolventKernel z a ∂s.val.1.measure).im at he
  rw [← he]
  simp only [regularizedResolventKernel_im]

/-- Every valid anchored state gives a Nevanlinna function: the upper half-plane
is mapped into its closure. -/
theorem anchoredNevanlinna_im_nonneg (s : AnchoredCountingState)
    {z : ℂ} (hz : 0 < z.im) : 0 ≤ (anchoredNevanlinna s z).im := by
  rw [anchoredNevanlinna_im_eq s hz.ne']
  exact add_nonneg (mul_nonneg hz.le (anchoredLinearCoefficient_nonneg s))
    (integral_nonneg (fun a => div_nonneg hz.le (Complex.normSq_nonneg _)))

/-- Reconstruction preserves the exact value used to anchor the state. -/
@[simp] theorem anchoredNevanlinna_I (s : AnchoredCountingState) :
    anchoredNevanlinna s Complex.I = s.val.2 := by
  apply Complex.ext <;> simp [anchoredNevanlinna, Complex.I_sq]

/-- The linear coefficient is bounded by every positive imaginary value. -/
theorem mul_anchoredLinearCoefficient_le_im (s : AnchoredCountingState)
    {z : ℂ} (hz : 0 < z.im) :
    z.im * anchoredLinearCoefficient s ≤ (anchoredNevanlinna s z).im := by
  rw [anchoredNevanlinna_im_eq s hz.ne']
  exact le_add_of_nonneg_right
    (integral_nonneg (fun a => div_nonneg hz.le (Complex.normSq_nonneg _)))

/-- Reflection gives the corresponding lower-half-plane sign. -/
theorem anchoredNevanlinna_im_nonpos (s : AnchoredCountingState)
    {z : ℂ} (hz : z.im < 0) : (anchoredNevanlinna s z).im ≤ 0 := by
  have hh := anchoredNevanlinna_im_nonneg s (z := conj z) (by simpa using neg_pos.mpr hz)
  rw [anchoredNevanlinna_conj] at hh
  simpa only [Complex.conj_im, neg_nonneg] using hh

/-- If the anchor lies in the open upper half-plane, so does every reconstructed
value there. The positive Poisson kernel rules out boundary values. -/
theorem anchoredNevanlinna_im_pos (s : AnchoredCountingState)
    (hs : 0 < s.val.2.im) {z : ℂ} (hz : 0 < z.im) :
    0 < (anchoredNevanlinna s z).im := by
  have hb := anchoredLinearCoefficient_nonneg s
  by_cases hbp : 0 < anchoredLinearCoefficient s
  · exact lt_of_lt_of_le (mul_pos hz hbp) (mul_anchoredLinearCoefficient_le_im s hz)
  · have hbe : anchoredLinearCoefficient s = 0 := le_antisymm (le_of_not_gt hbp) hb
    have hwpos : 0 < ∫ a, nevanlinnaWeight a ∂s.val.1.measure := by
      dsimp [anchoredLinearCoefficient] at hbe
      linarith
    have hweight (a : ℝ) : 0 < nevanlinnaWeight a := by dsimp [nevanlinnaWeight]; positivity
    have hsupport : Function.support nevanlinnaWeight = Set.univ :=
      Set.eq_univ_of_forall (fun a => (hweight a).ne')
    have hmass : 0 < s.val.1.measure Set.univ := by
      simpa only [hsupport] using
        (integral_pos_iff_support_of_nonneg nevanlinnaWeight_nonneg s.integrable_weight).mp hwpos
    have hpi (a : ℝ) : 0 < z.im / Complex.normSq ((a : ℂ) - z) :=
      div_pos hz (Complex.normSq_pos.mpr (real_sub_offReal_ne_zero a hz.ne'))
    have hpisupport : Function.support (fun a : ℝ => z.im / Complex.normSq ((a : ℂ) - z)) = Set.univ :=
      Set.eq_univ_of_forall (fun a => (hpi a).ne')
    have hi : Integrable (fun a : ℝ => z.im / Complex.normSq ((a : ℂ) - z)) s.val.1.measure := by
      have hh := (integrable_regularizedResolventKernel s hz.ne').im
      change Integrable (fun a => (regularizedResolventKernel z a).im) s.val.1.measure at hh
      simpa only [regularizedResolventKernel_im] using hh
    have hipos : 0 < ∫ a, z.im / Complex.normSq ((a : ℂ) - z) ∂s.val.1.measure :=
      (integral_pos_iff_support_of_nonneg (fun a => (hpi a).le) hi).mpr (by simpa only [hpisupport] using hmass)
    rw [anchoredNevanlinna_im_eq s hz.ne', hbe, mul_zero, zero_add]
    exact hipos

end BourgadeHuang
