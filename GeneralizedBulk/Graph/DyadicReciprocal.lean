import GeneralizedBulk.Graph.SpectralCompression

/-!
# The HY reciprocal-distance bound by an explicit finite dyadic majorant

Only mesoscopic eigenvalue counts are used. Each annulus contributes a fixed
constant; the central interval retains the exact factor `h / eta`.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GeneralizedBulk.Graph
open External.RegularSpectralData

def dyadicRadius (h : ℝ) (k : ℕ) : ℝ := (2 : ℝ) ^ k * h

@[simp] theorem dyadicRadius_zero (h : ℝ) : dyadicRadius h 0 = h := by simp [dyadicRadius]

theorem dyadicRadius_pos {h : ℝ} (hh : 0 < h) (k : ℕ) : 0 < dyadicRadius h k := by
  dsimp [dyadicRadius]; positivity

theorem dyadicRadius_succ (h : ℝ) (k : ℕ) : dyadicRadius h (k + 1) = 2 * dyadicRadius h k := by
  simp only [dyadicRadius, pow_succ]; ring

theorem inverse_spectral_coefficient_le_height (x E eta : ℝ) (heta : 0 < eta) :
    ‖((x : ℂ) - spectralParameter E eta)⁻¹‖ ≤ eta⁻¹ := by
  have hn : eta ≤ ‖(x : ℂ) - spectralParameter E eta‖ := by
    simpa only [spectralParameter, Complex.sub_im, Complex.ofReal_im, Complex.add_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero,
      add_zero, zero_add, zero_sub, abs_neg, abs_of_pos heta] using
      Complex.abs_im_le_norm ((x : ℂ) - spectralParameter E eta)
  rw [norm_inv]
  exact (inv_le_inv₀ (heta.trans_le hn) heta).mpr hn

/-- Pointwise finite dyadic majorant. It deliberately uses nested intervals,
so no extraction or measurable choice of an annulus is required. -/
theorem inverse_spectral_coefficient_le_dyadic (x E eta h : ℝ)
    (heta : 0 < eta) (hh : 0 < h) (m : ℕ) (hx : |x - E| ≤ dyadicRadius h m) :
    ‖((x : ℂ) - spectralParameter E eta)⁻¹‖ ≤
      (if |x - E| ≤ h then eta⁻¹ else 0) +
        ∑ k ∈ Finset.range m, if |x - E| ≤ dyadicRadius h (k + 1) then (dyadicRadius h k)⁻¹ else 0 := by
  induction m with
  | zero =>
      simp only [dyadicRadius_zero] at hx
      simpa only [if_pos hx, Finset.range_zero, Finset.sum_empty, add_zero] using
        inverse_spectral_coefficient_le_height x E eta heta
  | succ m ih =>
      rw [Finset.sum_range_succ]
      by_cases hprev : |x - E| ≤ dyadicRadius h m
      · have hp := ih hprev
        have hlast : 0 ≤ if |x - E| ≤ dyadicRadius h (m + 1) then (dyadicRadius h m)⁻¹ else 0 := by
          rw [if_pos hx]
          exact inv_nonneg.mpr (dyadicRadius_pos hh _).le
        linarith
      · have hb := inverse_spectral_coefficient_le_of_gap x E eta (dyadicRadius h m)
          (dyadicRadius_pos hh m) (le_of_lt (lt_of_not_ge hprev))
        rw [if_pos hx]
        have hc : 0 ≤ if |x - E| ≤ h then eta⁻¹ else 0 := by split_ifs <;> positivity
        have hs : 0 ≤ ∑ k ∈ Finset.range m,
            if |x - E| ≤ dyadicRadius h (k + 1) then (dyadicRadius h k)⁻¹ else 0 := by
          apply Finset.sum_nonneg
          intro k hk
          split_ifs
          · exact inv_nonneg.mpr (dyadicRadius_pos hh _).le
          · exact le_refl _
        linarith

end GeneralizedBulk.Graph

namespace GeneralizedBulk.External.RegularSpectralData
open Graph
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

theorem sum_window_indicator (E R b : ℝ) :
    (∑ k : Fin (N n), if |D.eigenvalue n ω k - E| ≤ R then b else 0) =
      b * (D.eigenvalueWindowCount n ω E R : ℝ) := by
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, eigenvalueWindowCount, eigenvalueWindow]
  ring

/-- Exact finite normalized reciprocal-distance estimate from counts at the
chosen dyadic radii. The selected window may be any subset of the last ball. -/
theorem normalized_reciprocal_sum_le_dyadic
    (s : Finset (Fin (N n))) (E eta h C : ℝ) (heta : 0 < eta) (hh : 0 < h)
    (hC : 0 ≤ C) (m : ℕ)
    (hs : ∀ k ∈ s, |D.eigenvalue n ω k - E| ≤ dyadicRadius h m)
    (hcount : ∀ k : ℕ, k ≤ m → (D.eigenvalueWindowCount n ω E (dyadicRadius h k) : ℝ) ≤
      2 * (N n : ℝ) * C * dyadicRadius h k) :
    (∑ k ∈ s, ‖(N n : ℂ)⁻¹ * ((D.eigenvalue n ω k : ℂ) - spectralParameter E eta)⁻¹‖) ≤
      2 * C * h / eta + 4 * C * m := by
  let W (k : Fin (N n)) := (if |D.eigenvalue n ω k - E| ≤ h then eta⁻¹ else 0) +
    ∑ j ∈ Finset.range m, if |D.eigenvalue n ω k - E| ≤ dyadicRadius h (j + 1) then (dyadicRadius h j)⁻¹ else 0
  have hW (k : Fin (N n)) : 0 ≤ W k := by
    apply add_nonneg
    · split_ifs <;> positivity
    · apply Finset.sum_nonneg
      intro j hj
      split_ifs
      · exact inv_nonneg.mpr (dyadicRadius_pos hh _).le
      · exact le_refl _
  have hraw : (∑ k ∈ s, ‖((D.eigenvalue n ω k : ℂ) - spectralParameter E eta)⁻¹‖) ≤
      2 * (N n : ℝ) * C * h / eta + 4 * (N n : ℝ) * C * m := by
    calc
      _ ≤ ∑ k ∈ s, W k := Finset.sum_le_sum (fun k hk =>
        inverse_spectral_coefficient_le_dyadic _ E eta h heta hh m (hs k hk))
      _ ≤ ∑ k, W k := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) (fun k _ _ => hW k)
      _ = eta⁻¹ * (D.eigenvalueWindowCount n ω E h : ℝ) +
          ∑ j ∈ Finset.range m, (dyadicRadius h j)⁻¹ *
            (D.eigenvalueWindowCount n ω E (dyadicRadius h (j + 1)) : ℝ) := by
        simp only [W, Finset.sum_add_distrib, D.sum_window_indicator n ω]
        rw [Finset.sum_comm]
        simp_rw [D.sum_window_indicator n ω]
      _ ≤ eta⁻¹ * (2 * (N n : ℝ) * C * h) +
          ∑ j ∈ Finset.range m, (dyadicRadius h j)⁻¹ *
            (2 * (N n : ℝ) * C * dyadicRadius h (j + 1)) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (by simpa only [dyadicRadius_zero] using hcount 0 (Nat.zero_le m)) (by positivity)
        · apply Finset.sum_le_sum
          intro j hj
          exact mul_le_mul_of_nonneg_left (hcount (j + 1) (Finset.mem_range.mp hj))
            (inv_nonneg.mpr (dyadicRadius_pos hh j).le)
      _ = _ := by
        have heach (j : ℕ) : (dyadicRadius h j)⁻¹ *
            (2 * (N n : ℝ) * C * dyadicRadius h (j + 1)) = 4 * (N n : ℝ) * C := by
          rw [dyadicRadius_succ]
          field_simp [ne_of_gt (dyadicRadius_pos hh j)]
          ring
        simp_rw [heach]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
  have hN : (N n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (D.size_pos n))
  have hscaled := mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr (Nat.cast_nonneg (N n)))
  have hlhs : (∑ k ∈ s, ‖(N n : ℂ)⁻¹ * ((D.eigenvalue n ω k : ℂ) - spectralParameter E eta)⁻¹‖) =
      (N n : ℝ)⁻¹ * ∑ k ∈ s, ‖((D.eigenvalue n ω k : ℂ) - spectralParameter E eta)⁻¹‖ := by
    simp only [norm_mul, norm_inv, Complex.norm_natCast, Finset.mul_sum]
  rw [hlhs]
  convert hscaled using 1 <;> field_simp <;> ring

/-- HY gives the required cumulative counts at every radius above the
mesoscopic cutoff; radii larger than one use the trivial total-count bound. -/
theorem normalized_reciprocal_sum_le_dyadic_of_HY
    {P : Measure Ω} [IsProbabilityMeasure P] {K : Set ℝ} {alpha : ℝ}
    (H : HYMesoscopicInput D P K alpha) (hn : H.events.threshold ≤ n) (hω : ω ∈ H.events.good n)
    (s : Finset (Fin (N n))) (E eta h : ℝ) (hE : E ∈ K) (heta : 0 < eta) (hh : 0 < h)
    (hmeso : (N n : ℝ) ^ (-1 + alpha) ≤ h) (m : ℕ)
    (hs : ∀ k ∈ s, |D.eigenvalue n ω k - E| ≤ dyadicRadius h m) :
    (∑ k ∈ s, ‖(N n : ℂ)⁻¹ * ((D.eigenvalue n ω k : ℂ) - spectralParameter E eta)⁻¹‖) ≤
      2 * max H.events.constant 1 * h / eta + 4 * max H.events.constant 1 * m := by
  let C := max H.events.constant 1
  have hC : 1 ≤ C := le_max_right _ _
  apply D.normalized_reciprocal_sum_le_dyadic n ω s E eta h C heta hh (by linarith) m hs
  intro k hk
  have hr : 0 < dyadicRadius h k := dyadicRadius_pos hh k
  have hrh : h ≤ dyadicRadius h k := by
    have hp : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    simpa only [dyadicRadius, one_mul] using mul_le_mul_of_nonneg_right hp hh.le
  by_cases hupper : dyadicRadius h k ≤ 1
  · exact (D.eigenvalueWindowCount_le_of_HY n ω H hn hω E hE _ hr (hmeso.trans hrh) hupper).trans
      (by
        have hp := mul_le_mul_of_nonneg_left (le_max_left H.events.constant 1)
          (show 0 ≤ 2 * (N n : ℝ) * dyadicRadius h k by positivity)
        simpa only [mul_assoc, mul_left_comm, mul_comm] using hp)
  · have hc : (D.eigenvalueWindowCount n ω E (dyadicRadius h k) : ℝ) ≤ N n := by
      have hc : (D.eigenvalueWindow n ω E (dyadicRadius h k)).card ≤ (N n) := by
        exact (Finset.card_le_card (Finset.filter_subset _ Finset.univ)).trans_eq (by simp)
      exact_mod_cast hc
    have hNc : 0 ≤ (N n : ℝ) := Nat.cast_nonneg _
    have hCr : 1 ≤ C * dyadicRadius h k := by nlinarith [lt_of_not_ge hupper]
    exact hc.trans (by nlinarith)

end GeneralizedBulk.External.RegularSpectralData
