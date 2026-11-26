import GeneralizedBulk.Spectral.TreeStarUniform
import GeneralizedBulk.Graph.ResolventCovariance

/-! The actual HY local-star approximation implies the normalized Gaussian
wave covariance comparison, using the proved actual tree boundary limit. -/
noncomputable section
namespace GeneralizedBulk.External.RegularSpectralData
open Set MeasureTheory GeneralizedBulk.KestenMcKay
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

theorem HYLocalStar_covariance_boundary_uniform {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : 3 ≤ (d : ℝ)) (K : Set ℝ) (hK : IsCompact K)
    (hbulk : ∀ E ∈ K, E ^ 2 < 4 * ((d : ℝ) - 1)) (c0 : ℝ)
    (H : HYLocalStarInput D P K c0 (treeGreenStar d hd)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, H.events.threshold ≤ n → ∀ ω ∈ H.events.good n,
      ∀ root : Fin (N n), root ∉ H.badRoots n ω → ∀ E ∈ K, ∀ i j : Fin (d + 1),
      let eta := (N n : ℝ) ^ (-c0)
      let vertex : Fin (d + 1) → Fin (N n) := Fin.cases root (D.neighbor n ω root)
      let sigma := (diagonalBoundary d E).im
      |D.resolventCovariance n ω E eta sigma (vertex i) (vertex j) - starWaveCovariance d E i j| ≤
        ((N n : ℝ) ^ (-H.local_exponent) + C * eta) / sigma := by
  obtain ⟨C, hC, hu⟩ := treeGreenStar_height_uniform d hd K hK hbulk
  refine ⟨C, hC, ?_⟩
  intro n hn ω hω root hroot E hE i j
  let eta := (N n : ℝ) ^ (-c0)
  let vertex : Fin (d + 1) → Fin (N n) := Fin.cases root (D.neighbor n ω root)
  let sigma := (diagonalBoundary d E).im
  let z := (E : ℂ) + (eta : ℂ) * Complex.I
  have heta : 0 < eta := Real.rpow_pos_of_pos (Nat.cast_pos.mpr (D.size_pos n)) _
  have hsigma : 0 < sigma := diagonalBoundary_im_pos d E hd (hbulk E hE)
  have hz : (⟨E, eta⟩ : ℂ) = z := by apply Complex.ext <;> simp [z]
  have ha := H.approximation n hn ω hω root hroot E hE i j
  change ‖D.resolvent n ω z (vertex i) (vertex j) - treeGreenStar d hd z i j‖ ≤ _ at ha
  have hb := hu E hE eta heta i j
  change ‖treeGreenStar d hd z i j - boundaryStar d E i j‖ ≤ C * eta at hb
  have htriangle : ‖D.resolvent n ω z (vertex i) (vertex j) - boundaryStar d E i j‖ ≤
      ‖D.resolvent n ω z (vertex i) (vertex j) - treeGreenStar d hd z i j‖ +
        ‖treeGreenStar d hd z i j - boundaryStar d E i j‖ := by
    simpa only [dist_eq_norm] using dist_triangle (D.resolvent n ω z (vertex i) (vertex j))
      (treeGreenStar d hd z i j) (boundaryStar d E i j)
  have htotal := htriangle.trans (add_le_add ha hb)
  have hIm : |(D.resolvent n ω z (vertex i) (vertex j)).im - sigma * starWaveCovariance d E i j| ≤
      (N n : ℝ) ^ (-H.local_exponent) + C * eta := by
    rw [← boundaryStar_im d hd E (hbulk E hE)]
    exact (Complex.abs_im_le_norm (D.resolvent n ω z (vertex i) (vertex j) - boundaryStar d E i j)).trans htotal
  change |D.resolventCovariance n ω E eta sigma (vertex i) (vertex j) - starWaveCovariance d E i j| ≤ _
  rw [D.resolventCovariance_entry n ω E eta sigma heta, hz]
  have hid : (D.resolvent n ω z (vertex i) (vertex j)).im / sigma - starWaveCovariance d E i j =
      ((D.resolvent n ω z (vertex i) (vertex j)).im - sigma * starWaveCovariance d E i j) / sigma := by field_simp
  rw [hid, abs_div, abs_of_pos hsigma]
  exact div_le_div_of_nonneg_right hIm hsigma.le

/-- Good-root genuine resolvent entries have a fixed uniform bound up to the
literal HY approximation error; no real-part bound is postulated. -/
theorem HYLocalStar_resolvent_entry_norm {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : 3 ≤ (d : ℝ)) (K : Set ℝ) (c0 : ℝ)
    (H : HYLocalStarInput D P K c0 (treeGreenStar d hd))
    (n : ℕ) (hn : H.events.threshold ≤ n) (ω : Ω) (hω : ω ∈ H.events.good n)
    (root : Fin (N n)) (hroot : root ∉ H.badRoots n ω) (E : ℝ) (hE : E ∈ K) (i j : Fin (d + 1)) :
    let eta := (N n : ℝ) ^ (-c0)
    let vertex : Fin (d + 1) → Fin (N n) := Fin.cases root (D.neighbor n ω root)
    ‖D.resolvent n ω ((E : ℂ) + (eta : ℂ) * Complex.I) (vertex i) (vertex j)‖ ≤
      2 + (N n : ℝ) ^ (-H.local_exponent) := by
  let eta := (N n : ℝ) ^ (-c0)
  let vertex : Fin (d + 1) → Fin (N n) := Fin.cases root (D.neighbor n ω root)
  let z := (E : ℂ) + (eta : ℂ) * Complex.I
  have heta : 0 < eta := Real.rpow_pos_of_pos (Nat.cast_pos.mpr (D.size_pos n)) _
  have hz : 0 < z.im := by simpa [z] using heta
  have ha := H.approximation n hn ω hω root hroot E hE i j
  have hb := treeGreenStar_norm_bound d hd z hz i j
  have ht := norm_sub_norm_le (D.resolvent n ω z (vertex i) (vertex j)) (treeGreenStar d hd z i j)
  change ‖D.resolvent n ω z (vertex i) (vertex j) - treeGreenStar d hd z i j‖ ≤ _ at ha
  change ‖D.resolvent n ω z (vertex i) (vertex j)‖ ≤ _
  linarith

/-- Eliminating the normalization by its proved compact-bulk positive floor
yields the standard actual local covariance rate. -/
theorem HYLocalStar_covariance_rate_uniform {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : 3 ≤ (d : ℝ)) (K : Set ℝ) (hK : IsCompact K)
    (hbulk : ∀ E ∈ K, E ^ 2 < 4 * ((d : ℝ) - 1)) (c0 : ℝ)
    (H : HYLocalStarInput D P K c0 (treeGreenStar d hd)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, H.events.threshold ≤ n → ∀ ω ∈ H.events.good n,
      ∀ root : Fin (N n), root ∉ H.badRoots n ω → ∀ E ∈ K, ∀ i j : Fin (d + 1),
      let eta := (N n : ℝ) ^ (-c0)
      let vertex : Fin (d + 1) → Fin (N n) := Fin.cases root (D.neighbor n ω root)
      let sigma := (diagonalBoundary d E).im
      |D.resolventCovariance n ω E eta sigma (vertex i) (vertex j) - starWaveCovariance d E i j| ≤
        C * ((N n : ℝ) ^ (-H.local_exponent) + eta) := by
  obtain ⟨C0, hC0, hu⟩ := D.HYLocalStar_covariance_boundary_uniform hd K hK hbulk c0 H
  obtain ⟨c, hc, hfloor⟩ := diagonalBoundary_im_uniform d hd K hK hbulk
  refine ⟨(1 + C0) / c, by positivity, ?_⟩
  intro n hn ω hω root hroot E hE i j
  have hh := hu n hn ω hω root hroot E hE i j
  let eta := (N n : ℝ) ^ (-c0)
  let r := (N n : ℝ) ^ (-H.local_exponent)
  have he : 0 ≤ eta := (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (D.size_pos n)) _).le
  have hr : 0 ≤ r := (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (D.size_pos n)) _).le
  have hn0 : 0 ≤ r + C0 * eta := by positivity
  have hn1 : r + C0 * eta ≤ (1 + C0) * (r + eta) := by nlinarith [mul_nonneg hC0.le hr]
  exact hh.trans ((div_le_div_of_nonneg_left hn0 hc (hfloor E hE).1).trans
    (by convert div_le_div_of_nonneg_right hn1 hc.le using 1 <;> ring))

end GeneralizedBulk.External.RegularSpectralData
