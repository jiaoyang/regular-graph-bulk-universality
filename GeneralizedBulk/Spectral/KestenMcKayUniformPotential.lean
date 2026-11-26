import GeneralizedBulk.Spectral.KestenMcKayBulkPotential

/-! Compact-bulk uniform constants in the proved Kesten–McKay potential
comparison. -/
noncomputable section
open Set
namespace GeneralizedBulk.KestenMcKay

theorem bulkHeightScale_eq (d E : ℝ) (hd : 3 ≤ d) :
    bulkHeightScale d E = Real.sqrt (discriminant d E) / 2 := by
  dsimp [bulkHeightScale, cavityBoundary]
  have hq : d - 1 ≠ 0 := by linarith
  field_simp
  <;> ring

theorem continuous_bulkHeightScale (d : ℝ) (hd : 3 ≤ d) : Continuous (bulkHeightScale d) := by
  have hf : bulkHeightScale d = fun E => Real.sqrt (discriminant d E) / 2 := funext (fun E => bulkHeightScale_eq d E hd)
  rw [hf]
  unfold discriminant
  fun_prop

/-- Both the height threshold and O(eta) constant are genuinely uniform on
any compact subset of the open bulk. -/
theorem regularizedPotential_bulk_uniform (d : ℝ) (hd : 3 ≤ d)
    (K : Set ℝ) (hK : IsCompact K) (hbulk : ∀ E ∈ K, E ^ 2 < 4 * (d - 1)) :
    ∃ eta0 : ℝ, 0 < eta0 ∧ ∃ C : ℝ, 0 < C ∧ ∀ E ∈ K, ∀ eta : ℝ,
      0 < eta → eta ≤ eta0 → |regularizedPotential d E eta - bulkPotential d E| ≤ C * eta := by
  by_cases hne : K.Nonempty
  · obtain ⟨E0, hE0, hmin⟩ := hK.exists_isMinOn hne (continuous_bulkHeightScale d hd).continuousOn
    let kappa := bulkHeightScale d E0
    have hk : 0 < kappa := bulkHeightScale_pos d E0 hd (hbulk E0 hE0)
    have hdpos : 0 < d := by linarith
    have hr : 0 < radius d := radius_pos d hd
    refine ⟨kappa, hk, d / kappa + radius d / kappa ^ 2, by positivity, ?_⟩
    intro E hE eta heta heta'
    have hb : 0 < bulkHeightScale d E := bulkHeightScale_pos d E hd (hbulk E hE)
    have hkb : kappa ≤ bulkHeightScale d E := hmin hE
    have ha : |E| ≤ radius d := by
      apply (sq_le_sq₀ (abs_nonneg E) hr.le).mp
      rw [sq_abs, radius_sq d hd]
      exact (hbulk E hE).le
    have hsq : kappa ^ 2 ≤ bulkHeightScale d E ^ 2 := (sq_le_sq₀ hk.le hb.le).mpr hkb
    have hc : d / bulkHeightScale d E + |E| / bulkHeightScale d E ^ 2 ≤ d / kappa + radius d / kappa ^ 2 := by
      apply add_le_add (div_le_div_of_nonneg_left hdpos.le hk hkb)
      exact (div_le_div_of_nonneg_right ha (sq_nonneg _)).trans
        (div_le_div_of_nonneg_left hr.le (sq_pos_of_pos hk) hsq)
    exact (regularizedPotential_bulk_error d E hd (hbulk E hE) eta heta (heta'.trans hkb)).trans
      (mul_le_mul_of_nonneg_right hc heta.le)
  · refine ⟨1, by norm_num, 1, by norm_num, ?_⟩
    intro E hE
    exact (hne ⟨E, hE⟩).elim

end GeneralizedBulk.KestenMcKay
