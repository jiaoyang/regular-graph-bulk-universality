import GeneralizedBulk.Spectral.TreeCavityAlgebra

/-! Existence and uniqueness of the actual small upper-half-plane tree cavity
root. Algebraic closedness is used only to construct the two quadratic roots. -/
noncomputable section
namespace GeneralizedBulk.KestenMcKay

theorem quadratic_cavity_roots (d : ℝ) (hd : 3 ≤ d) (z : ℂ) :
    ∃ g h : ℂ, IsCavityRoot d z g ∧ IsCavityRoot d z h ∧ ((d - 1 : ℝ) : ℂ) * g * h = 1 := by
  let q : ℂ := ((d - 1 : ℝ) : ℂ)
  have hq : q ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith : d - 1 ≠ 0)
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (z ^ 2 - 4 * q) (by norm_num : 0 < (2 : ℕ))
  refine ⟨(-z + s) / (2 * q), (-z - s) / (2 * q), ?_, ?_, ?_⟩
  · unfold IsCavityRoot
    change q * ((-z + s) / (2 * q)) ^ 2 + z * ((-z + s) / (2 * q)) + 1 = 0
    field_simp [hq]
    linear_combination (2 * q ^ 2) * hs
  · unfold IsCavityRoot
    change q * ((-z - s) / (2 * q)) ^ 2 + z * ((-z - s) / (2 * q)) + 1 = 0
    field_simp [hq]
    linear_combination (2 * q ^ 2) * hs
  · change q * ((-z + s) / (2 * q)) * ((-z - s) / (2 * q)) = 1
    field_simp [hq]
    linear_combination -q * hs

theorem cavity_roots_normalized_norm_product (d : ℝ) (g h : ℂ)
    (hprod : ((d - 1 : ℝ) : ℂ) * g * h = 1) :
    ((d - 1) * Complex.normSq g) * ((d - 1) * Complex.normSq h) = 1 := by
  have hh := congrArg Complex.normSq hprod
  simp only [Complex.normSq_mul, Complex.normSq_ofReal, map_one] at hh
  nlinarith [hh]

/-- There is an actual small quadratic root for every upper-half-plane point. -/
theorem exists_small_cavityRoot (d : ℝ) (hd : 3 ≤ d) (z : ℂ) (hz : 0 < z.im) :
    ∃ g : ℂ, IsCavityRoot d z g ∧ (d - 1) * Complex.normSq g < 1 := by
  obtain ⟨g, h, hg, hh, hp⟩ := quadratic_cavity_roots d hd z
  have hn := cavity_roots_normalized_norm_product d g h hp
  by_cases hs : (d - 1) * Complex.normSq g < 1
  · exact ⟨g, hg, hs⟩
  · have hlarge : 1 < (d - 1) * Complex.normSq g :=
      lt_of_le_of_ne (le_of_not_gt hs) (Ne.symm (hg.not_critical_circle hz))
    refine ⟨h, hh, ?_⟩
    have hnonneg : 0 ≤ (d - 1) * Complex.normSq h := mul_nonneg (by linarith) (Complex.normSq_nonneg h)
    nlinarith

/-- The small root is unique, independently of how the quadratic roots were
constructed. -/
theorem small_cavityRoot_unique (d : ℝ) (hd : 3 ≤ d) (z g h : ℂ)
    (hg : IsCavityRoot d z g) (hh : IsCavityRoot d z h)
    (hgs : (d - 1) * Complex.normSq g < 1) (hhs : (d - 1) * Complex.normSq h < 1) : g = h := by
  by_contra hne
  have hp := cavity_roots_normalized_norm_product d g h (hg.product_of_ne hh hne)
  have hgn : 0 ≤ (d - 1) * Complex.normSq g := mul_nonneg (by linarith) (Complex.normSq_nonneg g)
  have hhn : 0 ≤ (d - 1) * Complex.normSq h := mul_nonneg (by linarith) (Complex.normSq_nonneg h)
  have hm := mul_le_mul_of_nonneg_right hgs.le hhn
  have hb : ((d - 1) * Complex.normSq g) * ((d - 1) * Complex.normSq h) < 1 :=
    hm.trans_lt (by simpa only [one_mul] using hhs)
  rw [hp] at hb
  exact lt_irrefl 1 hb

end GeneralizedBulk.KestenMcKay
