import GeneralizedBulk.Spectral.KestenMcKayQuantile

/-! An explicit quadrature bound for actual equal-mass quantile cells. The
weaker Lipschitz error suffices for polynomial mesoscopic rates. -/
noncomputable section
open scoped BigOperators
open Set MeasureTheory
namespace GeneralizedBulk.Spectral

theorem quantile_cell_error (rho f : ℝ → ℝ) (a b L N : ℝ) (hab : a ≤ b)
    (hN : 0 < N) (hL : 0 ≤ L) (hrho : ContinuousOn rho (Icc a b))
    (hrho0 : ∀ x ∈ Icc a b, 0 ≤ rho x) (hf : ContinuousOn f (Icc a b))
    (hLip : ∀ x ∈ Icc a b, |f x - f a| ≤ L * |x - a|)
    (hmass : (∫ x in a..b, rho x) = 1 / N) :
    |(∫ x in a..b, f x * rho x) - f a / N| ≤ L * (b - a) / N := by
  have hwidth : 0 ≤ b - a := sub_nonneg.mpr hab
  have hi : IntervalIntegrable rho volume a b := hrho.intervalIntegrable_of_Icc hab
  have hiF : IntervalIntegrable (fun x => f x * rho x) volume a b := (hf.mul hrho).intervalIntegrable_of_Icc hab
  have hid : (∫ x in a..b, (f x - f a) * rho x) = (∫ x in a..b, f x * rho x) - f a / N := by
    simp_rw [sub_mul]
    rw [intervalIntegral.integral_sub hiF (hi.const_mul (f a)), intervalIntegral.integral_const_mul, hmass]
    ring
  have hdom : ∀ᵐ x ∂volume.restrict (uIoc a b), ‖(f x - f a) * rho x‖ ≤ L * (b - a) * rho x := by
    apply (ae_restrict_iff' measurableSet_uIoc).mpr
    apply ae_of_all
    intro x hx
    rw [uIoc_of_le hab] at hx
    have hx' : x ∈ Icc a b := ⟨hx.1.le, hx.2⟩
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hrho0 x hx')]
    apply mul_le_mul_of_nonneg_right _ (hrho0 x hx')
    have hxa : |x - a| ≤ b - a := by
      rw [abs_of_nonneg (sub_nonneg.mpr hx'.1)]
      linarith [hx'.2]
    exact (hLip x hx').trans (mul_le_mul_of_nonneg_left hxa hL)
  have hh := intervalIntegral.norm_integral_le_of_norm_le hdom (hi.const_mul (L * (b - a)))
  rw [intervalIntegral.integral_const_mul, hmass, abs_of_nonneg (by positivity : 0 ≤ L * (b - a) * (1 / N)),
    Real.norm_eq_abs, hid] at hh
  simpa only [mul_one_div] using hh

/-- Summing the cell errors telescopes their widths, giving the full
support-length/N quadrature error rather than a mesh-size assumption. -/
theorem quantile_quadrature (rho f : ℝ → ℝ) (q : ℕ → ℝ) (hq : Monotone q)
    (N : ℕ) (hN : 0 < N) (L : ℝ) (hL : 0 ≤ L)
    (hrho : ContinuousOn rho (Icc (q 0) (q N)))
    (hrho0 : ∀ x ∈ Icc (q 0) (q N), 0 ≤ rho x)
    (hf : ContinuousOn f (Icc (q 0) (q N)))
    (hLip : ∀ x ∈ Icc (q 0) (q N), ∀ y ∈ Icc (q 0) (q N), |f x - f y| ≤ L * |x - y|)
    (hmass : ∀ j < N, (∫ x in q j..q (j + 1), rho x) = 1 / (N : ℝ)) :
    |(∫ x in (q 0)..(q N), f x * rho x) - (∑ j ∈ Finset.range N, f (q j)) / (N : ℝ)| ≤
      L * (q N - q 0) / N := by
  have hsub (j : ℕ) (hj : j < N) : Icc (q j) (q (j + 1)) ⊆ Icc (q 0) (q N) :=
    Icc_subset_Icc (hq (Nat.zero_le j)) (hq (by omega))
  have hcell (j : ℕ) (hj : j < N) :
      |(∫ x in q j..q (j + 1), f x * rho x) - f (q j) / (N : ℝ)| ≤ L * (q (j + 1) - q j) / N := by
    exact quantile_cell_error rho f _ _ L N (hq (Nat.le_succ j)) (Nat.cast_pos.mpr hN) hL
      (hrho.mono (hsub j hj)) (fun x hx => hrho0 x (hsub j hj hx)) (hf.mono (hsub j hj))
      (fun x hx => hLip x (hsub j hj hx) (q j) ⟨hq (Nat.zero_le j), hq (by omega)⟩) (hmass j hj)
  have hs := intervalIntegral.sum_integral_adjacent_intervals (n := N) (μ := volume) (f := fun x => f x * rho x)
    (fun j hj => ((hf.mul hrho).mono (hsub j hj)).intervalIntegrable_of_Icc (hq (Nat.le_succ j)))
  calc
    _ = |∑ j ∈ Finset.range N, ((∫ x in q j..q (j + 1), f x * rho x) - f (q j) / (N : ℝ))| := by
      rw [Finset.sum_sub_distrib, hs, Finset.sum_div]
    _ ≤ ∑ j ∈ Finset.range N, |(∫ x in q j..q (j + 1), f x * rho x) - f (q j) / (N : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range N, L * (q (j + 1) - q j) / (N : ℝ) :=
      Finset.sum_le_sum (fun j hj => hcell j (Finset.mem_range.mp hj))
    _ = _ := by
      rw [← Finset.sum_div, ← Finset.mul_sum, Finset.sum_range_sub]

/-- Right endpoint version, retaining an explicit factor two. -/
theorem quantile_quadrature_right (rho f : ℝ → ℝ) (q : ℕ → ℝ) (hq : Monotone q)
    (N : ℕ) (hN : 0 < N) (L : ℝ) (hL : 0 ≤ L)
    (hrho : ContinuousOn rho (Icc (q 0) (q N)))
    (hrho0 : ∀ x ∈ Icc (q 0) (q N), 0 ≤ rho x)
    (hf : ContinuousOn f (Icc (q 0) (q N)))
    (hLip : ∀ x ∈ Icc (q 0) (q N), ∀ y ∈ Icc (q 0) (q N), |f x - f y| ≤ L * |x - y|)
    (hmass : ∀ j < N, (∫ x in q j..q (j + 1), rho x) = 1 / (N : ℝ)) :
    |(∫ x in (q 0)..(q N), f x * rho x) - (∑ j ∈ Finset.range N, f (q (j + 1))) / (N : ℝ)| ≤
      2 * L * (q N - q 0) / N := by
  have hh := quantile_quadrature rho f q hq N hN L hL hrho hrho0 hf hLip hmass
  have hs : (∑ j ∈ Finset.range N, f (q (j + 1))) - (∑ j ∈ Finset.range N, f (q j)) = f (q N) - f (q 0) := by
    have hl := Finset.sum_range_succ' (fun j => f (q j)) N
    have hr := Finset.sum_range_succ (fun j => f (q j)) N
    linarith
  have ht := hLip (q N) ⟨hq (Nat.zero_le N), le_rfl⟩ (q 0) ⟨le_rfl, hq (Nat.zero_le N)⟩
  rw [abs_of_nonneg (sub_nonneg.mpr (hq (Nat.zero_le N)))] at ht
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hend : |(∑ j ∈ Finset.range N, f (q j)) / (N : ℝ) -
      (∑ j ∈ Finset.range N, f (q (j + 1))) / (N : ℝ)| ≤ L * (q N - q 0) / N := by
    rw [← sub_div, abs_div, abs_sub_comm, abs_of_pos hn, hs]
    exact div_le_div_of_nonneg_right ht hn.le
  have htri := abs_sub_le (∫ x in (q 0)..(q N), f x * rho x)
    ((∑ j ∈ Finset.range N, f (q j)) / (N : ℝ))
    ((∑ j ∈ Finset.range N, f (q (j + 1))) / (N : ℝ))
  exact htri.trans ((add_le_add hh hend).trans_eq (by ring))

end GeneralizedBulk.Spectral
