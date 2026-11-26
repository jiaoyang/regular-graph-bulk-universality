import GeneralizedBulk.Graph.ProposalMarks

/-! Centered finite-uniform second moments and a deterministic exceptional set. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GeneralizedBulk.Graph

variable {A : Type*} [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]

theorem integrable_finiteUniform_complex (f : A → ℂ) : Integrable f (finiteUniform A) := by
  apply (integrable_finset_sum_measure.mpr (fun _ _ => integrable_dirac)).smul_measure
  exact ENNReal.inv_ne_top.mpr (by exact_mod_cast (Fintype.card_ne_zero : Fintype.card A ≠ 0))

/-- Jensen's square estimate is proved directly from finite Cauchy--Schwarz. -/
theorem norm_finiteUniform_mean_sq_le (f : A → ℂ) :
    ‖∫ a, f a ∂finiteUniform A‖ ^ 2 ≤ ∫ a, ‖f a‖ ^ 2 ∂finiteUniform A := by
  rw [integral_finiteUniform_complex, integral_finiteUniform]
  have hcard : (Fintype.card A : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hnorm := (sq_le_sq₀ (norm_nonneg (∑ a, f a))
    (Finset.sum_nonneg (fun a _ => norm_nonneg (f a)))).mpr (norm_sum_le Finset.univ f)
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun a => ‖f a‖) (fun _ : A => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hCS
  have hh := mul_le_mul_of_nonneg_left (hnorm.trans hCS) (sq_nonneg (Fintype.card A : ℝ)⁻¹)
  change ‖(Fintype.card A : ℂ)⁻¹ * ∑ a, f a‖ ^ 2 ≤ _
  rw [norm_mul, mul_pow, norm_inv, Complex.norm_natCast]
  convert hh using 1 <;> field_simp <;> ring

/-- Centering at the actual finite mean costs at most four times a second
moment about any deterministic reference value. -/
theorem finiteUniform_centered_secondMoment_le (f : A → ℂ) (b : ℂ) :
    (∫ a, ‖f a - ∫ x, f x ∂finiteUniform A‖ ^ 2 ∂finiteUniform A) ≤
      4 * (∫ a, ‖f a - b‖ ^ 2 ∂finiteUniform A) := by
  letI := finiteUniform_isProbability A
  let m := ∫ x, f x ∂finiteUniform A
  have hmean : (∫ a, f a - b ∂finiteUniform A) = m - b := by
    rw [integral_sub (integrable_finiteUniform_complex f) (integrable_const b)]
    simp only [integral_const, measureReal_univ_eq_one, one_smul]
    rfl
  have hJ := norm_finiteUniform_mean_sq_le (fun a => f a - b)
  rw [hmean] at hJ
  have hpoint (a : A) : ‖f a - m‖ ^ 2 ≤ 2 * ‖f a - b‖ ^ 2 + 2 * ‖m - b‖ ^ 2 := by
    have heq : f a - m = (f a - b) - (m - b) := by ring
    rw [heq]
    have hs := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
      (norm_sub_le (f a - b) (m - b))
    nlinarith [sq_nonneg (‖f a - b‖ - ‖m - b‖)]
  have hf := integrable_finiteUniform_real (fun a => ‖f a - m‖ ^ 2)
  have hg := integrable_finiteUniform_real (fun a => ‖f a - b‖ ^ 2)
  have hc := integrable_const (μ := finiteUniform A) (2 * ‖m - b‖ ^ 2)
  have hi := integral_mono hf ((hg.const_mul 2).add hc) hpoint
  simp only [Pi.add_apply] at hi
  rw [integral_add (hg.const_mul 2) hc, integral_const_mul, integral_const,
    measureReal_univ_eq_one, one_smul] at hi
  linarith

/-- A function equal to a deterministic value outside an exceptional set has
centered variance controlled by the actual exceptional probability. -/
theorem finiteUniform_variance_le_exceptional_set
    (f : A → ℂ) (bad : Set A) (b : ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hgood : ∀ a, a ∉ bad → f a = b) (hbound : ∀ a, ‖f a - b‖ ≤ C) :
    (∫ a, ‖f a - ∫ x, f x ∂finiteUniform A‖ ^ 2 ∂finiteUniform A) ≤
      4 * C ^ 2 * (finiteUniform A).real bad := by
  letI := finiteUniform_isProbability A
  have hbad : MeasurableSet bad := Set.toFinite bad |>.measurableSet
  have hpoint (a : A) : ‖f a - b‖ ^ 2 ≤ bad.indicator (fun _ => C ^ 2) a := by
    by_cases ha : a ∈ bad
    · rw [Set.indicator_of_mem ha]
      exact (sq_le_sq₀ (norm_nonneg _) hC).mpr (hbound a)
    · rw [Set.indicator_of_not_mem ha, hgood a ha, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  have hp := integral_mono (integrable_finiteUniform_real (fun a => ‖f a - b‖ ^ 2))
    ((integrable_const _).indicator hbad) hpoint
  rw [integral_indicator hbad, setIntegral_const] at hp
  have hc := finiteUniform_centered_secondMoment_le f b
  simp only [smul_eq_mul] at hp
  nlinarith

/-- Uniform approximation survives actual centering and finite second
moments. A scalar error `delta` contributes at most `8 delta²` to the
variance comparison. -/
theorem finiteUniform_centered_variance_le_comparison
    (f g : A → ℂ) (delta : ℝ) (hdelta : 0 ≤ delta) (happrox : ∀ a, ‖f a - g a‖ ≤ delta) :
    (∫ a, ‖f a - ∫ x, f x ∂finiteUniform A‖ ^ 2 ∂finiteUniform A) ≤
      2 * (∫ a, ‖g a - ∫ x, g x ∂finiteUniform A‖ ^ 2 ∂finiteUniform A) + 8 * delta ^ 2 := by
  letI := finiteUniform_isProbability A
  let mf := ∫ x, f x ∂finiteUniform A
  let mg := ∫ x, g x ∂finiteUniform A
  let h := fun a => f a - g a
  have hmean : (∫ a, h a ∂finiteUniform A) = mf - mg :=
    integral_sub (integrable_finiteUniform_complex f) (integrable_finiteUniform_complex g)
  have hbounded : (∫ a, ‖h a‖ ^ 2 ∂finiteUniform A) ≤ delta ^ 2 := by
    have hp := integral_mono (integrable_finiteUniform_real (fun a => ‖h a‖ ^ 2))
      (integrable_const (μ := finiteUniform A) (delta ^ 2))
      (fun a => (sq_le_sq₀ (norm_nonneg _) hdelta).mpr (happrox a))
    simpa only [integral_const, measureReal_univ_eq_one, one_smul] using hp
  have hcenter := finiteUniform_centered_secondMoment_le h 0
  simp only [sub_zero] at hcenter
  have hdiff : (∫ a, ‖h a - (mf - mg)‖ ^ 2 ∂finiteUniform A) ≤ 4 * delta ^ 2 := by
    rw [hmean] at hcenter
    exact hcenter.trans (mul_le_mul_of_nonneg_left hbounded (by norm_num))
  have hpoint (a : A) : ‖f a - mf‖ ^ 2 ≤
      2 * ‖g a - mg‖ ^ 2 + 2 * ‖h a - (mf - mg)‖ ^ 2 := by
    have heq : f a - mf = (g a - mg) + (h a - (mf - mg)) := by dsimp [h]; ring
    rw [heq]
    have hn := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
      (norm_add_le (g a - mg) (h a - (mf - mg)))
    nlinarith [sq_nonneg (‖g a - mg‖ - ‖h a - (mf - mg)‖)]
  have hiG := integrable_finiteUniform_real (fun a => ‖g a - mg‖ ^ 2)
  have hiH := integrable_finiteUniform_real (fun a => ‖h a - (mf - mg)‖ ^ 2)
  have hp := integral_mono (integrable_finiteUniform_real (fun a => ‖f a - mf‖ ^ 2))
    ((hiG.const_mul 2).add (hiH.const_mul 2)) hpoint
  simp only [Pi.add_apply] at hp
  rw [integral_add (hiG.const_mul 2) (hiH.const_mul 2), integral_const_mul, integral_const_mul] at hp
  calc
    _ ≤ 2 * (∫ a, ‖g a - mg‖ ^ 2 ∂finiteUniform A) +
        2 * (∫ a, ‖h a - (mf - mg)‖ ^ 2 ∂finiteUniform A) := hp
    _ ≤ 2 * (∫ a, ‖g a - mg‖ ^ 2 ∂finiteUniform A) + 2 * (4 * delta ^ 2) :=
      add_le_add_left (mul_le_mul_of_nonneg_left hdiff (by norm_num : (0 : ℝ) ≤ 2)) _
    _ = _ := by ring

/-- A globally bounded observable which is constant on good samples has
small centered variance, even when the good set happens to be empty. -/
theorem finiteUniform_variance_le_bounded_exceptional_set
    (f : A → ℂ) (bad : Set A) (b : ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hgood : ∀ a, a ∉ bad → f a = b) (hbound : ∀ a, ‖f a‖ ≤ M) :
    (∫ a, ‖f a - ∫ x, f x ∂finiteUniform A‖ ^ 2 ∂finiteUniform A) ≤
      16 * M ^ 2 * (finiteUniform A).real bad := by
  letI := finiteUniform_isProbability A
  by_cases hne : ∃ a : A, a ∉ bad
  · obtain ⟨a,ha⟩ := hne
    have hb : ‖b‖ ≤ M := by rw [← hgood a ha]; exact hbound a
    have hdiff (a : A) : ‖f a - b‖ ≤ 2 * M :=
      (norm_sub_le _ _).trans (by linarith [hbound a])
    have hp := finiteUniform_variance_le_exceptional_set f bad b (2 * M) (by positivity) hgood hdiff
    convert hp using 1 <;> ring
  · have hbad : bad = Set.univ := by
      ext a
      simp only [Set.mem_univ, iff_true]
      by_contra ha
      exact hne ⟨a,ha⟩
    have hp := finiteUniform_variance_le_exceptional_set f Set.univ 0 M hM (by simp)
      (fun a => by simpa only [sub_zero] using hbound a)
    rw [hbad, measureReal_univ_eq_one, mul_one]
    simp only [measureReal_univ_eq_one, mul_one] at hp
    exact hp.trans (by nlinarith [sq_nonneg M])

end GeneralizedBulk.Graph
