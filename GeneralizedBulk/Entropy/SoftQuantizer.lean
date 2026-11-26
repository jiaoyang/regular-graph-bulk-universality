import GeneralizedBulk.Entropy.BoxAverage

/-! An actual C¹ partition of unity obtained by double-box-dithering an
arbitrary measurable finite scalar quantizer. -/
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace GeneralizedBulk.Entropy

variable {B : Type*} [Fintype B] [DecidableEq B] [MeasurableSpace B] [MeasurableSingletonClass B]

def hardLabel (J : ℝ → B) (b : B) (x : ℝ) : ℝ := if J x = b then 1 else 0

theorem measurable_hardLabel (J : ℝ → B) (hJ : Measurable J) (b : B) : Measurable (hardLabel J b) := by
  apply Measurable.ite _ measurable_const measurable_const
  change MeasurableSet (J ⁻¹' {b})
  exact hJ (measurableSet_singleton b)

theorem hardLabel_nonneg (J : ℝ → B) (b : B) (x : ℝ) : 0 ≤ hardLabel J b x := by
  unfold hardLabel; split_ifs <;> norm_num

theorem hardLabel_le_one (J : ℝ → B) (b : B) (x : ℝ) : hardLabel J b x ≤ 1 := by
  unfold hardLabel; split_ifs <;> norm_num

theorem hardLabel_sum (J : ℝ → B) (x : ℝ) : ∑ b,hardLabel J b x = 1 := by
  simp [hardLabel,eq_comm]

theorem boxAverage_partition (f : B → ℝ → ℝ) (hf : ∀ b,Measurable (f b))
    (hf0 : ∀ b x,0 ≤ f b x) (hf1 : ∀ b x,f b x ≤ 1) (hsum : ∀ x,∑ b,f b x = 1)
    (ℓ : ℝ) (hℓ : 0 < ℓ) (x : ℝ) : ∑ b,boxAverage (f b) ℓ x = 1 := by
  simp only [boxAverage]
  rw [← Finset.mul_sum,← intervalIntegral.integral_finset_sum
    (fun b hb => intervalIntegrable_of_unit_bounded (f b) (hf b) (hf0 b) (hf1 b) _ _)]
  simp_rw [hsum]
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul,mul_one]
  field_simp
  ring

def firstSoftLabel (J : ℝ → B) (ℓ : ℝ) (b : B) : ℝ → ℝ := boxAverage (hardLabel J b) ℓ

def softLabel (J : ℝ → B) (ℓ : ℝ) (b : B) : ℝ → ℝ := boxAverage (firstSoftLabel J ℓ b) ℓ

theorem firstSoftLabel_continuous (J : ℝ → B) (hJ : Measurable J) (ℓ : ℝ) (hℓ : 0 < ℓ) (b : B) :
    Continuous (firstSoftLabel J ℓ b) :=
  (boxAverage_lipschitz (hardLabel J b) ℓ hℓ (measurable_hardLabel J hJ b)
    (hardLabel_nonneg J b) (hardLabel_le_one J b)).continuous

theorem firstSoftLabel_nonneg (J : ℝ → B) (ℓ : ℝ) (hℓ : 0 < ℓ) (b : B) (x : ℝ) :
    0 ≤ firstSoftLabel J ℓ b x := boxAverage_nonneg _ _ hℓ (hardLabel_nonneg J b) x

theorem firstSoftLabel_le_one (J : ℝ → B) (hJ : Measurable J) (ℓ : ℝ) (hℓ : 0 < ℓ) (b : B) (x : ℝ) :
    firstSoftLabel J ℓ b x ≤ 1 := boxAverage_le_one _ _ hℓ (measurable_hardLabel J hJ b)
      (hardLabel_nonneg J b) (hardLabel_le_one J b) x

theorem firstSoftLabel_sum (J : ℝ → B) (hJ : Measurable J) (ℓ : ℝ) (hℓ : 0 < ℓ) (x : ℝ) :
    ∑ b,firstSoftLabel J ℓ b x = 1 := boxAverage_partition _ (measurable_hardLabel J hJ)
      (hardLabel_nonneg J) (hardLabel_le_one J) (hardLabel_sum J) ℓ hℓ x

theorem softLabel_nonneg (J : ℝ → B) (ℓ : ℝ) (hℓ : 0 < ℓ) (b : B) (x : ℝ) :
    0 ≤ softLabel J ℓ b x := boxAverage_nonneg _ _ hℓ (firstSoftLabel_nonneg J ℓ hℓ b) x

theorem softLabel_le_one (J : ℝ → B) (hJ : Measurable J) (ℓ : ℝ) (hℓ : 0 < ℓ) (b : B) (x : ℝ) :
    softLabel J ℓ b x ≤ 1 := boxAverage_le_one _ _ hℓ (firstSoftLabel_continuous J hJ ℓ hℓ b).measurable
      (firstSoftLabel_nonneg J ℓ hℓ b) (firstSoftLabel_le_one J hJ ℓ hℓ b) x

theorem softLabel_sum (J : ℝ → B) (hJ : Measurable J) (ℓ : ℝ) (hℓ : 0 < ℓ) (x : ℝ) :
    ∑ b,softLabel J ℓ b x = 1 := boxAverage_partition _
      (fun b => (firstSoftLabel_continuous J hJ ℓ hℓ b).measurable)
      (firstSoftLabel_nonneg J ℓ hℓ) (firstSoftLabel_le_one J hJ ℓ hℓ)
      (firstSoftLabel_sum J hJ ℓ hℓ) ℓ hℓ x

theorem contDiff_one_softLabel (J : ℝ → B) (hJ : Measurable J) (ℓ : ℝ) (hℓ : 0 < ℓ) (b : B) :
    ContDiff ℝ 1 (softLabel J ℓ b) :=
  contDiff_one_boxAverage _ (firstSoftLabel_continuous J hJ ℓ hℓ b) ℓ

theorem hasDerivAt_softLabel (J : ℝ → B) (hJ : Measurable J) (ℓ : ℝ) (hℓ : 0 < ℓ) (b : B) (x : ℝ) :
    HasDerivAt (softLabel J ℓ b)
      ((2*ℓ)⁻¹*(firstSoftLabel J ℓ b (x+ℓ)-firstSoftLabel J ℓ b (x-ℓ))) x :=
  hasDerivAt_boxAverage _ (firstSoftLabel_continuous J hJ ℓ hℓ b) ℓ x

theorem abs_deriv_softLabel_le (J : ℝ → B) (hJ : Measurable J) (ℓ : ℝ) (hℓ : 0 < ℓ) (b : B) (x : ℝ) :
    |deriv (softLabel J ℓ b) x| ≤ (2*ℓ)⁻¹ := by
  rw [(hasDerivAt_softLabel J hJ ℓ hℓ b x).deriv,abs_mul,abs_of_nonneg (by positivity : 0 ≤ (2*ℓ)⁻¹)]
  have hp0 := firstSoftLabel_nonneg J ℓ hℓ b (x+ℓ)
  have hm0 := firstSoftLabel_nonneg J ℓ hℓ b (x-ℓ)
  have hp1 := firstSoftLabel_le_one J hJ ℓ hℓ b (x+ℓ)
  have hm1 := firstSoftLabel_le_one J hJ ℓ hℓ b (x-ℓ)
  have h := mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith,by linarith⟩ :
    |firstSoftLabel J ℓ b (x+ℓ)-firstSoftLabel J ℓ b (x-ℓ)| ≤ 1) (by positivity : 0 ≤ (2*ℓ)⁻¹)
  simpa only [mul_one] using h

theorem softLabel_abs_sub_le (J : ℝ → B) (hJ : Measurable J) (ℓ : ℝ) (hℓ : 0 < ℓ) (b : B) (x y : ℝ) :
    |softLabel J ℓ b x-softLabel J ℓ b y| ≤ (2*ℓ)⁻¹*|x-y| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Set.univ) (f := softLabel J ℓ b)
    (fun z hz => (hasDerivAt_softLabel J hJ ℓ hℓ b z).differentiableAt)
    (fun z hz => by simpa only [Real.norm_eq_abs] using abs_deriv_softLabel_le J hJ ℓ hℓ b z)
    convex_univ (Set.mem_univ y) (Set.mem_univ x)
  exact h

end GeneralizedBulk.Entropy
