import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Fundamental theorem of calculus with finitely many singularities.
The function remains continuous at the exceptional points.  Thus these points
contribute no boundary term; no differentiability at a collision is required. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BourgadeHuang.RationalBulk

theorem integral_eq_sub_of_hasDerivAt_off_finset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (S : Finset ℝ) {f g : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, x ∉ S → HasDerivAt f (g x) x)
    (hg : IntervalIntegrable g volume a b) :
    (∫ x in a..b, g x) = f b - f a := by
  classical
  induction S using Finset.induction_on generalizing a b with
  | empty =>
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hc
      (fun x hx => hd x hx (by simp)) hg
  | @insert t S ht ih =>
    by_cases htab : t ∈ Ioo a b
    · have hgl : IntervalIntegrable g volume a t := hg.mono_set (by
        simpa only [uIcc_of_le htab.1.le, uIcc_of_le hab] using
          Icc_subset_Icc le_rfl htab.2.le)
      have hgr : IntervalIntegrable g volume t b := hg.mono_set (by
        simpa only [uIcc_of_le htab.2.le, uIcc_of_le hab] using
          Icc_subset_Icc htab.1.le le_rfl)
      have hleft := ih htab.1.le
        (hc.mono (Icc_subset_Icc le_rfl htab.2.le))
        (fun x hx hS => hd x ⟨hx.1, hx.2.trans htab.2⟩
          (by simp only [Finset.mem_insert, not_or]; exact ⟨ne_of_lt hx.2, hS⟩)) hgl
      have hright := ih htab.2.le
        (hc.mono (Icc_subset_Icc htab.1.le le_rfl))
        (fun x hx hS => hd x ⟨htab.1.trans hx.1, hx.2⟩
          (by simp only [Finset.mem_insert, not_or]; exact ⟨ne_of_gt hx.1, hS⟩)) hgr
      rw [← intervalIntegral.integral_add_adjacent_intervals hgl hgr, hleft, hright]
      abel
    · apply ih hab hc _ hg
      intro x hx hS
      apply hd x hx
      simp only [Finset.mem_insert, not_or]
      exact ⟨fun h => htab (h ▸ hx), hS⟩

theorem integral_of_hasDerivAt_off_finset_of_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (S : Finset ℝ) {f g : ℝ → E} {m n : E}
    (hc : Continuous f) (hd : ∀ x ∉ S, HasDerivAt f (g x) x)
    (hg : Integrable g) (hbot : Tendsto f atBot (𝓝 m))
    (htop : Tendsto f atTop (𝓝 n)) : (∫ x, g x) = n - m := by
  have hi := intervalIntegral_tendsto_integral hg
    (tendsto_neg_atTop_atBot : Tendsto (fun t : ℝ => -t) atTop atBot)
    (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop)
  have ht : Tendsto (fun t : ℝ => f t - f (-t)) atTop (𝓝 (n - m)) :=
    htop.sub (hbot.comp tendsto_neg_atTop_atBot)
  apply tendsto_nhds_unique hi
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact (integral_eq_sub_of_hasDerivAt_off_finset S (by linarith)
    hc.continuousOn (fun x _ hx => hd x hx) hg.intervalIntegrable).symm

/-- Collision singularities do not contribute a boundary term. -/
theorem integral_eq_zero_of_hasDerivAt_off_finset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (S : Finset ℝ) {f g : ℝ → E}
    (hc : Continuous f) (hd : ∀ x ∉ S, HasDerivAt f (g x) x)
    (hg : Integrable g) (hbot : Tendsto f atBot (𝓝 0))
    (htop : Tendsto f atTop (𝓝 0)) : (∫ x, g x) = 0 := by
  simpa using integral_of_hasDerivAt_off_finset_of_tendsto S hc hd hg hbot htop

theorem integral_eq_zero_of_hasDerivAt_off_finset_of_integrable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (S : Finset ℝ) {f g : ℝ → E}
    (hc : Continuous f) (hd : ∀ x ∉ S, HasDerivAt f (g x) x)
    (hg : Integrable g) (hf : Integrable f) : (∫ x, g x) = 0 := by
  obtain ⟨a, ha⟩ := S.finite_toSet.bddBelow
  obtain ⟨b, hb⟩ := S.finite_toSet.bddAbove
  apply integral_eq_zero_of_hasDerivAt_off_finset S hc hd hg
  · apply tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a := a - 1) _
      hg.integrableOn hf.integrableOn
    intro x hx
    apply hd x
    intro hS
    have := ha hS
    have hx' : x ≤ a - 1 := hx
    linarith
  · apply tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := b) _
      hg.integrableOn hf.integrableOn
    intro x hx
    apply hd x
    intro hS
    exact (not_lt_of_ge (hb hS)) hx

end BourgadeHuang.RationalBulk
