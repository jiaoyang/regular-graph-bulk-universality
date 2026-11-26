import Mathlib

/-! A concrete probabilistic-method selection lemma. A single nonnegative
integrable potential yields simultaneous finite-test accuracy and a root
energy bound. This avoids postulating deterministic realizations. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GaussianWave.BS

/-- If the combined second-moment/energy budget is below one, an actual
sample realizes every prescribed finite-test accuracy and the energy bound. -/
theorem exists_sample_of_variance_energy_budget
    {Ω J : Type*} [MeasurableSpace Ω] [Fintype J]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : J → Ω → ℝ) (target : J → ℝ) (H : Ω → ℝ)
    (hH : Integrable H μ) (hH0 : ∀ ω,0 ≤ H ω)
    (hX : ∀ j,Integrable (fun ω => (X j ω-target j)^2) μ)
    (B V M ε : ℝ) (hM : 0 < M) (hε : 0 < ε)
    (hB : (∫ ω,H ω ∂μ) ≤ B)
    (hV : ∀ j,(∫ ω,(X j ω-target j)^2 ∂μ) ≤ V)
    (hbudget : B/M+(Fintype.card J : ℝ)*V/ε^2 < 1) :
    ∃ ω,H ω < M ∧ ∀ j,|X j ω-target j| < ε := by
  let Z (ω : Ω) := H ω/M+∑ j : J,(X j ω-target j)^2/ε^2
  have hiZ : Integrable Z μ := (hH.div_const M).add
    (integrable_finset_sum _ (fun j _ => (hX j).div_const (ε^2)))
  have hi : (∫ ω,Z ω ∂μ) < 1 := by
    have he : (∫ ω,Z ω ∂μ) = (∫ ω,H ω ∂μ)/M+
        ∑ j : J,(∫ ω,(X j ω-target j)^2 ∂μ)/ε^2 := by
      rw [integral_add (hH.div_const M)
        (integrable_finset_sum _ (fun j _ => (hX j).div_const (ε^2))),
        integral_div,integral_finset_sum _ (fun j _ => (hX j).div_const (ε^2))]
      simp only [integral_div]
    rw [he]
    apply lt_of_le_of_lt _ hbudget
    have hsum : (∑ j : J,(∫ ω,(X j ω-target j)^2 ∂μ)/ε^2) ≤
        (Fintype.card J : ℝ)*V/ε^2 := by
      calc
        _ ≤ ∑ _j : J,V/ε^2 := Finset.sum_le_sum (fun j _ => div_le_div_of_nonneg_right (hV j) (sq_nonneg ε))
        _ = _ := by simp [mul_div_assoc]
    exact add_le_add (div_le_div_of_nonneg_right hB hM.le) hsum
  have hex : ∃ ω,Z ω < 1 := by
    by_contra hno
    push_neg at hno
    have hlo := integral_mono (integrable_const (1 : ℝ)) hiZ hno
    have he : (∫ _ : Ω,(1 : ℝ) ∂μ)=1 := by simp
    linarith
  obtain ⟨ω,hω⟩ := hex
  have hs0 : ∀ j : J,0 ≤ (X j ω-target j)^2/ε^2 := fun _ => div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hHle : H ω/M ≤ Z ω := le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => hs0 j))
  have hHlt : H ω < M := (div_lt_one hM).mp (hHle.trans_lt hω)
  refine ⟨ω,hHlt,fun j => ?_⟩
  have hterm : (X j ω-target j)^2/ε^2 ≤ Z ω := by
    have hs : (X j ω-target j)^2/ε^2 ≤ ∑ i : J,(X i ω-target i)^2/ε^2 :=
      Finset.single_le_sum (fun i _ => hs0 i) (Finset.mem_univ j)
    exact hs.trans (le_add_of_nonneg_left (div_nonneg (hH0 ω) hM.le))
  have he : (X j ω-target j)^2 < ε^2 := (div_lt_one (sq_pos_of_pos hε)).mp (hterm.trans_lt hω)
  exact (sq_lt_sq₀ (abs_nonneg _) hε.le).mp (by simpa only [sq_abs] using he)

end GaussianWave.BS
