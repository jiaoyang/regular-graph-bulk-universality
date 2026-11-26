import GeneralizedBulk.Graph.HYEmpiricalFourthMoments

/-! One-color physical fourth bounds give the actual joint-star norm moment
required by the qualitative BS Gaussian limit adapter. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.External.RegularSpectralData
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

theorem star_coordinate_fourth_eq_discrepancy {k : ℕ} (selection : Fin k → Fin (N n))
    (j : Fin k × Fin (d + 1)) :
    (∫ x, x j ^ 4 ∂D.starLaw n ω (fun a => D.eigenvector n ω (selection a))) =
      D.empiricalFourthWickDiscrepancy n ω (fun _ : Fin 1 => selection j.1)
        (0,j.2) (0,j.2) (0,j.2) (0,j.2) + 3 := by
  classical
  rw [D.integral_starLaw n ω]
  unfold empiricalFourthWickDiscrepancy empiricalGaussianCovariance
  simp only [ite_true,one_mul,starWaveCovariance_self,mul_one]
  simp only [empiricalStarWeight,EmpiricalStarSample,Finset.mul_sum,starSample]
  have heq : (∑ s : Fin (N n) × Equiv.Perm (Fin d),
      (Fintype.card (Fin (N n) × Equiv.Perm (Fin d)) : ℝ)⁻¹ *
        (Real.sqrt (N n) * D.eigenvector n ω (selection j.1)
          (Fin.cases s.1 (fun i => D.neighbor n ω s.1 (s.2 i)) j.2)) ^ 4) =
      ∑ s : Fin (N n) × Equiv.Perm (Fin d),
        (Fintype.card (Fin (N n) × Equiv.Perm (Fin d)) : ℝ)⁻¹ *
          (Real.sqrt (N n) * D.eigenvector n ω (selection j.1)
            (Fin.cases s.1 (fun i => D.neighbor n ω s.1 (s.2 i)) j.2)) *
          (Real.sqrt (N n) * D.eigenvector n ω (selection j.1)
            (Fin.cases s.1 (fun i => D.neighbor n ω s.1 (s.2 i)) j.2)) *
          (Real.sqrt (N n) * D.eigenvector n ω (selection j.1)
            (Fin.cases s.1 (fun i => D.neighbor n ω s.1 (s.2 i)) j.2)) *
          (Real.sqrt (N n) * D.eigenvector n ω (selection j.1)
            (Fin.cases s.1 (fun i => D.neighbor n ω s.1 (s.2 i)) j.2)) := by
    apply Finset.sum_congr rfl
    intro s hs
    ring
  rw [heq]
  ring

theorem starLaw_norm_fourth_le_of_one_color_Wick {k : ℕ} (hk : 0 < k)
    (selection : Fin k → Fin (N n)) (epsilon : ℝ)
    (hfourth : ∀ a : Fin k, ∀ j : Fin (d + 1),
      |D.empiricalFourthWickDiscrepancy n ω (fun _ : Fin 1 => selection a)
        (0,j) (0,j) (0,j) (0,j)| ≤ epsilon) :
    (∫ x, ‖x‖ ^ 4 ∂D.starLaw n ω (fun a => D.eigenvector n ω (selection a))) ≤
      ((k * (d + 1) : ℕ) : ℝ) * (3 + epsilon) := by
  classical
  letI : Nonempty (Fin k × Fin (d + 1)) := ⟨(⟨0,hk⟩,0)⟩
  let Q := D.starLaw n ω (fun a => D.eigenvector n ω (selection a))
  have hp (x : (Fin k × Fin (d + 1)) → ℝ) : ‖x‖ ^ 4 ≤ ∑ j, x j ^ 4 := by
    obtain ⟨j,hj,hmax⟩ := Finset.exists_max_image Finset.univ (fun j => ‖x j‖) Finset.univ_nonempty
    have hnorm : ‖x‖ ≤ ‖x j‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      (fun l => hmax l (Finset.mem_univ l))
    calc
      _ ≤ ‖x j‖ ^ 4 := pow_le_pow_left₀ (norm_nonneg _) hnorm 4
      _ = x j ^ 4 := by rw [Real.norm_eq_abs,← abs_pow,abs_of_nonneg (by positivity)]
      _ ≤ _ := Finset.single_le_sum (fun j hj => Even.pow_nonneg (by decide : Even (4 : ℕ)) (x j))
        (Finset.mem_univ j)
  have hcoord (j : Fin k × Fin (d + 1)) : (∫ x, x j ^ 4 ∂Q) ≤ 3 + epsilon := by
    have hh := le_abs_self (D.empiricalFourthWickDiscrepancy n ω (fun _ : Fin 1 => selection j.1)
      (0,j.2) (0,j.2) (0,j.2) (0,j.2))
    rw [star_coordinate_fourth_eq_discrepancy]
    linarith [hfourth j.1 j.2]
  calc
    _ ≤ ∫ x, ∑ j, x j ^ 4 ∂Q := integral_mono (D.integrable_starLaw n ω _ _)
      (D.integrable_starLaw n ω _ _) hp
    _ = ∑ j, ∫ x, x j ^ 4 ∂Q := integral_finset_sum _ (fun j hj => D.integrable_starLaw n ω _ _)
    _ ≤ ∑ _j : Fin k × Fin (d + 1), (3 + epsilon) := Finset.sum_le_sum (fun j hj => hcoord j)
    _ = _ := by simp; ring

end GeneralizedBulk.External.RegularSpectralData
