import BourgadeHuang.CMS.GeneralBranches
import BourgadeHuang.CMS.ShiftedRays

/-! Explicit inverse-gap bounds for the true conjugated CMS coefficients. -/
noncomputable section
open scoped BigOperators
namespace BourgadeHuang.CMS

def branchCoefficientSize {d : ℕ} (β : ℂ) (c : Fin d → ℂ) (σ : Fin d → Sign) : ℝ :=
  ∑i,∑j,‖couplingExponent β c σ i j‖

theorem branchCoefficientSize_nonneg {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (σ : Fin d → Sign) : 0≤branchCoefficientSize β c σ := by
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))

theorem branchCoefficientSize_row {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (σ : Fin d → Sign) (i : Fin d) :
    (∑j∈Finset.univ.erase i,‖couplingExponent β c σ i j‖)≤branchCoefficientSize β c σ := by
  apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
    (fun _ _ _ => norm_nonneg _))
  exact Finset.single_le_sum (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (Finset.mem_univ i)

theorem norm_branchCorrection_le {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (σ : Fin d → Sign) (z : Point d) {R : ℝ} (hR : 0<R)
    (hsep : ∀i j,i≠j→R≤‖z i-z j‖) (i : Fin d) :
    ‖branchCorrection β c σ i z‖≤branchCoefficientSize β c σ/R := by
  unfold branchCorrection
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑j∈Finset.univ.erase i,‖couplingExponent β c σ i j‖/R := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_div]
      exact div_le_div_of_nonneg_left (norm_nonneg _) hR (hsep i j (Finset.ne_of_mem_erase hj).symm)
    _ = (∑j∈Finset.univ.erase i,‖couplingExponent β c σ i j‖)/R := by rw [Finset.sum_div]
    _ ≤ _ := div_le_div_of_nonneg_right (branchCoefficientSize_row β c σ i) hR.le

theorem norm_branchCorrectionDerivative_le {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (σ : Fin d → Sign) (z : Point d) {R : ℝ} (hR : 0<R)
    (hsep : ∀i j,i≠j→R≤‖z i-z j‖) (i : Fin d) :
    ‖branchCorrectionDerivative β c σ i z‖≤branchCoefficientSize β c σ/R^2 := by
  unfold branchCorrectionDerivative
  rw [norm_neg]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑j∈Finset.univ.erase i,‖couplingExponent β c σ i j‖/R^2 := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_div,norm_pow]
      apply div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hR)
      exact pow_le_pow_left₀ hR.le (hsep i j (Finset.ne_of_mem_erase hj).symm) 2
    _ = (∑j∈Finset.univ.erase i,‖couplingExponent β c σ i j‖)/R^2 := by rw [Finset.sum_div]
    _ ≤ _ := div_le_div_of_nonneg_right (branchCoefficientSize_row β c σ i) (sq_nonneg R)

def branchPotentialSize {d : ℕ} (β : ℂ) (c : Fin d → ℂ) (σ : Fin d → Sign)
    (i : Fin d) : ℝ :=
  branchCoefficientSize β c σ+(branchCoefficientSize β c σ)^2+
    ‖2/β‖*(∑j∈Finset.univ.erase i,(‖c i‖*‖c j‖+‖c i‖^2))*branchCoefficientSize β c σ

theorem branchPotentialSize_nonneg {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (σ : Fin d → Sign) (i : Fin d) : 0≤branchPotentialSize β c σ i := by
  have h := branchCoefficientSize_nonneg β c σ
  unfold branchPotentialSize
  positivity

theorem norm_generalBranchPotential_le {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (σ : Fin d → Sign) (z : Point d) {R : ℝ} (hR : 0<R)
    (hsep : ∀i j,i≠j→R≤‖z i-z j‖) (i : Fin d) :
    ‖generalBranchPotential β c σ i z‖≤branchPotentialSize β c σ i/R^2 := by
  let A := branchCoefficientSize β c σ
  have hA : 0≤A := branchCoefficientSize_nonneg β c σ
  have hΩ j : ‖branchCorrection β c σ j z‖≤A/R := norm_branchCorrection_le β c σ z hR hsep j
  have ht j (hj : j∈Finset.univ.erase i) :
      ‖(c i*c j*branchCorrection β c σ i z-c i^2*branchCorrection β c σ j z)/(z i-z j)‖≤
        (‖c i‖*‖c j‖+‖c i‖^2)*A/R^2 := by
    rw [norm_div]
    apply (div_le_div_of_nonneg_left (norm_nonneg _) hR (hsep i j (Finset.ne_of_mem_erase hj).symm)).trans
    apply (div_le_div_of_nonneg_right (norm_sub_le _ _) hR.le).trans
    simp only [norm_mul,norm_pow]
    calc
      _ ≤ (‖c i‖*‖c j‖*(A/R)+‖c i‖^2*(A/R))/R := by
        apply div_le_div_of_nonneg_right _ hR.le
        exact add_le_add (mul_le_mul_of_nonneg_left (hΩ i) (by positivity))
          (mul_le_mul_of_nonneg_left (hΩ j) (by positivity))
      _ = _ := by ring
  have hsum :
      ‖∑j∈Finset.univ.erase i,(c i*c j*branchCorrection β c σ i z-
        c i^2*branchCorrection β c σ j z)/(z i-z j)‖≤
      (∑j∈Finset.univ.erase i,(‖c i‖*‖c j‖+‖c i‖^2))*A/R^2 := by
    apply (norm_sum_le _ _).trans
    apply (Finset.sum_le_sum ht).trans_eq
    rw [← Finset.sum_div,← Finset.sum_mul]
  unfold generalBranchPotential
  apply (norm_add_le _ _).trans
  apply (add_le_add ((norm_add_le _ _).trans (add_le_add
    (norm_branchCorrectionDerivative_le β c σ z hR hsep i)
    (by simpa only [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) (hΩ i) 2)))
    (by simpa only [norm_mul] using mul_le_mul_of_nonneg_left hsum (norm_nonneg (2/β)))).trans_eq
  unfold branchPotentialSize
  dsimp only [A]
  ring

/-- Along the genuine shifted ray the scalar remainder is bounded by a fixed
constant times the inverse square of the radial parameter. -/
theorem norm_generalBranchPotential_shiftedRay_le {d : ℕ}
    (β : ℂ) (c : Fin d → ℂ) (σ τ : Fin d → Sign) {z : Point d}
    (hz : z∈OrderedDomain d) {R r : ℝ} (hR : 0<R) (hr : 0≤r)
    (hsep : ∀i j,i≠j→R≤‖z i-z j‖) (i : Fin d) :
    ‖generalBranchPotential β c σ i (shiftedRay τ z r)‖≤
      16*branchPotentialSize β c σ i/(R+r)^2 := by
  have hpos : 0<(R+r)/4 := by positivity
  have h := norm_generalBranchPotential_le β c σ (shiftedRay τ z r) hpos
    (shiftedRay_separation τ hz hsep hr) i
  convert h using 1
  field_simp
  ring

end BourgadeHuang.CMS
