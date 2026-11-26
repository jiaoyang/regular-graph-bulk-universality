import GeneralizedBulk.Graph.StarCovariance

/-! The literal regular adjacency eigenvalues lie in `[-d,d]`. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GeneralizedBulk.External.RegularSpectralData
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

/-- The elementary maximum-coordinate argument supplies the actual compact
spectral interval needed for polynomial approximation. -/
theorem eigenvalue_abs_le_degree (k : Fin (N n)) : |D.eigenvalue n ω k| ≤ d := by
  letI : Nonempty (Fin (N n)) := ⟨⟨0,D.size_pos n⟩⟩
  obtain ⟨v,hv,hmax⟩ := Finset.exists_max_image Finset.univ
    (fun v => |D.eigenvector n ω k v|) Finset.univ_nonempty
  have hpos : 0 < |D.eigenvector n ω k v| := by
    by_contra hn
    have hzero : ∀ w, D.eigenvector n ω k w = 0 := by
      intro w
      have hh := hmax w (Finset.mem_univ w)
      exact abs_eq_zero.mp (by linarith [abs_nonneg (D.eigenvector n ω k w)])
    have ho := D.orthonormal n ω k k
    simp only [hzero, zero_mul, Finset.sum_const_zero, ↓reduceIte] at ho
    norm_num at ho
  have hbound : |D.eigenvalue n ω k| * |D.eigenvector n ω k v| ≤
      (d : ℝ) * |D.eigenvector n ω k v| := by
    calc
      _ = |∑ j : Fin d, D.eigenvector n ω k (D.neighbor n ω v j)| := by
        rw [D.eigenvector_neighbor_sum n ω, abs_mul]
      _ ≤ ∑ j : Fin d, |D.eigenvector n ω k (D.neighbor n ω v j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin d, |D.eigenvector n ω k v| :=
        Finset.sum_le_sum (fun j _ => hmax _ (Finset.mem_univ _))
      _ = _ := by simp
  exact (mul_le_mul_right hpos).mp hbound

theorem eigenvalue_mem_spectralInterval (k : Fin (N n)) :
    D.eigenvalue n ω k ∈ Set.Icc (-(d : ℝ)) (d : ℝ) :=
  abs_le.mp (D.eigenvalue_abs_le_degree n ω k)

end GeneralizedBulk.External.RegularSpectralData
