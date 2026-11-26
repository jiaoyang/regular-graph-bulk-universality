import GeneralizedBulk.Gaussian.StarReferenceDeterminant
import GeneralizedBulk.Matrix.ColorBlocks
import GeneralizedBulk.Matrix.PositiveColorBlocks

/-! Actual root-neighbor wave covariance has a uniform positive floor on
compact bulk sets. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.Gaussian
open GeneralizedBulk.Covariance

theorem edgeWaveCovariance_quadratic (d : ℕ) (E : ℝ) (x : Fin 2 → ℝ) :
    dotProduct x ((edgeWaveCovariance d E).mulVec x)=x 0^2+x 1^2+2*(E/d)*x 0*x 1 := by
  simp [dotProduct,Matrix.mulVec,Fin.sum_univ_two,edgeWaveCovariance]
  ring

theorem edgeWaveCovariance_quadratic_floor (d : ℕ) (E : ℝ) (x : Fin 2 → ℝ) :
    (1-|E/d|)*(∑ i,x i^2) ≤ dotProduct x ((edgeWaveCovariance d E).mulVec x) := by
  rw [edgeWaveCovariance_quadratic,Fin.sum_univ_two]
  have hs : 2*|x 0| *|x 1| ≤ x 0^2+x 1^2 := by nlinarith [sq_nonneg (|x 0|-|x 1|),sq_abs (x 0),sq_abs (x 1)]
  have hh := mul_le_mul_of_nonneg_left hs (abs_nonneg (E/(d : ℝ)))
  have hx := neg_abs_le (E/(d : ℝ)*x 0*x 1)
  rw [abs_mul,abs_mul] at hx
  nlinarith only [hh,hx]

theorem edgeWaveCovariance_trace (d : ℕ) (E : ℝ) : Matrix.trace (edgeWaveCovariance d E)=2 := by
  norm_num [edgeWaveCovariance,Matrix.trace,Matrix.diag,Fin.sum_univ_two]

theorem edgeWaveCovariance_uniform_floor (d : ℕ) (hd : 0 < d) (K : Set ℝ) (hK : IsCompact K)
    (hbulk : ∀ E ∈ K,|E| < d) :
    ∃ kappa : ℝ,0 < kappa ∧ ∀ E ∈ K,∀ x : Fin 2 → ℝ,
      kappa*(∑ i,x i^2) ≤ dotProduct x ((edgeWaveCovariance d E).mulVec x) := by
  let f := fun E : ℝ => 1-|E/(d : ℝ)|
  have hp (E : ℝ) (hE : E ∈ K) : 0 < f E := by
    have hdR : (0:ℝ) < d := Nat.cast_pos.mpr hd
    have hh : |E/(d : ℝ)| < 1 := by rw [abs_div,abs_of_pos hdR,div_lt_one hdR]; exact hbulk E hE
    dsimp [f]
    linarith
  by_cases hne : K.Nonempty
  · obtain ⟨E0,hE0,hmin⟩ := hK.exists_isMinOn hne (show ContinuousOn f K from (by fun_prop : Continuous f).continuousOn)
    refine ⟨f E0,hp E0 hE0,fun E hE x => ?_⟩
    exact (mul_le_mul_of_nonneg_right (hmin hE) (Finset.sum_nonneg (fun i _ => sq_nonneg _))).trans
      (edgeWaveCovariance_quadratic_floor d E x)
  · exact ⟨1,by norm_num,fun E hE => False.elim (hne ⟨E,hE⟩)⟩

theorem coloredEdgeWaveCovariance_uniform_floor (d k : ℕ) (hd : 0 < d) (K : Set ℝ) (hK : IsCompact K)
    (hbulk : ∀ E ∈ K,|E| < d) :
    ∃ kappa : ℝ,0 < kappa ∧ ∀ energy : Fin k → ℝ,(∀ a,energy a ∈ K) →
      ∀ x : Fin k × Fin 2 → ℝ,kappa*(∑ i,x i^2) ≤
        dotProduct x ((colorBlock (fun a => edgeWaveCovariance d (energy a))).mulVec x) := by
  obtain ⟨κ,hκ,hf⟩ := edgeWaveCovariance_uniform_floor d hd K hK hbulk
  exact ⟨κ,hκ,fun energy hE x => colorBlock_quadratic_floor _ κ (fun a y => hf (energy a) (hE a) y) x⟩

end GeneralizedBulk.Gaussian
