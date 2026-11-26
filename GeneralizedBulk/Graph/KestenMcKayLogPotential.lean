import GeneralizedBulk.Spectral.KestenMcKayQuadrature
import GeneralizedBulk.Graph.HYLogPotential

/-! A fully deterministic Kesten–McKay log-potential comparison from the
actual HY rigidity event and the proved finite quantile quadrature. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Spectral GeneralizedBulk.KestenMcKay
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

def kestenMcKayQuantile (hd : 3 ≤ (d : ℝ)) (n : ℕ) : Fin (N n) → ℝ :=
  finiteQuantile d hd (N n) (D.size_pos n)

theorem HY_kestenMcKay_logPotential {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : 3 ≤ (d : ℝ)) (H : HYCoarseInput D P (D.kestenMcKayQuantile hd))
    (n : ℕ) (hn : H.events.threshold ≤ n) (ω : Ω) (hω : ω ∈ H.events.good n)
    (E eta : ℝ) (heta : 0 < eta) :
    |(∑ i : Fin (N n), regularizedLog E eta (D.eigenvalue n ω i)) / (N n : ℝ) -
      regularizedPotential d E eta| ≤
      (N n : ℝ) ^ (-H.rigidity_exponent) / eta +
        (|(d : ℝ) - radius d| + 4 * radius d) / ((N n : ℝ) * eta) := by
  let r : ℝ := (N n : ℝ) ^ (-H.rigidity_exponent)
  let i0 : Fin (N n) := ⟨0, D.size_pos n⟩
  have hN : (0 : ℝ) < N n := Nat.cast_pos.mpr (D.size_pos n)
  have hgamma0 : D.kestenMcKayQuantile hd n i0 = radius d := by
    change quantileNode d hd (N n) (D.size_pos n) ((N n) - 0) = radius d
    simpa only [Nat.sub_zero] using quantileNode_upper d hd (N n) (D.size_pos n)
  have hpoint (i : Fin (N n)) :
      |regularizedLog E eta (D.eigenvalue n ω i) - regularizedLog E eta (D.kestenMcKayQuantile hd n i)| ≤
      eta⁻¹ * r + if i = i0 then eta⁻¹ * |(d : ℝ) - radius d| else 0 := by
    by_cases hi : i = i0
    · subst i
      rw [if_pos rfl, hgamma0, D.constant_eigenvalue]
      exact (regularizedLog_lipschitz E eta heta _ _).trans (le_add_of_nonneg_left (by dsimp [r]; positivity))
    · rw [if_neg hi, add_zero]
      apply (regularizedLog_lipschitz E eta heta _ _).trans
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr heta.le)
      apply H.rigidity n hn ω hω i
      intro hz
      apply hi
      apply Fin.ext
      exact hz
  have hfinite :
      |(∑ i : Fin (N n), regularizedLog E eta (D.eigenvalue n ω i)) / (N n : ℝ) -
        (∑ i : Fin (N n), regularizedLog E eta (D.kestenMcKayQuantile hd n i)) / (N n : ℝ)| ≤
      r / eta + |(d : ℝ) - radius d| / ((N n : ℝ) * eta) := by
    rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hN]
    apply (div_le_iff₀ hN).mpr
    have hh := (Finset.abs_sum_le_sum_abs (s := Finset.univ)
      (f := fun i => regularizedLog E eta (D.eigenvalue n ω i) - regularizedLog E eta (D.kestenMcKayQuantile hd n i))).trans
      (Finset.sum_le_sum (fun i _ => hpoint i))
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hh
    convert hh using 1 <;> field_simp <;> ring
  have hquad := regularizedPotential_quantile_error d hd (N n) (D.size_pos n) E eta heta
  rw [abs_sub_comm] at hquad
  have htri := abs_sub_le
    ((∑ i : Fin (N n), regularizedLog E eta (D.eigenvalue n ω i)) / (N n : ℝ))
    ((∑ i : Fin (N n), regularizedLog E eta (D.kestenMcKayQuantile hd n i)) / (N n : ℝ))
    (regularizedPotential d E eta)
  exact htri.trans ((add_le_add hfinite hquad).trans_eq (by dsimp [r]; ring))

end GeneralizedBulk.External.RegularSpectralData
