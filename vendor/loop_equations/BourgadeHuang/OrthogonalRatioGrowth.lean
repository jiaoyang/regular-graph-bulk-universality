import BourgadeHuang.OrthogonalRatioPaths
import BourgadeHuang.OrthogonalRatioAnalytic

/-! Exact exponential growth of the genuine orthogonal ratio expectation.
Only relative straight-path costs enter the remaining constant. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang

theorem norm_entireCharacteristicRatios_normalized_upper {q : ℕ}
    (s : AnchoredCountingState) (u v : Fin q → ℂ)
    (hu : ∀j,(u j).im≠0) (hv : ∀j,(v j).im≠0) :
    ‖entireCharacteristicRatios s u v‖ =
      Real.exp (∑j,(|(u j).im|-|(v j).im|))*
        ∏j,‖normalizedUpperRatio s (upperRepresentative (u j)) (upperRepresentative (v j))‖ := by
  unfold entireCharacteristicRatios
  rw [norm_prod]
  simp_rw [norm_entireCharacteristicRatio_normalized_upper s (hu _) (hv _)]
  rw [Finset.prod_mul_distrib,← Real.exp_sum]

theorem orthogonalCharacteristicRatios_sq {q : ℕ} (s : AnchoredCountingState)
    (u v w : Fin q → ℂ) (hwv : ∀j,SameOpenHalfPlane (w j) (v j)) :
    orthogonalCharacteristicRatios s u v w ^ 2 =
      entireCharacteristicRatios s u v * entireCharacteristicRatios s u w := by
  unfold orthogonalCharacteristicRatios entireCharacteristicRatios
  rw [← Finset.prod_pow]
  simp_rw [orthogonalCharacteristicRatio_sq s _ (hwv _)]
  exact Finset.prod_mul_distrib

/-- Finite products of normalized reflected ratios have uniform moments under
an actual orthogonal hierarchy. -/
theorem orthogonal_normalized_ratio_product_bound {q : ℕ} (hq : 0<q)
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hh : ExactAnchoredHierarchy ν .one) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState=>Real.exp (a*‖s.val.2‖^2)) ν)
    (u v : Fin q → ℂ) (hu : ∀j,(u j).im≠0) (hv : ∀j,(v j).im≠0)
    {D : ℝ} (hD : 0≤D)
    (hcost : ∀j,‖upperRepresentative (u j)-upperRepresentative (v j)‖≤
      D*min |(u j).im| |(v j).im|) :
    Integrable (fun s=>∏j,‖normalizedUpperRatio s (upperRepresentative (u j))
      (upperRepresentative (v j))‖) ν ∧
    (∫s,∏j,‖normalizedUpperRatio s (upperRepresentative (u j))
      (upperRepresentative (v j))‖ ∂ν)≤
      (q:ℝ)*(2*Real.exp (((q:ℝ)*D)^2/(4*orthogonalBulkExponentialScale))) := by
  let f := fun j s=>‖normalizedUpperRatio s (upperRepresentative (u j)) (upperRepresentative (v j))‖
  have hup j : 0<(upperRepresentative (u j)).im := by simpa using abs_pos.mpr (hu j)
  have hvp j : 0<(upperRepresentative (v j)).im := by simpa using abs_pos.mpr (hv j)
  have hscalar j := orthogonal_normalizedUpperRatio_rpow_bound ν hh ha he (hup j) (hvp j)
    hD (show (0:ℝ)≤(q:ℝ) by positivity) (by simpa using hcost j)
  apply finite_product_integral_bound hq ν f
    (fun j=>(measurable_normalizedUpperRatio (Or.inl ⟨hup j,hvp j⟩)).norm)
    (fun _ _=>norm_nonneg _)
  · intro j
    simpa only [f,Real.rpow_natCast] using (hscalar j).1
  · intro j
    simpa only [f,Real.rpow_natCast] using (hscalar j).2

/-- Both denominator branches carry precisely half their deterministic rate.
All dependence on relative endpoint locations is confined to a constant. -/
theorem expectedOrthogonalCharacteristicRatios_growth {q : ℕ} (hq : 0<q)
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hh : ExactAnchoredHierarchy ν .one) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState=>Real.exp (a*‖s.val.2‖^2)) ν)
    (u v w : Fin q → ℂ) (hu : ∀j,(u j).im≠0)
    (hwv : ∀j,SameOpenHalfPlane (w j) (v j)) {D : ℝ} (hD : 0≤D)
    (hvCost : ∀j,‖upperRepresentative (u j)-upperRepresentative (v j)‖≤
      D*min |(u j).im| |(v j).im|)
    (hwCost : ∀j,‖upperRepresentative (u j)-upperRepresentative (w j)‖≤
      D*min |(u j).im| |(w j).im|) :
    ‖expectedOrthogonalCharacteristicRatios ν u v w‖≤
      ((q:ℝ)*(2*Real.exp (((q:ℝ)*D)^2/(4*orthogonalBulkExponentialScale))))*
      Real.exp (∑j, (|(u j).im|-(|(v j).im|+|(w j).im|)/2)) := by
  have hv j : (v j).im≠0 := (hwv j).elim (fun h=>h.2.ne') (fun h=>h.2.ne)
  have hw j : (w j).im≠0 := (hwv j).elim (fun h=>h.1.ne') (fun h=>h.1.ne)
  let A := fun s=>∏j,‖normalizedUpperRatio s (upperRepresentative (u j)) (upperRepresentative (v j))‖
  let B := fun s=>∏j,‖normalizedUpperRatio s (upperRepresentative (u j)) (upperRepresentative (w j))‖
  let M := Real.exp (∑j, (|(u j).im|-(|(v j).im|+|(w j).im|)/2))
  let C := (q:ℝ)*(2*Real.exp (((q:ℝ)*D)^2/(4*orthogonalBulkExponentialScale)))
  have hM : 0≤M := (Real.exp_pos _).le
  have hA s : 0≤A s := Finset.prod_nonneg (fun _ _=>norm_nonneg _)
  have hB s : 0≤B s := Finset.prod_nonneg (fun _ _=>norm_nonneg _)
  obtain ⟨hiA,hbA⟩ := orthogonal_normalized_ratio_product_bound hq ν hh ha he u v hu hv hD hvCost
  obtain ⟨hiB,hbB⟩ := orthogonal_normalized_ratio_product_bound hq ν hh ha he u w hu hw hD hwCost
  have hpow : Real.exp (∑j, (|(u j).im|-|(v j).im|))*
      Real.exp (∑j, (|(u j).im|-|(w j).im|))=M^2 := by
    rw [← Real.exp_add]
    dsimp [M]
    rw [sq,← Real.exp_add]
    congr 1
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hsq s : ‖orthogonalCharacteristicRatios s u v w‖^2=M^2*A s*B s := by
    have h := congrArg norm (orthogonalCharacteristicRatios_sq s u v w hwv)
    rw [norm_pow,norm_mul,norm_entireCharacteristicRatios_normalized_upper s u v hu hv,
      norm_entireCharacteristicRatios_normalized_upper s u w hu hw] at h
    change _=(Real.exp _*A s)*(Real.exp _*B s) at h
    rw [h]
    calc
      _ = (Real.exp (∑j, (|(u j).im|-|(v j).im|))*Real.exp (∑j, (|(u j).im|-|(w j).im|)))*A s*B s := by ring
      _ = _ := by rw [hpow]
  have hpoint s : ‖orthogonalCharacteristicRatios s u v w‖≤M*((A s+B s)/2) := by
    have hright : 0≤M*((A s+B s)/2) := by positivity
    apply (sq_le_sq₀ (norm_nonneg _) hright).mp
    rw [hsq]
    nlinarith [mul_nonneg (sq_nonneg M) (sq_nonneg (A s-B s))]
  have hi := (integrable_orthogonalCharacteristicRatios ν ha he u v w hwv).norm
  calc
    _ ≤ ∫s,‖orthogonalCharacteristicRatios s u v w‖ ∂ν := norm_integral_le_integral_norm _
    _ ≤ ∫s,M*((A s+B s)/2) ∂ν := integral_mono hi (((hiA.add hiB).div_const 2).const_mul M) hpoint
    _ = M*((∫s,A s ∂ν)+(∫s,B s ∂ν))/2 := by
      rw [integral_const_mul,integral_div,integral_add hiA hiB]
      ring
    _ ≤ M*(C+C)/2 := by gcongr
    _ = _ := by dsimp [M,C]; ring

end BourgadeHuang
