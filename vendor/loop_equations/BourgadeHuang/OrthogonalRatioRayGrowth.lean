import BourgadeHuang.OrthogonalRatioGrowth

/-! Genuine orthogonal expectations have uniform exact exponential rates on
homogeneous rays; no asymptotic observable-growth assumption is introduced. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang

theorem upperRepresentative_real_mul (z : ℂ) {r : ℝ} (hr : 0≤r) :
    upperRepresentative ((r:ℂ)*z)=(r:ℂ)*upperRepresentative z := by
  apply Complex.ext <;> simp [upperRepresentative,abs_mul,abs_of_nonneg hr]

theorem sameOpenHalfPlane_real_mul {u v : ℂ} (h : SameOpenHalfPlane u v)
    {r : ℝ} (hr : 0<r) : SameOpenHalfPlane ((r:ℂ)*u) ((r:ℂ)*v) := by
  rcases h with h|h
  · left
    simpa using And.intro (mul_pos hr h.1) (mul_pos hr h.2)
  · right
    simpa using And.intro (mul_neg_of_pos_of_neg hr h.1) (mul_neg_of_pos_of_neg hr h.2)

theorem reflected_ratio_cost_real_mul {u v : ℂ} {D r : ℝ} (hr : 0≤r)
    (h : ‖upperRepresentative u-upperRepresentative v‖≤D*min |u.im| |v.im|) :
    ‖upperRepresentative ((r:ℂ)*u)-upperRepresentative ((r:ℂ)*v)‖≤
      D*min |((r:ℂ)*u).im| |((r:ℂ)*v).im| := by
  rw [upperRepresentative_real_mul u hr,upperRepresentative_real_mul v hr,← mul_sub,norm_mul]
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,abs_mul,abs_of_nonneg hr]
  rw [← mul_min_of_nonneg _ _ hr]
  simpa only [mul_left_comm D r] using mul_le_mul_of_nonneg_left h hr

/-- A uniform constant exists before the scale parameter is chosen. -/
theorem expectedOrthogonalCharacteristicRatios_homogeneous_growth {q : ℕ}
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hh : ExactAnchoredHierarchy ν .one) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState=>Real.exp (a*‖s.val.2‖^2)) ν)
    (u v w : Fin q → ℂ) (hu : ∀j,(u j).im≠0)
    (hwv : ∀j,SameOpenHalfPlane (w j) (v j)) :
    ∃C : ℝ, 0≤C ∧ ∀r : ℝ, 0<r →
      ‖expectedOrthogonalCharacteristicRatios ν
        (fun j=>(r:ℂ)*u j) (fun j=>(r:ℂ)*v j) (fun j=>(r:ℂ)*w j)‖≤
      C*Real.exp (r*(∑j,(|(u j).im|-(|(v j).im|+|(w j).im|)/2))) := by
  by_cases hq : q=0
  · subst q
    refine ⟨1,zero_le_one,?_⟩
    intro r _
    simp [expectedOrthogonalCharacteristicRatios,orthogonalCharacteristicRatios]
  have hqp := Nat.pos_of_ne_zero hq
  have hv j : (v j).im≠0 := (hwv j).elim (fun h=>h.2.ne') (fun h=>h.2.ne)
  have hw j : (w j).im≠0 := (hwv j).elim (fun h=>h.1.ne') (fun h=>h.1.ne)
  let dv := fun j=>‖upperRepresentative (u j)-upperRepresentative (v j)‖/min |(u j).im| |(v j).im|
  let dw := fun j=>‖upperRepresentative (u j)-upperRepresentative (w j)‖/min |(u j).im| |(w j).im|
  have hvmin j : 0<min |(u j).im| |(v j).im| := lt_min (abs_pos.mpr (hu j)) (abs_pos.mpr (hv j))
  have hwmin j : 0<min |(u j).im| |(w j).im| := lt_min (abs_pos.mpr (hu j)) (abs_pos.mpr (hw j))
  have hdv j : 0≤dv j := div_nonneg (norm_nonneg _) (hvmin j).le
  have hdw j : 0≤dw j := div_nonneg (norm_nonneg _) (hwmin j).le
  let D := (∑j,dv j)+(∑j,dw j)
  have hD : 0≤D := add_nonneg (Finset.sum_nonneg (fun j _=>hdv j)) (Finset.sum_nonneg (fun j _=>hdw j))
  have hvc j : ‖upperRepresentative (u j)-upperRepresentative (v j)‖≤D*min |(u j).im| |(v j).im| := by
    apply (div_le_iff₀ (hvmin j)).mp
    exact (Finset.single_le_sum (fun i _=>hdv i) (Finset.mem_univ j)).trans
      (le_add_of_nonneg_right (Finset.sum_nonneg (fun i _=>hdw i)))
  have hwc j : ‖upperRepresentative (u j)-upperRepresentative (w j)‖≤D*min |(u j).im| |(w j).im| := by
    apply (div_le_iff₀ (hwmin j)).mp
    exact (Finset.single_le_sum (fun i _=>hdw i) (Finset.mem_univ j)).trans
      (le_add_of_nonneg_left (Finset.sum_nonneg (fun i _=>hdv i)))
  refine ⟨(q:ℝ)*(2*Real.exp (((q:ℝ)*D)^2/(4*orthogonalBulkExponentialScale))),by positivity,?_⟩
  intro r hr
  have hur j : ((r:ℂ)*u j).im≠0 := by
    simpa using mul_ne_zero hr.ne' (hu j)
  have h := expectedOrthogonalCharacteristicRatios_growth hqp ν hh ha he
    (fun j=>(r:ℂ)*u j) (fun j=>(r:ℂ)*v j) (fun j=>(r:ℂ)*w j)
    hur (fun j=>sameOpenHalfPlane_real_mul (hwv j) hr) hD
    (fun j=>reflected_ratio_cost_real_mul hr.le (hvc j))
    (fun j=>reflected_ratio_cost_real_mul hr.le (hwc j))
  convert h using 1
  congr 2
  simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,
    abs_mul,abs_of_pos hr,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end BourgadeHuang
