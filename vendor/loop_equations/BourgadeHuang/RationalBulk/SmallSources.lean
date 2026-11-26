import BourgadeHuang.RationalBulk.CompactSources
import BourgadeHuang.OrthogonalMixedNormalization

/-! General-beta small-source normalization with explicit vanishing error. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalBulk

theorem finiteReflectedCompactSource_exponential_close
    {T : Type*} [TopologicalSpace T] [TopologicalSpace.MetrizableSpace T]
    [SecondCountableTopology T] [CompactSpace T] [MeasurableSpace T] [BorelSpace T]
    {q : ℕ} (hq : 0<q) (κ : Measure T) [IsProbabilityMeasure κ]
    (ε : Fin q → Bool) (γ ρ : Fin q → T → ℂ)
    (hγ : ∀j, Continuous (γ j)) (hρ : ∀j, Continuous (ρ j)) (hup : ∀j t, 0<(γ j t).im)
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (β : ℝ) (hh : ExactHierarchy ν β) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    {δ : ℝ} (hδ : 0<δ) (hb : ∀j t, ‖ρ j t‖≤δ*(γ j t).im) :
    Integrable (fun s => Complex.exp (∑j, reflectComplex (ε j)
      (compactCenteredSource κ (γ j) (ρ j) s))) ν ∧
    ‖(∫ s, Complex.exp (∑j, reflectComplex (ε j)
      (compactCenteredSource κ (γ j) (ρ j) s)) ∂ν)-1‖ ≤
      δ*(16*localLawConstant β*(q:ℝ)^2+(q:ℝ)*Real.exp (((q:ℝ)*δ)^2/bulkExponentialScale β)) := by
  let X := fun j s => reflectComplex (ε j) (compactCenteredSource κ (γ j) (ρ j) s)
  have hm j : Measurable (X j) := (continuous_reflectComplex (ε j)).measurable.comp
    (measurable_compactCenteredSource κ (γ j) (ρ j) (hγ j) (hρ j) (hup j))
  have h2 j := compactCenteredSource_second_moment κ (γ j) (ρ j) (hγ j) (hρ j) (hup j)
    ν β hh ha he hδ.le (hb j)
  have h2i j : Integrable (fun s => ‖X j s‖^2) ν := by
    simpa only [X,norm_reflectComplex] using (h2 j).1
  have h2b j : (∫s, ‖X j s‖^2 ∂ν)≤(32*localLawConstant β)*δ^2 := by
    simpa only [X,norm_reflectComplex] using (h2 j).2
  obtain ⟨hXi2,hXb2⟩ := finite_sum_second_moment_bound ν X hm h2i ((32*localLawConstant β)*δ^2) h2b
  have hE j := compactCenteredSource_exp_bound κ (γ j) (ρ j) (hγ j) (hρ j) (hup j)
    ν β hh ha he hδ.le (show 0≤2*(q:ℝ) by positivity) (hb j)
  have hEi j : Integrable (fun s => Real.exp (2*(q:ℝ)*‖X j s‖)) ν := by
    simpa only [X,norm_reflectComplex] using (hE j).1
  have hEb j : (∫s, Real.exp (2*(q:ℝ)*‖X j s‖) ∂ν)≤
      2*Real.exp ((2*(q:ℝ)*δ)^2/(4*bulkExponentialScale β)) := by
    simpa only [X,norm_reflectComplex] using (hE j).2
  obtain ⟨hXiE,hXbE⟩ := finite_sum_exp_moment_bound hq ν X hm (by norm_num : (0:ℝ)≤2)
    hEi _ hEb
  obtain ⟨hi,hb'⟩ := exponential_expectation_close_of_second_moment ν
    (fun s => ∑j, X j s) (Finset.measurable_sum _ (fun j _ => hm j)) hXi2 hXiE hδ
  refine ⟨hi,hb'.trans ?_⟩
  calc
    _ ≤ ((q:ℝ)^2*((32*localLawConstant β)*δ^2))/(2*δ)+(δ/2)*
        ((q:ℝ)*(2*Real.exp ((2*(q:ℝ)*δ)^2/(4*bulkExponentialScale β)))) :=
      add_le_add (div_le_div_of_nonneg_right hXb2 (by positivity))
        (mul_le_mul_of_nonneg_left hXbE (by positivity))
    _ = _ := by
      have heq : (2*(q:ℝ)*δ)^2/(4*bulkExponentialScale β)=
          ((q:ℝ)*δ)^2/bulkExponentialScale β := by ring
      rw [heq]
      field_simp
      ring

end BourgadeHuang.RationalBulk
