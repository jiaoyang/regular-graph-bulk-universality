import BourgadeHuang.RationalEdge.RootPathBounds
import BourgadeHuang.RationalEdge.ChargeReanchoring
import BourgadeHuang.EdgeCMS.PhysicalChamber

/-! Uniform bounds for the actual phase-normalized charged expectation on
positive dilations of bounded off-real sectors. The moving common anchors
cancel by the two charge balances. No asymptotic observable bound is assumed. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory
namespace BourgadeHuang.RationalEdge
open RationalBulk EdgeCMS

/-- The actual charged expectation with its deterministic Airy phase removed.
The two fixed anchors are `i` and `-i`. -/
def phaseNormalizedObservable {d : ℕ} (ν : Measure AnchoredCountingState)
    (c : Fin d → ℂ) (epsilon : Fin d → Bool) (z : Fin d → ℂ) : ℂ :=
  Complex.exp (-(∑ i, c i * edgePrimitive (z i))) *
    expectedChargedObservable ν c (fun i => reflectComplex (epsilon i) Complex.I) z

private theorem reflect_twice (e : Bool) (z : ℂ) :
    reflectComplex e (reflectComplex e z) = z := by
  cases e <;> simp [reflectComplex]

/-- Neutrality removes both the moving random anchor and its deterministic
phase, before applying any estimate. -/
theorem phaseNormalizedObservable_eq_moving_anchor {d : ℕ}
    (ν : Measure AnchoredCountingState) (c : Fin d → ℂ) (epsilon : Fin d → Bool)
    (hzero : ∑ i, c i = 0)
    (hsigned : ∑ i, c i * CMS.signValue (epsilon i) = 0)
    (z : Fin d → ℂ) (hz : ∀ i, 0 < (reflectComplex (epsilon i) (z i)).im)
    {r : ℝ} (hr : 0 < r) :
    phaseNormalizedObservable ν c epsilon z =
      Complex.exp (-(∑ i, c i * (edgePrimitive (z i) -
        edgePrimitive ((r : ℂ) * reflectComplex (epsilon i) Complex.I)))) *
        expectedChargedObservable ν c
          (fun i => (r : ℂ) * reflectComplex (epsilon i) Complex.I) z := by
  have hb (e : Bool) :
      SameOpenHalfPlane ((r : ℂ) * reflectComplex e Complex.I) (reflectComplex e Complex.I) := by
    apply sameOpenHalfPlane_of_reflect_pos e
    · rw [reflectComplex_ofReal_mul, reflect_twice]
      simpa using hr
    · rw [reflect_twice]
      norm_num
  have hzb i : SameOpenHalfPlane (z i) (reflectComplex (epsilon i) Complex.I) := by
    apply sameOpenHalfPlane_of_reflect_pos (epsilon i) (hz i)
    rw [reflect_twice]
    norm_num
  have he := expectedChargedObservable_reanchor_halfplanes ν c epsilon z
    (fun e => reflectComplex e Complex.I)
    (fun e => (r : ℂ) * reflectComplex e Complex.I) hzero hsigned hzb hb
  have hp : (∑ i, c i * (edgePrimitive (z i) -
      edgePrimitive ((r : ℂ) * reflectComplex (epsilon i) Complex.I))) =
      ∑ i, c i * edgePrimitive (z i) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, sum_charge_bool_eq_zero c epsilon hzero hsigned
      (fun e => edgePrimitive ((r : ℂ) * reflectComplex e Complex.I)), sub_zero]
  unfold phaseNormalizedObservable
  rw [hp, he]

/-- Uniform sector estimate under every positive dilation. All constants are
independent of the dilation and of the point in the prescribed bounded sector. -/
theorem exists_phaseNormalizedObservable_dilation_bound
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν] (β : ℝ)
    (hh : ExactHierarchy ν β) {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a * ‖s.val.2‖ ^ 2)) ν)
    {d : ℕ} (hd : 0 < d) (c : Fin d → ℂ) (epsilon : Fin d → Bool)
    (hzero : ∑ i, c i = 0)
    (hsigned : ∑ i, c i * CMS.signValue (epsilon i) = 0)
    (η M : ℝ) (hη : 0 < η) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → ∀ z : Fin d → ℂ,
      (∀ i, η ≤ (reflectComplex (epsilon i) (z i)).im) →
      (∀ i, (reflectComplex (epsilon i) (z i)).re ≤
        (reflectComplex (epsilon i) (z i)).im) →
      (∀ i, ‖z i‖ ≤ M) →
      ‖phaseNormalizedObservable ν c epsilon (fun i => (r : ℂ) * z i)‖ ≤ C := by
  let L : ℝ := ‖c‖ + 1
  have hL : 0 < L := by dsimp [L]; positivity
  have hc i : ‖c i‖ ≤ L := (norm_le_pi_norm c i).trans (by dsimp [L]; linarith)
  let m : ℝ := min η 1
  have hm : 0 < m := lt_min hη (by norm_num)
  let δ : ℝ := L * (M + 1) / m
  have hδ : 0 < δ := div_pos (mul_pos hL (by linarith)) hm
  have hδm : δ * m = L * (M + 1) := div_mul_cancel₀ _ hm.ne'
  let B : ℝ := δ * (16 * localLawConstant β * edgeStabilityConstant 4 * (d : ℝ)^2 +
    (d : ℝ) * Real.exp (((d : ℝ) * δ)^2 / edgeExponentialScale β 4))
  refine ⟨|B| + 1, by positivity, ?_⟩
  intro r hr z him hsector hnorm
  let u : Fin d → ℂ := fun i => (r : ℂ) * z i
  let v : Fin d → ℂ := fun i => (r : ℂ) * reflectComplex (epsilon i) Complex.I
  have hui i : (reflectComplex (epsilon i) (u i)).im =
      r * (reflectComplex (epsilon i) (z i)).im := by
    dsimp [u]
    rw [reflectComplex_ofReal_mul]
    simp
  have hvi i : (reflectComplex (epsilon i) (v i)).im = r := by
    dsimp [v]
    rw [reflectComplex_ofReal_mul, reflect_twice]
    simp
  have hu i : 0 < (reflectComplex (epsilon i) (u i)).im := by
    rw [hui]
    exact mul_pos hr (hη.trans_le (him i))
  have hv i : 0 < (reflectComplex (epsilon i) (v i)).im := by
    rw [hvi]
    exact hr
  have hus i : (reflectComplex (epsilon i) (u i)).re ≤
      (reflectComplex (epsilon i) (u i)).im := by
    dsimp [u]
    rw [reflectComplex_ofReal_mul]
    simpa using mul_le_mul_of_nonneg_left (hsector i) hr.le
  have hvs i : (reflectComplex (epsilon i) (v i)).re ≤
      (reflectComplex (epsilon i) (v i)).im := by
    dsimp [v]
    rw [reflectComplex_ofReal_mul, reflect_twice]
    simpa using hr.le
  have hcost i : ‖c i * (u i - v i)‖ ≤ δ * min
      (reflectComplex (epsilon i) (u i)).im
      (reflectComplex (epsilon i) (v i)).im := by
    have hdist : ‖z i - reflectComplex (epsilon i) Complex.I‖ ≤ M + 1 := by
      exact (norm_sub_le _ _).trans (by simpa using add_le_add_right (hnorm i) 1)
    have hmin : r * m ≤ min (reflectComplex (epsilon i) (u i)).im
        (reflectComplex (epsilon i) (v i)).im := by
      rw [hui, hvi]
      apply le_min
      · exact mul_le_mul_of_nonneg_left ((min_le_left η 1).trans (him i)) hr.le
      · simpa using mul_le_mul_of_nonneg_left (min_le_right η 1) hr.le
    calc
      ‖c i * (u i - v i)‖ = r * (‖c i‖ * ‖z i - reflectComplex (epsilon i) Complex.I‖) := by
        dsimp [u, v]
        rw [← mul_sub, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
        ring
      _ ≤ r * (L * (M + 1)) := mul_le_mul_of_nonneg_left
        (mul_le_mul (hc i) hdist (norm_nonneg _) hL.le) hr.le
      _ = δ * (r * m) := by rw [← hδm]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmin hδ.le
  have hbound := expectedChargedObservable_airyPhase_bound ν β hh ha he hd c u v epsilon
    hu hv hus hvs hδ hcost
  have hrew := phaseNormalizedObservable_eq_moving_anchor ν c epsilon hzero hsigned u hu hr
  change phaseNormalizedObservable ν c epsilon u = _ at hrew
  rw [← hrew] at hbound
  have hn : ‖phaseNormalizedObservable ν c epsilon u‖ ≤ B + 1 := by
    calc
      _ = ‖(phaseNormalizedObservable ν c epsilon u - 1) + 1‖ := by congr 1; ring
      _ ≤ ‖phaseNormalizedObservable ν c epsilon u - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ B + 1 := by simpa only [norm_one] using add_le_add_right hbound 1
  exact hn.trans (add_le_add_right (le_abs_self B) 1)

end BourgadeHuang.RationalEdge
