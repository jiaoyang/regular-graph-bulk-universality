import BourgadeHuang.CMS.BlockCoordinates
import BourgadeHuang.CMS.ExplicitSolutions
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! The explicit reduced solutions lifted to the original beta=2 equations.
All coordinate regularity needed by the gauge theorem is derived from genuine
multivariable complex analyticity. -/
noncomputable section
open scoped BigOperators Topology
namespace BourgadeHuang.CMS

/-- Restrict a combined-coordinate function to the two blocks of Appendix D. -/
def restrictBlocks {n m : ℕ} (f : Point (n + m) → ℂ)
    (t : Point n) (s : Point m) : ℂ := f (Fin.append t s)

@[simp] theorem blockFunction_restrictBlocks {n m : ℕ} (f : Point (n + m) → ℂ) :
    blockFunction (restrictBlocks f) = f := by
  funext z
  simp only [blockFunction, restrictBlocks, Fin.append_castAdd_natAdd]

/-- Coordinate-line restrictions of a multivariable analytic function are analytic. -/
theorem analyticAt_restrictBlocks_left {n m : ℕ} (f : Point (n + m) → ℂ)
    (t : Point n) (s : Point m) (i : Fin n)
    (hf : AnalyticAt ℂ f (Fin.append t s)) :
    AnalyticAt ℂ (fun u : ℂ => restrictBlocks f (Function.update t i u) s) (t i) := by
  have hm : AnalyticAt ℂ (fun u : ℂ => Fin.append (Function.update t i u) s) (t i) := by
    apply AnalyticAt.pi
    intro r
    refine Fin.addCases (fun j => ?_) (fun a => ?_) r
    · by_cases hji : j = i
      · subst j
        simpa only [Fin.append_left, Function.update_self] using
          (analyticAt_id : AnalyticAt ℂ (fun u : ℂ => u) (t i))
      · simpa only [Fin.append_left, Function.update_of_ne hji] using
          (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => t j) (t i))
    · simpa only [Fin.append_right] using
        (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => s a) (t i))
  exact hf.comp_of_eq hm (by simp)

theorem analyticAt_restrictBlocks_right {n m : ℕ} (f : Point (n + m) → ℂ)
    (t : Point n) (s : Point m) (a : Fin m)
    (hf : AnalyticAt ℂ f (Fin.append t s)) :
    AnalyticAt ℂ (fun u : ℂ => restrictBlocks f t (Function.update s a u)) (s a) := by
  have hm : AnalyticAt ℂ (fun u : ℂ => Fin.append t (Function.update s a u)) (s a) := by
    apply AnalyticAt.pi
    intro r
    refine Fin.addCases (fun i => ?_) (fun b => ?_) r
    · simpa only [Fin.append_left] using
        (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => t i) (s a))
    · by_cases hba : b = a
      · subst b
        simpa only [Fin.append_right, Function.update_self] using
          (analyticAt_id : AnalyticAt ℂ (fun u : ℂ => u) (s a))
      · simpa only [Fin.append_right, Function.update_of_ne hba] using
          (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => s b) (s a))
  exact hf.comp_of_eq hm (by simp)

/-- Pointwise gauge equivalence with regularity supplied solely by genuine
multivariable analyticity of the combined-coordinate function. -/
theorem analytic_gauge_system_iff {n m : ℕ} (t : Point n) (s : Point m)
    (f : Point (n + m) → ℂ) (hz : CollisionFree (Fin.append t s))
    (hf : AnalyticAt ℂ f (Fin.append t s)) :
    ((∀ i, leftOriginal i (fun t s => mixedVandermonde t s * restrictBlocks f t s) t s = 0) ∧
     (∀ a, rightOriginal a (fun t s => mixedVandermonde t s * restrictBlocks f t s) t s = 0)) ↔
    (∀ r, reducedOperator r f (Fin.append t s) = 0) := by
  obtain ⟨ht, hs, hc⟩ := (collisionFree_append t s).mp hz
  have hl (i : Fin n) := analyticAt_restrictBlocks_left f t s i hf
  have hr (a : Fin m) := analyticAt_restrictBlocks_right f t s a hf
  have hgl (i : Fin n) : ∀ᶠ u in 𝓝 (t i),
      DifferentiableAt ℂ (fun v => restrictBlocks f (Function.update t i v) s) u :=
    (hl i).eventually_analyticAt.mono (fun _ h => h.differentiableAt)
  have hgr (a : Fin m) : ∀ᶠ u in 𝓝 (s a),
      DifferentiableAt ℂ (fun v => restrictBlocks f t (Function.update s a v)) u :=
    (hr a).eventually_analyticAt.mono (fun _ h => h.differentiableAt)
  have hgl2 (i : Fin n) : DifferentiableAt ℂ
      (fun u => leftPartial i (restrictBlocks f) (Function.update t i u) s) (t i) := by
    simpa only [leftPartial, Function.update_idem, Function.update_self] using
      (hl i).deriv.differentiableAt
  have hgr2 (a : Fin m) : DifferentiableAt ℂ
      (fun u => rightPartial a (restrictBlocks f) t (Function.update s a u)) (s a) := by
    simpa only [rightPartial, Function.update_idem, Function.update_self] using
      (hr a).deriv.differentiableAt
  simpa only [blockFunction_restrictBlocks] using
    gauge_combined_system_iff t s (restrictBlocks f) hc ht hs hgl hgr hgl2 hgr2

/-- The branch-free explicit function `P G_sigma`, before identifying the
finite products with the displayed form (6.1). -/
def liftedExplicitSolution {n m : ℕ} (σ : Fin (n + m) → Sign)
    (t : Point n) (s : Point m) : ℂ :=
  mixedVandermonde t s * explicitSolution σ (Fin.append t s)

/-- Every actual explicit reduced solution lifts to an actual solution of the
original beta=2 system. There are no regularity or PDE hypotheses: only the
collision-free evaluation domain is assumed. -/
theorem liftedExplicitSolution_solves {n m : ℕ} (σ : Fin (n + m) → Sign)
    (t : Point n) (s : Point m) (hz : CollisionFree (Fin.append t s)) :
    (∀ i, leftOriginal i (liftedExplicitSolution σ) t s = 0) ∧
    (∀ a, rightOriginal a (liftedExplicitSolution σ) t s = 0) := by
  have h := (analytic_gauge_system_iff t s (explicitSolution σ) hz
    (analyticAt_explicitSolution σ hz)).mpr
      (fun r => explicitSolution_isReducedSolution σ (Fin.append t s) hz r)
  simpa only [liftedExplicitSolution, restrictBlocks] using h

/-- The branch-free meaning of formula (6.1): same-block opposite-sign pairs
contribute inverses, and cross-block equal-sign pairs contribute differences. -/
def formula61 {n m : ℕ} (ε : Fin n → Sign) (η : Fin m → Sign)
    (t : Point n) (s : Point m) : ℂ :=
  Complex.exp (phase ε t + phase η s) * delta ε t * delta η s *
    ∏ i, ∏ a, if ε i = η a then t i - s a else 1

theorem phase_append {n m : ℕ} (ε : Fin n → Sign) (η : Fin m → Sign)
    (t : Point n) (s : Point m) :
    phase (Fin.append ε η) (Fin.append t s) = phase ε t + phase η s := by
  unfold phase
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  ring

/-- The ordered rational product splits into its within-block and cross-block
factors. The reverse cross block has no ordered pairs and contributes one. -/
theorem delta_append {n m : ℕ} (ε : Fin n → Sign) (η : Fin m → Sign)
    (t : Point n) (s : Point m) :
    delta (Fin.append ε η) (Fin.append t s) = delta ε t * delta η s *
      ∏ i, ∏ a, if ε i ≠ η a then (t i - s a)⁻¹ else 1 := by
  have hlt (i : Fin n) (a : Fin m) : Fin.castAdd m i < Fin.natAdd n a :=
    Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right n a.val)
  have hnot (a : Fin m) (i : Fin n) : ¬ Fin.natAdd n a < Fin.castAdd m i :=
    not_lt_of_ge (le_of_lt (hlt i a))
  simp only [delta, oppositePairs, Finset.prod_filter, Fintype.prod_prod_type]
  rw [Fin.prod_univ_add]
  simp_rw [Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right, hlt, hnot, false_and,
    true_and, if_false, Finset.prod_const_one, one_mul]
  simp only [Fin.lt_def, Fin.coe_castAdd, Fin.coe_natAdd, Nat.add_lt_add_iff_left]
  rw [Finset.prod_mul_distrib]
  ring

/-- Cancellation of the cross-block inverse factors uses the explicitly stated
noncollision hypotheses; no division by zero is used. -/
theorem mixedVandermonde_mul_crossInverse {n m : ℕ}
    (ε : Fin n → Sign) (η : Fin m → Sign) (t : Point n) (s : Point m)
    (hc : CrossDistinct t s) :
    mixedVandermonde t s * (∏ i, ∏ a, if ε i ≠ η a then (t i - s a)⁻¹ else 1) =
      ∏ i, ∏ a, if ε i = η a then t i - s a else 1 := by
  unfold mixedVandermonde
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro a _
  by_cases h : ε i = η a
  · simp [h]
  · simp [h, sub_ne_zero.mpr (hc i a)]

/-- Literal finite-product identification with formula (6.1), including its
fixed ordering of all factors. -/
theorem liftedExplicitSolution_eq_formula61 {n m : ℕ}
    (ε : Fin n → Sign) (η : Fin m → Sign) (t : Point n) (s : Point m)
    (hc : CrossDistinct t s) :
    liftedExplicitSolution (Fin.append ε η) t s = formula61 ε η t s := by
  unfold liftedExplicitSolution explicitSolution formula61
  rw [phase_append, delta_append]
  have h := mixedVandermonde_mul_crossInverse ε η t s hc
  calc
    _ = (Complex.exp (phase ε t + phase η s) * delta ε t * delta η s) *
      (mixedVandermonde t s * ∏ i, ∏ a, if ε i ≠ η a then (t i - s a)⁻¹ else 1) := by ring
    _ = _ := by rw [h]


/-- The original differential operators depend only on the function's germ
inside the open cross-noncollision domain. -/
theorem originalOperators_congr_crossDistinct {n m : ℕ}
    (F H : Point n → Point m → ℂ)
    (heq : ∀ t s, CrossDistinct t s → F t s = H t s)
    (t : Point n) (s : Point m) (hc : CrossDistinct t s) :
    (∀ i, leftOriginal i F t s = leftOriginal i H t s) ∧
    (∀ a, rightOriginal a F t s = rightOriginal a H t s) := by
  have hl (i : Fin n) :
      (fun u => F (Function.update t i u) s) =ᶠ[𝓝 (t i)]
        (fun u => H (Function.update t i u) s) := by
    filter_upwards [eventually_crossDistinct_left t s i hc] with u hu
    exact heq _ _ hu
  have hr (a : Fin m) :
      (fun u => F t (Function.update s a u)) =ᶠ[𝓝 (s a)]
        (fun u => H t (Function.update s a u)) := by
    filter_upwards [eventually_crossDistinct_right t s a hc] with u hu
    exact heq _ _ hu
  have hl1 (i : Fin n) : leftPartial i F t s = leftPartial i H t s := (hl i).deriv_eq
  have hr1 (a : Fin m) : rightPartial a F t s = rightPartial a H t s := (hr a).deriv_eq
  have hl2 (i : Fin n) : leftPartial i (leftPartial i F) t s =
      leftPartial i (leftPartial i H) t s := by
    simpa only [leftPartial, Function.update_idem, Function.update_self] using
      (hl i).deriv.deriv_eq
  have hr2 (a : Fin m) : rightPartial a (rightPartial a F) t s =
      rightPartial a (rightPartial a H) t s := by
    simpa only [rightPartial, Function.update_idem, Function.update_self] using
      (hr a).deriv.deriv_eq
  have h0 := heq t s hc
  constructor
  · intro i
    simp only [leftOriginal, hl2, hl1, hr1, h0]
  · intro a
    simp only [rightOriginal, hr2, hr1, hl1, h0]

/-- The displayed functions (6.1), with all exponents represented by explicit
inverse/difference alternatives, solve the original beta=2 system. -/
theorem formula61_solves {n m : ℕ} (ε : Fin n → Sign) (η : Fin m → Sign)
    (t : Point n) (s : Point m) (hz : CollisionFree (Fin.append t s)) :
    (∀ i, leftOriginal i (formula61 ε η) t s = 0) ∧
    (∀ a, rightOriginal a (formula61 ε η) t s = 0) := by
  have hc := ((collisionFree_append t s).mp hz).2.2
  have heq := originalOperators_congr_crossDistinct
    (liftedExplicitSolution (Fin.append ε η)) (formula61 ε η)
    (fun t s hc => liftedExplicitSolution_eq_formula61 ε η t s hc) t s hc
  have h := liftedExplicitSolution_solves (Fin.append ε η) t s hz
  constructor
  · intro i
    rw [← heq.1 i]
    exact h.1 i
  · intro a
    rw [← heq.2 a]
    exact h.2 a


end BourgadeHuang.CMS
