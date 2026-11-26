import GaussianWave.BS.Lower.CoverRecoloring
import GaussianWave.BS.Lower.ApproximateCodingEntropy

/-! Literal finite product masses restrict to the product of their selected
one-site masses along every finite injection. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
namespace GaussianWave.BS.Lower
open GaussianWave.BS.Reused.Entropy GaussianWave.BS.Reused.Entropy.Finite

def finiteProductColoringLaw {V : Type*} [Fintype V] {q : ℕ}
    (p : V → Fin q → ℝ) (hp : ∀ v b, 0 ≤ p v b) (hs : ∀ v, ∑ b, p v b = 1) :
    Measure (V → Fin q) := Measure.pi (fun v => finiteColorLaw (p v) (hp v) (hs v))

instance finiteProductColoringLaw_probability {V : Type*} [Fintype V] {q : ℕ}
    (p : V → Fin q → ℝ) (hp : ∀ v b, 0 ≤ p v b) (hs : ∀ v, ∑ b, p v b = 1) :
    IsProbabilityMeasure (finiteProductColoringLaw p hp hs) := by
  unfold finiteProductColoringLaw
  infer_instance

theorem finiteProductColoringLaw_lawMass {V : Type*} [Fintype V] {q : ℕ}
    (p : V → Fin q → ℝ) (hp : ∀ v b, 0 ≤ p v b) (hs : ∀ v, ∑ b, p v b = 1) :
    lawMass (finiteProductColoringLaw p hp hs) id = fun c => ∏ v, p v (c v) := by
  funext c
  have hc : ({c} : Set (V → Fin q)) = Set.univ.pi (fun v => {c v}) := by
    ext w
    simp [funext_iff]
  change (finiteProductColoringLaw p hp hs {c}).toReal = _
  rw [finiteProductColoringLaw, hc, Measure.pi_pi]
  simp only [finiteColorLaw_singleton, ENNReal.toReal_prod, ENNReal.toReal_ofReal (hp _ _)]

theorem finiteProductColoringLaw_eval {V : Type*} [Fintype V] {q : ℕ}
    (p : V → Fin q → ℝ) (hp : ∀ v b, 0 ≤ p v b) (hs : ∀ v, ∑ b, p v b = 1) (v : V) :
    Measure.map (fun c : V → Fin q => c v) (finiteProductColoringLaw p hp hs) =
      finiteColorLaw (p v) (hp v) (hs v) := by
  ext s hsmeas
  rw [Measure.map_apply (measurable_pi_apply v) hsmeas, finiteProductColoringLaw]
  change (Measure.pi (fun w => finiteColorLaw (p w) (hp w) (hs w))) (Function.eval v ⁻¹' s) = _
  rw [← Set.univ_pi_update_univ (α := fun _ : V => Fin q) v s, Measure.pi_pi]
  rw [Finset.prod_eq_single v]
  · simp only [Function.update_self]
  · intro w _ hwv
    simp only [Function.update_of_ne hwv, measure_univ]
  · simp

theorem finiteProductColoringLaw_restrict_mass {V S : Type*} [Fintype V] [Fintype S] {q : ℕ}
    (p : V → Fin q → ℝ) (hp : ∀ v b, 0 ≤ p v b) (hs : ∀ v, ∑ b, p v b = 1)
    (site : S ↪ V) (w : S → Fin q) :
    lawMass (finiteProductColoringLaw p hp hs) (fun c i => c (site i)) w =
      ∏ i, p (site i) (w i) := by
  let P := finiteProductColoringLaw p hp hs
  have hInd : iIndepFun (fun v (c : V → Fin q) => c v) P := by
    apply (iIndepFun_iff_map_fun_eq_pi_map (fun v => (measurable_pi_apply v).aemeasurable)).mpr
    change Measure.map id (finiteProductColoringLaw p hp hs) = _
    rw [Measure.map_id]
    change finiteProductColoringLaw p hp hs = Measure.pi (fun v =>
      Measure.map (fun c : V → Fin q => c v) (finiteProductColoringLaw p hp hs))
    simp_rw [finiteProductColoringLaw_eval]
    rfl
  have hIndS := hInd.precomp site.injective
  have hevent : (fun c : V → Fin q => fun i => c (site i)) ⁻¹' {w} =
      ⋂ i : S, (fun c : V → Fin q => c (site i)) ⁻¹' {w i} := by
    ext c
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter]
    exact funext_iff
  have hmarg (i : S) : P ((fun c : V → Fin q => c (site i)) ⁻¹' {w i}) =
      ENNReal.ofReal (p (site i) (w i)) := by
    rw [← Measure.map_apply (measurable_pi_apply (site i)) (measurableSet_singleton (w i))]
    change Measure.map _ (finiteProductColoringLaw p hp hs) _ = _
    rw [finiteProductColoringLaw_eval, finiteColorLaw_singleton]
  change (P ((fun c : V → Fin q => fun i => c (site i)) ⁻¹' {w})).toReal = _
  rw [hevent]
  have heq := hIndS.measure_inter_preimage_eq_mul Finset.univ
    (sets := fun i : S => {w i}) (fun i _ => measurableSet_singleton (w i))
  simp only [Finset.mem_univ, Set.iInter_true] at heq
  rw [heq]
  simp_rw [hmarg]
  simp only [ENNReal.toReal_prod, ENNReal.toReal_ofReal (hp _ _)]

theorem finiteProductMass_restrict_push {V S : Type*} [Fintype V] [Fintype S] {q : ℕ}
    (p : V → Fin q → ℝ) (hp : ∀ v b, 0 ≤ p v b) (hs : ∀ v, ∑ b, p v b = 1)
    (site : S ↪ V) (b : S → Fin q) :
    pushMass (fun c : V → Fin q => fun i => c (site i))
      (fun c => ∏ v, p v (c v)) b = ∏ i, p (site i) (b i) := by
  rw [← finiteProductColoringLaw_lawMass p hp hs,
    finite_pushMass_lawMass _ id measurable_id]
  exact finiteProductColoringLaw_restrict_mass p hp hs site b

theorem finiteProductMass_marker_factor {V : Type*} [Fintype V] (w : V → ℝ) (m : ℕ) :
    (∏ v, w v / (m : ℝ)) = (∏ v, w v) * ((m : ℝ) ^ Fintype.card V)⁻¹ := by
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const, Finset.card_univ, div_eq_mul_inv]

theorem finiteEntropy_marker {F : Type*} [Fintype F]
    (p : F → ℝ) (hs : ∑ b, p b = 1) (m : ℕ) (hm : 0 < m) :
    entropy (fun b : F × Fin m => p b.1 / (m : ℝ)) = entropy p + Real.log m := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hu : (∑ _ : Fin m, (m : ℝ)⁻¹) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_inv_cancel₀ hm0
  have hent : entropy (fun _ : Fin m => (m : ℝ)⁻¹) = Real.log m := by
    simp only [entropy, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Real.negMulLog_def, Real.log_inv]
    field_simp
  simpa only [div_eq_mul_inv, hent] using
    entropy_product p (fun _ : Fin m => (m : ℝ)⁻¹) hs hu

end GaussianWave.BS.Lower
