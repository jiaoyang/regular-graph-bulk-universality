import BourgadeHuang.PointProcessModel

/-!
# Finite-particle integrability

Off-real reciprocal denominators are bounded independently of the particle positions.
Consequently every finite-N resolvent moment and every mixed loop integrand is
integrable for a finite measure, as soon as the particle coordinates are measurable.
These are proved consequences of the finite-particle model, not probabilistic inputs.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace BourgadeHuang

/-- Interaction bound for a diagonal parameter or its conjugate. -/
theorem norm_interaction_le {N : ℕ} (x : Fin N → ℝ) (center : ℝ)
    {w v : ℂ} (hw : 0 < w.im) (hv : v = w ∨ v = star w) :
    ‖interaction x w v‖ ≤ ‖microscopicResolvent x center w‖ / w.im ^ 2 := by
  have hn (i : Fin N) :
      ‖((x i : ℂ) - v)⁻¹‖ = ‖((x i : ℂ) - w)⁻¹‖ := by
    rcases hv with rfl | rfl
    · rfl
    · have h : ((x i : ℂ) - star w)⁻¹ = star (((x i : ℂ) - w)⁻¹) := by simp
      rw [h, norm_star]
  have hb (i : Fin N) : ‖((x i : ℂ) - w)⁻¹‖ ≤ 1 / w.im := by
    simpa only [abs_of_pos hw] using norm_reciprocal_le_im (x i) (ne_of_gt hw)
  calc
    ‖interaction x w v‖ ≤
        ∑ i, ‖((x i : ℂ) - w)⁻¹ * (((x i : ℂ) - v)⁻¹) ^ 2‖ :=
      norm_sum_le _ _
    _ = ∑ i, ‖((x i : ℂ) - w)⁻¹‖ * ‖((x i : ℂ) - w)⁻¹‖ ^ 2 := by
      simp only [norm_mul, norm_pow, hn]
    _ ≤ ∑ i, (1 / w.im) * ‖((x i : ℂ) - w)⁻¹‖ ^ 2 := by
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_right (hb i) (sq_nonneg _)
    _ = (1 / w.im) * ∑ i, (Complex.normSq ((x i : ℂ) - w))⁻¹ := by
      simp only [Complex.sq_norm, Complex.normSq_inv, Finset.mul_sum]
    _ = (microscopicResolvent x center w).im / w.im ^ 2 := by
      rw [microscopicResolvent_im_eq]
      field_simp [ne_of_gt hw]
      ring
    _ ≤ ‖microscopicResolvent x center w‖ / w.im ^ 2 :=
      div_le_div_of_nonneg_right (Complex.im_le_norm _) (sq_nonneg _)

private def BoundedMeasurable {Ω : Type*} [MeasurableSpace Ω] (f : Ω → ℂ) : Prop :=
  Measurable f ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ ω, ‖f ω‖ ≤ C

private theorem boundedMeasurable_const {Ω : Type*} [MeasurableSpace Ω] (c : ℂ) :
    BoundedMeasurable (fun _ : Ω => c) :=
  ⟨measurable_const, ‖c‖, norm_nonneg c, fun _ => le_rfl⟩

private theorem BoundedMeasurable.add {Ω : Type*} [MeasurableSpace Ω]
    {f g : Ω → ℂ} (hf : BoundedMeasurable f) (hg : BoundedMeasurable g) :
    BoundedMeasurable (fun ω => f ω + g ω) := by
  obtain ⟨C, hC, hCf⟩ := hf.2
  obtain ⟨D, hD, hDg⟩ := hg.2
  exact ⟨hf.1.add hg.1, C + D, add_nonneg hC hD,
    fun ω => (norm_add_le _ _).trans (add_le_add (hCf ω) (hDg ω))⟩

private theorem BoundedMeasurable.sub {Ω : Type*} [MeasurableSpace Ω]
    {f g : Ω → ℂ} (hf : BoundedMeasurable f) (hg : BoundedMeasurable g) :
    BoundedMeasurable (fun ω => f ω - g ω) := by
  obtain ⟨C, hC, hCf⟩ := hf.2
  obtain ⟨D, hD, hDg⟩ := hg.2
  exact ⟨hf.1.sub hg.1, C + D, add_nonneg hC hD,
    fun ω => (norm_sub_le _ _).trans (add_le_add (hCf ω) (hDg ω))⟩

private theorem BoundedMeasurable.mul {Ω : Type*} [MeasurableSpace Ω]
    {f g : Ω → ℂ} (hf : BoundedMeasurable f) (hg : BoundedMeasurable g) :
    BoundedMeasurable (fun ω => f ω * g ω) := by
  obtain ⟨C, hC, hCf⟩ := hf.2
  obtain ⟨D, hD, hDg⟩ := hg.2
  refine ⟨hf.1.mul hg.1, C * D, mul_nonneg hC hD, fun ω => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hCf ω) (hDg ω) (norm_nonneg _) hC

private theorem BoundedMeasurable.pow {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → ℂ} (hf : BoundedMeasurable f) (q : ℕ) :
    BoundedMeasurable (fun ω => f ω ^ q) := by
  obtain ⟨C, hC, hCf⟩ := hf.2
  refine ⟨hf.1.pow_const q, C ^ q, pow_nonneg hC q, fun ω => ?_⟩
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hCf ω) q

private theorem boundedMeasurable_sum {Ω ι : Type*} [MeasurableSpace Ω]
    (s : Finset ι) (f : ι → Ω → ℂ) (hf : ∀ i ∈ s, BoundedMeasurable (f i)) :
    BoundedMeasurable (fun ω => ∑ i ∈ s, f i ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using boundedMeasurable_const (Ω := Ω) 0
  | @insert a s ha ih =>
    simpa [Finset.sum_insert ha] using
      (hf a (Finset.mem_insert_self a s)).add
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private theorem boundedMeasurable_prod {Ω ι : Type*} [MeasurableSpace Ω]
    (s : Finset ι) (f : ι → Ω → ℂ) (hf : ∀ i ∈ s, BoundedMeasurable (f i)) :
    BoundedMeasurable (fun ω => ∏ i ∈ s, f i ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using boundedMeasurable_const (Ω := Ω) 1
  | @insert a s ha ih =>
    simpa [Finset.prod_insert ha] using
      (hf a (Finset.mem_insert_self a s)).mul
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private theorem BoundedMeasurable.integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℂ} (hf : BoundedMeasurable f) :
    Integrable f μ := by
  obtain ⟨C, _, hC⟩ := hf.2
  exact (integrable_const C).mono' hf.1.aestronglyMeasurable
    (Filter.Eventually.of_forall hC)

private theorem boundedMeasurable_reciprocal {Ω : Type*} [MeasurableSpace Ω]
    {x : Ω → ℝ} (hx : Measurable x) {w : ℂ} (hw : w.im ≠ 0) :
    BoundedMeasurable (fun ω => ((x ω : ℂ) - w)⁻¹) := by
  refine ⟨((Complex.continuous_ofReal.measurable.comp hx).sub_const w).inv,
    1 / |w.im|, div_nonneg (by norm_num) (abs_nonneg _), ?_⟩
  exact fun ω => norm_reciprocal_le_im (x ω) hw

private theorem boundedMeasurable_microscopicResolvent {Ω : Type*}
    [MeasurableSpace Ω] {N : ℕ} {x : Ω → Fin N → ℝ}
    (hx : ∀ i, Measurable (fun ω => x ω i)) (center : ℝ) {w : ℂ}
    (hw : w.im ≠ 0) :
    BoundedMeasurable (fun ω => microscopicResolvent (x ω) center w) := by
  exact (boundedMeasurable_sum Finset.univ
    (fun i ω => ((x ω i : ℂ) - w)⁻¹)
    (fun i _ => boundedMeasurable_reciprocal (hx i) hw)).sub
      (boundedMeasurable_const (center : ℂ))

private theorem boundedMeasurable_resolventDerivative {Ω : Type*}
    [MeasurableSpace Ω] {N : ℕ} {x : Ω → Fin N → ℝ}
    (hx : ∀ i, Measurable (fun ω => x ω i)) {w : ℂ} (hw : w.im ≠ 0) :
    BoundedMeasurable (fun ω => resolventDerivative (x ω) w) := by
  exact boundedMeasurable_sum Finset.univ
    (fun i ω => (((x ω i : ℂ) - w)⁻¹) ^ 2)
    (fun i _ => (boundedMeasurable_reciprocal (hx i) hw).pow 2)

private theorem boundedMeasurable_interaction {Ω : Type*} [MeasurableSpace Ω]
    {N : ℕ} {x : Ω → Fin N → ℝ} (hx : ∀ i, Measurable (fun ω => x ω i))
    {w v : ℂ} (hw : w.im ≠ 0) (hv : v.im ≠ 0) :
    BoundedMeasurable (fun ω => interaction (x ω) w v) := by
  exact boundedMeasurable_sum Finset.univ _ (fun i _ =>
    (boundedMeasurable_reciprocal (hx i) hw).mul
      ((boundedMeasurable_reciprocal (hx i) hv).pow 2))

theorem measurable_microscopicResolvent {Ω : Type*} [MeasurableSpace Ω]
    {N : ℕ} {x : Ω → Fin N → ℝ} (hx : ∀ i, Measurable (fun ω => x ω i))
    (center : ℝ) {w : ℂ} (hw : w.im ≠ 0) :
    Measurable (fun ω => microscopicResolvent (x ω) center w) :=
  (boundedMeasurable_microscopicResolvent hx center hw).1

theorem integrable_microscopicResolvent {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {N : ℕ} {x : Ω → Fin N → ℝ}
    (hx : ∀ i, Measurable (fun ω => x ω i)) (center : ℝ) {w : ℂ}
    (hw : w.im ≠ 0) :
    Integrable (fun ω => microscopicResolvent (x ω) center w) μ :=
  (boundedMeasurable_microscopicResolvent hx center hw).integrable

theorem measurable_resolventDerivative {Ω : Type*} [MeasurableSpace Ω]
    {N : ℕ} {x : Ω → Fin N → ℝ} (hx : ∀ i, Measurable (fun ω => x ω i))
    {w : ℂ} (hw : w.im ≠ 0) :
    Measurable (fun ω => resolventDerivative (x ω) w) :=
  (boundedMeasurable_resolventDerivative hx hw).1

theorem integrable_resolventDerivative {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {N : ℕ} {x : Ω → Fin N → ℝ}
    (hx : ∀ i, Measurable (fun ω => x ω i)) {w : ℂ} (hw : w.im ≠ 0) :
    Integrable (fun ω => resolventDerivative (x ω) w) μ :=
  (boundedMeasurable_resolventDerivative hx hw).integrable

theorem measurable_interaction {Ω : Type*} [MeasurableSpace Ω]
    {N : ℕ} {x : Ω → Fin N → ℝ} (hx : ∀ i, Measurable (fun ω => x ω i))
    {w v : ℂ} (hw : w.im ≠ 0) (hv : v.im ≠ 0) :
    Measurable (fun ω => interaction (x ω) w v) :=
  (boundedMeasurable_interaction hx hw hv).1

theorem integrable_interaction {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {N : ℕ} {x : Ω → Fin N → ℝ}
    (hx : ∀ i, Measurable (fun ω => x ω i)) {w v : ℂ}
    (hw : w.im ≠ 0) (hv : v.im ≠ 0) :
    Integrable (fun ω => interaction (x ω) w v) μ :=
  (boundedMeasurable_interaction hx hw hv).integrable

/-- All fixed finite products of resolvent powers are integrable. -/
theorem integrable_microscopicResolvent_product {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {N n : ℕ} {x : Ω → Fin N → ℝ}
    (hx : ∀ i, Measurable (fun ω => x ω i)) (center : ℝ)
    (w : Fin n → ℂ) (hw : ∀ a, (w a).im ≠ 0) (q : Fin n → ℕ) :
    Integrable (fun ω => ∏ a, microscopicResolvent (x ω) center (w a) ^ q a) μ :=
  (boundedMeasurable_prod Finset.univ _ (fun a _ =>
    (boundedMeasurable_microscopicResolvent hx center (hw a)).pow (q a))).integrable

/-- Every fixed finite-particle resolvent moment is integrable. -/
theorem integrable_microscopicResolvent_norm_pow {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {N : ℕ} {x : Ω → Fin N → ℝ}
    (hx : ∀ i, Measurable (fun ω => x ω i)) (center : ℝ) {w : ℂ}
    (hw : w.im ≠ 0) (q : ℕ) :
    Integrable (fun ω => ‖microscopicResolvent (x ω) center w‖ ^ q) μ := by
  have hf := boundedMeasurable_microscopicResolvent hx center hw
  obtain ⟨C, _, hC⟩ := hf.2
  refine (integrable_const (C ^ q)).mono'
    (hf.1.norm.pow_const q).aestronglyMeasurable ?_
  apply Filter.Eventually.of_forall
  intro ω
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) q)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hC ω) q

/-- The complete loop integrand is integrable, including repeated parameters and
parameters in different half-planes. -/
theorem integrable_loopIntegrand {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {N n : ℕ} {x : Ω → Fin N → ℝ}
    (hx : ∀ i, Measurable (fun ω => x ω i)) (β : Beta) (center : ℝ)
    {w : ℂ} (hw : w.im ≠ 0) (aux : Fin n → ℂ)
    (haux : ∀ a, (aux a).im ≠ 0) :
    Integrable (fun ω => loopIntegrand β (x ω) center w aux) μ := by
  have hs := boundedMeasurable_microscopicResolvent hx center hw
  have hd := boundedMeasurable_resolventDerivative hx hw
  have ha (a : Fin n) := boundedMeasurable_microscopicResolvent hx center (haux a)
  have hp := boundedMeasurable_prod Finset.univ
    (fun a ω => microscopicResolvent (x ω) center (aux a)) (fun a _ => ha a)
  have he (a : Fin n) : BoundedMeasurable (fun ω =>
      excludedProduct (fun b => microscopicResolvent (x ω) center (aux b)) a) :=
    boundedMeasurable_prod (Finset.univ.erase a) _ (fun b _ => ha b)
  have hi := boundedMeasurable_sum Finset.univ
    (fun a ω => interaction (x ω) w (aux a) *
      excludedProduct (fun b => microscopicResolvent (x ω) center (aux b)) a)
    (fun a _ => (boundedMeasurable_interaction hx hw (haux a)).mul (he a))
  exact (((((boundedMeasurable_const ((2 - β.value) / β.value)).mul hd).add
    (hs.pow 2)).add (boundedMeasurable_const 1)).mul hp |>.add
      ((boundedMeasurable_const (2 / β.value)).mul hi)).integrable

/-- The full finite loop observable is measurable. -/
theorem measurable_loopIntegrand {Ω : Type*} [MeasurableSpace Ω]
    {N n : ℕ} {x : Ω → Fin N → ℝ}
    (hx : ∀ i, Measurable (fun ω => x ω i)) (β : Beta) (center : ℝ)
    {w : ℂ} (hw : w.im ≠ 0) (aux : Fin n → ℂ)
    (haux : ∀ a, (aux a).im ≠ 0) :
    Measurable (fun ω => loopIntegrand β (x ω) center w aux) := by
  have hs := boundedMeasurable_microscopicResolvent hx center hw
  have hd := boundedMeasurable_resolventDerivative hx hw
  have ha (a : Fin n) := boundedMeasurable_microscopicResolvent hx center (haux a)
  have hp := boundedMeasurable_prod Finset.univ
    (fun a ω => microscopicResolvent (x ω) center (aux a)) (fun a _ => ha a)
  have he (a : Fin n) : BoundedMeasurable (fun ω =>
      excludedProduct (fun b => microscopicResolvent (x ω) center (aux b)) a) :=
    boundedMeasurable_prod (Finset.univ.erase a) _ (fun b _ => ha b)
  have hi := boundedMeasurable_sum Finset.univ
    (fun a ω => interaction (x ω) w (aux a) *
      excludedProduct (fun b => microscopicResolvent (x ω) center (aux b)) a)
    (fun a _ => (boundedMeasurable_interaction hx hw (haux a)).mul (he a))
  exact (((((boundedMeasurable_const ((2 - β.value) / β.value)).mul hd).add
    (hs.pow 2)).add (boundedMeasurable_const 1)).mul hp |>.add
      ((boundedMeasurable_const (2 / β.value)).mul hi)).1

theorem resolventMoments_of_measurable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {x : (N : ℕ) → Ω → Fin N → ℝ}
    (hx : ∀ N i, Measurable (fun ω => x N ω i)) (center : ℝ) :
    ResolventMoments μ x center := by
  intro N w hw q
  exact integrable_microscopicResolvent_norm_pow (hx N) center hw q

theorem hierarchyIntegrable_of_measurable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {x : (N : ℕ) → Ω → Fin N → ℝ}
    (hx : ∀ N i, Measurable (fun ω => x N ω i)) (β : Beta) (center : ℝ) :
    HierarchyIntegrable μ β x center := by
  intro N n w hw aux haux
  exact integrable_loopIntegrand (hx N) β center hw aux haux

end BourgadeHuang
