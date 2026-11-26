import BourgadeHuang.CMS.VolterraOperators
import Mathlib.Topology.MetricSpace.Contracting

/-! Actual weighted Volterra existence and uniqueness for the normalized CMS
radial system.  We identify the weighted space with bounded continuous functions
by `Z(t)=t Y*(t)`.  All integral operators and contraction estimates are proved. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction
namespace BourgadeHuang.CMS
set_option linter.unusedSectionVars false

section Coefficient
variable {X E F : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Multiplication by a bounded continuous operator-valued coefficient. -/
def boundedCoefficientOperator (A : X →ᵇ (E →L[ℝ] F)) :
    (X →ᵇ E) →L[ℝ] (X →ᵇ F) :=
  LinearMap.mkContinuous
    { toFun := fun f => BoundedContinuousFunction.ofNormedAddCommGroup
        (fun x => A x (f x)) (A.continuous.clm_apply f.continuous) (‖A‖*‖f‖)
        (fun x => (A x).le_opNorm _ |>.trans
          (mul_le_mul (A.norm_coe_le_norm x) (f.norm_coe_le_norm x)
            (norm_nonneg (f x)) (norm_nonneg A)))
      map_add' := by intro f g; ext x; exact map_add (A x) (f x) (g x)
      map_smul' := by intro c f; ext x; exact map_smul (A x) c (f x) }
    ‖A‖ (fun f => (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg A) (norm_nonneg f))).2
      (fun x => (A x).le_opNorm _ |>.trans
        (mul_le_mul (A.norm_coe_le_norm x) (f.norm_coe_le_norm x)
          (norm_nonneg (f x)) (norm_nonneg A))))

@[simp] lemma boundedCoefficientOperator_apply (A : X →ᵇ (E →L[ℝ] F))
    (f : X →ᵇ E) (x : X) : boundedCoefficientOperator A f x = A x (f x) := rfl

lemma norm_boundedCoefficientOperator_le (A : X →ᵇ (E →L[ℝ] F)) :
    ‖boundedCoefficientOperator A‖ ≤ ‖A‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg A) _
end Coefficient

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Bounded continuous radial coefficients together with the genuine principal
backward kernel and its exponential estimate.  No solution or fixed point is
part of these data. -/
structure VolterraData (R a C : ℝ) where
  C01 : Tail R →ᵇ (E →L[ℝ] ℂ)
  C10 : Tail R →ᵇ (ℂ →L[ℝ] E)
  C11 : Tail R →ᵇ (E →L[ℝ] E)
  evolution : Tail R → ℝ → E →L[ℝ] E
  continuous_evolution : Continuous (Function.uncurry evolution)
  norm_evolution_le : ∀ t u, 0<u → ‖evolution t u‖ ≤ C*Real.exp (-a*u)

namespace VolterraData
variable {R a C : ℝ} (D : VolterraData (E:=E) R a C)
  (hR : 0<R) (ha : 0<a) (hC : 0≤C)

/-- `t` times the correction to the empty jet. -/
def primitive : (Tail R →ᵇ E) →L[ℝ] (Tail R →ᵇ ℂ) :=
  (inverseSquareKernel hR D.C01).operator (norm_nonneg D.C01)

def propagator : (Tail R →ᵇ E) →L[ℝ] (Tail R →ᵇ E) :=
  (exponentialTailKernel hR ha hC D.evolution D.continuous_evolution D.norm_evolution_le).operator
    (mul_nonneg (mul_nonneg hC (inv_nonneg.mpr hR.le)) (inv_nonneg.mpr ha.le))

def forcing : Tail R →ᵇ E :=
  (exponentialForcingKernel hR ha hC D.evolution D.continuous_evolution D.norm_evolution_le).operator
    (mul_nonneg hC (inv_nonneg.mpr ha.le))
    (boundedCoefficientOperator D.C10 (BoundedContinuousFunction.const _ (1:ℂ)))

def linearPart : (Tail R →ᵇ E) →L[ℝ] (Tail R →ᵇ E) :=
  (D.propagator hR ha hC).comp
    ((boundedCoefficientOperator D.C10).comp (D.primitive hR) + boundedCoefficientOperator D.C11)

def map (Z : Tail R →ᵇ E) : Tail R →ᵇ E :=
  D.forcing hR ha hC + D.linearPart hR ha hC Z

/-- The explicit contraction constant, which tends to zero as the starting
radius increases while the coefficient bounds remain fixed. -/
def contractionConstant : ℝ := C*R⁻¹*a⁻¹*(‖D.C10‖*‖D.C01‖+‖D.C11‖)

include hR ha hC in
lemma contractionConstant_nonneg : 0≤D.contractionConstant := by
  exact mul_nonneg (mul_nonneg (mul_nonneg hC (inv_nonneg.mpr hR.le)) (inv_nonneg.mpr ha.le))
    (add_nonneg (mul_nonneg (norm_nonneg D.C10) (norm_nonneg D.C01)) (norm_nonneg D.C11))

lemma norm_primitive_le : ‖D.primitive hR‖ ≤ ‖D.C01‖ :=
  (inverseSquareKernel hR D.C01).norm_operator_le _

lemma norm_propagator_le : ‖D.propagator hR ha hC‖ ≤ C*R⁻¹*a⁻¹ :=
  (exponentialTailKernel hR ha hC D.evolution D.continuous_evolution D.norm_evolution_le).norm_operator_le _

lemma norm_forcing_le : ‖D.forcing hR ha hC‖ ≤ C*a⁻¹*‖D.C10‖ := by
  apply le_trans (ContinuousLinearMap.le_opNorm _ _)
  apply mul_le_mul
  · exact (exponentialForcingKernel hR ha hC D.evolution D.continuous_evolution D.norm_evolution_le).norm_operator_le _
  · calc
      _ ≤ ‖boundedCoefficientOperator D.C10‖ * ‖BoundedContinuousFunction.const (Tail R) (1:ℂ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖D.C10‖ * 1 := mul_le_mul (norm_boundedCoefficientOperator_le _)
        (by simpa only [norm_one] using BoundedContinuousFunction.norm_const_le (α:=Tail R) (1:ℂ))
        (norm_nonneg _) (norm_nonneg D.C10)
      _ = _ := mul_one _
  · exact norm_nonneg _
  · exact mul_nonneg hC (inv_nonneg.mpr ha.le)

lemma norm_linearPart_le : ‖D.linearPart hR ha hC‖ ≤ D.contractionConstant := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  apply mul_le_mul (D.norm_propagator_le hR ha hC)
  · apply (norm_add_le _ _).trans
    exact add_le_add ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (norm_boundedCoefficientOperator_le _) (D.norm_primitive_le hR)
        (norm_nonneg _) (norm_nonneg D.C10))) (norm_boundedCoefficientOperator_le _)
  · exact norm_nonneg _
  · exact mul_nonneg (mul_nonneg hC (inv_nonneg.mpr hR.le)) (inv_nonneg.mpr ha.le)

lemma norm_map_sub_le (Z W : Tail R →ᵇ E) :
    ‖D.map hR ha hC Z-D.map hR ha hC W‖ ≤ D.contractionConstant * ‖Z-W‖ := by
  simp only [map,add_sub_add_left_eq_sub,← map_sub]
  exact (D.linearPart hR ha hC).le_opNorm _ |>.trans
    (mul_le_mul_of_nonneg_right (D.norm_linearPart_le hR ha hC) (norm_nonneg _))

lemma contracting (hsmall : D.contractionConstant<1) :
    ContractingWith ⟨D.contractionConstant,D.contractionConstant_nonneg hR ha hC⟩ (D.map hR ha hC) := by
  refine ⟨hsmall, LipschitzWith.of_dist_le_mul ?_⟩
  intro Z W
  simpa only [dist_eq_norm] using D.norm_map_sub_le hR ha hC Z W

/-- Existence and uniqueness for the actual integral Volterra map. -/
theorem existsUnique_fixedPoint (hsmall : D.contractionConstant<1) :
    ∃! Z : Tail R →ᵇ E, D.map hR ha hC Z = Z := by
  let hc := D.contracting hR ha hC hsmall
  refine ⟨hc.fixedPoint, hc.fixedPoint_isFixedPt, ?_⟩
  intro Z hZ
  exact hc.fixedPoint_unique hZ

/-- Quantitative weighted bound for the constructed normalized jet. -/
theorem fixedPoint_norm_le (hsmall : D.contractionConstant<1)
    {Z : Tail R →ᵇ E} (hZ : D.map hR ha hC Z = Z) :
    ‖Z‖ ≤ (C*a⁻¹*‖D.C10‖)/(1-D.contractionConstant) := by
  have hi : ‖Z‖ ≤ C*a⁻¹*‖D.C10‖ + D.contractionConstant*‖Z‖ := by
    calc
      ‖Z‖ = ‖D.forcing hR ha hC + D.linearPart hR ha hC Z‖ := congrArg norm hZ.symm
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add (D.norm_forcing_le hR ha hC)
        ((D.linearPart hR ha hC).le_opNorm Z |>.trans
          (mul_le_mul_of_nonneg_right (D.norm_linearPart_le hR ha hC) (norm_nonneg Z))))
  apply (le_div_iff₀ (sub_pos.mpr hsmall)).2
  nlinarith

lemma primitive_apply (Z : Tail R →ᵇ E) (t : Tail R) :
    D.primitive hR Z t = ∫ u : ℝ in Ioi 0,
      (-(t.val * (tailShift t u).val⁻¹^2)) • D.C01 (tailShift t u) (Z (tailShift t u)) := rfl

lemma forcing_apply (t : Tail R) :
    D.forcing hR ha hC t = ∫ u : ℝ in Ioi 0,
      (-(t.val * (tailShift t u).val⁻¹)) • D.evolution t u (D.C10 (tailShift t u) 1) := rfl

lemma map_apply (Z : Tail R →ᵇ E) (t : Tail R) :
    D.map hR ha hC Z t =
      (∫ u : ℝ in Ioi 0, (-(t.val * (tailShift t u).val⁻¹)) •
        D.evolution t u (D.C10 (tailShift t u) 1)) +
      ∫ u : ℝ in Ioi 0, (-(t.val * (tailShift t u).val⁻¹^2)) •
        D.evolution t u (D.C10 (tailShift t u) (D.primitive hR Z (tailShift t u)) +
          D.C11 (tailShift t u) (Z (tailShift t u))) := rfl

include hR ha hC in
lemma contractionConstant_lt_one_of_radius {M : ℝ} (hM : 0≤M)
    (h01 : ‖D.C01‖≤M) (h10 : ‖D.C10‖≤M) (h11 : ‖D.C11‖≤M)
    (hlarge : C*a⁻¹*(M*M+M)<R) : D.contractionConstant<1 := by
  calc
    _ ≤ C*R⁻¹*a⁻¹*(M*M+M) := mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul h10 h01 (norm_nonneg D.C01) hM) h11)
      (mul_nonneg (mul_nonneg hC (inv_nonneg.mpr hR.le)) (inv_nonneg.mpr ha.le))
    _ = (C*a⁻¹*(M*M+M))/R := by ring
    _ < 1 := (div_lt_one hR).2 hlarge

end VolterraData

/-- Recover the decaying function from its bounded weighted representative. -/
def unweight {R : ℝ} (Z : Tail R →ᵇ E) (t : Tail R) : E := t.val⁻¹ • Z t

lemma continuous_unweight {R : ℝ} (hR : 0<R) (Z : Tail R →ᵇ E) :
    Continuous (unweight Z) :=
  (continuous_subtype_val.inv₀ (fun t => (hR.trans_le t.property).ne')).smul Z.continuous

lemma norm_unweight_le {R : ℝ} (hR : 0<R) (Z : Tail R →ᵇ E) (t : Tail R) :
    ‖unweight Z t‖ ≤ ‖Z‖/t.val := by
  rw [unweight,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (hR.trans_le t.property).le)]
  simpa only [div_eq_mul_inv,mul_comm] using
    mul_le_mul_of_nonneg_left (Z.norm_coe_le_norm t) (inv_nonneg.mpr (hR.trans_le t.property).le)

lemma tendsto_unweight_zero {R : ℝ} (hR : 0<R) (Z : Tail R →ᵇ E) :
    Tendsto (unweight Z) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hi : Tendsto (fun t : Tail R => t.val⁻¹) atTop (𝓝 0) :=
    tendsto_comp_val_Ici_atTop.mpr tendsto_inv_atTop_zero
  have hlim : Tendsto (fun t : Tail R => ‖Z‖/t.val) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using hi.const_mul ‖Z‖
  exact squeeze_zero (fun _ => norm_nonneg _) (norm_unweight_le hR Z) hlim

namespace VolterraData
variable {R a C : ℝ} (D : VolterraData (E:=E) R a C)
  (hR : 0<R) (ha : 0<a) (hC : 0≤C)

/-- The empty component has the prescribed normalization at infinity and a
quantitative reciprocal decay estimate, without an asymptotic hypothesis. -/
theorem empty_normalization (Z : Tail R →ᵇ E) :
    Tendsto (fun t => (1:ℂ)+unweight (D.primitive hR Z) t) atTop (𝓝 1) ∧
    ∀ t : Tail R, ‖((1:ℂ)+unweight (D.primitive hR Z) t)-1‖ ≤ ‖D.C01‖*‖Z‖/t.val := by
  constructor
  · simpa only [add_zero] using (tendsto_unweight_zero hR (D.primitive hR Z)).const_add 1
  · intro t
    simp only [add_sub_cancel_left]
    apply (norm_unweight_le hR (D.primitive hR Z) t).trans
    apply div_le_div_of_nonneg_right _ (hR.trans_le t.property).le
    exact (D.primitive hR).le_opNorm Z |>.trans
      (mul_le_mul_of_nonneg_right (D.norm_primitive_le hR) (norm_nonneg Z))

end VolterraData

end BourgadeHuang.CMS
