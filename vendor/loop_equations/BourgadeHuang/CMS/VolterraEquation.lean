import BourgadeHuang.CMS.ImproperVariation

/-! Unweighted form of the actual Volterra fixed-point equation. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction
namespace BourgadeHuang.CMS
set_option maxHeartbeats 600000
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The inverse-weight map is bounded on a positive half-line. -/
def boundedUnweight {R : ℝ} (hR : 0<R) (Z : Tail R →ᵇ E) : Tail R →ᵇ E :=
  BoundedContinuousFunction.ofNormedAddCommGroup (unweight Z) (continuous_unweight hR Z)
    (‖Z‖/R) (fun t => (norm_unweight_le hR Z t).trans
      (div_le_div_of_nonneg_left (norm_nonneg Z) hR t.property))

@[simp] lemma boundedUnweight_apply {R : ℝ} (hR : 0<R) (Z : Tail R →ᵇ E) (t : Tail R) :
    boundedUnweight hR Z t = t.val⁻¹ • Z t := rfl

/-- Continuous bounded extension from the half-line, constant before its endpoint. -/
def tailExtension {R : ℝ} (Z : Tail R →ᵇ E) : ℝ →ᵇ E :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t => Z ⟨max R t,le_max_left _ _⟩)
    (Z.continuous.comp ((continuous_const.max continuous_id).subtype_mk _)) ‖Z‖
    (fun _ => Z.norm_coe_le_norm _)

@[simp] lemma tailExtension_apply {R : ℝ} (Z : Tail R →ᵇ E) (t : Tail R) :
    tailExtension Z t.val = Z t := by
  change Z ⟨max R t.val,_⟩=Z t
  congr 1
  apply Subtype.ext
  exact max_eq_right t.property

namespace VolterraData
variable {R a C : ℝ} (D : VolterraData (E:=E) R a C)
  (hR : 0<R) (ha : 0<a) (hC : 0≤C)

/-- The actual inhomogeneous term in the radial differential equation. -/
def source (Z : Tail R →ᵇ E) : Tail R →ᵇ E :=
  boundedUnweight hR
    (boundedCoefficientOperator D.C10 (BoundedContinuousFunction.const _ (1:ℂ)+
      boundedUnweight hR (D.primitive hR Z))+
      boundedCoefficientOperator D.C11 (boundedUnweight hR Z))

@[simp] lemma source_apply (Z : Tail R →ᵇ E) (t : Tail R) :
    D.source hR Z t = t.val⁻¹ •
      (D.C10 t (1+t.val⁻¹ • D.primitive hR Z t)+D.C11 t (t.val⁻¹ • Z t)) := rfl

/-- Removing the weight gives exactly the improper variation-of-constants
integral, including the eliminated empty component. -/
theorem unweight_map_eq_integral (Z : Tail R →ᵇ E) (t : Tail R) :
    unweight (D.map hR ha hC Z) t =
      -(∫ u : ℝ in Ioi 0, D.evolution t u (D.source hR Z (tailShift t u))) := by
  let Q : Tail R →ᵇ E := boundedCoefficientOperator D.C10 (BoundedContinuousFunction.const (Tail R) (1:ℂ))
  let W : Tail R →ᵇ E := boundedCoefficientOperator D.C10 (D.primitive hR Z)+boundedCoefficientOperator D.C11 Z
  have h1 := (exponentialForcingKernel hR ha hC D.evolution D.continuous_evolution
    D.norm_evolution_le).integrable_integrand Q t
  have h2 := (exponentialTailKernel hR ha hC D.evolution D.continuous_evolution
    D.norm_evolution_le).integrable_integrand W t
  unfold ContinuousIntegralKernel.integrand at h1 h2
  dsimp only [exponentialForcingKernel,exponentialTailKernel] at h1 h2
  simp only [Q,W,ContinuousLinearMap.smul_apply,boundedCoefficientOperator_apply,
    BoundedContinuousFunction.const_apply,BoundedContinuousFunction.add_apply] at h1 h2
  have hj := integral_add (h1.smul t.val⁻¹) (h2.smul t.val⁻¹)
  simp only [Pi.smul_apply] at hj
  rw [unweight,D.map_apply,smul_add,← integral_smul,← integral_smul,←hj,← integral_neg]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  simp only [source_apply,map_smul,map_add,smul_add,smul_smul,neg_smul]
  have ht : t.val⁻¹*t.val=1 := inv_mul_cancel₀ (hR.trans_le t.property).ne'
  match_scalars <;> field_simp [(hR.trans_le t.property).ne'] <;> ring

end VolterraData
end BourgadeHuang.CMS
