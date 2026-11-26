import BourgadeHuang.EdgeCMS.PhysicalCoefficients
import BourgadeHuang.EdgeCMS.ConeRestriction
import BourgadeHuang.CMS.GaugeCommutators

/-! Exact conjugation and Airy-coordinate reduction of the physical edge PDE.
The analytic normalized function below is constructed from the original
observable, and the displayed homogeneous equation is proved from its PDE. -/
noncomputable section
open scoped BigOperators Topology
open Filter Set
namespace BourgadeHuang.EdgeCMS
open CMS
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 150000

/-- The actual normalized observable in the original spectral coordinates. -/
def physicalNormalized {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (F : Point d → ℂ) (z : Point d) : ℂ :=
  F z / physicalGauge β c z

/-- The actual normalized observable in Airy coordinates. -/
def physicalAiryNormalized {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (F : Point d → ℂ) (y : Point d) : ℂ :=
  physicalNormalized β c F (airyInverseCoordinates y)

@[simp] theorem physicalGauge_mul_normalized {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (F : Point d → ℂ) (z : Point d) :
    physicalGauge β c z * physicalNormalized β c F z = F z := by
  simp only [physicalNormalized, mul_div_cancel₀ _ (physicalGauge_ne_zero β c z)]

theorem analyticAt_physicalNormalized {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    {F : Point d → ℂ} {z : Point d} (hF : AnalyticAt ℂ F z)
    (hz : z ∈ PhysicalRootDomain d) : AnalyticAt ℂ (physicalNormalized β c F) z :=
  hF.div (analyticAt_physicalGauge β c hz) (physicalGauge_ne_zero β c z)

theorem analyticAt_physicalAiryNormalized {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    {F : Point d → ℂ} {y : Point d} (hy : ∀ i, y i ∈ Complex.slitPlane)
    (hz : airyInverseCoordinates y ∈ PhysicalRootDomain d)
    (hF : AnalyticAt ℂ F (airyInverseCoordinates y)) :
    AnalyticAt ℂ (physicalAiryNormalized β c F) y :=
  (analyticAt_physicalNormalized β c hF hz).comp (analyticAt_airyInverseCoordinates hy)

theorem physicalFirstRaw_action {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (hβ : β ≠ 0) {z : Point d} (hz : z ∈ PhysicalRootDomain d)
    (hcoll : CollisionFree z) (i : Fin d) (v : Fin d → ℂ) :
    z i * (∑ j, physicalFirstRaw β c i j z * v j) =
      2 * physicalCorrection β c i z * root (z i) * v i +
        (2/β) * ∑ j ∈ Finset.univ.erase i,
          (c i*c j*root (z i)*v i-c i^2*root (z j)*v j)/(z i-z j) := by
  classical
  have hzi := Complex.slitPlane_ne_zero (hz i)
  have hri := root_ne_zero (z i)
  have hsq := root_sq hzi
  have hs : (∑ j, (2/β)*c i^2*root (z j)/(z i*(z i-z j))*v j) =
      ∑ j ∈ Finset.univ.erase i, (2/β)*c i^2*root (z j)/(z i*(z i-z j))*v j := by
    have hh := Finset.sum_erase_add Finset.univ
      (fun j => (2/β)*c i^2*root (z j)/(z i*(z i-z j))*v j) (Finset.mem_univ i)
    simpa only [sub_self,mul_zero,div_zero,zero_mul,add_zero] using hh.symm
  simp only [physicalFirstRaw,sub_mul,ite_mul,zero_mul,Finset.sum_sub_distrib,
    Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rw [hs,mul_sub,add_mul,mul_add]
  have ha : z i*(2*physicalCorrection β c i z/root (z i))*v i =
      2*physicalCorrection β c i z*root (z i)*v i := by
    generalize he : root (z i) = r at hsq hri ⊢
    rw [← hsq]
    field_simp [hri]
    <;> ring
  rw [← mul_assoc, ha]
  rw [add_sub_assoc]
  congr 1
  simp only [Finset.mul_sum,Finset.sum_mul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hdiff := hcoll.sub_ne_zero (Finset.ne_of_mem_erase hj).symm
  generalize he : root (z i) = r at hsq hri ⊢
  rw [← hsq] at hdiff ⊢
  field_simp [hri,hβ,hdiff]
  <;> ring


/-- All scalar contributions are the proved physical WKB remainder. -/
theorem conjugatedEdgeOperator_physical {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (hβ : β ≠ 0) {z : Point d} (hz : z ∈ PhysicalRootDomain d)
    (hcoll : CollisionFree z) (i : Fin d) (W : Point d → ℂ) :
    conjugatedEdgeOperator β c (physicalGaugeLog β c) i W z =
      secondPartial i W z +
        2*(scalarWKBLogDerivative (c i) (z i)+physicalCorrection β c i z)*coordDeriv i W z +
        physicalScalarRemainder β c i z*W z +
        (2/β)*∑ j ∈ Finset.univ.erase i,
          (c i*c j*coordDeriv i W z-c i^2*coordDeriv j W z)/(z i-z j) := by
  have hs := physicalGauge_scalar_cancellation β c hβ hz hcoll i
  have hp (j : Fin d) :
      (c i*c j*coordDeriv i W z-c i^2*coordDeriv j W z+
        (c i*c j*coordDeriv i (physicalGaugeLog β c) z-
          c i^2*coordDeriv j (physicalGaugeLog β c) z)*W z)/(z i-z j) =
      (c i*c j*coordDeriv i W z-c i^2*coordDeriv j W z)/(z i-z j)+
        ((c i*c j*coordDeriv i (physicalGaugeLog β c) z-
          c i^2*coordDeriv j (physicalGaugeLog β c) z)/(z i-z j))*W z := by ring
  unfold conjugatedEdgeOperator
  simp_rw [hp]
  rw [Finset.sum_add_distrib,← Finset.sum_mul,mul_add]
  have hq := coordDeriv_physicalGaugeLog β c hz i
  rw [hq]
  rw [hq] at hs
  linear_combination hs * W z

/-- The complete actual WKB conjugation becomes the displayed homogeneous
Airy-coordinate operator after division by the nonzero spectral coordinate. -/
theorem conjugatedEdgeOperator_airy {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (hβ : β ≠ 0) {z : Point d} (hz : z ∈ PhysicalRootDomain d)
    (hcoll : CollisionFree z) (i : Fin d) {f : Point d → ℂ}
    (hf : AnalyticAt ℂ f (airyCoordinates z)) :
    conjugatedEdgeOperator β c (physicalGaugeLog β c) i
      (fun w => f (airyCoordinates w)) z =
    z i * (secondPartial i f (airyCoordinates z) +
      (2*c i)*coordDeriv i f (airyCoordinates z) +
      (∑ j, physicalFirstRaw β c i j z*coordDeriv j f (airyCoordinates z)) +
      physicalScalarRaw β c i z*f (airyCoordinates z)) := by
  rw [conjugatedEdgeOperator_physical β c hβ hz hcoll,
    secondPartial_airy_pullback hf i (hz i)]
  simp_rw [coordDeriv_airy_pullback hf _ (hz _)]
  have hfirst := physicalFirstRaw_action β c hβ hz hcoll i
    (fun j => coordDeriv j f (airyCoordinates z))
  have hzi := Complex.slitPlane_ne_zero (hz i)
  have hri := root_ne_zero (z i)
  have hsq := root_sq hzi
  have hscalar : z i*physicalScalarRaw β c i z = physicalScalarRemainder β c i z := by
    unfold physicalScalarRaw
    exact mul_div_cancel₀ _ hzi
  have hcoef : 1/(2*root (z i)) +
      2*(scalarWKBLogDerivative (c i) (z i)+physicalCorrection β c i z)*root (z i) =
      z i*(2*c i)+2*physicalCorrection β c i z*root (z i) := by
    unfold scalarWKBLogDerivative
    generalize he : root (z i) = r at hsq hri ⊢
    rw [← hsq]
    field_simp [hri]
    <;> ring
  simp only [mul_assoc] at hfirst ⊢
  linear_combination hcoef * coordDeriv i f (airyCoordinates z) - hfirst +
    -hscalar * f (airyCoordinates z)


theorem edgeOperator_congr_nhds {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (i : Fin d) {F G : Point d → ℂ} {z : Point d} (hFG : F =ᶠ[𝓝 z] G) :
    edgeOperator β c i F z = edgeOperator β c i G z := by
  simp only [edgeOperator,secondPartial_congr_nhds hFG,
    coordDeriv_congr_nhds hFG,hFG.eq_of_nhds]

/-- A genuine physical edge solution satisfies the normalized homogeneous
operator at every comparison point in the right spectral sector. -/
theorem physicalAiryNormalized_operator_eq_zero {d : ℕ}
    (β : ℂ) (c : Fin d → ℂ) (hβ : β ≠ 0)
    {F : Point d → ℂ} {y : Point d} (hy : y ∈ (physicalAiryCone d).carrier)
    (hright : ∀ i, 0 < (airyInverseCoordinates y i).re)
    (hF : AnalyticAt ℂ F (airyInverseCoordinates y))
    (hop : ∀ i, edgeOperator β c i F (airyInverseCoordinates y) = 0) (i : Fin d) :
    (physicalSectorialData β c hβ).operator i (physicalAiryNormalized β c F) y = 0 := by
  let z := airyInverseCoordinates y
  have hz : z ∈ PhysicalRootDomain d := airyInverseCoordinates_mem_rootDomain y
  have hcoll : CollisionFree z := airyInverseCoordinates_collisionFree hy
  have hcoord : airyCoordinates z = y :=
    airyCoordinates_inverseCoordinates (fun j => Complex.slitPlane_ne_zero (hy.1 j))
  have hG := analyticAt_physicalAiryNormalized β c hy.1 hz hF
  have hG' : AnalyticAt ℂ (physicalAiryNormalized β c F) (airyCoordinates z) := by
    simpa only [hcoord] using hG
  have hrightOpen : IsOpen {w : Point d | ∀ j, 0 < (w j).re} := by
    simp only [setOf_forall]
    apply isOpen_iInter_of_finite
    intro j
    exact isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_apply j))
  have heq : (fun w => Complex.exp (physicalGaugeLog β c w) *
      physicalAiryNormalized β c F (airyCoordinates w)) =ᶠ[𝓝 z] F := by
    filter_upwards [hrightOpen.eventually_mem hright] with w hw
    change physicalGauge β c w *
      physicalNormalized β c F (airyInverseCoordinates (airyCoordinates w)) = F w
    rw [airyInverseCoordinates_coordinates hw,physicalGauge_mul_normalized]
  have hzero : edgeOperator β c i
      (fun w => Complex.exp (physicalGaugeLog β c w) *
        physicalAiryNormalized β c F (airyCoordinates w)) z = 0 :=
    (edgeOperator_congr_nhds β c i heq).trans (hop i)
  have hc := (edgeOperator_exp_mul_eq_zero_iff β c
    (analyticAt_physicalGaugeLog β c hz)
    (hG'.comp (analyticAt_airyCoordinates hz)) i).mp hzero
  change conjugatedEdgeOperator β c (physicalGaugeLog β c) i
    (fun w => physicalAiryNormalized β c F (airyCoordinates w)) z = 0 at hc
  rw [conjugatedEdgeOperator_airy β c hβ hz hcoll i hG',hcoord] at hc
  have hinner := (mul_eq_zero.mp hc).resolve_left (Complex.slitPlane_ne_zero (hz i))
  exact hinner

/-- The normalized observable is an actual solution on any comparison cone
where its original physical observable is analytic and satisfies the edge PDE. -/
theorem physicalAiryNormalized_isSolution {d : ℕ}
    (β : ℂ) (c : Fin d → ℂ) (hβ : β ≠ 0) (C : OpenCone d)
    (hC : C.carrier ⊆ (physicalAiryCone d).carrier)
    (hright : ∀ y ∈ C.carrier, ∀ i, 0 < (airyInverseCoordinates y i).re)
    {F : Point d → ℂ}
    (hF : ∀ y ∈ C.carrier, AnalyticAt ℂ F (airyInverseCoordinates y))
    (hop : ∀ y ∈ C.carrier, ∀ i, edgeOperator β c i F (airyInverseCoordinates y) = 0) :
    ((physicalSectorialData β c hβ).restrict hC).IsSolution
      (physicalAiryNormalized β c F) := by
  constructor
  · intro y hy
    exact analyticAt_physicalAiryNormalized β c (hC hy).1
      (airyInverseCoordinates_mem_rootDomain y) (hF y hy)
  · intro y hy i
    exact physicalAiryNormalized_operator_eq_zero β c hβ (hC hy)
      (hright y hy) (hF y hy) (hop y hy) i


end BourgadeHuang.EdgeCMS
