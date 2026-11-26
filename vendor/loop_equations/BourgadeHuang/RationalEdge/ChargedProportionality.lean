import BourgadeHuang.EdgeCMS.GenericBoundedUniqueness
import BourgadeHuang.RationalEdge.ChargedSectorialSolution

/-! Actual edge charged expectations span one analytic germ. The terminal
functional is constructed from their bounded scaled-jet ODE, and its nonzero
reference value follows from the exact diagonal normalization of a probability
law. No growth, terminal uniqueness, or proportionality hypothesis is supplied. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Set Filter
namespace BourgadeHuang.RationalEdge
open RationalBulk EdgeCMS CMS
set_option maxHeartbeats 1000000

theorem expectedChargedObservable_local_proportionality {n m : ℕ}
    (μ ν : ProbabilityMeasure AnchoredCountingState) (β : ℝ) (hβ : 0<β)
    (hμ : ExactHierarchy (μ : Measure AnchoredCountingState) β)
    (hν : ExactHierarchy (ν : Measure AnchoredCountingState) β)
    {a b : ℝ} (ha : 0<a) (hb : 0<b)
    (heμ : Integrable (fun s : AnchoredCountingState=>Real.exp (a*‖s.val.2‖^2))
      (μ : Measure AnchoredCountingState))
    (heν : Integrable (fun s : AnchoredCountingState=>Real.exp (b*‖s.val.2‖^2))
      (ν : Measure AnchoredCountingState))
    (hd : 0<n+m) (theta : Fin n→Bool) (eta : Fin m→Bool)
    (hn : (n:ℝ)=(m:ℝ)*β/2)
    (hbal : β*(signCount eta true:ℝ)=2*(signCount theta true:ℝ)) :
    ∃(c : ℂ)(z : Point (n+m)), z∈denominatorDomain n eta ∧
      expectedChargedObservable (μ : Measure AnchoredCountingState) (charges β n m)
        (blockAnchors theta eta) =ᶠ[𝓝 z]
      fun w => c*expectedChargedObservable (ν : Measure AnchoredCountingState) (charges β n m)
        (blockAnchors theta eta) w := by
  let c := charges β n m
  let upper := Fin.append theta eta
  have hβC : (β:ℂ)≠0 := by exact_mod_cast hβ.ne'
  let D := physicalComparisonData (β:ℂ) c hβC upper
  let Gμ := physicalNormalizedObservable (μ : Measure AnchoredCountingState) (β:ℂ) c upper
  let Gν := physicalNormalizedObservable (ν : Measure AnchoredCountingState) (β:ℂ) c upper
  have hGμ : D.IsSolution Gμ := physicalNormalizedObservable_isSolution
    (μ : Measure AnchoredCountingState) β hβ hμ ha heμ theta eta hn hbal
  have hGν : D.IsSolution Gν := physicalNormalizedObservable_isSolution
    (ν : Measure AnchoredCountingState) β hβ hν hb heν theta eta hn hbal
  obtain ⟨y,hy⟩ := chargedPhysicalOpenCone_nonempty hβ theta eta
  have hy' : y∈physicalChamberSet c upper := hy
  have hc : ∀i,c i= -1 ∨ c i=(β:ℂ)/2 := charges_physical β n m
  have hz : ∑i,c i=0 := charges_sum_zero hn
  have hs : ∑i,c i*signValue (upper i)=0 := charges_signed_sum_zero theta eta hn hbal
  obtain ⟨Uμ,Cμ,hUμ,hCμ,hsubμ,hboundμ⟩ :=
    physicalNormalizedObservable_local_dilation_bound (μ : Measure AnchoredCountingState)
      β hβ.ne' hμ ha heμ hd c upper hc hz hs hy'
  obtain ⟨Uν,Cν,hUν,hCν,hsubν,hboundν⟩ :=
    physicalNormalizedObservable_local_dilation_bound (ν : Measure AnchoredCountingState)
      β hβ.ne' hν hb heν hd c upper hc hz hs hy'
  let F : (ℂ × ℂ) →ₗ[ℂ] (Point (n+m)→ℂ) :=
    { toFun := fun v w => v.1*Gμ w+v.2*Gν w
      map_add' := by intro v w; funext x; simp only [Prod.fst_add,Prod.snd_add,Pi.add_apply]; ring
      map_smul' := by intro a v; funext x; simp only [Prod.smul_fst,Prod.smul_snd,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; ring }
  have hF (v : ℂ × ℂ) : D.IsSolution (F v) :=
    EdgeCMS.SectorialData.IsSolution.add D
      (EdgeCMS.SectorialData.IsSolution.smul D hGμ v.1)
      (EdgeCMS.SectorialData.IsSolution.smul D hGν v.2)
  have hbound (v : ℂ × ℂ) : ∃M : ℝ, ∀t : ℝ,0<t→∀w∈Uμ∩Uν,
      ‖F v ((t:ℂ)•w)‖≤M := by
    refine ⟨‖v.1‖*Cμ+‖v.2‖*Cν,?_⟩
    intro t ht w hw
    exact (norm_add_le _ _).trans
      (add_le_add (by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hboundμ w hw.1 t ht) (norm_nonneg _))
        (by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hboundν w hw.2 t ht) (norm_nonneg _)))
  obtain ⟨R,hR,L,hker⟩ := D.exists_terminal_zero_germ_of_dilation_nhds F hF hy
    (physicalComparisonData_coordinate_gap (β:ℂ) c hβC upper hy')
    (Uμ∩Uν) (inter_mem hUμ hUν) hbound
  have hRp : 0<R := zero_lt_one.trans hR
  have hyp : (R:ℂ)•y∈physicalChamberSet c upper :=
    (physicalOpenCone c upper).scale_mem hRp hy'
  have hLg : L (0,1)≠0 := by
    intro h
    have hh := hker (0,1) h
    have hzν : Gν =ᶠ[𝓝 ((R:ℂ)•y)] 0 := by
      change (fun w => (0:ℂ)*Gμ w+(1:ℂ)*Gν w) =ᶠ[𝓝 ((R:ℂ)•y)] 0 at hh
      simpa only [zero_mul,one_mul,zero_add] using hh
    exact physicalNormalizedObservable_not_eventually_zero ν β hb heν theta eta hyp
      (chargedPhysicalChamber_inverse_denominatorDomain hyp) hzν
  let A : ℂ := L (1,0)/L (0,1)
  have hLzero : L ((1,0)-A•(0,1))=0 := by
    rw [map_sub,map_smul,smul_eq_mul]
    dsimp [A]
    rw [div_mul_cancel₀ _ hLg,sub_self]
  have hzero := hker ((1,0)-A•(0,1)) hLzero
  have hprop : Gμ =ᶠ[𝓝 ((R:ℂ)•y)] fun w=>A*Gν w := by
    filter_upwards [hzero] with w hw
    dsimp [F] at hw
    simpa only [Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,
      mul_zero,sub_zero,one_mul,mul_one,zero_sub,neg_mul,← sub_eq_add_neg,Pi.zero_apply,
      sub_eq_zero] using hw
  refine ⟨A,airyInverseCoordinates ((R:ℂ)•y),
    chargedPhysicalChamber_inverse_denominatorDomain hyp,?_⟩
  exact charged_block_germ_proportional_of_normalized
    (μ : Measure AnchoredCountingState) (ν : Measure AnchoredCountingState)
    β theta eta A hyp hprop

end BourgadeHuang.RationalEdge
