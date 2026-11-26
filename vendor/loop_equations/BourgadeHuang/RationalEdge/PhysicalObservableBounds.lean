import BourgadeHuang.RationalEdge.ScaledObservableBounds
import BourgadeHuang.EdgeCMS.PhysicalChamberBounds

/-! The actual normalized edge expectation is uniformly bounded on all positive
dilations of a neighborhood in the concrete physical Airy-coordinate cone. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Set Filter
namespace BourgadeHuang.RationalEdge
open RationalBulk EdgeCMS CMS

def airyPhaseNormalizedObservable {d : ℕ} (ν : Measure AnchoredCountingState)
    (c : Fin d→ℂ) (upper : Fin d→Bool) (y : Point d) : ℂ :=
  phaseNormalizedObservable ν c upper (fun i=>airyInverse (y i))

theorem airyPhaseNormalizedObservable_local_dilation_bound
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν] (β : ℝ)
    (hh : ExactHierarchy ν β) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState=>Real.exp (a*‖s.val.2‖^2)) ν)
    {d : ℕ} (hd : 0<d) (c : Fin d→ℂ) (upper : Fin d→Bool)
    (hzero : ∑i,c i=0) (hsigned : ∑i,c i*signValue (upper i)=0)
    {y : Point d} (hy : y∈physicalChamberSet c upper) :
    ∃(U : Set (Point d)) (C : ℝ), U∈𝓝 y ∧ 0<C ∧ U⊆physicalChamberSet c upper ∧
      ∀v∈U,∀r : ℝ,0<r→‖airyPhaseNormalizedObservable ν c upper ((r:ℂ) • v)‖≤C := by
  obtain ⟨U,η,M,hU,hη,hM,hsub,hbounds⟩ := physicalChamber_neighborhood_bounds hd hy
  obtain ⟨C,hC,hbound⟩ := exists_phaseNormalizedObservable_dilation_bound ν β hh ha he
    hd c upper hzero hsigned η M hη hM.le
  refine ⟨U,C,hU,hC,hsub,fun v hv r hr=>?_⟩
  obtain ⟨u,hu,huc⟩ := exists_positive_cube_root hr
  have hucC : (u:ℂ)^3=(r:ℂ) := by exact_mod_cast huc
  have hscale i : airyInverse (((r:ℂ) • v) i) = ((u^2:ℝ):ℂ)*airyInverse (v i) := by
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [←hucC,airyInverse_ofReal_cube_mul hu
      (Complex.slitPlane_ne_zero ((hsub hv).1 i).1.1),Complex.ofReal_pow]
  have hsector i : (reflectComplex (upper i) (airyInverse (v i))).re≤
      (reflectComplex (upper i) (airyInverse (v i))).im := by
    have h := ((hsub hv).1 i).1.2.2.le
    cases e: upper i <;> simpa only [reflectComplex,e,Bool.false_eq_true,if_false,if_true,
      Complex.conj_re] using h
  have hb := hbound (u^2) (sq_pos_of_pos hu) (fun i=>airyInverse (v i))
    (fun i=>(hbounds v hv i).1) hsector (fun i=>(hbounds v hv i).2)
  simpa only [airyPhaseNormalizedObservable,hscale] using hb

end BourgadeHuang.RationalEdge
