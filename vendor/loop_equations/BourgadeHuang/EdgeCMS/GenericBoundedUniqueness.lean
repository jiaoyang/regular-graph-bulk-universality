import BourgadeHuang.EdgeCMS.BoundedJetMaps
import BourgadeHuang.EdgeCMS.RadialBlocks
import BourgadeHuang.EdgeCMS.SectorialUniqueness

/-! Scalar boundedness of genuine normalized sectorial solutions determines
at most one analytic germ. The scalar terminal map is constructed from the
actual finite derivative system and its proved backward integral equation. -/
noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction
namespace BourgadeHuang.EdgeCMS
open CMS
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option linter.unusedSectionVars false

/-- On the interior of its tail a bounded packaging has exactly the derivative
of the original function. -/
theorem hasDerivAt_tailExtension_of_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {R : ℝ} (Y : Tail R →ᵇ E) (f : ℝ → E)
    (he : ∀ t : Tail R, Y t = f t.val) {t : ℝ} (ht : R < t)
    {f' : E} (hd : HasDerivAt f f' t) : HasDerivAt (tailExtension Y) f' t := by
  apply hd.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds ht] with s hs
  change Y ⟨max R s, le_max_left _ _⟩ = f s
  rw [he]
  simp only [max_eq_right hs.le]

namespace SectorialData
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {d : ℕ}
  {C : OpenCone d} (D : SectorialData C) (F : V →ₗ[ℂ] (Point d → ℂ))
  (hF : ∀ v, D.IsSolution (F v))
  (z : Point d) (r : ℝ) (hr : 0 < r) (hball : Metric.ball z r ⊆ C.carrier)
  (hgap : ∀ i, 0 < (-(z i * D.phase i)).re)
  (r₀ : ℝ)
  (hb : ∀ v, ∃ M : ℝ, ∀ t : ℝ, r₀ ≤ t → ∀ w ∈ Metric.ball z r,
    ‖F v ((t : ℂ) • w)‖ ≤ M)

include hF hr hball hgap hb

/-- The terminal map is obtained from the genuine scaled-jet equations, and
its kernel has every actual square-free derivative zero at a common point. -/
theorem exists_dilation_terminal_with_zero_jets :
    ∃ R : ℝ, max r₀ 0 < R ∧ ∃ L : V →ₗ[ℂ] ℂ,
      ∀ v, L v = 0 → ∀ S : Finset (Fin d),
        squareFreeDerivative S (F v) ((R : ℂ) • z) = 0 := by
  classical
  obtain ⟨a, ha, hlam⟩ := D.exists_radial_gap z hgap
  let R := constantRadialRadius a (d + 1) (max r₀ 0)
    (D.radialN z) (D.radialC01 z) (D.radialC10 z) (D.radialC11 z)
  have hR : 0 < R := constantRadialRadius_pos _ _ _ _ _ _ _
  have hlarge : max r₀ 0 < R := lt_constantRadialRadius _ _ _ _ _ _ _
  have hbound : ∀ v, ∃ M : ℝ, ∀ t : ℝ, R ≤ t → ∀ w ∈ Metric.ball z r,
      ‖F v ((t : ℂ) • w)‖ ≤ M := by
    intro v
    obtain ⟨M, hM⟩ := hb v
    exact ⟨M, fun t ht => hM t ((le_max_left r₀ 0).trans (hlarge.le.trans ht))⟩
  let Y0 : V →ₗ[ℂ] (Tail R →ᵇ (Unit → ℂ)) :=
    dilationBoundedJetMap F C (fun v => (hF v).1) z r hr hball R hR hbound (fun _ => ∅)
  let Y1 : V →ₗ[ℂ] (Tail R →ᵇ (NonemptySubset d → ℂ)) :=
    dilationBoundedJetMap F C (fun v => (hF v).1) z r hr hball R hR hbound (fun S => S.val)
  have hY0 (v : V) (t : Tail R) (u : Unit) :
      Y0 v t u = scaledSquareFree ∅ (F v) ((t.val : ℂ) • z) t.val := rfl
  have hY1 (v : V) (t : Tail R) (S : NonemptySubset d) :
      Y1 v t S = scaledSquareFree S.val (F v) ((t.val : ℂ) • z) t.val := rfl
  have hz : z ∈ C.carrier := hball (Metric.mem_ball_self hr)
  have h0 : ∀ v, ∀ t : Tail R, R < t.val → HasDerivAt (tailExtension (Y0 v))
      (t.val⁻¹ • (D.radialC01 z) (Y1 v t)) t.val := by
    intro v t ht
    apply hasDerivAt_tailExtension_of_eq (Y0 v)
      (fun s : ℝ => fun _ : Unit => scaledSquareFree ∅ (F v) ((s : ℂ) • z) s)
      (fun s => by ext u; exact hY0 v s u) ht
    apply hasDerivAt_pi.mpr
    intro u
    cases u
    simpa only [Pi.smul_apply, hY1] using
      D.hasDerivAt_dilation_empty hz (hF v) (hR.trans ht)
  have h1 : ∀ v, ∀ t : Tail R, R < t.val → HasDerivAt (tailExtension (Y1 v))
      (complexDiagonalOperator (D.radialLambda z) (Y1 v t) + (D.radialN z) (Y1 v t) +
        t.val⁻¹ • ((D.radialC10 z) (Y0 v t) + (D.radialC11 z) (Y1 v t))) t.val := by
    intro v t ht
    apply hasDerivAt_tailExtension_of_eq (Y1 v)
      (fun s : ℝ => fun S : NonemptySubset d => scaledSquareFree S.val (F v) ((s : ℂ) • z) s)
      (fun s => by ext S; exact hY1 v s S) ht
    apply hasDerivAt_pi.mpr
    intro S
    simpa only [Pi.add_apply, Pi.smul_apply, complexDiagonalOperator_apply, hY0, hY1] using
      D.hasDerivAt_dilation_nonempty hz (hF v) (hR.trans ht) S
  have hsmall := constant_radial_smallness ha hR (D.radialLambda z) hlam (d + 1)
    (D.radialN z) (D.radialC01 z) (D.radialC10 z) (D.radialC11 z)
    (constantRadialRadius_large _ _ _ _ _ _ _)
  obtain ⟨L, hlim, hker⟩ := exists_radial_terminal_linearMap hR ha
    (D.radialLambda z) hlam (fun S : NonemptySubset d => S.val.card)
    (BoundedContinuousFunction.const (Tail R) (D.radialN z))
    (D.radialN_strictlyLowerDegree z R) (d + 1) (fun S => radial_degree_lt S)
    (BoundedContinuousFunction.const (Tail R) (D.radialC01 z))
    (BoundedContinuousFunction.const (Tail R) (D.radialC10 z))
    (BoundedContinuousFunction.const (Tail R) (D.radialC11 z))
    Y0 Y1 h0 h1 hsmall
  let Lscalar : V →ₗ[ℂ] ℂ := (LinearMap.proj ()).comp L
  refine ⟨R, hlarge, Lscalar, ?_⟩
  intro v hv S
  have hLv : L v = 0 := by
    ext u
    cases u
    exact hv
  obtain ⟨hzero, hone⟩ := hker v hLv
  have hs : scaledSquareFree S (F v) ((R : ℂ) • z) R = 0 := by
    by_cases hS : S.Nonempty
    · have hh := congrArg (fun Y : Tail R →ᵇ (NonemptySubset d → ℂ) =>
        Y ⟨R, le_rfl⟩ ⟨S, hS⟩) hone
      simpa only [hY1, BoundedContinuousFunction.coe_zero, Pi.zero_apply] using hh
    · have hS0 : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      subst S
      have hh := congrArg (fun Y : Tail R →ᵇ (Unit → ℂ) => Y ⟨R, le_rfl⟩ ()) hzero
      simpa only [hY0, BoundedContinuousFunction.coe_zero, Pi.zero_apply] using hh
  exact (mul_eq_zero.mp hs).resolve_left (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hR.ne'))

/-- Minimal-growth uniqueness for the actual normalized sectorial system:
scalar bounds produce a scalar terminal functional whose kernel is the zero
analytic germ. No bounded derivative or terminal-value assumption is imposed. -/
theorem exists_dilation_terminal_with_zero_germ :
    ∃ R : ℝ, max r₀ 0 < R ∧ ∃ L : V →ₗ[ℂ] ℂ,
      ∀ v, L v = 0 → F v =ᶠ[𝓝 ((R : ℂ) • z)] 0 := by
  obtain ⟨R, hR, L, hL⟩ := D.exists_dilation_terminal_with_zero_jets
    F hF z r hr hball hgap r₀ hb
  refine ⟨R, hR, L, fun v hv => ?_⟩
  exact locally_zero_of_squareFree (hF v)
    (C.scale_mem ((le_max_right r₀ 0).trans_lt hR) (hball (Metric.mem_ball_self hr))) (hL v hv)

end SectorialData

namespace SectorialData
/-- Neighborhood form of the same theorem, convenient for actual observable
estimates uniform on a neighborhood of one direction. -/
theorem exists_terminal_zero_germ_of_dilation_nhds
    {V : Type*} [AddCommGroup V] [Module ℂ V] {d : ℕ}
    {C : OpenCone d} (D : SectorialData C) (F : V →ₗ[ℂ] (Point d → ℂ))
    (hF : ∀ v, D.IsSolution (F v)) {z : Point d} (hz : z ∈ C.carrier)
    (hgap : ∀ i, 0 < (-(z i * D.phase i)).re)
    (U : Set (Point d)) (hU : U ∈ 𝓝 z)
    (hb : ∀ v, ∃ M : ℝ, ∀ t : ℝ, 0 < t → ∀ w ∈ U,
      ‖F v ((t : ℂ) • w)‖ ≤ M) :
    ∃ R : ℝ, 1 < R ∧ ∃ L : V →ₗ[ℂ] ℂ,
      ∀ v, L v = 0 → F v =ᶠ[𝓝 ((R : ℂ) • z)] 0 := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem hU (C.isOpen.mem_nhds hz))
  have hb' : ∀ v, ∃ M : ℝ, ∀ t : ℝ, (1 : ℝ) ≤ t → ∀ w ∈ Metric.ball z r,
      ‖F v ((t : ℂ) • w)‖ ≤ M := by
    intro v
    obtain ⟨M, hM⟩ := hb v
    exact ⟨M, fun t ht w hw => hM t (zero_lt_one.trans_le ht) w (hball hw).1⟩
  simpa only [max_eq_left zero_le_one] using
    D.exists_dilation_terminal_with_zero_germ F hF z r hr
      (fun w hw => (hball hw).2) hgap 1 hb'
end SectorialData
end BourgadeHuang.EdgeCMS
