import BourgadeHuang.RationalEdge.GaussianCenteredLoop
import BourgadeHuang.RationalEdge.Foundation
import BourgadeHuang.RationalBulk.GaussianReferenceBridge

/-! Exact soft-edge coordinates of the genuine Gaussian beta density.
The original density has support scale [-2N,2N]. Its right-edge particles are
(x_i-2N)/t, where t^3=N, and the centered transform is sum_i(y_i-w)^(-1)+t. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalEdge
open RationalBulk

def edgeParticles {N : ℕ} (t : ℝ) (x : Fin N → ℝ) : Fin N → ℝ :=
  fun i => (x i - 2*N)/t

def edgeParameter (N : ℕ) (t : ℝ) (w : ℂ) : ℂ := 2*N+(t:ℂ)*w

def finiteEdgeState {N : ℕ} (t : ℝ) (x : Fin N → ℝ) : AnchoredCountingState :=
  finiteAnchoredState (edgeParticles t x) (-t)

theorem edgeParameter_im (N : ℕ) (t : ℝ) (w : ℂ) :
    (edgeParameter N t w).im = t*w.im := by
  simp [edgeParameter,Complex.mul_im]

theorem edgeParameter_offReal (N : ℕ) {t : ℝ} (ht : t≠0) {w : ℂ} (hw : w.im≠0) :
    (edgeParameter N t w).im≠0 := by
  rw [edgeParameter_im]
  exact mul_ne_zero ht hw

theorem edge_particle_reciprocal {N : ℕ} {t : ℝ} (ht : t≠0)
    (x : Fin N → ℝ) (i : Fin N) (w : ℂ) :
    (((edgeParticles t x i : ℝ):ℂ)-w)⁻¹ =
      (t:ℂ)*((x i:ℂ)-edgeParameter N t w)⁻¹ := by
  have htC : (t:ℂ)≠0 := by exact_mod_cast ht
  have h : (((edgeParticles t x i:ℝ):ℂ)-w) = ((x i:ℂ)-edgeParameter N t w)/(t:ℂ) := by
    unfold edgeParticles edgeParameter
    push_cast
    field_simp
    <;> ring
  rw [h,inv_div]
  simp [div_eq_mul_inv]

theorem edge_microscopicResolvent {N : ℕ} {t : ℝ} (ht : t≠0)
    (x : Fin N → ℝ) (w : ℂ) :
    microscopicResolvent (edgeParticles t x) (-t) w =
      (t:ℂ)*microscopicResolvent x (-1) (edgeParameter N t w) := by
  unfold microscopicResolvent
  simp_rw [edge_particle_reciprocal ht, ←Finset.mul_sum]
  push_cast
  ring

theorem edge_resolventDerivative {N : ℕ} {t : ℝ} (ht : t≠0)
    (x : Fin N → ℝ) (w : ℂ) :
    resolventDerivative (edgeParticles t x) w =
      (t:ℂ)^2*resolventDerivative x (edgeParameter N t w) := by
  unfold resolventDerivative
  simp_rw [edge_particle_reciprocal ht,mul_pow,←Finset.mul_sum]

theorem edge_interaction {N : ℕ} {t : ℝ} (ht : t≠0)
    (x : Fin N → ℝ) (w v : ℂ) :
    interaction (edgeParticles t x) w v =
      (t:ℂ)^3*interaction x (edgeParameter N t w) (edgeParameter N t v) := by
  unfold interaction
  simp_rw [edge_particle_reciprocal ht]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem finiteEdgeState_nevanlinna {N : ℕ} {t : ℝ} (ht : t≠0)
    (x : Fin N → ℝ) {w : ℂ} (hw : w.im≠0) :
    anchoredNevanlinna (finiteEdgeState t x) w =
      (t:ℂ)*microscopicResolvent x (-1) (edgeParameter N t w) := by
  rw [finiteEdgeState,finiteAnchoredState_nevanlinna _ _ hw,edge_microscopicResolvent ht]

theorem finiteEdgeState_derivative {N : ℕ} {t : ℝ} (ht : t≠0)
    (x : Fin N → ℝ) {w : ℂ} (hw : w.im≠0) :
    anchoredDerivative (finiteEdgeState t x) w =
      (t:ℂ)^2*resolventDerivative x (edgeParameter N t w) := by
  calc
    _ = resolventDerivative (edgeParticles t x) w :=
      anchoredDerivative_eq_finite (edgeParticles t x) (-t) _ rfl hw
    _ = _ := edge_resolventDerivative ht x w

theorem finiteEdgeState_interaction {N : ℕ} {t : ℝ} (ht : t≠0)
    (x : Fin N → ℝ) {w v : ℂ} (hw : w.im≠0) (hv : v.im≠0) :
    anchoredInteraction (finiteEdgeState t x) w v =
      (t:ℂ)^3*interaction x (edgeParameter N t w) (edgeParameter N t v) := by
  calc
    _ = interaction (edgeParticles t x) w v :=
      anchoredInteraction_eq_finite (edgeParticles t x) (-t) _ rfl hw hv
    _ = _ := edge_interaction ht x w v

theorem measurable_edgeParticles (N : ℕ) (t : ℝ) :
    Measurable (edgeParticles (N:=N) t) := by
  apply measurable_pi_lambda
  intro i
  exact ((measurable_pi_apply i : Measurable (fun x : Fin N → ℝ => x i)).sub_const
    (2*(N:ℝ))).div_const t

theorem measurable_finiteEdgeState (N : ℕ) (t : ℝ) :
    Measurable (finiteEdgeState (N:=N) t) :=
  (measurable_finiteAnchoredState N (-t)).comp (measurable_edgeParticles N t)

theorem finiteEdgeState_moment {N : ℕ} (μ : Measure (Fin N → ℝ)) [IsFiniteMeasure μ]
    (t : ℝ) (q : ℕ) : Integrable (fun x => ‖(finiteEdgeState t x).val.2‖^q) μ := by
  exact integrable_microscopicResolvent_norm_pow
    (fun i => (measurable_pi_apply i).comp (measurable_edgeParticles N t)) (-t) (by simp) q

/-- The exact finite rescaling identity. The error is a single resolvent monomial
with coefficient w/t; it vanishes uniformly on every compact off-real set. -/
theorem edge_loop_scale_identity {N n : ℕ} (β : ℝ) (hβ : β≠0) {t : ℝ}
    (ht : t≠0) (hcube : t^3=(N:ℝ)) (x : Fin N → ℝ)
    {w : ℂ} {aux : Fin n → ℂ} (hw : w.im≠0) (ha : ∀a,(aux a).im≠0) :
    RationalEdge.loopIntegrand β (finiteEdgeState t x) w aux +
      (w/(t:ℂ))*resolventMonomial (finiteEdgeState t x) w aux =
    (t:ℂ)^(n+2)*centeredGaussianLoop β x (-1) (edgeParameter N t w)
      (fun a => edgeParameter N t (aux a)) := by
  have htC : (t:ℂ)≠0 := by exact_mod_cast ht
  have hb : (β:ℂ)≠0 := by exact_mod_cast hβ
  have hc : (t:ℂ)^3=(N:ℂ) := by exact_mod_cast hcube
  have hn : (N:ℂ)≠0 := by rw [←hc]; exact pow_ne_zero _ htC
  let R := fun v => microscopicResolvent x (-1) (edgeParameter N t v)
  let P := ∏ a,R (aux a)
  have hp : (∏ a,anchoredNevanlinna (finiteEdgeState t x) (aux a)) = (t:ℂ)^n*P := by
    simp only [finiteEdgeState_nevanlinna ht x (ha _),Finset.prod_mul_distrib,
      Finset.prod_const,Finset.card_univ,Fintype.card_fin,P,R]
  have he (a : Fin n) :
      (t:ℂ)^3*excludedProduct (fun b=>anchoredNevanlinna (finiteEdgeState t x) (aux b)) a =
      (t:ℂ)^(n+2)*excludedProduct (fun b=>R (aux b)) a := by
    unfold excludedProduct
    simp only [finiteEdgeState_nevanlinna ht x (ha _),Finset.prod_mul_distrib,
      Finset.prod_const,Finset.card_erase_of_mem (Finset.mem_univ a),
      Finset.card_univ,Fintype.card_fin]
    rw [←mul_assoc,←pow_add]
    have hnpos : 0<n := Nat.zero_lt_of_lt a.isLt
    have hexp : 3+(n-1)=n+2 := by omega
    simpa only [hexp,R]
  have hlead : (t:ℂ)^2*((2-(β:ℂ))/(β:ℂ))*resolventDerivative x (edgeParameter N t w) +
      ((t:ℂ)*R w)^2-w+(w/(t:ℂ))*((t:ℂ)*R w) =
      (t:ℂ)^2*(((2-(β:ℂ))/(β:ℂ))*resolventDerivative x (edgeParameter N t w) +
        (microscopicResolvent x 0 (edgeParameter N t w))^2+1+
        (edgeParameter N t w/(N:ℂ))*microscopicResolvent x 0 (edgeParameter N t w)) := by
    have hs : R w=microscopicResolvent x 0 (edgeParameter N t w)+1 := by
      simp [R,microscopicResolvent]
    rw [hs]
    simp only [edgeParameter,←hc]
    field_simp
    <;> ring
  unfold RationalEdge.loopIntegrand resolventMonomial centeredGaussianLoop
  rw [hp,finiteEdgeState_nevanlinna ht x hw,finiteEdgeState_derivative ht x hw]
  simp_rw [finiteEdgeState_interaction ht x hw (ha _)]
  have htail : (∑ a,(t:ℂ)^3*interaction x (edgeParameter N t w) (edgeParameter N t (aux a))*
      excludedProduct (fun b=>anchoredNevanlinna (finiteEdgeState t x) (aux b)) a) =
    (t:ℂ)^(n+2)*∑ a,interaction x (edgeParameter N t w) (edgeParameter N t (aux a))*
      excludedProduct (fun b=>R (aux b)) a := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    calc
      _ = interaction x (edgeParameter N t w) (edgeParameter N t (aux a))*
        ((t:ℂ)^3*excludedProduct (fun b=>anchoredNevanlinna (finiteEdgeState t x) (aux b)) a) := by ring
      _ = _ := by rw [he]; ring
  rw [htail]
  have hpow : (t:ℂ)^(n+2)=(t:ℂ)^2*(t:ℂ)^n := by rw [pow_add]; ring
  rw [hpow]
  dsimp [R,P] at hlead ⊢
  linear_combination (t:ℂ)^n*(∏ a,microscopicResolvent x (-1) (edgeParameter N t (aux a)))*hlead

end BourgadeHuang.RationalEdge
