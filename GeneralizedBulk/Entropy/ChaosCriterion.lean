import GeneralizedBulk.EntropyOptimization
import Mathlib

/-!
# Abstract entropy-to-fourth-chaos criterion

This is the abstract theorem in Generalization I of the blueprint. The
expansion, Taylor remainder, entropy monotonicity and coercivity are honest
analytic hypotheses; this module does not verify them for graph channels.
Unlike the numerical optimization lemma, the theorem uses the summable full
chaos expansion and all admissible smoothing scales. In particular the third
chaos may be nonzero and the zero-deficit case follows by a genuine limit.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace GeneralizedBulk.Entropy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- For Gaussian applications `E` is L² of the reference Gaussian and the
operators are its conditional expectations onto the observation channels. -/
def channelQuadratic {m : ℕ} (weight : Fin m → ℝ)
    (channel : Fin m → E →L[ℝ] E) (h : E) : ℝ :=
  ‖h‖ ^ 2 - ∑ i, weight i * ‖channel i h‖ ^ 2

/-- The objects entering the analytic hypotheses. Degrees are natural Hermite
degrees; the smoothing argument of `smoothed` and `deficit` is `t=x²`. -/
structure ChaosEntropyData (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  component : ℕ → E
  smoothed : ℝ → E
  quadratic : E → ℝ
  deficit : ℝ → ℝ

/-- Precisely the analytic expansion, degree positivity, fourth coercivity,
Taylor and entropy-deficit conditions of the abstract criterion. These remain
separate obligations for each concrete observation channel. -/
structure ChaosEntropyHypotheses (D : ChaosEntropyData E)
    (kappa A radius epsilon : ℝ) : Prop where
  chaos_nonnegative : ∀ j : ℕ, 3 ≤ j → 0 ≤ D.quadratic (D.component j)
  fourth_coercive : kappa * ‖D.component 4‖ ^ 2 ≤ D.quadratic (D.component 4)
  hermite_expansion : ∀ x : ℝ, 0 < x → x ≤ radius →
    HasSum (fun n : ℕ => x ^ (n + 3) • D.component (n + 3)) (D.smoothed (x ^ 2))
  energy_summable : ∀ x : ℝ, 0 < x → x ≤ radius →
    Summable (fun n : ℕ => x ^ (2 * (n + 3)) * D.quadratic (D.component (n + 3)))
  energy_expansion : ∀ x : ℝ, 0 < x → x ≤ radius →
    D.quadratic (D.smoothed (x ^ 2)) =
      ∑' n : ℕ, x ^ (2 * (n + 3)) * D.quadratic (D.component (n + 3))
  taylor : ∀ x : ℝ, 0 < x → x ≤ radius →
    |D.deficit (x ^ 2) - D.quadratic (D.smoothed (x ^ 2)) / 2| ≤ A * x ^ 9
  deficit_bounds : ∀ x : ℝ, 0 < x → x ≤ radius →
    0 ≤ D.deficit (x ^ 2) ∧ D.deficit (x ^ 2) ≤ epsilon

namespace ChaosEntropyHypotheses
variable {D : ChaosEntropyData E} {kappa A radius epsilon : ℝ}

/-- Every other chaos is discarded by positivity in an actual summable energy
series. This includes degree three; no third-moment cancellation is assumed. -/
theorem fourth_energy_lower (H : ChaosEntropyHypotheses D kappa A radius epsilon)
    {x : ℝ} (hx : 0 < x) (hxr : x ≤ radius) :
    kappa * x ^ 8 * ‖D.component 4‖ ^ 2 ≤ D.quadratic (D.smoothed (x ^ 2)) := by
  rw [H.energy_expansion x hx hxr]
  have ht := (H.energy_summable x hx hxr).le_tsum 1 (fun n hn =>
    mul_nonneg (pow_nonneg hx.le _) (H.chaos_nonnegative _ (by omega)))
  norm_num at ht
  have hc := mul_le_mul_of_nonneg_left H.fourth_coercive (pow_nonneg hx.le 8)
  calc
    kappa * x ^ 8 * ‖D.component 4‖ ^ 2 = x ^ 8 * (kappa * ‖D.component 4‖ ^ 2) := by ring
    _ ≤ _ := hc.trans ht

/-- The all-scale lower entropy estimate is derived from chaos coercivity and
the absolute Taylor error, rather than supplied to the optimizer. -/
theorem lower_deficit (H : ChaosEntropyHypotheses D kappa A radius epsilon)
    {x : ℝ} (hx : 0 < x) (hxr : x ≤ radius) :
    kappa / 2 * x ^ 8 * ‖D.component 4‖ ^ 2 - A * x ^ 9 ≤ D.deficit (x ^ 2) := by
  have he := H.fourth_energy_lower hx hxr
  have ht := (abs_le.mp (H.taylor x hx hxr)).1
  nlinarith

/-- At every admissible scale the complete chaos argument gives the expected
bias-versus-deficit estimate. -/
theorem at_scale (H : ChaosEntropyHypotheses D kappa A radius epsilon)
    (hkappa : 0 < kappa) {x : ℝ} (hx : 0 < x) (hxr : x ≤ radius) :
    ‖D.component 4‖ ^ 2 ≤ (2 / kappa) * (epsilon / x ^ 8 + A * x) :=
  one_scale_bound epsilon (D.deficit (x ^ 2)) kappa A x ‖D.component 4‖
    hkappa hx (H.deficit_bounds x hx hxr).2 (H.lower_deficit hx hxr)

/-- A zero entropy deficit forces the fourth component to vanish by sending
all admissible positive smoothing scales to zero. -/
theorem fourth_eq_zero (H : ChaosEntropyHypotheses D kappa A radius 0)
    (hkappa : 0 < kappa) (hradius : 0 < radius) : D.component 4 = 0 := by
  have hlim : Tendsto (fun x : ℝ => (2 / kappa) * (A * x)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using ((tendsto_const_nhds.mul (tendsto_const_nhds.mul
      (tendsto_id : Tendsto (fun x : ℝ => x) (𝓝 (0 : ℝ)) (𝓝 0)))).mono_left nhdsWithin_le_nhds)
  have hb : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), ‖D.component 4‖ ^ 2 ≤ (2 / kappa) * (A * x) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hradius).filter_mono nhdsWithin_le_nhds] with x hx hxr
    simpa only [zero_div, zero_add] using H.at_scale hkappa hx hxr.le
  have hz := ge_of_tendsto hlim hb
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (D.component 4)])

/-- The optimized positive-deficit estimate now follows from the complete
analytic hypotheses at the balancing scale, provided it is in the domain. -/
theorem optimized (H : ChaosEntropyHypotheses D kappa A radius epsilon)
    (hkappa : 0 < kappa) (hepsilon : 0 < epsilon) (hA : 0 < A)
    (hscale : (epsilon / A) ^ ((9 : ℝ)⁻¹) ≤ radius) :
    ‖D.component 4‖ ≤ (2 / Real.sqrt kappa) * A ^ (4 / 9 : ℝ) * epsilon ^ (1 / 18 : ℝ) := by
  obtain ⟨hx, _⟩ := ninth_root_balance epsilon A hepsilon hA
  exact optimized_quartic_norm epsilon (D.deficit (((epsilon / A) ^ ((9 : ℝ)⁻¹)) ^ 2))
    kappa A ‖D.component 4‖ hkappa hepsilon hA (norm_nonneg _)
    (H.deficit_bounds _ hx hscale).2 (H.lower_deficit hx hscale)

end ChaosEntropyHypotheses

/-- The manuscript's small-deficit condition puts the balancing scale in the
expansion domain with its correct `B⁻⁶` dependence. -/
theorem bounded_law_balancing_scale (epsilon C B eta : ℝ)
    (hepsilon : 0 < epsilon) (hC : 0 < C) (hB : 0 < B) (heta : 0 < eta)
    (hsmall : epsilon ≤ C * eta ^ 9 / B ^ 6) :
    (epsilon / (C * B ^ 3)) ^ ((9 : ℝ)⁻¹) ≤ eta / B := by
  let x := (epsilon / (C * B ^ 3)) ^ ((9 : ℝ)⁻¹)
  have hA : 0 < C * B ^ 3 := mul_pos hC (pow_pos hB _)
  obtain ⟨hx, hbalance⟩ := ninth_root_balance epsilon (C * B ^ 3) hepsilon hA
  have hboundary : (C * B ^ 3) * (eta / B) ^ 9 = C * eta ^ 9 / B ^ 6 := by
    field_simp
    ring
  have hp : x ^ 9 ≤ (eta / B) ^ 9 := by
    apply (mul_le_mul_left hA).mp
    change (C * B ^ 3) * ((epsilon / (C * B ^ 3)) ^ ((9 : ℝ)⁻¹)) ^ 9 ≤ _
    rw [← hbalance, hboundary]
    exact hsmall
  exact (pow_le_pow_iff_left₀ hx.le (div_pos heta hB).le (by decide : (9 : ℕ) ≠ 0)).mp hp

/-- A convenient explicit smoothing radius implies both original restrictions
`t≤1/2` and `t≤c B⁻²`. -/
theorem bounded_law_original_domain (B eta c x : ℝ)
    (hB : 2 ≤ B) (heta1 : eta ≤ 1) (hetac : eta ^ 2 ≤ c)
    (hx : 0 ≤ x) (hxr : x ≤ eta / B) : x ^ 2 ≤ 1 / 2 ∧ x ^ 2 ≤ c / B ^ 2 := by
  have hBp : 0 < B := by linarith
  have hprod := (le_div_iff₀ hBp).mp hxr
  have hxb : 2 * x ≤ x * B := by nlinarith
  constructor
  · nlinarith [sq_nonneg (x - 1 / 2)]
  · apply (le_div_iff₀ (sq_pos_of_pos hBp)).2
    have hs := pow_le_pow_left₀ (mul_nonneg hx hBp.le) hprod 2
    nlinarith

/-- The complete abstract bounded-law quartic estimate, including epsilon=0.
All analytic ingredients remain explicit channel-dependent hypotheses. -/
theorem abstract_entropy_to_quartic (D : ChaosEntropyData E)
    (kappa C B eta epsilon : ℝ)
    (hkappa : 0 < kappa) (hC : 0 < C) (hB : 0 < B) (heta : 0 < eta)
    (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ C * eta ^ 9 / B ^ 6)
    (H : ChaosEntropyHypotheses D kappa (C * B ^ 3) (eta / B) epsilon) :
    ‖D.component 4‖ ≤ (2 / Real.sqrt kappa) * C ^ (4 / 9 : ℝ) *
      B ^ (4 / 3 : ℝ) * epsilon ^ (1 / 18 : ℝ) := by
  by_cases he : epsilon = 0
  · subst epsilon
    rw [H.fourth_eq_zero hkappa (div_pos heta hB), norm_zero]
    positivity
  · have hep : 0 < epsilon := lt_of_le_of_ne hepsilon (Ne.symm he)
    have hb := H.optimized hkappa hep (mul_pos hC (pow_pos hB _))
      (bounded_law_balancing_scale epsilon C B eta hep hC hB heta hsmall)
    rw [bounded_law_power_identity C B hC hB] at hb
    exact hb.trans_eq (by ring)

/-- A homogeneous quartic discrepancy is a bounded functional of its fourth
Hermite component once its degree-zero and degree-two contributions match. -/
theorem quartic_functional_bound (D : ChaosEntropyData E)
    (kappa C B eta epsilon : ℝ)
    (hkappa : 0 < kappa) (hC : 0 < C) (hB : 0 < B) (heta : 0 < eta)
    (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ C * eta ^ 9 / B ^ 6)
    (H : ChaosEntropyHypotheses D kappa (C * B ^ 3) (eta / B) epsilon)
    (quartic : E →L[ℝ] ℝ) :
    |quartic (D.component 4)| ≤ ‖quartic‖ * ((2 / Real.sqrt kappa) * C ^ (4 / 9 : ℝ) *
      B ^ (4 / 3 : ℝ) * epsilon ^ (1 / 18 : ℝ)) := by
  calc
    _ = ‖quartic (D.component 4)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖quartic‖ * ‖D.component 4‖ := quartic.le_opNorm _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (abstract_entropy_to_quartic D kappa C B eta epsilon hkappa hC hB heta hepsilon hsmall H)
      (norm_nonneg _)

/-- The concrete Cauchy--Schwarz form for pairing a fixed quartic Hermite
projection with the fourth component. -/
theorem quartic_inner_bound (D : ChaosEntropyData E)
    (kappa C B eta epsilon : ℝ)
    (hkappa : 0 < kappa) (hC : 0 < C) (hB : 0 < B) (heta : 0 < eta)
    (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ C * eta ^ 9 / B ^ 6)
    (H : ChaosEntropyHypotheses D kappa (C * B ^ 3) (eta / B) epsilon) (P4 : E) :
    |@inner ℝ E _ P4 (D.component 4)| ≤ ‖P4‖ * ((2 / Real.sqrt kappa) * C ^ (4 / 9 : ℝ) *
      B ^ (4 / 3 : ℝ) * epsilon ^ (1 / 18 : ℝ)) := by
  have hcs : |@inner ℝ E _ P4 (D.component 4)| ≤ ‖P4‖ * ‖D.component 4‖ := by
    simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) P4 (D.component 4)
  apply hcs.trans
  exact mul_le_mul_of_nonneg_left
    (abstract_entropy_to_quartic D kappa C B eta epsilon hkappa hC hB heta hepsilon hsmall H)
    (norm_nonneg _)

/-- A fixed linear map from quartic coefficients to the fourth Hermite
projection makes the estimate uniform on bounded coefficient sets. The
application still proves that its polynomial discrepancy is this pairing. -/
theorem quartic_coefficient_bound {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (D : ChaosEntropyData E) (kappa C B eta epsilon : ℝ)
    (hkappa : 0 < kappa) (hC : 0 < C) (hB : 0 < B) (heta : 0 < eta)
    (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ C * eta ^ 9 / B ^ 6)
    (H : ChaosEntropyHypotheses D kappa (C * B ^ 3) (eta / B) epsilon)
    (projection : V →L[ℝ] E) (coeff : V) (L : ℝ) (hcoeff : ‖coeff‖ ≤ L) :
    |@inner ℝ E _ (projection coeff) (D.component 4)| ≤
      (‖projection‖ * L) * ((2 / Real.sqrt kappa) * C ^ (4 / 9 : ℝ) *
        B ^ (4 / 3 : ℝ) * epsilon ^ (1 / 18 : ℝ)) := by
  have hb := quartic_inner_bound D kappa C B eta epsilon hkappa hC hB heta
    hepsilon hsmall H (projection coeff)
  have hproj : ‖projection coeff‖ ≤ ‖projection‖ * L :=
    (projection.le_opNorm coeff).trans (mul_le_mul_of_nonneg_left hcoeff (norm_nonneg _))
  apply hb.trans
  apply mul_le_mul_of_nonneg_right hproj
  positivity

/-- Any quartic discrepancy identified with its fourth-chaos functional
inherits the quantitative estimate. Degree-zero and degree-two matching are
the reason for this identification in Gaussian applications. -/
theorem quartic_discrepancy_bound (D : ChaosEntropyData E)
    (kappa C B eta epsilon : ℝ)
    (hkappa : 0 < kappa) (hC : 0 < C) (hB : 0 < B) (heta : 0 < eta)
    (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ C * eta ^ 9 / B ^ 6)
    (H : ChaosEntropyHypotheses D kappa (C * B ^ 3) (eta / B) epsilon)
    (quartic : E →L[ℝ] ℝ) (discrepancy : ℝ)
    (hdiscrepancy : discrepancy = quartic (D.component 4)) :
    |discrepancy| ≤ ‖quartic‖ * ((2 / Real.sqrt kappa) * C ^ (4 / 9 : ℝ) *
      B ^ (4 / 3 : ℝ) * epsilon ^ (1 / 18 : ℝ)) := by
  rw [hdiscrepancy]
  exact quartic_functional_bound D kappa C B eta epsilon hkappa hC hB heta hepsilon hsmall H quartic

end GeneralizedBulk.Entropy
