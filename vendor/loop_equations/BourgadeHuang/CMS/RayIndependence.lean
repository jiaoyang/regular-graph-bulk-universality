import BourgadeHuang.CMS.Clearing
import BourgadeHuang.CMS.AsymptoticIndependence
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith

/-!
# Independence of the genuine beta = 2 explicit solutions

Each candidate sign pattern has its own imaginary ray. Its exponential rate
is uniquely maximal on that ray, and all pairwise ray directions are distinct.
Clearing the collision denominators permits analytic continuation of a
relation from any nonempty open collision-free set to these rays.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace BourgadeHuang.CMS

def realSign (s : Sign) : ℝ := if s then 1 else -1

@[simp] theorem ofReal_realSign (s : Sign) : (realSign s : ℂ) = signValue s := by
  cases s <;> simp [realSign, signValue]

def rayWeight {d : ℕ} (j : Fin d) : ℝ := (j.val : ℝ) + 1

theorem rayWeight_pos {d : ℕ} (j : Fin d) : 0 < rayWeight j := by
  unfold rayWeight
  have : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
  linarith

def rayDirection {d : ℕ} (σ : Fin d → Sign) (j : Fin d) : ℂ :=
  -Complex.I * (realSign (σ j) * rayWeight j : ℝ)

def candidateRay {d : ℕ} (σ : Fin d → Sign) (R : ℝ) : Point d :=
  fun j => (R : ℂ) * rayDirection σ j

def dominantRate (d : ℕ) : ℝ := ∑ j : Fin d, rayWeight j

def rayRate {d : ℕ} (σ τ : Fin d → Sign) : ℝ :=
  ∑ j, realSign (τ j) * realSign (σ j) * rayWeight j

def rayDegree {d : ℕ} (τ : Fin d → Sign) : ℕ := (samePairs τ).card

def rayCoefficient {d : ℕ} (σ τ : Fin d → Sign) : ℂ :=
  ∏ p ∈ samePairs τ, (rayDirection σ p.1 - rayDirection σ p.2)

theorem rayDirection_collisionFree {d : ℕ} (σ : Fin d → Sign) :
    CollisionFree (rayDirection σ) := by
  intro i j hij
  have him := congrArg Complex.im hij
  have hi := rayWeight_pos i
  have hj := rayWeight_pos j
  cases hsi : σ i <;> cases hsj : σ j <;>
    simp [rayDirection, realSign, hsi, hsj] at him
  · apply Fin.ext
    unfold rayWeight at him
    exact_mod_cast (by linarith : (i.val : ℝ) = (j.val : ℝ))
  · linarith
  · linarith
  · apply Fin.ext
    unfold rayWeight at him
    exact_mod_cast (by linarith : (i.val : ℝ) = (j.val : ℝ))

theorem rayCoefficient_ne_zero {d : ℕ} (σ τ : Fin d → Sign) :
    rayCoefficient σ τ ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  have hp' : p.1 < p.2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  exact (rayDirection_collisionFree σ).sub_ne_zero (ne_of_lt hp')

@[simp] theorem rayRate_self {d : ℕ} (σ : Fin d → Sign) :
    rayRate σ σ = dominantRate d := by
  unfold rayRate dominantRate
  apply Finset.sum_congr rfl
  intro j _
  cases σ j <;> simp [realSign]

theorem rayRate_lt_dominant {d : ℕ} (σ τ : Fin d → Sign) (hne : τ ≠ σ) :
    rayRate σ τ < dominantRate d := by
  have hex : ∃ j, τ j ≠ σ j := by
    by_contra hn
    apply hne
    funext j
    by_contra h
    exact hn ⟨j, h⟩
  obtain ⟨j₀, hj₀⟩ := hex
  unfold rayRate dominantRate
  apply Finset.sum_lt_sum
  · intro j _
    have hj := rayWeight_pos j
    cases hσ : σ j <;> cases hτ : τ j <;> simp [realSign] <;> linarith
  · refine ⟨j₀, Finset.mem_univ _, ?_⟩
    have hj := rayWeight_pos j₀
    cases hσ : σ j₀ <;> cases hτ : τ j₀ <;> simp [hσ, hτ] at hj₀ ⊢ <;>
      simp [realSign] <;> linarith

theorem phase_candidateRay {d : ℕ} (σ τ : Fin d → Sign) (R : ℝ) :
    phase τ (candidateRay σ R) = ((R * rayRate σ τ : ℝ) : ℂ) := by
  unfold phase candidateRay rayRate
  rw [Finset.mul_sum, Finset.mul_sum, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro j _
  cases hσ : σ j <;> cases hτ : τ j <;>
    simp [rayDirection, realSign, signValue, hσ, Complex.ofReal_mul] <;>
      ring_nf <;> simp [Complex.I_sq]

/-- Exact scaling along a real ray; the prefactor is a nonzero homogeneous
polynomial coefficient, not an asymptotic assumption. -/
theorem clearedSolution_candidateRay {d : ℕ} (σ τ : Fin d → Sign) (R : ℝ) :
    clearedSolution τ (candidateRay σ R) =
      Complex.exp ((R * rayRate σ τ : ℝ) : ℂ) * (R : ℂ) ^ rayDegree τ *
        rayCoefficient σ τ := by
  unfold clearedSolution
  rw [phase_candidateRay]
  have hp : (∏ p ∈ samePairs τ,
      (candidateRay σ R p.1 - candidateRay σ R p.2)) =
      (R : ℂ) ^ rayDegree τ * rayCoefficient σ τ := by
    calc
      _ = ∏ p ∈ samePairs τ,
          ((R : ℂ) * (rayDirection σ p.1 - rayDirection σ p.2)) := by
        apply Finset.prod_congr rfl
        intro p _
        simp only [candidateRay]
        ring
      _ = _ := by rw [Finset.prod_mul_distrib]; simp [rayDegree, rayCoefficient]
  rw [hp]
  ring

def candidateNormalization {d : ℕ} (σ : Fin d → Sign) (R : ℝ) : ℂ :=
  ((Real.exp (-dominantRate d * R) * R ^ (-(rayDegree σ : ℝ)) : ℝ) : ℂ) /
    rayCoefficient σ σ

theorem real_normalized_ray_factor (R a b : ℝ) (m n : ℕ) (hR : 0 < R) :
    (Real.exp (-a * R) * R ^ (-(m : ℝ))) * (Real.exp (R * b) * R ^ n) =
      R ^ ((n : ℝ) - (m : ℝ)) * Real.exp (-(a - b) * R) := by
  rw [show -(a - b) * R = -a * R + R * b by ring, Real.exp_add]
  rw [show (n : ℝ) - (m : ℝ) = -(m : ℝ) + (n : ℝ) by ring,
    Real.rpow_add hR, Real.rpow_natCast]
  ring

theorem normalized_candidateRay {d : ℕ} (σ τ : Fin d → Sign)
    (R : ℝ) (hR : 0 < R) :
    candidateNormalization σ R * clearedSolution τ (candidateRay σ R) =
      ((R ^ ((rayDegree τ : ℝ) - (rayDegree σ : ℝ)) *
          Real.exp (-(dominantRate d - rayRate σ τ) * R) : ℝ) : ℂ) *
        (rayCoefficient σ τ / rayCoefficient σ σ) := by
  rw [clearedSolution_candidateRay]
  unfold candidateNormalization
  rw [← Complex.ofReal_exp, ← Complex.ofReal_pow]
  rw [← real_normalized_ray_factor R (dominantRate d) (rayRate σ τ)
    (rayDegree σ) (rayDegree τ) hR]
  simp only [Complex.ofReal_mul, div_eq_mul_inv]
  ring

/-- Every candidate normalization isolates exactly its own cleared solution. -/
theorem tendsto_normalized_candidateRay {d : ℕ} (σ τ : Fin d → Sign) :
    Tendsto (fun R : ℝ =>
      candidateNormalization σ R * clearedSolution τ (candidateRay σ R))
      atTop (𝓝 (if τ = σ then (1 : ℂ) else 0)) := by
  by_cases hτσ : τ = σ
  · subst τ
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    rw [normalized_candidateRay σ σ R hR]
    simp [rayCoefficient_ne_zero]
  · simp only [if_neg hτσ]
    have hgap : 0 < dominantRate d - rayRate σ τ :=
      sub_pos.mpr (rayRate_lt_dominant σ τ hτσ)
    have hr := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      ((rayDegree τ : ℝ) - (rayDegree σ : ℝ))
      (dominantRate d - rayRate σ τ) hgap
    have hc := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hr
    have hm := hc.mul_const (rayCoefficient σ τ / rayCoefficient σ σ)
    apply (show Tendsto (fun R : ℝ =>
        ((R ^ ((rayDegree τ : ℝ) - (rayDegree σ : ℝ)) *
            Real.exp (-(dominantRate d - rayRate σ τ) * R) : ℝ) : ℂ) *
          (rayCoefficient σ τ / rayCoefficient σ σ)) atTop (𝓝 (0 : ℂ)) by
      simpa using hm).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact (normalized_candidateRay σ τ R hR).symm

theorem linearIndependent_clearedSolution (d : ℕ) :
    LinearIndependent ℂ (clearedSolution (d := d)) := by
  exact linearIndependent_of_asymptotic_duals atTop clearedSolution
    candidateRay candidateNormalization tendsto_normalized_candidateRay

/-- Genuine explicit CMS solutions are independent on every nonempty open
collision-free domain. Connectedness of that domain is unnecessary here. -/
theorem linearIndependent_explicitSolution_on_open {d : ℕ}
    (U : Set (Point d)) (hU : IsOpen U) (hne : U.Nonempty)
    (hfree : ∀ z ∈ U, CollisionFree z) :
    LinearIndependent ℂ (fun σ : Fin d → Sign =>
      fun z : U => explicitSolution σ z.val) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc σ
  have hrel : ∀ z ∈ U, (∑ τ, c τ * explicitSolution τ z) = 0 := by
    intro z hz
    have heval := congrFun hc ⟨z, hz⟩
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using heval
  have hglobal := cleared_relation_global_of_open c U hU hne hfree hrel
  apply (Fintype.linearIndependent_iff.mp (linearIndependent_clearedSolution d)) c _ σ
  funext z
  have heval := congrFun hglobal z
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using heval

end BourgadeHuang.CMS
