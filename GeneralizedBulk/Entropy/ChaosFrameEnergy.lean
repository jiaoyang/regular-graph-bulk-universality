import GeneralizedBulk.Entropy.GaussianDerivativeChannels

/-! Exact directional chaos energy from a concrete weighted Euclidean frame. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Hermite
variable {I K L : Type*} [Fintype I] [DecidableEq I] [Fintype K] [Fintype L]

/-- A finite weighted frame identity transfers to the energies of actual
Gaussian polynomial directional derivatives by integration. -/
theorem weighted_directionalLp_energy (a : K → I → ℕ) (coeff : K → ℝ)
    (v : L → I → ℝ) (weight : L → ℝ)
    (hframe : ∀ u : I → ℝ, (∑ l, weight l * (∑ i, v l i * u i) ^ 2) = ∑ i, u i ^ 2) :
    (∑ l, weight l * ‖directionalLp a coeff (v l)‖ ^ 2) =
      ∑ i, ‖chaosDerivativeLp a coeff i‖ ^ 2 := by
  have hd (l : L) : Integrable (fun x => weight l * directionalFunction a coeff (v l) x ^ 2)
      (standardGaussian I) := (directionalFunction_memLp_two a coeff (v l)).integrable_sq.const_mul _
  have hi (i : I) : Integrable (fun x => chaosDerivativeFunction a coeff i x ^ 2)
      (standardGaussian I) :=
    ((memLp_congr_ae (chaosDerivativeLp_ae a coeff i)).1 (Lp.memLp _)).integrable_sq
  calc
    _ = ∫ x, ∑ l, weight l * directionalFunction a coeff (v l) x ^ 2 ∂standardGaussian I := by
      rw [integral_finset_sum _ (fun l _ => hd l)]
      simp_rw [integral_const_mul, integral_directionalFunction_sq]
    _ = ∫ x, ∑ i, chaosDerivativeFunction a coeff i x ^ 2 ∂standardGaussian I := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => hframe (fun i => chaosDerivativeFunction a coeff i x))
    _ = _ := by
      rw [integral_finset_sum _ (fun i _ => hi i)]
      simp_rw [integral_chaosDerivativeFunction_sq]


/-- The same integration argument applies when a concrete frame identity is
needed only on the actual pointwise gradient subspace. -/
theorem weighted_directionalLp_energy_on_subspace (a : K → I → ℕ) (coeff : K → ℝ)
    (v : L → I → ℝ) (weight : L → ℝ) (S : Submodule ℝ (I → ℝ))
    (hgrad : ∀ x, (fun i => chaosDerivativeFunction a coeff i x) ∈ S)
    (hframe : ∀ u ∈ S, (∑ l, weight l * (∑ i, v l i * u i) ^ 2) = ∑ i, u i ^ 2) :
    (∑ l, weight l * ‖directionalLp a coeff (v l)‖ ^ 2) =
      ∑ i, ‖chaosDerivativeLp a coeff i‖ ^ 2 := by
  have hd (l : L) : Integrable (fun x => weight l * directionalFunction a coeff (v l) x ^ 2)
      (standardGaussian I) := (directionalFunction_memLp_two a coeff (v l)).integrable_sq.const_mul _
  have hi (i : I) : Integrable (fun x => chaosDerivativeFunction a coeff i x ^ 2)
      (standardGaussian I) :=
    ((memLp_congr_ae (chaosDerivativeLp_ae a coeff i)).1 (Lp.memLp _)).integrable_sq
  calc
    _ = ∫ x, ∑ l, weight l * directionalFunction a coeff (v l) x ^ 2 ∂standardGaussian I := by
      rw [integral_finset_sum _ (fun l _ => hd l)]
      simp_rw [integral_const_mul, integral_directionalFunction_sq]
    _ = ∫ x, ∑ i, chaosDerivativeFunction a coeff i x ^ 2 ∂standardGaussian I := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => hframe _ (hgrad x))
    _ = _ := by
      rw [integral_finset_sum _ (fun i _ => hi i)]
      simp_rw [integral_chaosDerivativeFunction_sq]

/-- The concrete retained-coordinate linear subspace after orthogonal change
of basis. -/
def observationSubspace (O : Matrix I I ℝ) (observed : Finset I) : Submodule ℝ (I → ℝ) where
  carrier := {u | ∀ i, i ∉ observed → O.transpose.mulVec u i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro u v hu hv i hi
    simp only [Matrix.mulVec_add, Pi.add_apply, hu i hi, hv i hi, add_zero]
  smul_mem' := by
    intro c u hu i hi
    simp only [Matrix.mulVec_smul, Pi.smul_apply, hu i hi, smul_zero]

/-- A frame of the observation subspace recovers the full derivative energy
of the actual Gaussian conditional polynomial. -/
theorem projected_directionalLp_degree_energy {J : Type*} [Fintype J]
    (O : Matrix I I ℝ) (hO : O * O.transpose = 1) (observed : Finset I)
    (a : K → I → ℕ) (coeff : K → ℝ) (b : J → I → ℕ) (other : J → ℝ)
    (hbinj : Function.Injective b) (degree : ℕ) (ha : ∀ k, (∑ i, a k i) ≤ degree)
    (hb : ∀ j, (∑ i, b j i) = degree)
    (heq : chaosLp b other = subspaceConditionalL2 O hO observed (chaosLp a coeff))
    (v : L → I → ℝ) (weight : L → ℝ)
    (hframe : ∀ u ∈ observationSubspace O observed,
      (∑ l, weight l * (∑ i, v l i * u i) ^ 2) = ∑ i, u i ^ 2) :
    (∑ l, weight l * ‖directionalLp b other (v l)‖ ^ 2) =
      (degree : ℝ) * ‖chaosLp b other‖ ^ 2 := by
  rw [weighted_directionalLp_energy_on_subspace b other v weight (observationSubspace O observed)
    (fun x i hi => subspaceConditionalL2_gradient_retained O hO observed a coeff b other degree ha
      (fun j => (hb j).le) heq x i hi) hframe]
  exact chaos_derivative_energy b hbinj other degree hb

/-- The weighted directional energy of a homogeneous polynomial is its true
Gaussian chaos degree times its squared L² norm. -/
theorem weighted_directionalLp_degree_energy (a : K → I → ℕ) (ha : Function.Injective a)
    (coeff : K → ℝ) (degree : ℕ) (hdegree : ∀ k, ∑ i, a k i = degree)
    (v : L → I → ℝ) (weight : L → ℝ)
    (hframe : ∀ u : I → ℝ, (∑ l, weight l * (∑ i, v l i * u i) ^ 2) = ∑ i, u i ^ 2) :
    (∑ l, weight l * ‖directionalLp a coeff (v l)‖ ^ 2) =
      (degree : ℝ) * ‖chaosLp a coeff‖ ^ 2 := by
  rw [weighted_directionalLp_energy a coeff v weight hframe]
  exact chaos_derivative_energy a ha coeff degree hdegree


/-- Paired form of the frame identity used by the star channels. -/
theorem paired_directionalLp_degree_energy (a : K → I → ℕ) (ha : Function.Injective a)
    (coeff : K → ℝ) (degree : ℕ) (hdegree : ∀ k, ∑ i, a k i = degree)
    (A B : L → I → ℝ) (tA tB : L → ℝ)
    (hframe : ∀ u : I → ℝ, (∑ l, (tA l * (∑ i, A l i * u i) ^ 2 +
      tB l * (∑ i, B l i * u i) ^ 2)) = ∑ i, u i ^ 2) :
    (∑ l, (tA l * ‖directionalLp a coeff (A l)‖ ^ 2 +
      tB l * ‖directionalLp a coeff (B l)‖ ^ 2)) =
      (degree : ℝ) * ‖chaosLp a coeff‖ ^ 2 := by
  have hh := weighted_directionalLp_degree_energy a ha coeff degree hdegree
    (Sum.elim A B) (Sum.elim tA tB) (fun u => by
      simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, ← Finset.sum_add_distrib] using hframe u)
  simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, ← Finset.sum_add_distrib] using hh

/-- The unweighted ON-frame energy of an actual conditional polynomial. -/
theorem paired_projected_directionalLp_degree_energy {J : Type*} [Fintype J]
    (O : Matrix I I ℝ) (hO : O * O.transpose = 1) (observed : Finset I)
    (a : K → I → ℕ) (coeff : K → ℝ) (b : J → I → ℕ) (other : J → ℝ)
    (hbinj : Function.Injective b) (degree : ℕ) (ha : ∀ k, (∑ i, a k i) ≤ degree)
    (hb : ∀ j, (∑ i, b j i) = degree)
    (heq : chaosLp b other = subspaceConditionalL2 O hO observed (chaosLp a coeff))
    (A B : L → I → ℝ)
    (hframe : ∀ u ∈ observationSubspace O observed,
      (∑ l, ((∑ i, A l i * u i) ^ 2 + (∑ i, B l i * u i) ^ 2)) = ∑ i, u i ^ 2) :
    (∑ l, (‖directionalLp b other (A l)‖ ^ 2 + ‖directionalLp b other (B l)‖ ^ 2)) =
      (degree : ℝ) * ‖chaosLp b other‖ ^ 2 := by
  have hh := projected_directionalLp_degree_energy O hO observed a coeff b other hbinj degree ha hb heq
    (Sum.elim A B) (fun _ => 1) (fun u hu => by
      simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, one_mul, ← Finset.sum_add_distrib] using hframe u hu)
  simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, one_mul, ← Finset.sum_add_distrib] using hh

end GeneralizedBulk.Entropy.Hermite
