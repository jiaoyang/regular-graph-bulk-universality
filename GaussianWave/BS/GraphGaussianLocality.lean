import GaussianWave.BS.GraphGaussianBlockFactor

/-! Actual graph-distance locality of the adjacency-polynomial Gaussian rule,
including graphs with cycles and disconnected graphs. Extended distance avoids
any connectivity premise. -/
noncomputable section
open scoped BigOperators Classical
namespace GaussianWave.BS

variable {V : Type*} (G : SimpleGraph V) [G.LocallyFinite]

def FinsuppSupportedInBall (u : V) (R : ℕ) (a : V →₀ ℝ) : Prop :=
  ∀ v,a v ≠ 0 → G.edist u v ≤ (R : ℕ∞)

private theorem supported_mono {u : V} {R S : ℕ} {a : V →₀ ℝ}
    (h : FinsuppSupportedInBall G u R a) (hRS : R ≤ S) :
    FinsuppSupportedInBall G u S a := by
  intro v hv
  exact (h v hv).trans (by exact_mod_cast hRS)

private theorem supported_add {u : V} {R : ℕ} {a b : V →₀ ℝ}
    (ha : FinsuppSupportedInBall G u R a) (hb : FinsuppSupportedInBall G u R b) :
    FinsuppSupportedInBall G u R (a+b) := by
  intro v hv
  by_cases hav : a v=0
  · exact hb v (by simpa [hav] using hv)
  · exact ha v hav

private theorem supported_smul {u : V} {R : ℕ} {a : V →₀ ℝ}
    (ha : FinsuppSupportedInBall G u R a) (c : ℝ) :
    FinsuppSupportedInBall G u R (c • a) := by
  intro v hv
  exact ha v (by intro he; simp [he] at hv)

/-- One adjacency step enlarges the coefficient support by at most one. -/
theorem finiteAdjacency_supported {u : V} {R : ℕ} {a : V →₀ ℝ}
    (ha : FinsuppSupportedInBall G u R a) :
    FinsuppSupportedInBall G u (R+1) (finiteAdjacency G a) := by
  intro v hv
  rw [finiteAdjacency_apply] at hv
  obtain ⟨z,hz,haz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
  calc
    G.edist u v ≤ G.edist u z.val+G.edist z.val v := SimpleGraph.edist_triangle
    _ ≤ (R : ℕ∞)+1 := add_le_add (ha z.val haz)
      (by rw [(SimpleGraph.edist_eq_one_iff_adj).mpr z.property.symm])
    _ = _ := by norm_cast

/-- The sphere polynomial of degree n has radius at most n on every graph. -/
theorem radialSphereOperator_supported (d : ℝ) (u : V) (n : ℕ) :
    FinsuppSupportedInBall G u n
      (radialSphereOperator (finiteAdjacency G) d n (Finsupp.single u 1)) := by
  have h0 : FinsuppSupportedInBall G u 0 (Finsupp.single u (1 : ℝ)) := by
    intro v hv
    have he : u=v := by by_contra h; simp [Finsupp.single_apply,h] at hv
    subst v
    simp
  induction n using Nat.twoStepInduction with
  | zero => exact h0
  | one => exact finiteAdjacency_supported G h0
  | more n hn hn1 =>
    simp only [radialSphereOperator,LinearMap.sub_apply,Module.End.mul_apply,LinearMap.smul_apply]
    rw [sub_eq_add_neg]
    apply supported_add G (finiteAdjacency_supported G hn1)
    have hneg := supported_smul G (supported_mono G hn (by omega : n ≤ n+2))
      (-(if n=0 then d else d-1))
    simpa only [neg_smul] using hneg

/-- Every radial filter is supported in its prescribed finite radius. -/
theorem radialFilterOperator_supported (d : ℝ) (u : V) (R : ℕ) (f : ℕ → ℝ) :
    FinsuppSupportedInBall G u R
      (radialFilterOperator (finiteAdjacency G) d R f (Finsupp.single u 1)) := by
  intro v hv
  simp only [radialFilterOperator,LinearMap.sum_apply,LinearMap.smul_apply,
    Finsupp.finset_sum_apply,Finsupp.smul_apply,smul_eq_mul] at hv
  obtain ⟨n,hn,hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
  have han : radialSphereOperator (finiteAdjacency G) d n (Finsupp.single u 1) v ≠ 0 := by
    intro he
    simp only [he,mul_zero] at hne
    exact hne rfl
  exact (radialSphereOperator_supported G d u n v han).trans
    (by exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hn)))

/-- The actual Gaussian graph rule uses only labels within b+1. -/
theorem graphRadialGaussianCoefficient_supported (d : ℕ) (x : ℝ) (b : ℕ) (u : V) :
    FinsuppSupportedInBall G u (b+1) (graphRadialGaussianCoefficient G d x b u) := by
  apply supported_smul G
  exact radialFilterOperator_supported G _ _ _ _

/-- Literal sample locality, derived from the actual coefficient support. -/
theorem graphRadialGaussianSample_local (d : ℕ) (x : ℝ) (b : ℕ) (u : V) (ξ ζ : V → ℝ)
    (h : ∀ v,G.edist u v ≤ (b+1 : ℕ) → ξ v=ζ v) :
    finiteSupportGaussianSample (graphRadialGaussianCoefficient G d x b) ξ u =
      finiteSupportGaussianSample (graphRadialGaussianCoefficient G d x b) ζ u := by
  unfold finiteSupportGaussianSample Finsupp.sum
  apply Finset.sum_congr rfl
  intro v hv
  change _ * ξ v = _ * ζ v
  rw [h v (graphRadialGaussianCoefficient_supported G d x b u v
    (Finsupp.mem_support_iff.mp hv))]

end GaussianWave.BS
