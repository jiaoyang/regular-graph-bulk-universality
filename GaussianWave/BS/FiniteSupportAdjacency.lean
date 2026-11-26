import Mathlib

/-! Actual finite-support adjacency and its symmetric Euclidean pairing.
This is the operator layer behind radial Gaussian convolution filters. -/
noncomputable section
open scoped BigOperators Classical
namespace GaussianWave.BS
variable {V : Type*}

/-- The ordinary finite Euclidean pairing on finitely supported vectors. -/
def finsuppPairing : (V →₀ ℝ) →ₗ[ℝ] (V →₀ ℝ) →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ (fun v => (Finsupp.lapply v : (V →₀ ℝ) →ₗ[ℝ] ℝ))

theorem finsuppPairing_apply (a b : V →₀ ℝ) :
    finsuppPairing a b = a.sum (fun v c => c*b v) := by
  simp [finsuppPairing, Finsupp.linearCombination_apply, Finsupp.sum]

@[simp] theorem finsuppPairing_single_left (v : V) (c : ℝ) (b : V →₀ ℝ) :
    finsuppPairing (Finsupp.single v c) b = c*b v := by
  simp [finsuppPairing, Finsupp.linearCombination_single]

@[simp] theorem finsuppPairing_single_right (a : V →₀ ℝ) (v : V) (c : ℝ) :
    finsuppPairing a (Finsupp.single v c) = a v*c := by
  rw [finsuppPairing_apply]
  unfold Finsupp.sum
  simp only [Finsupp.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq']
  by_cases hv : v ∈ a.support
  · simp [hv]
  · simp [hv, Finsupp.not_mem_support_iff.1 hv]

theorem finsuppPairing_symm (a b : V →₀ ℝ) : finsuppPairing a b=finsuppPairing b a := by
  refine Finsupp.induction_linear a ?_ ?_ ?_
  · simp
  · intro a c ha hc
    simp only [map_add, LinearMap.add_apply, ha, hc]
  · intro v c
    rw [finsuppPairing_single_left, finsuppPairing_single_right, mul_comm]

/-- The self-pairing is literally the finite sum of coefficient squares. -/
theorem finsuppPairing_self (a : V →₀ ℝ) :
    finsuppPairing a a=a.sum (fun _ c => c^2) := by
  simp [finsuppPairing_apply,Finsupp.sum,pow_two]

theorem finsuppPairing_self_nonneg (a : V →₀ ℝ) : 0 ≤ finsuppPairing a a := by
  rw [finsuppPairing_self]
  exact Finset.sum_nonneg (fun v hv => sq_nonneg _)

/-- Actual Cauchy--Schwarz for the finite Euclidean coefficient pairing. -/
theorem finsuppPairing_sq_le (a b : V →₀ ℝ) :
    finsuppPairing a b ^ 2 ≤ finsuppPairing a a*finsuppPairing b b := by
  let S := a.support ∪ b.support
  have ha : a.support ⊆ S := Finset.subset_union_left
  have hb : b.support ⊆ S := Finset.subset_union_right
  rw [finsuppPairing_apply,finsuppPairing_self,finsuppPairing_self,
    a.sum_of_support_subset ha (fun v c => c*b v) (by simp),
    a.sum_of_support_subset ha (fun _ c => c^2) (by simp),
    b.sum_of_support_subset hb (fun _ c => c^2) (by simp)]
  exact Finset.sum_mul_sq_le_sq_mul_sq S a b

variable (G : SimpleGraph V) [G.LocallyFinite]

/-- The actual adjacency row is finitely supported on the actual neighbor
set, without any finite-ambient-graph assumption. -/
def finiteAdjacencyRow (v : V) : V →₀ ℝ :=
  Finsupp.onFinset (G.neighborFinset v) (fun w => if G.Adj v w then 1 else 0)
    (by intro w hw; simpa only [SimpleGraph.mem_neighborFinset] using
      (show G.Adj v w from by by_contra h; simp [h] at hw))

@[simp] theorem finiteAdjacencyRow_apply (v w : V) :
    finiteAdjacencyRow G v w = if G.Adj v w then 1 else 0 := rfl

/-- Finite-support adjacency, constructed by extending its actual rows
linearly from point masses. -/
def finiteAdjacency : (V →₀ ℝ) →ₗ[ℝ] (V →₀ ℝ) :=
  Finsupp.linearCombination ℝ (finiteAdjacencyRow G)

@[simp] theorem finiteAdjacency_single (v : V) (c : ℝ) :
    finiteAdjacency G (Finsupp.single v c) = c • finiteAdjacencyRow G v :=
  Finsupp.linearCombination_single _ _ _

private theorem neighbor_sum_single (u v : V) (c : ℝ) :
    (∑ z : G.neighborSet u, Finsupp.single v c z.val) = if G.Adj u v then c else 0 := by
  by_cases huv : G.Adj u v
  · rw [if_pos huv]
    apply (Finset.sum_eq_single_of_mem (⟨v,huv⟩ : G.neighborSet u) (Finset.mem_univ _) ?_).trans
    · simp
    · intro z hz hne
      have hzv : z.val ≠ v := by intro he; exact hne (Subtype.ext he)
      simp [Finsupp.single_apply, Ne.symm hzv]
  · rw [if_neg huv]
    apply Finset.sum_eq_zero
    intro z hz
    have hzv : z.val ≠ v := by intro he; exact huv (he ▸ z.property)
    simp [Finsupp.single_apply, Ne.symm hzv]

/-- Pointwise, the constructed operator is literally the finite sum over
neighbors. -/
theorem finiteAdjacency_apply (a : V →₀ ℝ) (u : V) :
    finiteAdjacency G a u = ∑ z : G.neighborSet u, a z.val := by
  refine Finsupp.induction_linear a ?_ ?_ ?_
  · simp
  · intro a b ha hb
    simp only [map_add, Finsupp.add_apply, Finset.sum_add_distrib, ha, hb]
  · intro v c
    rw [finiteAdjacency_single, neighbor_sum_single]
    simp only [Finsupp.smul_apply, smul_eq_mul, finiteAdjacencyRow_apply]
    by_cases h : G.Adj u v
    · simp [h,h.symm]
    · have h' : ¬G.Adj v u := fun hvu => h hvu.symm
      simp [h,h']

/-- Adjacency is genuinely self-adjoint for the finite Euclidean pairing. -/
theorem finsuppPairing_adjacency (a b : V →₀ ℝ) :
    finsuppPairing (finiteAdjacency G a) b = finsuppPairing a (finiteAdjacency G b) := by
  refine Finsupp.induction_linear a ?_ ?_ ?_
  · simp
  · intro a c ha hc
    simp only [map_add, LinearMap.add_apply, ha, hc]
  · intro v c
    refine Finsupp.induction_linear b ?_ ?_ ?_
    · simp
    · intro b e hb he
      simp only [map_add, LinearMap.add_apply, hb, he]
    · intro w e
      simp only [finiteAdjacency_single, map_smul, LinearMap.smul_apply,
        finsuppPairing_single_left, finsuppPairing_single_right, Finsupp.smul_apply,
        smul_eq_mul, finiteAdjacencyRow_apply]
      by_cases h : G.Adj v w
      · simp [h,h.symm]; ring
      · have h' : ¬G.Adj w v := fun hwv => h hwv.symm
        simp [h,h']


/-- Adjacency of an actual point mass is the sum of point masses at all
actual neighbors. -/
theorem finiteAdjacency_single_sum (u : V) :
    finiteAdjacency G (Finsupp.single u 1)=
      ∑ z : G.neighborSet u, Finsupp.single z.val 1 := by
  ext v
  rw [finiteAdjacency_single,Finsupp.finset_sum_apply]
  simp only [one_smul,finiteAdjacencyRow_apply]
  have he : (∑ z : G.neighborSet u, Finsupp.single z.val (1 : ℝ) v)=
      ∑ z : G.neighborSet u, Finsupp.single v (1 : ℝ) z.val := by
    apply Finset.sum_congr rfl
    intro z hz
    simp only [Finsupp.single_apply]
    by_cases he : v=z.val
    · simp [he]
    · simp [he,Ne.symm he]
  rw [he,neighbor_sum_single]

end GaussianWave.BS
