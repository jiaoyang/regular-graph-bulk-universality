import Mathlib

/-!
# Exact finite-star covariance and regular-tree covariance recurrence

The finite-star proofs below are adapted from the user's earlier GeneralizedBulk
project (Graph/PermutationAverages and Graph/StarCovariance). They now depend only
on explicit finite spectral data, and contain no external probabilistic input.
The channel family is arbitrary, including arbitrary orthonormal vectors in a
multiple eigenspace. No assertion of eigenvector Gaussianity is assumed here.
-/

/-! Exact first- and two-position averages of uniform finite permutations. -/
noncomputable section
open scoped BigOperators

namespace GaussianWave.Permutation

theorem sum_perm_eval_eq {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℝ) (i j : α) :
    (∑ σ : Equiv.Perm α, f (σ i)) = ∑ σ : Equiv.Perm α, f (σ j) := by
  have h := Equiv.sum_comp (Equiv.mulRight (Equiv.swap i j))
    (fun σ : Equiv.Perm α => f (σ i))
  change (∑ σ : Equiv.Perm α, f ((σ * Equiv.swap i j) i)) = ∑ σ : Equiv.Perm α, f (σ i) at h
  simpa only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] using h.symm

theorem card_mul_sum_perm_eval {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℝ) (i : α) :
    (Fintype.card α : ℝ) * (∑ σ : Equiv.Perm α, f (σ i)) =
      (Fintype.card (Equiv.Perm α) : ℝ) * ∑ j, f j := by
  calc
    _ = ∑ j : α, ∑ σ : Equiv.Perm α, f (σ j) := by
      simp_rw [← sum_perm_eval_eq f i]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ∑ σ : Equiv.Perm α, ∑ j : α, f (σ j) := Finset.sum_comm
    _ = ∑ σ : Equiv.Perm α, ∑ j : α, f j := by
      apply Finset.sum_congr rfl
      intro σ hσ
      exact Equiv.sum_comp σ f
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem sum_perm_eval {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (f : α → ℝ) (i : α) :
    (∑ σ : Equiv.Perm α, f (σ i)) =
      (Fintype.card (Equiv.Perm α) : ℝ) / Fintype.card α * ∑ j, f j := by
  have hc : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h := card_mul_sum_perm_eval f i
  field_simp
  nlinarith only [h]

theorem exists_perm_pair {α : Type*} [DecidableEq α] (i j a b : α)
    (hij : i ≠ j) (hab : a ≠ b) :
    ∃ σ : Equiv.Perm α, σ i = a ∧ σ j = b := by
  let τ := Equiv.swap i a
  have hτi : τ i = a := Equiv.swap_apply_left i a
  have hτj : τ j ≠ a := by
    intro h
    apply hij
    exact τ.injective (hτi.trans h.symm)
  refine ⟨Equiv.swap (τ j) b * τ, ?_, ?_⟩
  · change Equiv.swap (τ j) b (τ i) = a
    rw [hτi, Equiv.swap_apply_of_ne_of_ne hτj.symm hab]
  · change Equiv.swap (τ j) b (τ j) = b
    exact Equiv.swap_apply_left _ _

theorem sum_perm_pair_eq {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → α → ℝ) (i j a b : α) (hij : i ≠ j) (hab : a ≠ b) :
    (∑ σ : Equiv.Perm α, f (σ i) (σ j)) =
      ∑ σ : Equiv.Perm α, f (σ a) (σ b) := by
  obtain ⟨τ, hτi, hτj⟩ := exists_perm_pair i j a b hij hab
  have h := Equiv.sum_comp (Equiv.mulRight τ)
    (fun σ : Equiv.Perm α => f (σ i) (σ j))
  change (∑ σ : Equiv.Perm α, f ((σ * τ) i) ((σ * τ) j)) =
    ∑ σ : Equiv.Perm α, f (σ i) (σ j) at h
  simpa only [Equiv.Perm.mul_apply, hτi, hτj] using h.symm

theorem sum_offdiagonal_const {α : Type*} [Fintype α] [DecidableEq α] (c : ℝ) :
    (∑ a : α, ∑ b : α, if a = b then 0 else c) =
      (Fintype.card α : ℝ) * (Fintype.card α - 1) * c := by
  have hi (a : α) : (∑ b : α, if a = b then 0 else c) = (Fintype.card α : ℝ) * c - c := by
    calc
      _ = ∑ b : α, (c - (if a = b then c else 0)) := by
        apply Finset.sum_congr rfl
        intro b hb
        split_ifs <;> simp
      _ = _ := by simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  simp_rw [hi]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

theorem card_mul_sum_perm_pair {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → α → ℝ) (i j : α) (hij : i ≠ j) :
    ((Fintype.card α : ℝ) * (Fintype.card α - 1)) *
      (∑ σ : Equiv.Perm α, f (σ i) (σ j)) =
      (Fintype.card (Equiv.Perm α) : ℝ) *
        ∑ a : α, ∑ b : α, if a = b then 0 else f a b := by
  have heq (a b : α) :
      (if a = b then 0 else ∑ σ : Equiv.Perm α, f (σ i) (σ j)) =
        if a = b then 0 else ∑ σ : Equiv.Perm α, f (σ a) (σ b) := by
    by_cases hab : a = b
    · simp only [hab, ↓reduceIte]
    · simp only [hab, ↓reduceIte]
      exact sum_perm_pair_eq f i j a b hij hab
  have hcomm (a b : α) :
      (if a = b then 0 else ∑ σ : Equiv.Perm α, f (σ a) (σ b)) =
        ∑ σ : Equiv.Perm α, if a = b then 0 else f (σ a) (σ b) := by
    by_cases hab : a = b <;> simp only [hab, ↓reduceIte, Finset.sum_const_zero]
  have hinvariant (σ : Equiv.Perm α) :
      (∑ a : α, ∑ b : α, if a = b then 0 else f (σ a) (σ b)) =
        ∑ a : α, ∑ b : α, if a = b then 0 else f a b := by
    calc
      _ = ∑ a : α, ∑ b : α, if σ a = σ b then 0 else f (σ a) (σ b) := by
        simp only [σ.injective.eq_iff]
      _ = ∑ a : α, ∑ b : α, if σ a = b then 0 else f (σ a) b := by
        apply Finset.sum_congr rfl
        intro a ha
        exact Equiv.sum_comp σ (fun b => if σ a = b then 0 else f (σ a) b)
      _ = _ := Equiv.sum_comp σ (fun a => ∑ b : α, if a = b then 0 else f a b)
  calc
    _ = ∑ a : α, ∑ b : α, if a = b then 0 else ∑ σ : Equiv.Perm α, f (σ i) (σ j) := by
      rw [sum_offdiagonal_const]
    _ = ∑ a : α, ∑ b : α, if a = b then 0 else ∑ σ : Equiv.Perm α, f (σ a) (σ b) := by
      simp_rw [heq]
    _ = ∑ a : α, ∑ b : α, ∑ σ : Equiv.Perm α, if a = b then 0 else f (σ a) (σ b) := by
      simp_rw [hcomm]
    _ = ∑ σ : Equiv.Perm α, ∑ a : α, ∑ b : α, if a = b then 0 else f (σ a) (σ b) := by
      calc
        _ = ∑ a : α, ∑ σ : Equiv.Perm α, ∑ b : α, if a = b then 0 else f (σ a) (σ b) := by
          apply Finset.sum_congr rfl
          intro a ha
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = _ := by simp_rw [hinvariant]; simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem sum_perm_pair {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : 2 ≤ Fintype.card α) (f : α → α → ℝ) (i j : α) (hij : i ≠ j) :
    (∑ σ : Equiv.Perm α, f (σ i) (σ j)) =
      (Fintype.card (Equiv.Perm α) : ℝ) /
        ((Fintype.card α : ℝ) * (Fintype.card α - 1)) *
          ∑ a : α, ∑ b : α, if a = b then 0 else f a b := by
  have hc : (2 : ℝ) ≤ Fintype.card α := by exact_mod_cast hcard
  have h0 : (Fintype.card α : ℝ) ≠ 0 := by linarith
  have h1 : (Fintype.card α : ℝ) - 1 ≠ 0 := by linarith
  have h := card_mul_sum_perm_pair f i j hij
  field_simp
  nlinarith only [h]

end GaussianWave.Permutation

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace GaussianWave

/-- A finite simple regular matrix graph with a chosen orthonormal family of
real eigenvectors. These fields are finite graph and spectral assumptions,
not probabilistic or asymptotic claims. -/
structure RegularEigenData (d N c : ℕ) where
  size_pos : 0 < N
  adjacency : Matrix (Fin N) (Fin N) ℝ
  eigenvalue : Fin c → ℝ
  eigenvector : Fin c → Fin N → ℝ
  neighbor : Fin N → Fin d → Fin N
  symmetric : ∀ v w, adjacency v w = adjacency w v
  diagonal_zero : ∀ v, adjacency v v = 0
  entry_zero_one : ∀ v w, adjacency v w = 0 ∨ adjacency v w = 1
  regular : ∀ v, ∑ w, adjacency v w = (d : ℝ)
  neighbor_injective : ∀ v, Function.Injective (neighbor v)
  neighbor_exact : ∀ v w, adjacency v w = 1 ↔ ∃ j, neighbor v j = w
  orthonormal : ∀ i j,
    ∑ v, eigenvector i v * eigenvector j v = if i = j then 1 else 0
  eigen_equation : ∀ i v,
    ∑ w, adjacency v w * eigenvector i w = eigenvalue i * eigenvector i v

end GaussianWave

namespace GaussianWave.RegularEigenData
variable {d N c : ℕ} (D : RegularEigenData d N c)

/-- Uniform root and uniform neighbor ordering, scaled by sqrt of vertex count. -/
def starLaw {k : ℕ} (q : Fin k → Fin N → ℝ) :
    Measure ((Fin k × Fin (d + 1)) → ℝ) := by
  classical
  let V := Fin N × Equiv.Perm (Fin d)
  let mark : V → (Fin k × Fin (d + 1)) → ℝ := fun sample aj =>
    Real.sqrt N * q aj.1
      (Fin.cases sample.1 (fun j => D.neighbor sample.1 (sample.2 j)) aj.2)
  exact (Fintype.card V : ENNReal)⁻¹ • ∑ sample : V, Measure.dirac (mark sample)

theorem starLaw_isProbability {k : ℕ} (q : Fin k → Fin N → ℝ) :
    IsProbabilityMeasure (D.starLaw q) := by
  classical
  letI : Nonempty (Fin N) := ⟨⟨0, D.size_pos⟩⟩
  have hN : N ≠ 0 := Nat.ne_of_gt D.size_pos
  constructor
  simp [starLaw, Measure.smul_apply, Finset.sum_apply]
  apply ENNReal.inv_mul_cancel
  · simp [hN, Fintype.card_ne_zero]
  · exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.natCast_ne_top _)

def starSample {k : ℕ} (q : Fin k → Fin N → ℝ)
    (sample : Fin N × Equiv.Perm (Fin d)) (aj : Fin k × Fin (d + 1)) : ℝ :=
  Real.sqrt N * q aj.1
    (Fin.cases sample.1 (fun j => D.neighbor sample.1 (sample.2 j)) aj.2)

theorem integrable_starLaw {k : ℕ} (q : Fin k → Fin N → ℝ)
    (f : ((Fin k × Fin (d + 1)) → ℝ) → ℝ) : Integrable f (D.starLaw q) := by
  classical
  let V := Fin N × Equiv.Perm (Fin d)
  have hV : (Fintype.card V : ENNReal) ≠ 0 := by
    simp [V, Nat.ne_of_gt (D.size_pos), Fintype.card_ne_zero]
  exact (integrable_finset_sum_measure.mpr (fun _ _ => integrable_dirac)).smul_measure
    (ENNReal.inv_ne_top.mpr hV)

theorem integral_starLaw {k : ℕ} (q : Fin k → Fin N → ℝ)
    (f : ((Fin k × Fin (d + 1)) → ℝ) → ℝ) :
    (∫ x, f x ∂D.starLaw q) =
      (Fintype.card (Fin N × Equiv.Perm (Fin d)) : ℝ)⁻¹ *
        ∑ sample, f (D.starSample q sample) := by
  classical
  rw [starLaw, integral_smul_measure,
    integral_finset_sum_measure (fun _ _ => integrable_dirac)]
  simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul, starSample]
  rfl

theorem integral_star_root {k : ℕ} (q : Fin k → Fin N → ℝ) (a : Fin k) :
    (∫ x, x (a, 0) ∂D.starLaw q) =
      (Real.sqrt N)⁻¹ * ∑ v, q a v := by
  classical
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (D.size_pos))
  have hP : (Fintype.card (Equiv.Perm (Fin d)) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hs : (Real.sqrt (N : ℝ)) ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg _)
  have hs0 : Real.sqrt (N : ℝ) ≠ 0 := by positivity
  rw [D.integral_starLaw]
  simp only [starSample, Fin.cases_zero, Fintype.sum_prod_type, Finset.sum_const,
    nsmul_eq_mul, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  field_simp
  linear_combination (Fintype.card (Equiv.Perm (Fin d)) : ℝ) * (∑ v, q a v) * hs

theorem integral_star_root_pair {k : ℕ} (q : Fin k → Fin N → ℝ) (a b : Fin k) :
    (∫ x, x (a, 0) * x (b, 0) ∂D.starLaw q) = ∑ v, q a v * q b v := by
  classical
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (D.size_pos))
  have hP : (Fintype.card (Equiv.Perm (Fin d)) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hs : (Real.sqrt (N : ℝ)) ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg _)
  rw [D.integral_starLaw]
  simp only [starSample, Fin.cases_zero, Fintype.sum_prod_type, Finset.sum_const,
    nsmul_eq_mul, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  have hterm (v : Fin N) : Real.sqrt N * q a v * (Real.sqrt N * q b v) =
      (N : ℝ) * (q a v * q b v) := by
    calc
      _ = (Real.sqrt (N : ℝ)) ^ 2 * (q a v * q b v) := by ring
      _ = _ := by rw [hs]
  simp_rw [hterm]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  field_simp
  ring

theorem integral_star_eigen_root_pair {k : ℕ} (a : Fin k → Fin c) (i j : Fin k) :
    (∫ x, x (i, 0) * x (j, 0) ∂D.starLaw (fun b => D.eigenvector (a b))) =
      if a i = a j then 1 else 0 := by
  rw [D.integral_star_root_pair, D.orthonormal]

theorem sum_neighbor (v : Fin N) (f : Fin N → ℝ) :
    (∑ j : Fin d, f (D.neighbor v j)) =
      ∑ w : Fin N, D.adjacency v w * f w := by
  classical
  let s := Finset.univ.image (D.neighbor v)
  have hinj : ∀ a ∈ (Finset.univ : Finset (Fin d)), ∀ b ∈ Finset.univ,
      D.neighbor v a = D.neighbor v b → a = b := by
    intro a ha b hb hab
    exact D.neighbor_injective v hab
  calc
    _ = ∑ w ∈ s, f w := (Finset.sum_image hinj).symm
    _ = ∑ w ∈ s, D.adjacency v w * f w := by
      apply Finset.sum_congr rfl
      intro w hw
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
      rw [(D.neighbor_exact v _).mpr ⟨j, rfl⟩, one_mul]
    _ = _ := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro w hw hws
      rcases D.entry_zero_one v w with hzero | hone
      · rw [hzero, zero_mul]
      · obtain ⟨j, hj⟩ := (D.neighbor_exact v w).mp hone
        exact False.elim (hws (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩))

theorem sum_neighbor_global (f : Fin N → ℝ) :
    (∑ v : Fin N, ∑ j : Fin d, f (D.neighbor v j)) =
      (d : ℝ) * ∑ w, f w := by
  simp_rw [D.sum_neighbor]
  rw [Finset.sum_comm]
  calc
    (∑ w, ∑ v, D.adjacency v w * f w) =
        ∑ w, (∑ v, D.adjacency w v) * f w := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro v hv
      rw [D.symmetric v w]
    _ = _ := by simp only [D.regular, Finset.mul_sum]

theorem eigenvector_neighbor_sum (a : Fin c) (v : Fin N) :
    (∑ j : Fin d, D.eigenvector a (D.neighbor v j)) =
      D.eigenvalue a * D.eigenvector a v := by
  rw [D.sum_neighbor]
  exact D.eigen_equation a v

theorem eigenvector_neighbor_cross (a b : Fin c) :
    (∑ v : Fin N, D.eigenvector a v *
      ∑ j : Fin d, D.eigenvector b (D.neighbor v j)) =
      D.eigenvalue b * (if a = b then 1 else 0) := by
  simp_rw [D.eigenvector_neighbor_sum]
  calc
    _ = D.eigenvalue b * ∑ v, D.eigenvector a v * D.eigenvector b v := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      ring
    _ = _ := by rw [D.orthonormal]

theorem eigenvector_neighbor_pair (a b : Fin c) :
    (∑ v : Fin N,
      (∑ j : Fin d, D.eigenvector a (D.neighbor v j)) *
      (∑ j : Fin d, D.eigenvector b (D.neighbor v j))) =
      (D.eigenvalue a * D.eigenvalue b) * (if a = b then 1 else 0) := by
  simp_rw [D.eigenvector_neighbor_sum]
  calc
    _ = (D.eigenvalue a * D.eigenvalue b) *
        ∑ v, D.eigenvector a v * D.eigenvector b v := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      ring
    _ = _ := by rw [D.orthonormal]

theorem eigenvector_neighbor_diagonal (a b : Fin c) :
    (∑ v : Fin N, ∑ j : Fin d,
      D.eigenvector a (D.neighbor v j) *
        D.eigenvector b (D.neighbor v j)) =
      (d : ℝ) * (if a = b then 1 else 0) := by
  rw [D.sum_neighbor_global (fun w => D.eigenvector a w * D.eigenvector b w),
    D.orthonormal]

theorem sum_offdiagonal_product {α : Type*} [Fintype α] [DecidableEq α] (f g : α → ℝ) :
    (∑ j : α, ∑ k : α, if j = k then 0 else f j * g k) =
      (∑ j, f j) * (∑ k, g k) - ∑ j, f j * g j := by
  have he (j : α) :
      (∑ k : α, if j = k then 0 else f j * g k) =
        f j * (∑ k, g k) - f j * g j := by
    calc
      _ = ∑ k : α, (f j * g k - (if j = k then f j * g k else 0)) := by
        apply Finset.sum_congr rfl
        intro k hk
        split_ifs <;> simp
      _ = _ := by simp [Finset.sum_sub_distrib, Finset.mul_sum]
  simp_rw [he]
  rw [Finset.sum_sub_distrib, Finset.sum_mul]

theorem eigenvector_neighbor_offdiagonal (a b : Fin c) :
    (∑ v : Fin N, ∑ j : Fin d, ∑ k : Fin d, if j = k then 0 else
      D.eigenvector a (D.neighbor v j) * D.eigenvector b (D.neighbor v k)) =
      (D.eigenvalue a * D.eigenvalue b - d) * (if a = b then 1 else 0) := by
  simp_rw [sum_offdiagonal_product]
  rw [Finset.sum_sub_distrib, D.eigenvector_neighbor_pair,
    D.eigenvector_neighbor_diagonal]
  ring

theorem sum_star_neighbor (j : Fin d) (f : Fin N → ℝ) :
    (∑ v : Fin N, ∑ σ : Equiv.Perm (Fin d), f (D.neighbor v (σ j))) =
      (Fintype.card (Equiv.Perm (Fin d)) : ℝ) * ∑ w, f w := by
  classical
  letI : Nonempty (Fin d) := ⟨j⟩
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt j.isLt)
  have he (v : Fin N) := Permutation.sum_perm_eval (fun a => f (D.neighbor v a)) j
  simp_rw [he]
  rw [← Finset.mul_sum, D.sum_neighbor_global]
  simp only [Fintype.card_fin]
  field_simp
  ring

theorem sum_star_root_neighbor (j : Fin d) (f g : Fin N → ℝ) :
    (∑ v : Fin N, ∑ σ : Equiv.Perm (Fin d), f v * g (D.neighbor v (σ j))) =
      (Fintype.card (Equiv.Perm (Fin d)) : ℝ) / d *
        ∑ v, f v * ∑ a : Fin d, g (D.neighbor v a) := by
  classical
  letI : Nonempty (Fin d) := ⟨j⟩
  have he (v : Fin N) := Permutation.sum_perm_eval (fun a => g (D.neighbor v a)) j
  simp_rw [← Finset.mul_sum, he]
  simp only [Fintype.card_fin]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  ring

theorem sum_star_distinct_neighbors (hd : 2 ≤ d) (j k : Fin d) (hjk : j ≠ k)
    (f g : Fin N → ℝ) :
    (∑ v : Fin N, ∑ σ : Equiv.Perm (Fin d),
      f (D.neighbor v (σ j)) * g (D.neighbor v (σ k))) =
      (Fintype.card (Equiv.Perm (Fin d)) : ℝ) / ((d : ℝ) * (d - 1)) *
        ∑ v, ∑ a : Fin d, ∑ b : Fin d, if a = b then 0 else
          f (D.neighbor v a) * g (D.neighbor v b) := by
  classical
  have hc : 2 ≤ Fintype.card (Fin d) := by simpa using hd
  have he (v : Fin N) := Permutation.sum_perm_pair hc
    (fun a b => f (D.neighbor v a) * g (D.neighbor v b)) j k hjk
  simp_rw [he]
  simp only [Fintype.card_fin]
  rw [Finset.mul_sum]

def starVertex (sample : Fin N × Equiv.Perm (Fin d)) (j : Fin (d + 1)) : Fin N :=
  Fin.cases sample.1 (fun k => D.neighbor sample.1 (sample.2 k)) j

theorem integral_star_coordinate_pair {k : ℕ} (q : Fin k → Fin N → ℝ)
    (a b : Fin k) (j l : Fin (d + 1)) :
    (∫ x, x (a, j) * x (b, l) ∂D.starLaw q) =
      (Fintype.card (Equiv.Perm (Fin d)) : ℝ)⁻¹ *
        ∑ v : Fin N, ∑ σ : Equiv.Perm (Fin d),
          q a (D.starVertex (v, σ) j) * q b (D.starVertex (v, σ) l) := by
  classical
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (D.size_pos))
  have hP : (Fintype.card (Equiv.Perm (Fin d)) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hs : (Real.sqrt (N : ℝ)) ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg _)
  have he (sample : Fin N × Equiv.Perm (Fin d)) :
      D.starSample q sample (a, j) * D.starSample q sample (b, l) =
        (N : ℝ) * (q a (D.starVertex sample j) * q b (D.starVertex sample l)) := by
    change (Real.sqrt N * q a (D.starVertex sample j)) *
      (Real.sqrt N * q b (D.starVertex sample l)) = _
    calc
      _ = (Real.sqrt (N : ℝ)) ^ 2 *
          (q a (D.starVertex sample j) * q b (D.starVertex sample l)) := by ring
      _ = _ := by rw [hs]
  rw [D.integral_starLaw]
  simp_rw [he]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  field_simp
  ring

theorem integral_star_eigen_root_neighbor {k : ℕ} (a : Fin k → Fin c)
    (i j : Fin k) (l : Fin d) :
    (∫ x, x (i, 0) * x (j, l.succ)
      ∂D.starLaw (fun b => D.eigenvector (a b))) =
      D.eigenvalue (a j) / d * (if a i = a j then 1 else 0) := by
  classical
  have hP : (Fintype.card (Equiv.Perm (Fin d)) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt l.isLt)
  rw [D.integral_star_coordinate_pair]
  simp only [starVertex, Fin.cases_zero, Fin.cases_succ]
  rw [D.sum_star_root_neighbor, D.eigenvector_neighbor_cross]
  field_simp
  ring_nf

theorem integral_star_eigen_same_neighbor {k : ℕ} (a : Fin k → Fin c)
    (i j : Fin k) (l : Fin d) :
    (∫ x, x (i, l.succ) * x (j, l.succ)
      ∂D.starLaw (fun b => D.eigenvector (a b))) =
      if a i = a j then 1 else 0 := by
  classical
  have hP : (Fintype.card (Equiv.Perm (Fin d)) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [D.integral_star_coordinate_pair]
  simp only [starVertex, Fin.cases_succ]
  rw [D.sum_star_neighbor l (fun v => D.eigenvector (a i) v * D.eigenvector (a j) v),
    D.orthonormal]
  field_simp

theorem integral_star_eigen_distinct_neighbor {k : ℕ} (hd : 2 ≤ d)
    (a : Fin k → Fin c) (i j : Fin k) (l m : Fin d) (hlm : l ≠ m) :
    (∫ x, x (i, l.succ) * x (j, m.succ)
      ∂D.starLaw (fun b => D.eigenvector (a b))) =
      (D.eigenvalue (a i) * D.eigenvalue (a j) - d) / ((d : ℝ) * (d - 1)) *
        (if a i = a j then 1 else 0) := by
  classical
  have hP : (Fintype.card (Equiv.Perm (Fin d)) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hd1 : (d : ℝ) - 1 ≠ 0 := by linarith
  rw [D.integral_star_coordinate_pair]
  simp only [starVertex, Fin.cases_succ]
  rw [D.sum_star_distinct_neighbors hd l m hlm, D.eigenvector_neighbor_offdiagonal]
  field_simp
  ring_nf

theorem integral_star_neighbor {k : ℕ} (q : Fin k → Fin N → ℝ)
    (a : Fin k) (j : Fin d) :
    (∫ x, x (a, j.succ) ∂D.starLaw q) =
      (Real.sqrt N)⁻¹ * ∑ v, q a v := by
  classical
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (D.size_pos))
  have hP : (Fintype.card (Equiv.Perm (Fin d)) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hs : (Real.sqrt (N : ℝ)) ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg _)
  have hs0 : Real.sqrt (N : ℝ) ≠ 0 := by positivity
  rw [D.integral_starLaw]
  simp only [starSample, Fin.cases_succ, Fintype.sum_prod_type,
    Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  simp_rw [← Finset.mul_sum]
  rw [D.sum_star_neighbor j]
  field_simp
  linear_combination (Fintype.card (Equiv.Perm (Fin d)) : ℝ) * (∑ v, q a v) * hs

theorem eigenvector_sum_zero (a : Fin c) (ha : D.eigenvalue a ≠ (d : ℝ)) :
    (∑ v, D.eigenvector a v) = 0 := by
  have hsum := D.sum_neighbor_global (D.eigenvector a)
  simp_rw [D.eigenvector_neighbor_sum] at hsum
  rw [← Finset.mul_sum] at hsum
  have hz : (D.eigenvalue a - (d : ℝ)) * ∑ v, D.eigenvector a v = 0 := by
    nlinarith [hsum]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr ha)

theorem integral_star_eigen_coordinate_zero {k : ℕ} (a : Fin k → Fin c)
    (ha : ∀ i, D.eigenvalue (a i) ≠ (d : ℝ)) (i : Fin k) (j : Fin (d + 1)) :
    (∫ x, x (i, j) ∂D.starLaw (fun b => D.eigenvector (a b))) = 0 := by
  refine Fin.cases ?_ (fun l => ?_) j
  · rw [D.integral_star_root, D.eigenvector_sum_zero (a i) (ha i), mul_zero]
  · rw [D.integral_star_neighbor, D.eigenvector_sum_zero (a i) (ha i), mul_zero]

/-- The regular-tree Gaussian-wave covariance restricted to one rooted star.
It is obtained here from exact finite spectral normalization. -/
def starWaveCovariance (degree : ℕ) (energy : ℝ) :
    Matrix (Fin (degree + 1)) (Fin (degree + 1)) ℝ :=
  fun j l => Fin.cases
    (Fin.cases 1 (fun _ => energy / degree) l)
    (fun a => Fin.cases (energy / degree)
      (fun b => if a = b then 1 else (energy ^ 2 - degree) / ((degree : ℝ) * (degree - 1))) l) j

theorem integral_star_eigen_covariance {k : ℕ} (hd : 2 ≤ d) (a : Fin k → Fin c)
    (i j : Fin k) (l m : Fin (d + 1)) :
    (∫ x, x (i, l) * x (j, m)
      ∂D.starLaw (fun b => D.eigenvector (a b))) =
      (if a i = a j then 1 else 0) * starWaveCovariance d (D.eigenvalue (a i)) l m := by
  classical
  refine Fin.cases ?_ (fun l => ?_) l
  · refine Fin.cases ?_ (fun m => ?_) m
    · rw [D.integral_star_eigen_root_pair]
      simp only [starWaveCovariance, Fin.cases_zero, mul_one]
    · rw [D.integral_star_eigen_root_neighbor]
      simp only [starWaveCovariance, Fin.cases_zero, Fin.cases_succ]
      by_cases hij : a i = a j <;> simp [hij]
  · refine Fin.cases ?_ (fun m => ?_) m
    · have heq : (fun x : (Fin k × Fin (d + 1)) → ℝ => x (i, l.succ) * x (j, 0)) =
          (fun x => x (j, 0) * x (i, l.succ)) := funext (fun x => mul_comm _ _)
      rw [heq, D.integral_star_eigen_root_neighbor]
      simp only [starWaveCovariance, Fin.cases_succ, Fin.cases_zero]
      by_cases hij : a i = a j
      · simp [hij]
      · simp [hij, Ne.symm hij]
    · by_cases hlm : l = m
      · subst m
        rw [D.integral_star_eigen_same_neighbor]
        simp only [starWaveCovariance, Fin.cases_succ, ↓reduceIte, mul_one]
      · rw [D.integral_star_eigen_distinct_neighbor hd a i j l m hlm]
        simp only [starWaveCovariance, Fin.cases_succ, hlm, ↓reduceIte]
        by_cases hij : a i = a j
        · simp only [hij, ↓reduceIte, one_mul, mul_one, pow_two]
        · simp only [hij, ↓reduceIte, zero_mul, mul_zero]

/-- Distinct orthonormal channels have exactly zero empirical cross-covariance,
and each channel has the explicit star covariance at its own eigenvalue. -/
theorem integral_star_orthonormal_eigen_covariance {k : ℕ} (hd : 2 ≤ d)
    (a : Fin k → Fin c) (ha : Function.Injective a)
    (i j : Fin k) (l m : Fin (d + 1)) :
    (∫ x, x (i, l) * x (j, m)
      ∂D.starLaw (fun b => D.eigenvector (a b))) =
      (if i = j then 1 else 0) * starWaveCovariance d (D.eigenvalue (a i)) l m := by
  simpa only [ha.eq_iff] using D.integral_star_eigen_covariance hd a i j l m

end GaussianWave.RegularEigenData

namespace GaussianWave

/-- Covariance at tree distance `r` of a variance-one Gaussian wave.
The definition is algebraic; no existence of a random process is assumed. -/
def sphericalCovariance (d : ℕ) (energy : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => energy / d
  | n + 2 =>
      (energy * sphericalCovariance d energy (n + 1) - sphericalCovariance d energy n) /
        ((d : ℝ) - 1)

@[simp] theorem sphericalCovariance_zero (d : ℕ) (energy : ℝ) :
    sphericalCovariance d energy 0 = 1 := rfl

@[simp] theorem sphericalCovariance_one (d : ℕ) (energy : ℝ) :
    sphericalCovariance d energy 1 = energy / d := rfl

theorem sphericalCovariance_recurrence (d : ℕ) (energy : ℝ)
    (hd : (d : ℝ) - 1 ≠ 0) (n : ℕ) :
    sphericalCovariance d energy n +
      ((d : ℝ) - 1) * sphericalCovariance d energy (n + 2) =
        energy * sphericalCovariance d energy (n + 1) := by
  rw [sphericalCovariance, mul_div_cancel₀ _ hd]
  ring

theorem sphericalCovariance_two (d : ℕ) (energy : ℝ) (hd : (d : ℝ) ≠ 0) :
    sphericalCovariance d energy 2 =
      (energy ^ 2 - d) / ((d : ℝ) * ((d : ℝ) - 1)) := by
  simp only [sphericalCovariance]
  field_simp
  ring

/-- Initial root covariance and the eigenvalue covariance recurrence determine
all radial covariances, including zero cross-channel covariance. -/
theorem covariance_eq_scaled_spherical (d : ℕ) (energy scale : ℝ)
    (hd0 : (d : ℝ) ≠ 0) (hd1 : (d : ℝ) - 1 ≠ 0)
    (c : ℕ → ℝ) (hzero : c 0 = scale)
    (hone : (d : ℝ) * c 1 = energy * c 0)
    (hrec : ∀ n, c n + ((d : ℝ) - 1) * c (n + 2) = energy * c (n + 1)) :
    ∀ n, c n = scale * sphericalCovariance d energy n := by
  apply Nat.twoStepInduction
  · simpa using hzero
  · simp only [sphericalCovariance_one]
    rw [← mul_div_assoc]
    apply (eq_div_iff hd0).2
    have hone' := hone
    rw [hzero] at hone'
    convert hone' using 1 <;> ring
  · intro n hn hn1
    rw [sphericalCovariance]
    rw [← mul_div_assoc]
    apply (eq_div_iff hd1).2
    have h := hrec n
    rw [hn, hn1] at h
    nlinarith

/-- Every fixed-distance covariance is continuous in the energy. -/
theorem continuous_sphericalCovariance (d r : ℕ) :
    Continuous (fun energy : ℝ => sphericalCovariance d energy r) := by
  induction r using Nat.twoStepInduction with
  | zero => simpa only [sphericalCovariance_zero] using
      (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ)))
  | one => simpa only [sphericalCovariance_one] using
      (continuous_id.div_const (d : ℝ))
  | more n hn hn1 =>
      simpa only [sphericalCovariance] using
        ((continuous_id.mul hn1).sub hn).div_const ((d : ℝ) - 1)

/-- A fixed finite distance array determines a covariance matrix continuously
in the energy. Positive semidefiniteness is a separate Gaussian-existence fact. -/
def windowCovariance {ι : Type*} (d : ℕ) (distance : ι → ι → ℕ) (energy : ℝ) :
    Matrix ι ι ℝ := fun i j => sphericalCovariance d energy (distance i j)

theorem continuous_windowCovariance {ι : Type*} (d : ℕ) (distance : ι → ι → ℕ)
    (i j : ι) : Continuous (fun energy : ℝ => windowCovariance d distance energy i j) :=
  continuous_sphericalCovariance d (distance i j)

end GaussianWave

namespace GaussianWave.RegularEigenData

theorem continuous_starWaveCovariance (degree : ℕ) (j l : Fin (degree + 1)) :
    Continuous (fun energy : ℝ => starWaveCovariance degree energy j l) := by
  refine Fin.cases ?_ (fun j => ?_) j
  · refine Fin.cases ?_ (fun l => ?_) l
    · exact continuous_const
    · exact continuous_id.div_const _
  · refine Fin.cases ?_ (fun l => ?_) l
    · exact continuous_id.div_const _
    · by_cases h : j = l
      · simp only [starWaveCovariance, Fin.cases_succ, h, ↓reduceIte]
        exact continuous_const
      · simp only [starWaveCovariance, Fin.cases_succ, h, ↓reduceIte]
        exact ((continuous_id.pow 2).sub continuous_const).div_const _

/-- Tree distance restricted to a root (index zero) and its ordered neighbors. -/
def starDistance (d : ℕ) : Fin (d + 1) → Fin (d + 1) → ℕ :=
  fun i j => Fin.cases
    (Fin.cases 0 (fun _ => 1) j)
    (fun a => Fin.cases 1 (fun b => if a = b then 0 else 2) j) i

theorem starWaveCovariance_eq_spherical (d : ℕ) (energy : ℝ)
    (hd : (d : ℝ) ≠ 0) (i j : Fin (d + 1)) :
    starWaveCovariance d energy i j =
      sphericalCovariance d energy (starDistance d i j) := by
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j <;>
      simp [starWaveCovariance, starDistance]
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp [starWaveCovariance, starDistance]
    · by_cases hij : i = j
      · simp [starWaveCovariance, starDistance, hij]
      · simpa [starWaveCovariance, starDistance, hij] using
          (sphericalCovariance_two d energy hd).symm

/-- Exact finite-star moments in the same radial form as a tree wave. -/
theorem integral_star_radial_covariance {d N c k : ℕ}
    (D : RegularEigenData d N c) (hd : 2 ≤ d)
    (a : Fin k → Fin c) (ha : Function.Injective a)
    (i j : Fin k) (l m : Fin (d + 1)) :
    (∫ x, x (i, l) * x (j, m) ∂D.starLaw (fun b => D.eigenvector (a b))) =
      (if i = j then 1 else 0) *
        sphericalCovariance d (D.eigenvalue (a i)) (starDistance d l m) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  rw [D.integral_star_orthonormal_eigen_covariance hd a ha,
    starWaveCovariance_eq_spherical d _ hd0]

end GaussianWave.RegularEigenData

namespace GaussianWave.RegularEigenData
variable {d N c : ℕ} (D : RegularEigenData d N c)

/-- The root fourth moment is the scalar empirical fourth moment, with the
normalization N sum u(v)^4 used in the research note. -/
theorem integral_star_root_fourth {k : ℕ} (q : Fin k → Fin N → ℝ) (a : Fin k) :
    (∫ x, x (a, 0) ^ 4 ∂D.starLaw q) = (N : ℝ) * ∑ v, q a v ^ 4 := by
  classical
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt D.size_pos)
  have hP : (Fintype.card (Equiv.Perm (Fin d)) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hs : Real.sqrt (N : ℝ) ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg _)
  have hs4 : Real.sqrt (N : ℝ) ^ 4 = (N : ℝ) ^ 2 := by
    calc
      _ = (Real.sqrt (N : ℝ) ^ 2) ^ 2 := by ring
      _ = _ := by rw [hs]
  rw [D.integral_starLaw]
  simp only [starSample, Fin.cases_zero, mul_pow, hs4, Fintype.sum_prod_type,
    Finset.sum_const, nsmul_eq_mul, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  field_simp
  ring

/-- Every fixed physical star position has exactly the same scalar fourth
moment, including a neighbor position on graphs with short cycles. -/
theorem integral_star_neighbor_fourth {k : ℕ} (q : Fin k → Fin N → ℝ)
    (a : Fin k) (j : Fin d) :
    (∫ x, x (a, j.succ) ^ 4 ∂D.starLaw q) = (N : ℝ) * ∑ v, q a v ^ 4 := by
  classical
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt D.size_pos)
  have hP : (Fintype.card (Equiv.Perm (Fin d)) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hs : Real.sqrt (N : ℝ) ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg _)
  have hs4 : Real.sqrt (N : ℝ) ^ 4 = (N : ℝ) ^ 2 := by
    calc
      _ = (Real.sqrt (N : ℝ) ^ 2) ^ 2 := by ring
      _ = _ := by rw [hs]
  rw [D.integral_starLaw]
  simp only [starSample, Fin.cases_succ, mul_pow, hs4, Fintype.sum_prod_type,
    Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  simp_rw [← Finset.mul_sum]
  rw [D.sum_star_neighbor j (fun v => q a v ^ 4)]
  field_simp
  ring

theorem integral_star_coordinate_fourth {k : ℕ} (q : Fin k → Fin N → ℝ)
    (a : Fin k) (j : Fin (d + 1)) :
    (∫ x, x (a, j) ^ 4 ∂D.starLaw q) = (N : ℝ) * ∑ v, q a v ^ 4 := by
  refine Fin.cases ?_ (fun j => ?_) j
  · exact D.integral_star_root_fourth q a
  · exact D.integral_star_neighbor_fourth q a j

end GaussianWave.RegularEigenData
