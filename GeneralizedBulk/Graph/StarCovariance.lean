import GeneralizedBulk.ExternalInputs
import GeneralizedBulk.Graph.PermutationAverages

/-!
# Exact empirical star normalization from finite regular spectral data

The identities here are finite sums. They use the literal neighbor enumeration,
regularity, symmetry, and orthonormal eigenchannels; no BS or HY consequence is
used to normalize the Gaussian limits.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace GeneralizedBulk.External.RegularSpectralData

variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

def starSample {k : ℕ} (q : Fin k → Fin (N n) → ℝ)
    (sample : Fin (N n) × Equiv.Perm (Fin d)) (aj : Fin k × Fin (d + 1)) : ℝ :=
  Real.sqrt (N n) * q aj.1
    (Fin.cases sample.1 (fun j => D.neighbor n ω sample.1 (sample.2 j)) aj.2)

theorem integrable_starLaw {k : ℕ} (q : Fin k → Fin (N n) → ℝ)
    (f : ((Fin k × Fin (d + 1)) → ℝ) → ℝ) : Integrable f (D.starLaw n ω q) := by
  classical
  let V := Fin (N n) × Equiv.Perm (Fin d)
  have hV : (Fintype.card V : ENNReal) ≠ 0 := by
    simp [V, Nat.ne_of_gt (D.size_pos n), Fintype.card_ne_zero]
  exact (integrable_finset_sum_measure.mpr (fun _ _ => integrable_dirac)).smul_measure
    (ENNReal.inv_ne_top.mpr hV)

theorem integral_starLaw {k : ℕ} (q : Fin k → Fin (N n) → ℝ)
    (f : ((Fin k × Fin (d + 1)) → ℝ) → ℝ) :
    (∫ x, f x ∂D.starLaw n ω q) =
      (Fintype.card (Fin (N n) × Equiv.Perm (Fin d)) : ℝ)⁻¹ *
        ∑ sample, f (D.starSample n ω q sample) := by
  classical
  rw [starLaw, integral_smul_measure,
    integral_finset_sum_measure (fun _ _ => integrable_dirac)]
  simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul, starSample]
  rfl

theorem integral_star_root {k : ℕ} (q : Fin k → Fin (N n) → ℝ) (a : Fin k) :
    (∫ x, x (a, 0) ∂D.starLaw n ω q) =
      (Real.sqrt (N n))⁻¹ * ∑ v, q a v := by
  classical
  have hN : (N n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (D.size_pos n))
  have hP : (Fintype.card (Equiv.Perm (Fin d)) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hs : (Real.sqrt (N n : ℝ)) ^ 2 = N n := Real.sq_sqrt (Nat.cast_nonneg _)
  have hs0 : Real.sqrt (N n : ℝ) ≠ 0 := by positivity
  rw [D.integral_starLaw n ω]
  simp only [starSample, Fin.cases_zero, Fintype.sum_prod_type, Finset.sum_const,
    nsmul_eq_mul, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  field_simp
  linear_combination (Fintype.card (Equiv.Perm (Fin d)) : ℝ) * (∑ v, q a v) * hs

theorem integral_star_root_pair {k : ℕ} (q : Fin k → Fin (N n) → ℝ) (a b : Fin k) :
    (∫ x, x (a, 0) * x (b, 0) ∂D.starLaw n ω q) = ∑ v, q a v * q b v := by
  classical
  have hN : (N n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (D.size_pos n))
  have hP : (Fintype.card (Equiv.Perm (Fin d)) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hs : (Real.sqrt (N n : ℝ)) ^ 2 = N n := Real.sq_sqrt (Nat.cast_nonneg _)
  rw [D.integral_starLaw n ω]
  simp only [starSample, Fin.cases_zero, Fintype.sum_prod_type, Finset.sum_const,
    nsmul_eq_mul, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  have hterm (v : Fin (N n)) : Real.sqrt (N n) * q a v * (Real.sqrt (N n) * q b v) =
      (N n : ℝ) * (q a v * q b v) := by
    calc
      _ = (Real.sqrt (N n : ℝ)) ^ 2 * (q a v * q b v) := by ring
      _ = _ := by rw [hs]
  simp_rw [hterm]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  field_simp
  ring

theorem integral_star_eigen_root_pair {k : ℕ} (a : Fin k → Fin (N n)) (i j : Fin k) :
    (∫ x, x (i, 0) * x (j, 0) ∂D.starLaw n ω (fun b => D.eigenvector n ω (a b))) =
      if a i = a j then 1 else 0 := by
  rw [D.integral_star_root_pair n ω, D.orthonormal]

theorem sum_neighbor (v : Fin (N n)) (f : Fin (N n) → ℝ) :
    (∑ j : Fin d, f (D.neighbor n ω v j)) =
      ∑ w : Fin (N n), D.adjacency n ω v w * f w := by
  classical
  let s := Finset.univ.image (D.neighbor n ω v)
  have hinj : ∀ a ∈ (Finset.univ : Finset (Fin d)), ∀ b ∈ Finset.univ,
      D.neighbor n ω v a = D.neighbor n ω v b → a = b := by
    intro a ha b hb hab
    exact D.neighbor_injective n ω v hab
  calc
    _ = ∑ w ∈ s, f w := (Finset.sum_image hinj).symm
    _ = ∑ w ∈ s, D.adjacency n ω v w * f w := by
      apply Finset.sum_congr rfl
      intro w hw
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
      rw [(D.neighbor_exact n ω v _).mpr ⟨j, rfl⟩, one_mul]
    _ = _ := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro w hw hws
      rcases D.entry_zero_one n ω v w with hzero | hone
      · rw [hzero, zero_mul]
      · obtain ⟨j, hj⟩ := (D.neighbor_exact n ω v w).mp hone
        exact False.elim (hws (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩))

theorem sum_neighbor_global (f : Fin (N n) → ℝ) :
    (∑ v : Fin (N n), ∑ j : Fin d, f (D.neighbor n ω v j)) =
      (d : ℝ) * ∑ w, f w := by
  simp_rw [D.sum_neighbor n ω]
  rw [Finset.sum_comm]
  calc
    (∑ w, ∑ v, D.adjacency n ω v w * f w) =
        ∑ w, (∑ v, D.adjacency n ω w v) * f w := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro v hv
      rw [D.symmetric n ω v w]
    _ = _ := by simp only [D.regular, Finset.mul_sum]

theorem eigenvector_neighbor_sum (a : Fin (N n)) (v : Fin (N n)) :
    (∑ j : Fin d, D.eigenvector n ω a (D.neighbor n ω v j)) =
      D.eigenvalue n ω a * D.eigenvector n ω a v := by
  rw [D.sum_neighbor n ω]
  exact D.eigen_equation n ω a v

theorem eigenvector_neighbor_cross (a b : Fin (N n)) :
    (∑ v : Fin (N n), D.eigenvector n ω a v *
      ∑ j : Fin d, D.eigenvector n ω b (D.neighbor n ω v j)) =
      D.eigenvalue n ω b * (if a = b then 1 else 0) := by
  simp_rw [D.eigenvector_neighbor_sum n ω]
  calc
    _ = D.eigenvalue n ω b * ∑ v, D.eigenvector n ω a v * D.eigenvector n ω b v := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      ring
    _ = _ := by rw [D.orthonormal]

theorem eigenvector_neighbor_pair (a b : Fin (N n)) :
    (∑ v : Fin (N n),
      (∑ j : Fin d, D.eigenvector n ω a (D.neighbor n ω v j)) *
      (∑ j : Fin d, D.eigenvector n ω b (D.neighbor n ω v j))) =
      (D.eigenvalue n ω a * D.eigenvalue n ω b) * (if a = b then 1 else 0) := by
  simp_rw [D.eigenvector_neighbor_sum n ω]
  calc
    _ = (D.eigenvalue n ω a * D.eigenvalue n ω b) *
        ∑ v, D.eigenvector n ω a v * D.eigenvector n ω b v := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      ring
    _ = _ := by rw [D.orthonormal]

theorem eigenvector_neighbor_diagonal (a b : Fin (N n)) :
    (∑ v : Fin (N n), ∑ j : Fin d,
      D.eigenvector n ω a (D.neighbor n ω v j) *
        D.eigenvector n ω b (D.neighbor n ω v j)) =
      (d : ℝ) * (if a = b then 1 else 0) := by
  rw [D.sum_neighbor_global n ω (fun w => D.eigenvector n ω a w * D.eigenvector n ω b w),
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

theorem eigenvector_neighbor_offdiagonal (a b : Fin (N n)) :
    (∑ v : Fin (N n), ∑ j : Fin d, ∑ k : Fin d, if j = k then 0 else
      D.eigenvector n ω a (D.neighbor n ω v j) * D.eigenvector n ω b (D.neighbor n ω v k)) =
      (D.eigenvalue n ω a * D.eigenvalue n ω b - d) * (if a = b then 1 else 0) := by
  simp_rw [sum_offdiagonal_product]
  rw [Finset.sum_sub_distrib, D.eigenvector_neighbor_pair n ω,
    D.eigenvector_neighbor_diagonal n ω]
  ring

theorem sum_star_neighbor (j : Fin d) (f : Fin (N n) → ℝ) :
    (∑ v : Fin (N n), ∑ σ : Equiv.Perm (Fin d), f (D.neighbor n ω v (σ j))) =
      (Fintype.card (Equiv.Perm (Fin d)) : ℝ) * ∑ w, f w := by
  classical
  letI : Nonempty (Fin d) := ⟨j⟩
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt j.isLt)
  have he (v : Fin (N n)) := Graph.sum_perm_eval (fun a => f (D.neighbor n ω v a)) j
  simp_rw [he]
  rw [← Finset.mul_sum, D.sum_neighbor_global n ω]
  simp only [Fintype.card_fin]
  field_simp
  ring

theorem sum_star_root_neighbor (j : Fin d) (f g : Fin (N n) → ℝ) :
    (∑ v : Fin (N n), ∑ σ : Equiv.Perm (Fin d), f v * g (D.neighbor n ω v (σ j))) =
      (Fintype.card (Equiv.Perm (Fin d)) : ℝ) / d *
        ∑ v, f v * ∑ a : Fin d, g (D.neighbor n ω v a) := by
  classical
  letI : Nonempty (Fin d) := ⟨j⟩
  have he (v : Fin (N n)) := Graph.sum_perm_eval (fun a => g (D.neighbor n ω v a)) j
  simp_rw [← Finset.mul_sum, he]
  simp only [Fintype.card_fin]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  ring

theorem sum_star_distinct_neighbors (hd : 2 ≤ d) (j k : Fin d) (hjk : j ≠ k)
    (f g : Fin (N n) → ℝ) :
    (∑ v : Fin (N n), ∑ σ : Equiv.Perm (Fin d),
      f (D.neighbor n ω v (σ j)) * g (D.neighbor n ω v (σ k))) =
      (Fintype.card (Equiv.Perm (Fin d)) : ℝ) / ((d : ℝ) * (d - 1)) *
        ∑ v, ∑ a : Fin d, ∑ b : Fin d, if a = b then 0 else
          f (D.neighbor n ω v a) * g (D.neighbor n ω v b) := by
  classical
  have hc : 2 ≤ Fintype.card (Fin d) := by simpa using hd
  have he (v : Fin (N n)) := Graph.sum_perm_pair hc
    (fun a b => f (D.neighbor n ω v a) * g (D.neighbor n ω v b)) j k hjk
  simp_rw [he]
  simp only [Fintype.card_fin]
  rw [Finset.mul_sum]

def starVertex (sample : Fin (N n) × Equiv.Perm (Fin d)) (j : Fin (d + 1)) : Fin (N n) :=
  Fin.cases sample.1 (fun k => D.neighbor n ω sample.1 (sample.2 k)) j

theorem integral_star_coordinate_pair {k : ℕ} (q : Fin k → Fin (N n) → ℝ)
    (a b : Fin k) (j l : Fin (d + 1)) :
    (∫ x, x (a, j) * x (b, l) ∂D.starLaw n ω q) =
      (Fintype.card (Equiv.Perm (Fin d)) : ℝ)⁻¹ *
        ∑ v : Fin (N n), ∑ σ : Equiv.Perm (Fin d),
          q a (D.starVertex n ω (v, σ) j) * q b (D.starVertex n ω (v, σ) l) := by
  classical
  have hN : (N n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (D.size_pos n))
  have hP : (Fintype.card (Equiv.Perm (Fin d)) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hs : (Real.sqrt (N n : ℝ)) ^ 2 = N n := Real.sq_sqrt (Nat.cast_nonneg _)
  have he (sample : Fin (N n) × Equiv.Perm (Fin d)) :
      D.starSample n ω q sample (a, j) * D.starSample n ω q sample (b, l) =
        (N n : ℝ) * (q a (D.starVertex n ω sample j) * q b (D.starVertex n ω sample l)) := by
    change (Real.sqrt (N n) * q a (D.starVertex n ω sample j)) *
      (Real.sqrt (N n) * q b (D.starVertex n ω sample l)) = _
    calc
      _ = (Real.sqrt (N n : ℝ)) ^ 2 *
          (q a (D.starVertex n ω sample j) * q b (D.starVertex n ω sample l)) := by ring
      _ = _ := by rw [hs]
  rw [D.integral_starLaw n ω]
  simp_rw [he]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  field_simp
  ring

theorem integral_star_eigen_root_neighbor {k : ℕ} (a : Fin k → Fin (N n))
    (i j : Fin k) (l : Fin d) :
    (∫ x, x (i, 0) * x (j, l.succ)
      ∂D.starLaw n ω (fun b => D.eigenvector n ω (a b))) =
      D.eigenvalue n ω (a j) / d * (if a i = a j then 1 else 0) := by
  classical
  have hP : (Fintype.card (Equiv.Perm (Fin d)) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt l.isLt)
  rw [D.integral_star_coordinate_pair n ω]
  simp only [starVertex, Fin.cases_zero, Fin.cases_succ]
  rw [D.sum_star_root_neighbor n ω, D.eigenvector_neighbor_cross n ω]
  field_simp
  ring

theorem integral_star_eigen_same_neighbor {k : ℕ} (a : Fin k → Fin (N n))
    (i j : Fin k) (l : Fin d) :
    (∫ x, x (i, l.succ) * x (j, l.succ)
      ∂D.starLaw n ω (fun b => D.eigenvector n ω (a b))) =
      if a i = a j then 1 else 0 := by
  classical
  have hP : (Fintype.card (Equiv.Perm (Fin d)) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [D.integral_star_coordinate_pair n ω]
  simp only [starVertex, Fin.cases_succ]
  rw [D.sum_star_neighbor n ω l (fun v => D.eigenvector n ω (a i) v * D.eigenvector n ω (a j) v),
    D.orthonormal]
  field_simp

theorem integral_star_eigen_distinct_neighbor {k : ℕ} (hd : 2 ≤ d)
    (a : Fin k → Fin (N n)) (i j : Fin k) (l m : Fin d) (hlm : l ≠ m) :
    (∫ x, x (i, l.succ) * x (j, m.succ)
      ∂D.starLaw n ω (fun b => D.eigenvector n ω (a b))) =
      (D.eigenvalue n ω (a i) * D.eigenvalue n ω (a j) - d) / ((d : ℝ) * (d - 1)) *
        (if a i = a j then 1 else 0) := by
  classical
  have hP : (Fintype.card (Equiv.Perm (Fin d)) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hd1 : (d : ℝ) - 1 ≠ 0 := by linarith
  rw [D.integral_star_coordinate_pair n ω]
  simp only [starVertex, Fin.cases_succ]
  rw [D.sum_star_distinct_neighbors n ω hd l m hlm, D.eigenvector_neighbor_offdiagonal n ω]
  field_simp
  ring

theorem integral_star_neighbor {k : ℕ} (q : Fin k → Fin (N n) → ℝ)
    (a : Fin k) (j : Fin d) :
    (∫ x, x (a, j.succ) ∂D.starLaw n ω q) =
      (Real.sqrt (N n))⁻¹ * ∑ v, q a v := by
  classical
  have hN : (N n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (D.size_pos n))
  have hP : (Fintype.card (Equiv.Perm (Fin d)) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hs : (Real.sqrt (N n : ℝ)) ^ 2 = N n := Real.sq_sqrt (Nat.cast_nonneg _)
  have hs0 : Real.sqrt (N n : ℝ) ≠ 0 := by positivity
  rw [D.integral_starLaw n ω]
  simp only [starSample, Fin.cases_succ, Fintype.sum_prod_type,
    Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  simp_rw [← Finset.mul_sum]
  rw [D.sum_star_neighbor n ω j]
  field_simp
  linear_combination (Fintype.card (Equiv.Perm (Fin d)) : ℝ) * (∑ v, q a v) * hs

theorem eigenvector_sum_zero (a : Fin (N n)) (ha : a ≠ ⟨0, D.size_pos n⟩) :
    (∑ v, D.eigenvector n ω a v) = 0 := by
  have hN : (0 : ℝ) < N n := by exact_mod_cast D.size_pos n
  have hs : Real.sqrt (N n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hN).ne'
  have ho := D.orthonormal n ω a ⟨0, D.size_pos n⟩
  simp only [ha, ↓reduceIte] at ho
  simp_rw [D.constant_eigenvector n ω] at ho
  rw [← Finset.sum_mul] at ho
  exact (mul_eq_zero.mp ho).resolve_right (inv_ne_zero hs)

theorem integral_star_eigen_coordinate_zero {k : ℕ} (a : Fin k → Fin (N n))
    (ha : ∀ i, a i ≠ ⟨0, D.size_pos n⟩) (i : Fin k) (j : Fin (d + 1)) :
    (∫ x, x (i, j) ∂D.starLaw n ω (fun b => D.eigenvector n ω (a b))) = 0 := by
  refine Fin.cases ?_ (fun l => ?_) j
  · rw [D.integral_star_root n ω, D.eigenvector_sum_zero n ω (a i) (ha i), mul_zero]
  · rw [D.integral_star_neighbor n ω, D.eigenvector_sum_zero n ω (a i) (ha i), mul_zero]

/-- The regular-tree Gaussian-wave covariance restricted to one rooted star.
It is obtained here from exact finite spectral normalization. -/
def starWaveCovariance (degree : ℕ) (energy : ℝ) :
    Matrix (Fin (degree + 1)) (Fin (degree + 1)) ℝ :=
  fun j l => Fin.cases
    (Fin.cases 1 (fun _ => energy / degree) l)
    (fun a => Fin.cases (energy / degree)
      (fun b => if a = b then 1 else (energy ^ 2 - degree) / ((degree : ℝ) * (degree - 1))) l) j

theorem integral_star_eigen_covariance {k : ℕ} (hd : 2 ≤ d) (a : Fin k → Fin (N n))
    (i j : Fin k) (l m : Fin (d + 1)) :
    (∫ x, x (i, l) * x (j, m)
      ∂D.starLaw n ω (fun b => D.eigenvector n ω (a b))) =
      (if a i = a j then 1 else 0) * starWaveCovariance d (D.eigenvalue n ω (a i)) l m := by
  classical
  refine Fin.cases ?_ (fun l => ?_) l
  · refine Fin.cases ?_ (fun m => ?_) m
    · rw [D.integral_star_eigen_root_pair n ω]
      simp only [starWaveCovariance, Fin.cases_zero, mul_one]
    · rw [D.integral_star_eigen_root_neighbor n ω]
      simp only [starWaveCovariance, Fin.cases_zero, Fin.cases_succ]
      by_cases hij : a i = a j <;> simp [hij]
  · refine Fin.cases ?_ (fun m => ?_) m
    · have heq : (fun x : (Fin k × Fin (d + 1)) → ℝ => x (i, l.succ) * x (j, 0)) =
          (fun x => x (j, 0) * x (i, l.succ)) := funext (fun x => mul_comm _ _)
      rw [heq, D.integral_star_eigen_root_neighbor n ω]
      simp only [starWaveCovariance, Fin.cases_succ, Fin.cases_zero]
      by_cases hij : a i = a j
      · simp [hij]
      · simp [hij, Ne.symm hij]
    · by_cases hlm : l = m
      · subst m
        rw [D.integral_star_eigen_same_neighbor n ω]
        simp only [starWaveCovariance, Fin.cases_succ, ↓reduceIte, mul_one]
      · rw [D.integral_star_eigen_distinct_neighbor n ω hd a i j l m hlm]
        simp only [starWaveCovariance, Fin.cases_succ, hlm, ↓reduceIte]
        by_cases hij : a i = a j
        · simp only [hij, ↓reduceIte, one_mul, mul_one, pow_two]
        · simp only [hij, ↓reduceIte, zero_mul, mul_zero]

/-- Distinct orthonormal channels have exactly zero empirical cross-covariance,
and each channel has the explicit star covariance at its own eigenvalue. -/
theorem integral_star_orthonormal_eigen_covariance {k : ℕ} (hd : 2 ≤ d)
    (a : Fin k → Fin (N n)) (ha : Function.Injective a)
    (i j : Fin k) (l m : Fin (d + 1)) :
    (∫ x, x (i, l) * x (j, m)
      ∂D.starLaw n ω (fun b => D.eigenvector n ω (a b))) =
      (if i = j then 1 else 0) * starWaveCovariance d (D.eigenvalue n ω (a i)) l m := by
  simpa only [ha.eq_iff] using D.integral_star_eigen_covariance n ω hd a i j l m

end GeneralizedBulk.External.RegularSpectralData
