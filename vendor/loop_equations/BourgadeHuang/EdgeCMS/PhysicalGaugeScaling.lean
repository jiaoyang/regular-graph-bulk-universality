import BourgadeHuang.EdgeCMS.PhysicalGauge
import BourgadeHuang.EdgeCMS.AiryPullback
import BourgadeHuang.CMS.GeneralBranchDegree

/-! Exact scaling of the physical edge WKB factor. For balanced physical
charges the logarithmic prefactor has degree zero, proved from the charges. -/
noncomputable section
open scoped BigOperators Topology
namespace BourgadeHuang.EdgeCMS
open CMS

theorem twice_upper_charge_products {d : ℕ} (c : Fin d → ℂ) :
    2 * (∑ p ∈ upperPairs d, c p.1 * c p.2) =
      (∑ i, c i) ^ 2 - ∑ i, c i ^ 2 := by
  classical
  let f : Fin d → Fin d → ℂ := fun i j => if i = j then 0 else c i * c j
  have hs : ∀ i j, f i j = f j i := by
    intro i j
    by_cases h : i = j
    · subst j; rfl
    · simp [f, h, Ne.symm h, mul_comm]
  have ht := twice_sum_upperPairs hs (fun i => by simp [f])
  have hp : (∑ p ∈ upperPairs d, f p.1 p.2) =
      ∑ p ∈ upperPairs d, c p.1 * c p.2 := by
    apply Finset.sum_congr rfl
    intro p hp
    simp [f, (Finset.mem_filter.mp hp).2.ne]
  rw [hp] at ht
  have hf (i j : Fin d) : f i j =
      c i * c j - (if j = i then c i ^ 2 else 0) := by
    by_cases h : j = i
    · subst j; simp [f, pow_two]
    · simp [f, h, Ne.symm h]
  rw [ht]
  simp_rw [hf, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  congr 1
  exact Finset.sum_comm

theorem sum_physical_charge_sq {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (hc : ∀ i, c i = -1 ∨ c i = β / 2) (hb : ∑ i, c i = 0) :
    (∑ i, c i ^ 2) = β * (d : ℂ) / 2 := by
  have hi (i : Fin d) : c i ^ 2 = (β / 2 - 1) * c i + β / 2 := by
    rcases hc i with h | h <;> rw [h] <;> ring
  simp_rw [hi]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hb]
  simp
  ring

theorem sum_rootPairExponent_balanced {d : ℕ} (β : ℂ) (hβ : β ≠ 0)
    (c : Fin d → ℂ) (hc : ∀ i, c i = -1 ∨ c i = β / 2)
    (hb : ∑ i, c i = 0) :
    (∑ p ∈ upperPairs d, rootPairExponent β c p.1 p.2) = (d : ℂ) / 2 := by
  have hs := twice_upper_charge_products c
  rw [hb, sum_physical_charge_sq β c hc hb, zero_pow (by norm_num), zero_sub] at hs
  simp only [rootPairExponent, mul_assoc, ← Finset.mul_sum]
  calc
    -(2 / β) * (∑ p ∈ upperPairs d, c p.1 * c p.2) =
        -(2 * (∑ p ∈ upperPairs d, c p.1 * c p.2)) / β := by ring
    _ = -(-(β * (d : ℂ) / 2)) / β := by rw [hs]
    _ = _ := by field_simp; ring

def physicalPhase {d : ℕ} (c : Fin d → ℂ) (z : Point d) : ℂ :=
  ∑ i, c i * airyCoordinate (z i)

def physicalPrefactorLog {d : ℕ} (β : ℂ) (c : Fin d → ℂ) (z : Point d) : ℂ :=
  physicalGaugeLog β c z - physicalPhase c z

def physicalPrefactor {d : ℕ} (β : ℂ) (c : Fin d → ℂ) (z : Point d) : ℂ :=
  Complex.exp (physicalPrefactorLog β c z)

theorem physicalPrefactorLog_eq {d : ℕ} (β : ℂ) (c : Fin d → ℂ) (z : Point d) :
    physicalPrefactorLog β c z =
      -(∑ i, Complex.log (z i) / 4) +
        ∑ p ∈ upperPairs d,
          rootPairExponent β c p.1 p.2 * Complex.log (root (z p.1) + root (z p.2)) := by
  unfold physicalPrefactorLog physicalGaugeLog physicalPhase scalarWKBLog airyCoordinate
  rw [Finset.sum_sub_distrib]
  have he : (∑ i, (2 / 3 : ℂ) * c i * z i * root (z i)) =
      ∑ i, c i * ((2 / 3 : ℂ) * z i * root (z i)) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  ring

theorem physicalGauge_factorization {d : ℕ} (β : ℂ) (c : Fin d → ℂ) (z : Point d) :
    physicalGauge β c z = Complex.exp (physicalPhase c z) * physicalPrefactor β c z := by
  unfold physicalGauge physicalPrefactor physicalPrefactorLog
  rw [← Complex.exp_add]
  congr 1
  ring

theorem physicalPhase_scale {d : ℕ} (c : Fin d → ℂ) {z : Point d}
    (hz : ∀ i, z i ≠ 0) {u : ℝ} (hu : 0 < u) :
    physicalPhase c (fun i => (u : ℂ) ^ 2 * z i) = (u : ℂ) ^ 3 * physicalPhase c z := by
  unfold physicalPhase
  simp only [airyCoordinate_ofReal_sq_mul hu (hz _), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem physicalPrefactorLog_scale {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    {z : Point d} (hz : z ∈ PhysicalRootDomain d) {u : ℝ} (hu : 0 < u)
    (hc : (∑ p ∈ upperPairs d, rootPairExponent β c p.1 p.2) = (d : ℂ) / 2) :
    physicalPrefactorLog β c (fun i => (u : ℂ) ^ 2 * z i) =
      physicalPrefactorLog β c z := by
  have hl (i : Fin d) : Complex.log ((u : ℂ) ^ 2 * z i) =
      2 * (Real.log u : ℂ) + Complex.log (z i) := by
    rw [← Complex.ofReal_pow, Complex.log_ofReal_mul (sq_pos_of_pos hu)
      (Complex.slitPlane_ne_zero (hz i)), Real.log_pow]
    push_cast
    rfl
  have hp (i j : Fin d) :
      Complex.log (root ((u : ℂ) ^ 2 * z i) + root ((u : ℂ) ^ 2 * z j)) =
        (Real.log u : ℂ) + Complex.log (root (z i) + root (z j)) := by
    rw [root_ofReal_sq_mul hu (Complex.slitPlane_ne_zero (hz i)),
      root_ofReal_sq_mul hu (Complex.slitPlane_ne_zero (hz j)), ← mul_add]
    exact Complex.log_ofReal_mul hu (Complex.slitPlane_ne_zero (rootSum_slit hz i j))
  rw [physicalPrefactorLog_eq, physicalPrefactorLog_eq]
  simp_rw [hl, hp, add_div, mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, hc]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem physicalPrefactor_scale_balanced {d : ℕ} (β : ℂ) (hβ : β ≠ 0)
    (c : Fin d → ℂ) (hc : ∀ i, c i = -1 ∨ c i = β / 2) (hb : ∑ i, c i = 0)
    {z : Point d} (hz : z ∈ PhysicalRootDomain d) {u : ℝ} (hu : 0 < u) :
    physicalPrefactor β c (fun i => (u : ℂ) ^ 2 * z i) = physicalPrefactor β c z := by
  unfold physicalPrefactor
  rw [physicalPrefactorLog_scale β c hz hu (sum_rootPairExponent_balanced β hβ c hc hb)]

end BourgadeHuang.EdgeCMS
