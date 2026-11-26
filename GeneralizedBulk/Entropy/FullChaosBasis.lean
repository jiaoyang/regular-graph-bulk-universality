import GeneralizedBulk.Entropy.GaussianAveraging

/-! Fixed finite-dimensional spaces of actual homogeneous Gaussian chaos. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Hermite

variable (I : Type*) [Fintype I]

/-- A finite index type for every multiindex of the prescribed total degree.
The bounded coordinates make finiteness immediate, without a support choice. -/
abbrev DegreeIndex (degree : ℕ) :=
  {a : I → Fin (degree + 1) // ∑ i, (a i).val = degree}

instance (degree : ℕ) : Fintype (DegreeIndex I degree) := Fintype.ofFinite _

def degreeIndexNat {degree : ℕ} (a : DegreeIndex I degree) (i : I) : ℕ := (a.val i).val

@[simp] theorem degreeIndexNat_sum {degree : ℕ} (a : DegreeIndex I degree) :
    (∑ i, degreeIndexNat I a i) = degree := a.property

theorem degreeIndexNat_injective (degree : ℕ) :
    Function.Injective (degreeIndexNat I (degree := degree)) := by
  intro a b hab
  apply Subtype.ext
  funext i
  apply Fin.ext
  exact congrFun hab i

/-- Every homogeneous multiindex has a canonical representative in the fixed
finite index set. -/
def degreeIndexOf (degree : ℕ) (a : I → ℕ) (ha : ∑ i, a i = degree) : DegreeIndex I degree := by
  classical
  refine ⟨fun i => ⟨a i, ?_⟩, ha⟩
  apply Nat.lt_succ_of_le
  rw [← ha]
  exact Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)

@[simp] theorem degreeIndexNat_of (degree : ℕ) (a : I → ℕ) (ha : ∑ i, a i = degree) :
    degreeIndexNat I (degreeIndexOf I degree a ha) = a := rfl

/-- The full finite chaos is embedded into the actual Gaussian L² space. -/
def fullChaosMap (degree : ℕ) : (DegreeIndex I degree → ℝ) →ₗ[ℝ] Lp ℝ 2 (standardGaussian I) where
  toFun coeff := chaosLp (degreeIndexNat I) coeff
  map_add' c d := by simp [chaosLp, add_smul, Finset.sum_add_distrib]
  map_smul' r c := by simp [chaosLp, Finset.smul_sum, smul_smul, mul_comm]

/-- The Gram matrix is the actual factorial-weighted Gaussian Gram matrix. -/
theorem fullChaosMap_inner_basis (degree : ℕ) (coeff : DegreeIndex I degree → ℝ)
    (a : DegreeIndex I degree) :
    @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ (fullChaosMap I degree coeff)
      (multiLp I (degreeIndexNat I a)) = coeff a * multiFactorial I (degreeIndexNat I a) := by
  classical
  change @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ (chaosLp (degreeIndexNat I) coeff)
    (multiLp I (degreeIndexNat I a)) = _
  simp only [chaosLp, sum_inner, inner_smul_left,
    starRingEnd_apply, star_trivial, multiLp_inner]
  simp_rw [(degreeIndexNat_injective I degree).eq_iff]
  simp [mul_ite]

theorem fullChaosMap_injective (degree : ℕ) : Function.Injective (fullChaosMap I degree) := by
  intro c d h
  funext a
  have hh := congrArg (fun z : Lp ℝ 2 (standardGaussian I) =>
    @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ z (multiLp I (degreeIndexNat I a))) h
  change @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ (fullChaosMap I degree c)
    (multiLp I (degreeIndexNat I a)) = @inner ℝ (Lp ℝ 2 (standardGaussian I)) _
      (fullChaosMap I degree d) (multiLp I (degreeIndexNat I a)) at hh
  rw [fullChaosMap_inner_basis, fullChaosMap_inner_basis] at hh
  exact mul_right_cancel₀ (ne_of_gt (multiFactorial_pos I (degreeIndexNat I a))) hh

/-- The source's fixed homogeneous chaos subspace is a literal subspace of
Gaussian L², independent of all spectral parameters. -/
def fullChaosSpace (degree : ℕ) : Submodule ℝ (Lp ℝ 2 (standardGaussian I)) :=
  LinearMap.range (fullChaosMap I degree)

instance (degree : ℕ) : FiniteDimensional ℝ (fullChaosSpace I degree) := by
  unfold fullChaosSpace
  infer_instance

/-- A finite basis for the actual Gaussian chaos, with its inherited L² norm. -/
def fullChaosBasis (degree : ℕ) : Basis (DegreeIndex I degree) ℝ (fullChaosSpace I degree) :=
  (Pi.basisFun ℝ (DegreeIndex I degree)).map
    (LinearEquiv.ofInjective (fullChaosMap I degree) (fullChaosMap_injective I degree))

@[simp] theorem fullChaosBasis_coe (degree : ℕ) (a : DegreeIndex I degree) :
    ((fullChaosBasis I degree a : fullChaosSpace I degree) : Lp ℝ 2 (standardGaussian I)) =
      multiLp I (degreeIndexNat I a) := by
  classical
  change fullChaosMap I degree (Pi.basisFun ℝ (DegreeIndex I degree) a) = _
  simp [fullChaosMap, chaosLp, Pi.basisFun_apply, Pi.single_apply, ite_smul]

theorem multiLp_mem_fullChaosSpace (degree : ℕ) (a : I → ℕ) (ha : ∑ i, a i = degree) :
    multiLp I a ∈ fullChaosSpace I degree := by
  have h := (fullChaosBasis I degree (degreeIndexOf I degree a ha)).property
  simpa only [fullChaosBasis_coe, degreeIndexNat_of] using h

/-- Every earlier finite homogeneous coefficient representation lands in the
canonical fixed finite-dimensional space. -/
theorem chaosLp_mem_fullChaosSpace {K : Type*} [Fintype K]
    (degree : ℕ) (a : K → I → ℕ) (ha : ∀ k, ∑ i, a k i = degree) (coeff : K → ℝ) :
    chaosLp a coeff ∈ fullChaosSpace I degree := by
  apply Submodule.sum_mem
  intro k hk
  exact Submodule.smul_mem _ _ (multiLp_mem_fullChaosSpace I degree (a k) (ha k))

/-- Different full Hermite degrees are genuinely orthogonal in Gaussian L². -/
theorem fullChaosSpace_orthogonal (n m : ℕ) (hnm : n ≠ m) :
    fullChaosSpace I n ⟂ fullChaosSpace I m := by
  intro f hf g hg
  obtain ⟨c, rfl⟩ := hf
  obtain ⟨d, rfl⟩ := hg
  rw [real_inner_comm]
  change @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ (chaosLp (degreeIndexNat I) c)
    (chaosLp (degreeIndexNat I) d) = 0
  have hcross (a : DegreeIndex I n) (b : DegreeIndex I m) :
      @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ (multiLp I (degreeIndexNat I a))
        (multiLp I (degreeIndexNat I b)) = 0 := by
    rw [multiLp_inner]
    have hab : degreeIndexNat I a ≠ degreeIndexNat I b := by
      intro heq
      have he := congrArg (fun e : I → ℕ => ∑ i, e i) heq
      change (∑ i, degreeIndexNat I a i) = ∑ i, degreeIndexNat I b i at he
      rw [degreeIndexNat_sum, degreeIndexNat_sum] at he
      exact hnm he
    simp [hab]
  simp only [chaosLp, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    starRingEnd_apply, star_trivial, hcross, mul_zero, Finset.sum_const_zero]

/-- The canonical actual degree space has the exact Gaussian derivative energy. -/
theorem fullChaos_derivative_energy [DecidableEq I] (degree : ℕ)
    (coeff : DegreeIndex I degree → ℝ) :
    (∑ i, ‖chaosDerivativeLp (degreeIndexNat I) coeff i‖ ^ 2) =
      (degree : ℝ) * ‖fullChaosMap I degree coeff‖ ^ 2 := by
  exact chaos_derivative_energy (degreeIndexNat I) (degreeIndexNat_injective I degree)
    coeff degree (degreeIndexNat_sum I)

end GeneralizedBulk.Entropy.Hermite
