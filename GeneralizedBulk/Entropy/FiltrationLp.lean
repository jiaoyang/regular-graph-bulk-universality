import GeneralizedBulk.Entropy.HermiteFiltration
import GeneralizedBulk.Gaussian.FiniteVector

/-! The finite triangular Hermite filtration inside actual Gaussian L². -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Hermite

variable (I : Type*) [Fintype I]

abbrev AtMostIndex (degree : ℕ) :=
  {a : I → Fin (degree + 1) // (∑ i, (a i).val) ≤ degree}

instance (degree : ℕ) : Fintype (AtMostIndex I degree) := Fintype.ofFinite _

def atMostIndexNat {degree : ℕ} (a : AtMostIndex I degree) (i : I) : ℕ := (a.val i).val

@[simp] theorem atMostIndexNat_degree {degree : ℕ} (a : AtMostIndex I degree) :
    (∑ i, atMostIndexNat I a i) ≤ degree := a.property

theorem atMostIndexNat_injective (degree : ℕ) : Function.Injective (atMostIndexNat I (degree := degree)) := by
  intro a b h
  apply Subtype.ext
  funext i
  apply Fin.ext
  exact congrFun h i

def atMostIndexOf (degree : ℕ) (a : I → ℕ) (ha : (∑ i, a i) ≤ degree) : AtMostIndex I degree := by
  classical
  refine ⟨fun i => ⟨a i, ?_⟩, ha⟩
  apply Nat.lt_succ_of_le
  exact (Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)).trans ha

@[simp] theorem atMostIndexNat_of (degree : ℕ) (a : I → ℕ) (ha : (∑ i, a i) ≤ degree) :
    atMostIndexNat I (atMostIndexOf I degree a ha) = a := rfl

/-- The triangular function filtration has a fixed finite spanning family. -/
theorem functionFiltration_eq_finite_span (degree : ℕ) : functionFiltration (I := I) degree =
    Submodule.span ℝ (Set.range (fun a : AtMostIndex I degree => multiHermite I (atMostIndexNat I a))) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f ⟨a, ha, rfl⟩
    exact Submodule.subset_span ⟨atMostIndexOf I degree a ha, rfl⟩
  · apply Submodule.span_le.mpr
    rintro f ⟨a, rfl⟩
    exact multiHermite_mem_functionFiltration _ _ a.property

instance (degree : ℕ) : FiniteDimensional ℝ (functionFiltration (I := I) degree) := by
  rw [functionFiltration_eq_finite_span, ← Fintype.range_linearCombination]
  infer_instance

theorem exists_functionFiltration_coefficients {f : (I → ℝ) → ℝ} {degree : ℕ}
    (hf : f ∈ functionFiltration degree) :
    ∃ coeff : AtMostIndex I degree → ℝ, chaosFunction (atMostIndexNat I) coeff = f := by
  rw [functionFiltration_eq_finite_span, Submodule.mem_span_range_iff_exists_fun] at hf
  obtain ⟨coeff, hc⟩ := hf
  refine ⟨coeff, ?_⟩
  calc
    chaosFunction (atMostIndexNat I) coeff = ∑ a, coeff a • multiHermite I (atMostIndexNat I a) := by
      funext x
      simp only [chaosFunction, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    _ = _ := hc

/-- The actual Gaussian L² triangular polynomial filtration. -/
def lpFiltration (degree : ℕ) : Submodule ℝ (Lp ℝ 2 (standardGaussian I)) :=
  Submodule.span ℝ (Set.range (fun a : AtMostIndex I degree => multiLp I (atMostIndexNat I a)))

instance (degree : ℕ) : FiniteDimensional ℝ (lpFiltration I degree) := by
  unfold lpFiltration
  rw [← Fintype.range_linearCombination]
  infer_instance

theorem multiLp_mem_lpFiltration (a : I → ℕ) (degree : ℕ) (ha : (∑ i, a i) ≤ degree) :
    multiLp I a ∈ lpFiltration I degree :=
  Submodule.subset_span ⟨atMostIndexOf I degree a ha, rfl⟩

theorem chaosLp_mem_lpFiltration {K : Type*} [Fintype K]
    (a : K → I → ℕ) (coeff : K → ℝ) (degree : ℕ) (ha : ∀ k, (∑ i, a k i) ≤ degree) :
    chaosLp a coeff ∈ lpFiltration I degree := by
  apply Submodule.sum_mem
  intro k hk
  exact Submodule.smul_mem _ _ (multiLp_mem_lpFiltration I (a k) degree (ha k))

theorem fullChaosSpace_le_lpFiltration (degree : ℕ) : fullChaosSpace I degree ≤ lpFiltration I degree := by
  rintro f ⟨coeff, rfl⟩
  exact chaosLp_mem_lpFiltration I _ coeff degree (fun a => (degreeIndexNat_sum I a).le)

theorem lpFiltration_mono {n m : ℕ} (hnm : n ≤ m) : lpFiltration I n ≤ lpFiltration I m := by
  apply Submodule.span_le.mpr
  rintro f ⟨a, rfl⟩
  exact multiLp_mem_lpFiltration I _ m (a.property.trans hnm)

theorem exists_lpFiltration_coefficients {f : Lp ℝ 2 (standardGaussian I)} {degree : ℕ}
    (hf : f ∈ lpFiltration I degree) :
    ∃ coeff : AtMostIndex I degree → ℝ, chaosLp (atMostIndexNat I) coeff = f := by
  rw [lpFiltration, Submodule.mem_span_range_iff_exists_fun] at hf
  exact hf

/-- A coefficient can be recovered by its genuine Gaussian inner product. -/
theorem atMostChaos_inner_basis (degree : ℕ) (coeff : AtMostIndex I degree → ℝ)
    (a : AtMostIndex I degree) :
    @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ (chaosLp (atMostIndexNat I) coeff)
      (multiLp I (atMostIndexNat I a)) = coeff a * multiFactorial I (atMostIndexNat I a) := by
  classical
  simp only [chaosLp, sum_inner, inner_smul_left, starRingEnd_apply, star_trivial, multiLp_inner]
  simp_rw [(atMostIndexNat_injective I degree).eq_iff]
  simp [mul_ite]

/-- A degree-n chaos is orthogonal to every polynomial of total Hermite degree
less than n, with all pairings taken in the actual Gaussian L² space. -/
theorem fullChaos_inner_lowerFiltration_zero (n m : ℕ) (hmn : m < n)
    (f : Lp ℝ 2 (standardGaussian I)) (hf : f ∈ fullChaosSpace I n)
    (g : Lp ℝ 2 (standardGaussian I)) (hg : g ∈ lpFiltration I m) :
    @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ f g = 0 := by
  obtain ⟨c, rfl⟩ := hf
  obtain ⟨d, rfl⟩ := exists_lpFiltration_coefficients I hg
  change @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ (chaosLp (degreeIndexNat I) c)
    (chaosLp (atMostIndexNat I) d) = 0
  have hcross (a : DegreeIndex I n) (b : AtMostIndex I m) :
      @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ (multiLp I (degreeIndexNat I a))
        (multiLp I (atMostIndexNat I b)) = 0 := by
    rw [multiLp_inner]
    have hab : degreeIndexNat I a ≠ atMostIndexNat I b := by
      intro heq
      have he := congrArg (fun e : I → ℕ => ∑ i, e i) heq
      change (∑ i, degreeIndexNat I a i) = ∑ i, atMostIndexNat I b i at he
      rw [degreeIndexNat_sum] at he
      have hb := b.property
      change (∑ i, atMostIndexNat I b i) ≤ m at hb
      omega
    simp [hab]
  simp only [chaosLp, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    starRingEnd_apply, star_trivial, hcross, mul_zero, Finset.sum_const_zero]

/-- Orthogonality to lower-degree polynomials selects the homogeneous degree
inside the finite triangular filtration. -/
theorem mem_fullChaos_of_filtration_orthogonal (degree : ℕ)
    (f : Lp ℝ 2 (standardGaussian I)) (hf : f ∈ lpFiltration I degree)
    (horth : ∀ g : Lp ℝ 2 (standardGaussian I), g ∈ lpFiltration I (degree - 1) →
      @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ f g = 0) :
    f ∈ fullChaosSpace I degree := by
  classical
  obtain ⟨coeff, rfl⟩ := exists_lpFiltration_coefficients I hf
  have hzero (a : AtMostIndex I degree) (ha : (∑ i, atMostIndexNat I a i) < degree) : coeff a = 0 := by
    have hg : multiLp I (atMostIndexNat I a) ∈ lpFiltration I (degree - 1) :=
      multiLp_mem_lpFiltration I _ _ (by omega)
    have hh := horth _ hg
    rw [atMostChaos_inner_basis] at hh
    exact (mul_eq_zero.mp hh).resolve_right (ne_of_gt (multiFactorial_pos I _))
  apply Submodule.sum_mem
  intro a ha
  by_cases hdeg : (∑ i, atMostIndexNat I a i) = degree
  · exact Submodule.smul_mem _ _ (multiLp_mem_fullChaosSpace I degree _ hdeg)
  · have hb := atMostIndexNat_degree I a
    have hz := hzero a (by omega)
    simp only [hz, zero_smul]
    exact Submodule.zero_mem _

/-- Positive homogeneous degree is exactly the triangular filtration with
its lower-degree orthogonal part removed. Degree zero is intentionally separate. -/
theorem mem_fullChaos_iff_filtration_orthogonal (degree : ℕ) (hdegree : 0 < degree)
    (f : Lp ℝ 2 (standardGaussian I)) :
    f ∈ fullChaosSpace I degree ↔ f ∈ lpFiltration I degree ∧
      ∀ g : Lp ℝ 2 (standardGaussian I), g ∈ lpFiltration I (degree - 1) →
        @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ f g = 0 := by
  constructor
  · intro hf
    refine ⟨fullChaosSpace_le_lpFiltration I degree hf, ?_⟩
    intro g hg
    exact fullChaos_inner_lowerFiltration_zero I degree (degree - 1) (by omega) f hf g hg
  · rintro ⟨hf, ho⟩
    exact mem_fullChaos_of_filtration_orthogonal I degree f hf ho

/-- Degree zero is exactly the constant Gaussian chaos; it is kept separate
from positivity and lower-degree orthogonality arguments. -/
theorem lpFiltration_zero_eq_fullChaos : lpFiltration I 0 = fullChaosSpace I 0 := by
  apply le_antisymm
  · intro f hf
    obtain ⟨coeff, rfl⟩ := exists_lpFiltration_coefficients I hf
    apply Submodule.sum_mem
    intro a ha
    apply Submodule.smul_mem
    exact multiLp_mem_fullChaosSpace I 0 _ (Nat.eq_zero_of_le_zero a.property)
  · exact fullChaosSpace_le_lpFiltration I 0

/-- An actual polynomial in the finite Hermite filtration cannot vanish merely
almost everywhere: factorial Gaussian orthogonality forces every coefficient zero. -/
theorem functionFiltration_eq_zero_of_ae_zero {f : (I → ℝ) → ℝ} {degree : ℕ}
    (hf : f ∈ functionFiltration degree) (hzero : f =ᵐ[standardGaussian I] (fun _ => 0)) :
    f = (fun _ => 0) := by
  classical
  obtain ⟨coeff, hc⟩ := exists_functionFiltration_coefficients I hf
  have hLp : chaosLp (atMostIndexNat I) coeff = 0 := by
    apply Lp.ext
    filter_upwards [chaosLp_ae (atMostIndexNat I) coeff, hzero,
      Lp.coeFn_zero ℝ 2 (standardGaussian I)] with x hcoef hz h0
    rw [hcoef, hc, hz, h0]
    rfl
  have hcoeff (a : AtMostIndex I degree) : coeff a = 0 := by
    have hh := atMostChaos_inner_basis I degree coeff a
    rw [hLp, inner_zero_left] at hh
    exact (mul_eq_zero.mp hh.symm).resolve_right (ne_of_gt (multiFactorial_pos I _))
  funext x
  rw [← hc]
  simp only [chaosFunction, hcoeff, zero_mul, Finset.sum_const_zero]

/-- Almost-everywhere equality of two actual Gaussian polynomials is an exact
pointwise polynomial identity. -/
theorem functionFiltration_eq_of_ae_eq {f g : (I → ℝ) → ℝ} {degree : ℕ}
    (hf : f ∈ functionFiltration degree) (hg : g ∈ functionFiltration degree)
    (heq : f =ᵐ[standardGaussian I] g) : f = g := by
  have hz : (fun x => f x - g x) =ᵐ[standardGaussian I] (fun _ => 0) :=
    heq.mono (fun x hx => sub_eq_zero.mpr hx)
  have hfz := functionFiltration_eq_zero_of_ae_zero I ((functionFiltration degree).sub_mem hf hg) hz
  funext x
  have hh := congrFun hfz x
  exact sub_eq_zero.mp hh

/-- Every actual finite Hermite polynomial lies in the degree filtration
predicted by its genuine multiindex degrees. -/
theorem chaosFunction_mem_functionFiltration {K : Type*} [Fintype K]
    (a : K → I → ℕ) (coeff : K → ℝ) (degree : ℕ) (ha : ∀ k, (∑ i, a k i) ≤ degree) :
    chaosFunction a coeff ∈ functionFiltration degree := by
  have hs : (∑ k : K, coeff k • multiHermite I (a k)) ∈ functionFiltration degree := by
    apply Submodule.sum_mem
    intro k hk
    exact Submodule.smul_mem _ _ (multiHermite_mem_functionFiltration (a k) degree (ha k))
  convert hs using 1
  funext x
  simp only [chaosFunction, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- Equality in Gaussian L² of any two bounded-degree Hermite polynomial
representations is a literal equality of their actual polynomial functions.
Neither representation needs distinct indices. -/
theorem chaosFunction_eq_of_chaosLp_eq {K J : Type*} [Fintype K] [Fintype J]
    (a : K → I → ℕ) (coeff : K → ℝ) (b : J → I → ℕ) (other : J → ℝ)
    (degree : ℕ) (ha : ∀ k, (∑ i, a k i) ≤ degree) (hb : ∀ j, (∑ i, b j i) ≤ degree)
    (heq : chaosLp a coeff = chaosLp b other) : chaosFunction a coeff = chaosFunction b other := by
  classical
  have hae : chaosFunction a coeff =ᵐ[standardGaussian I] chaosFunction b other := by
    filter_upwards [chaosLp_ae a coeff, chaosLp_ae b other] with x hx hy
    rw [heq] at hx
    exact hx.symm.trans hy
  exact functionFiltration_eq_of_ae_eq I (chaosFunction_mem_functionFiltration I a coeff degree ha)
    (chaosFunction_mem_functionFiltration I b other degree hb) hae

end GeneralizedBulk.Entropy.Hermite
