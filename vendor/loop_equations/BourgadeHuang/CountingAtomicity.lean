import BourgadeHuang.Factorial
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Atomicity of locally finite integer-valued measures

The compact-set integrality in `LocalCountingMeasure` implies that every
non-atom has a null open neighborhood. Thus the measure has no diffuse part,
and only finitely many atoms lie in any compact set.
-/
noncomputable section
open scoped BigOperators Topology ENNReal
open MeasureTheory Filter

namespace BourgadeHuang

/-- The locations of particles, without their multiplicities. -/
def LocalCountingMeasure.atoms (ξ : LocalCountingMeasure) : Set ℝ :=
  {x | ξ.measure {x} ≠ 0}

theorem LocalCountingMeasure.one_le_mass_of_mem_atoms
    (ξ : LocalCountingMeasure) {x : ℝ} (hx : x ∈ ξ.atoms) :
    1 ≤ ξ.measure {x} := by
  obtain ⟨n, hn⟩ := ξ.integer_compacts {x} (isCompact_singleton)
  rw [hn]
  have hn0 : n ≠ 0 := by
    intro h
    apply hx
    simp [hn, h]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0

theorem LocalCountingMeasure.exists_null_open_of_not_mem_atoms
    (ξ : LocalCountingMeasure) {x : ℝ} (hx : x ∉ ξ.atoms) :
    ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧ ξ.measure U = 0 := by
  have hx0 : ξ.measure {x} = 0 := by simpa [LocalCountingMeasure.atoms] using hx
  obtain ⟨U, hUsub, hUopen, hUmeasure⟩ :=
    Set.exists_isOpen_lt_of_lt (μ := ξ.measure) {x} 1 (by simp [hx0])
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds (hUsub (Set.mem_singleton x)))
  have hsmall : Metric.closedBall x (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith : ε / 2 < ε)).trans hεsub
  obtain ⟨n, hn⟩ := ξ.integer_compacts (Metric.closedBall x (ε / 2))
    (isCompact_closedBall x (ε / 2))
  have hnlt : (n : ℝ≥0∞) < 1 := by
    rw [← hn]
    exact (measure_mono hsmall).trans_lt hUmeasure
  have hn0 : n = 0 := Nat.lt_one_iff.mp (by exact_mod_cast hnlt)
  refine ⟨Metric.ball x (ε / 2), Metric.isOpen_ball,
    Metric.mem_ball_self (by linarith), ?_⟩
  exact measure_mono_null Metric.ball_subset_closedBall (by simp [hn, hn0])

theorem LocalCountingMeasure.measure_compl_atoms (ξ : LocalCountingMeasure) :
    ξ.measure ξ.atomsᶜ = 0 := by
  classical
  let Z := {U : Set ℝ // IsOpen U ∧ ξ.measure U = 0}
  obtain ⟨T, hTcount, hTcover⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun U : Z => (U : Set ℝ)) (fun U => U.2.1)
  apply measure_mono_null (t := ⋃ U ∈ T, (U : Set ℝ))
  · rw [hTcover]
    intro x hx
    obtain ⟨U, hUopen, hxU, hUzero⟩ := ξ.exists_null_open_of_not_mem_atoms hx
    exact Set.mem_iUnion.mpr ⟨⟨U, hUopen, hUzero⟩, hxU⟩
  · exact (measure_biUnion_null_iff hTcount).mpr (fun U _ => U.2.2)

theorem LocalCountingMeasure.finite_atoms_inter_compact (ξ : LocalCountingMeasure)
    {K : Set ℝ} (hK : IsCompact K) : (ξ.atoms ∩ K).Finite := by
  by_contra h
  have htop : ξ.measure (ξ.atoms ∩ K) = ⊤ :=
    Set.Infinite.meas_eq_top h ⟨1, one_ne_zero, fun x hx =>
      ξ.one_le_mass_of_mem_atoms hx.1⟩
  have hle := measure_mono (μ := ξ.measure) (Set.inter_subset_right : ξ.atoms ∩ K ⊆ K)
  rw [htop] at hle
  exact hK.measure_lt_top.ne (top_le_iff.mp hle)

/-- Restriction to finitely many atoms is the sum of their weighted Dirac measures. -/
theorem restrict_finset_eq_sum_dirac (μ : Measure ℝ) (s : Finset ℝ) :
    μ.restrict (s : Set ℝ) = ∑ x ∈ s, μ {x} • Measure.dirac x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.coe_insert, Set.insert_eq, Measure.restrict_union,
      Measure.restrict_singleton, ih, Finset.sum_insert ha]
    · simpa using ha
    · exact s.finite_toSet.measurableSet

/-- A compact restriction is a finite weighted atomic measure. This rules out
any diffuse component without strengthening the model's counting-measure definition. -/
theorem LocalCountingMeasure.restrict_compact_eq_sum_dirac
    (ξ : LocalCountingMeasure) {K : Set ℝ} (hK : IsCompact K) :
    ξ.measure.restrict K = ∑ x ∈ (ξ.finite_atoms_inter_compact hK).toFinset,
      ξ.measure {x} • Measure.dirac x := by
  rw [← restrict_finset_eq_sum_dirac, Set.Finite.coe_toFinset]
  apply Measure.restrict_congr_set
  have h := diff_null_ae_eq_self (s := K) ξ.measure_compl_atoms
  simpa only [Set.diff_compl, Set.inter_comm] using h.symm

/-- For a simple configuration every atom has unit mass. -/
theorem LocalCountingMeasure.mass_eq_one_of_simple
    (ξ : LocalCountingMeasure) (hsimple : ∀ x, ξ.measure {x} ≤ 1)
    {x : ℝ} (hx : x ∈ ξ.atoms) : ξ.measure {x} = 1 :=
  le_antisymm (hsimple x) (ξ.one_le_mass_of_mem_atoms hx)

/-- A compact restriction of a simple configuration is a finite sum of distinct Dirac masses. -/
theorem LocalCountingMeasure.restrict_compact_eq_sum_dirac_of_simple
    (ξ : LocalCountingMeasure) (hsimple : ∀ x, ξ.measure {x} ≤ 1)
    {K : Set ℝ} (hK : IsCompact K) :
    ξ.measure.restrict K =
      ∑ x ∈ (ξ.finite_atoms_inter_compact hK).toFinset, Measure.dirac x := by
  rw [ξ.restrict_compact_eq_sum_dirac hK]
  apply Finset.sum_congr rfl
  intro x hx
  have hx' : x ∈ ξ.atoms := ((ξ.finite_atoms_inter_compact hK).mem_toFinset.mp hx).1
  rw [ξ.mass_eq_one_of_simple hsimple hx', one_smul]

/-- Finite product measures of finite particle configurations enumerate all ordered labels. -/
theorem pi_sum_dirac {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (x : κ → ℝ) :
    Measure.pi (fun _ : ι => ∑ k : κ, Measure.dirac (x k)) =
      ∑ a : ι → κ, Measure.dirac (fun j => x (a j)) := by
  classical
  apply Measure.pi_eq
  intro s hs
  simp only [Measure.finset_sum_apply, Measure.dirac_apply,
    Set.indicator_apply, Pi.one_apply, Set.mem_univ_pi]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Fintype.prod_ite_zero]
  simp

/-- When particle locations are distinct, label-exclusion and location-exclusion agree. -/
theorem integral_injective_pi_sum_dirac {N q : ℕ}
    (x : Fin N → ℝ) (hx : Function.Injective x)
    (φ : (Fin q → ℝ) → ℝ) :
    (∫ y : Fin q → ℝ, if Function.Injective y then φ y else 0
      ∂Measure.pi (fun _ : Fin q => ∑ i, Measure.dirac (x i))) =
      factorialStatistic x φ := by
  classical
  rw [pi_sum_dirac, integral_finset_sum_measure (fun _ _ => integrable_dirac)]
  simp only [integral_dirac, factorialStatistic]
  apply Finset.sum_congr rfl
  intro a _
  have heq : Function.Injective (fun j => x (a j)) ↔ Function.Injective a :=
    ⟨fun h _ _ ha => h (congrArg x ha), fun h => hx.comp h⟩
  simp only [heq]

/-- A test supported in a compact box only depends on the compact restriction of the measure. -/
theorem integral_injective_pi_restrict {q : ℕ}
    (μ : Measure ℝ) [SigmaFinite μ] (K : Set ℝ) (hK : MeasurableSet K)
    (φ : (Fin q → ℝ) → ℝ)
    (hsupp : ∀ y, (¬ ∀ j, y j ∈ K) → φ y = 0) :
    (∫ y : Fin q → ℝ, if Function.Injective y then φ y else 0
      ∂Measure.pi (fun _ : Fin q => μ)) =
    (∫ y : Fin q → ℝ, if Function.Injective y then φ y else 0
      ∂Measure.pi (fun _ : Fin q => μ.restrict K)) := by
  classical
  rw [← Measure.restrict_pi_pi, ← integral_indicator (MeasurableSet.univ_pi (fun _ => hK))]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  by_cases hy : ∀ j, y j ∈ K
  · simp [hy]
  · simp [hy, hsupp y hy]

/-- A compact restriction of a simple configuration admits a finite injective particle list. -/
theorem LocalCountingMeasure.exists_compact_particle_list
    (ξ : LocalCountingMeasure) (hsimple : ∀ x, ξ.measure {x} ≤ 1)
    {K : Set ℝ} (hK : IsCompact K) :
    ∃ (N : ℕ) (x : Fin N → ℝ), Function.Injective x ∧
      (∀ i, x i ∈ K) ∧ ξ.measure.restrict K = ∑ i, Measure.dirac (x i) := by
  classical
  let s := (ξ.finite_atoms_inter_compact hK).toFinset
  let x : Fin s.card → ℝ := fun i => (s.equivFin.symm i).val
  refine ⟨s.card, x, ?_, ?_, ?_⟩
  · exact Subtype.val_injective.comp s.equivFin.symm.injective
  · intro i
    exact ((ξ.finite_atoms_inter_compact hK).mem_toFinset.mp
      (s.equivFin.symm i).property).2
  · rw [ξ.restrict_compact_eq_sum_dirac_of_simple hsimple hK]
    change (∑ z ∈ s, Measure.dirac z) = ∑ i, Measure.dirac (x i)
    rw [← Finset.sum_coe_sort]
    exact Fintype.sum_equiv s.equivFin _ _ (fun z => by simp [x])

set_option maxHeartbeats 800000 in
/-- Multiplicities can be represented by repeated labels in a finite particle list. -/
theorem LocalCountingMeasure.exists_compact_particle_list_with_multiplicity
    (ξ : LocalCountingMeasure) {K : Set ℝ} (hK : IsCompact K) :
    ∃ (N : ℕ) (x : Fin N → ℝ),
      (∀ i, x i ∈ K) ∧ ξ.measure.restrict K = ∑ i, Measure.dirac (x i) ∧
      ξ.measure K = N := by
  classical
  let s := (ξ.finite_atoms_inter_compact hK).toFinset
  let m : s → ℕ := fun z => (ξ.integer_compacts {z.val} isCompact_singleton).choose
  have hm (z : s) : ξ.measure {z.val} = (m z : ℝ≥0∞) :=
    (ξ.integer_compacts {z.val} isCompact_singleton).choose_spec
  let I := (z : s) × Fin (m z)
  let e := Fintype.equivFin I
  let x : Fin (Fintype.card I) → ℝ := fun i => (e.symm i).1.val
  have hμ : ξ.measure.restrict K = ∑ i, Measure.dirac (x i) := by
    rw [ξ.restrict_compact_eq_sum_dirac hK]
    change (∑ z ∈ s, ξ.measure {z} • Measure.dirac z) = _
    rw [← Finset.sum_coe_sort]
    calc
      (∑ z : s, ξ.measure {z.val} • Measure.dirac z.val) =
          ∑ z : s, ∑ _j : Fin (m z), Measure.dirac z.val := by
        apply Finset.sum_congr rfl
        intro z _
        rw [hm z]
        ext A hA
        simp [Measure.finset_sum_apply, Measure.smul_apply, nsmul_eq_mul]
      _ = ∑ i : I, Measure.dirac i.1.val := (Fintype.sum_sigma (fun i : I => Measure.dirac i.1.val)).symm
      _ = ∑ i, Measure.dirac (x i) :=
        Fintype.sum_equiv e _ _ (fun z => by simp [x])
  refine ⟨Fintype.card I, x, ?_, hμ, ?_⟩
  · intro i
    exact ((ξ.finite_atoms_inter_compact hK).mem_toFinset.mp (e.symm i).1.property).2
  · have hh := congrArg (fun μ : Measure ℝ => μ Set.univ) hμ
    simpa using hh

/-- Every compactly supported factorial integral of a simple configuration is
exactly a finite label-injective particle statistic. -/
theorem LocalCountingMeasure.factorial_integral_eq_particle_list
    (ξ : LocalCountingMeasure) (hsimple : ∀ x, ξ.measure {x} ≤ 1)
    {K : Set ℝ} (hK : IsCompact K) :
    ∃ (N : ℕ) (x : Fin N → ℝ), Function.Injective x ∧
      (∀ i, x i ∈ K) ∧ ξ.measure.restrict K = ∑ i, Measure.dirac (x i) ∧
      ∀ (q : ℕ) (φ : (Fin q → ℝ) → ℝ),
        (∀ y, (¬ ∀ j, y j ∈ K) → φ y = 0) →
        (∫ y : Fin q → ℝ, if Function.Injective y then φ y else 0
          ∂Measure.pi (fun _ : Fin q => ξ.measure)) = factorialStatistic x φ := by
  obtain ⟨N, x, hx, hxK, hμ⟩ := ξ.exists_compact_particle_list hsimple hK
  refine ⟨N, x, hx, hxK, hμ, ?_⟩
  intro q φ hφ
  rw [integral_injective_pi_restrict ξ.measure K hK.measurableSet φ hφ, hμ]
  exact integral_injective_pi_sum_dirac x hx φ

/-- Compact restriction preserves the original counting-measure structure. -/
def LocalCountingMeasure.restrictCompact (ξ : LocalCountingMeasure)
    (K : Set ℝ) (hK : IsCompact K) : LocalCountingMeasure where
  measure := ξ.measure.restrict K
  locallyFinite := inferInstance
  integer_compacts := by
    intro A hA
    rw [Measure.restrict_apply hA.measurableSet]
    exact ξ.integer_compacts (A ∩ K) (hA.inter hK)

@[simp] theorem LocalCountingMeasure.restrictCompact_measure (ξ : LocalCountingMeasure)
    (K : Set ℝ) (hK : IsCompact K) :
    (ξ.restrictCompact K hK).measure = ξ.measure.restrict K := rfl

/-- General factorial integrals of a simple configuration are bounded by the
appropriate power of its compact interval count. -/
theorem LocalCountingMeasure.abs_factorial_integral_le_count_pow
    (ξ : LocalCountingMeasure) (hsimple : ∀ x, ξ.measure {x} ≤ 1)
    {q : ℕ} (φ : (Fin q → ℝ) → ℝ) (a b C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ y, |φ y| ≤ C)
    (hsupport : ∀ y, (¬ ∀ j, y j ∈ Set.Icc a b) → φ y = 0) :
    |∫ y : Fin q → ℝ, if Function.Injective y then φ y else 0
      ∂Measure.pi (fun _ : Fin q => ξ.measure)| ≤
      C * (ξ.measure (Set.Icc a b)).toReal ^ q := by
  obtain ⟨N, x, hx, hxK, hμ, hint⟩ :=
    ξ.factorial_integral_eq_particle_list hsimple (K := Set.Icc a b) isCompact_Icc
  rw [hint q φ hsupport]
  have hcount : (ξ.measure (Set.Icc a b)).toReal = particleCount x a b := by
    rw [← finite_dirac_count, ← hμ, Measure.restrict_apply measurableSet_Icc,
      Set.inter_self]
  rw [hcount]
  exact abs_factorialStatistic_le_count_pow x φ a b C hC hbound hsupport

/-- The same compact-count bound holds almost surely for the target process. -/
theorem TargetProcess.ae_abs_factorial_integral_le_count_pow
    (target : TargetProcess) {q : ℕ} (φ : (Fin q → ℝ) → ℝ)
    (a b C : ℝ) (hC : 0 ≤ C) (hbound : ∀ y, |φ y| ≤ C)
    (hsupport : ∀ y, (¬ ∀ j, y j ∈ Set.Icc a b) → φ y = 0) :
    ∀ᵐ ξ ∂target.law,
      |∫ y : Fin q → ℝ, if Function.Injective y then φ y else 0
        ∂Measure.pi (fun _ : Fin q => ξ.measure)| ≤
        C * (ξ.measure (Set.Icc a b)).toReal ^ q := by
  filter_upwards [target.simple] with ξ hξ
  exact ξ.abs_factorial_integral_le_count_pow hξ φ a b C hC hbound hsupport

/-- Compact support alone gives inner integrability on a simple configuration,
even before any regularity of the test is used: its restriction is a finite sum. -/
theorem LocalCountingMeasure.integrable_injective_pi
    (ξ : LocalCountingMeasure) (hsimple : ∀ x, ξ.measure {x} ≤ 1)
    {q : ℕ} {K : Set ℝ} (hK : IsCompact K)
    (φ : (Fin q → ℝ) → ℝ)
    (hsupport : ∀ y, (¬ ∀ j, y j ∈ K) → φ y = 0) :
    Integrable (fun y : Fin q → ℝ => if Function.Injective y then φ y else 0)
      (Measure.pi (fun _ : Fin q => ξ.measure)) := by
  classical
  have hs : Function.support (fun y : Fin q → ℝ =>
      if Function.Injective y then φ y else 0) ⊆ Set.univ.pi (fun _ => K) := by
    intro y hy
    by_contra h
    have hφ := hsupport y (by simpa using h)
    simp [Function.mem_support, hφ] at hy
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  obtain ⟨N, x, hx, hxK, hμ⟩ := ξ.exists_compact_particle_list hsimple hK
  rw [IntegrableOn, Measure.restrict_pi_pi, hμ, pi_sum_dirac]
  exact integrable_finset_sum_measure.mpr (fun _ _ => integrable_dirac)

/-- Uniform approximation on a common compact box controls the difference of
the actual target factorial integrals by a count power. -/
theorem LocalCountingMeasure.abs_sub_factorial_integral_le_count_pow
    (ξ : LocalCountingMeasure) (hsimple : ∀ x, ξ.measure {x} ≤ 1)
    {q : ℕ} (φ ψ : (Fin q → ℝ) → ℝ) (a b C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ y, |φ y - ψ y| ≤ C)
    (hφ : ∀ y, (¬ ∀ j, y j ∈ Set.Icc a b) → φ y = 0)
    (hψ : ∀ y, (¬ ∀ j, y j ∈ Set.Icc a b) → ψ y = 0) :
    |(∫ y : Fin q → ℝ, if Function.Injective y then φ y else 0
        ∂Measure.pi (fun _ : Fin q => ξ.measure)) -
      (∫ y : Fin q → ℝ, if Function.Injective y then ψ y else 0
        ∂Measure.pi (fun _ : Fin q => ξ.measure))| ≤
      C * (ξ.measure (Set.Icc a b)).toReal ^ q := by
  classical
  rw [← integral_sub
    (ξ.integrable_injective_pi hsimple isCompact_Icc φ hφ)
    (ξ.integrable_injective_pi hsimple isCompact_Icc ψ hψ)]
  have heq : (fun y : Fin q → ℝ =>
      (if Function.Injective y then φ y else 0) -
      (if Function.Injective y then ψ y else 0)) =
      (fun y => if Function.Injective y then φ y - ψ y else 0) := by
    funext y
    split_ifs <;> simp
  rw [heq]
  apply ξ.abs_factorial_integral_le_count_pow hsimple (fun y => φ y - ψ y) a b C hC hbound
  intro y hy
  simp [hφ y hy, hψ y hy]

/-- Count moments give outer integrability once measurability is established,
for example by approximation with continuous tensor observables. -/
theorem TargetProcess.integrable_factorial_integral_of_aestronglyMeasurable
    (target : TargetProcess) {q : ℕ} (φ : (Fin q → ℝ) → ℝ)
    (hm : AEStronglyMeasurable (fun ξ : LocalCountingMeasure =>
      ∫ y : Fin q → ℝ, if Function.Injective y then φ y else 0
        ∂Measure.pi (fun _ : Fin q => ξ.measure)) target.law)
    (a b C : ℝ) (hC : 0 ≤ C) (hbound : ∀ y, |φ y| ≤ C)
    (hsupport : ∀ y, (¬ ∀ j, y j ∈ Set.Icc a b) → φ y = 0) :
    Integrable (fun ξ : LocalCountingMeasure =>
      ∫ y : Fin q → ℝ, if Function.Injective y then φ y else 0
        ∂Measure.pi (fun _ : Fin q => ξ.measure)) target.law := by
  apply ((target.count_moments_integrable a b q).const_mul C).mono' hm
  simpa only [Real.norm_eq_abs] using
    target.ae_abs_factorial_integral_le_count_pow φ a b C hC hbound hsupport

/-- Approximation also controls the expectations of target factorial statistics. -/
theorem TargetProcess.abs_sub_factorialExpectation_le
    (target : TargetProcess) {q : ℕ} (φ ψ : (Fin q → ℝ) → ℝ)
    (hφi : Integrable (fun ξ : LocalCountingMeasure =>
      ∫ y : Fin q → ℝ, if Function.Injective y then φ y else 0
        ∂Measure.pi (fun _ : Fin q => ξ.measure)) target.law)
    (hψi : Integrable (fun ξ : LocalCountingMeasure =>
      ∫ y : Fin q → ℝ, if Function.Injective y then ψ y else 0
        ∂Measure.pi (fun _ : Fin q => ξ.measure)) target.law)
    (a b C : ℝ) (hC : 0 ≤ C) (hbound : ∀ y, |φ y - ψ y| ≤ C)
    (hφ : ∀ y, (¬ ∀ j, y j ∈ Set.Icc a b) → φ y = 0)
    (hψ : ∀ y, (¬ ∀ j, y j ∈ Set.Icc a b) → ψ y = 0) :
    |target.factorialExpectation q φ - target.factorialExpectation q ψ| ≤
      C * ∫ ξ, (ξ.measure (Set.Icc a b)).toReal ^ q ∂target.law := by
  unfold TargetProcess.factorialExpectation
  rw [← integral_sub hφi hψi, ← integral_const_mul]
  apply abs_integral_le_integral_abs.trans
  apply integral_mono_ae (hφi.sub hψi).abs
    ((target.count_moments_integrable a b q).const_mul C)
  filter_upwards [target.simple] with ξ hξ
  exact ξ.abs_sub_factorial_integral_le_count_pow hξ φ ψ a b C hC hbound hφ hψ

end BourgadeHuang
