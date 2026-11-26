import GaussianWave.Compactness

/-!
# Countable compact-state projective extension

An actual consistent family of finite laws has an actual whole-process law.
The proof uses padded finite laws, compactness of probability laws, and
continuity of finite restrictions. No process existence assertion is assumed.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology Classical
namespace GaussianWave.BS

def finiteRestriction {I A : Type*} (S : Finset I) (x : I → A) : S → A :=
  fun i => x i.val

def finiteSubrestriction {I A : Type*} {S T : Finset I} (h : S ⊆ T) (x : T → A) : S → A :=
  fun i => x ⟨i.val, h i.property⟩

def finitePadding {I A : Type*} [Inhabited A] (S : Finset I) (x : S → A) : I → A :=
  fun i => if h : i ∈ S then x ⟨i, h⟩ else default

theorem continuous_finitePadding {I A : Type*} [TopologicalSpace A] [Inhabited A] (S : Finset I) :
    Continuous (finitePadding (A := A) S) := by
  apply continuous_pi
  intro i
  by_cases h : i ∈ S
  · simpa only [finitePadding, dif_pos h] using continuous_apply (⟨i, h⟩ : S)
  · simpa only [finitePadding, dif_neg h] using
      (continuous_const : Continuous (fun _ : S → A => (default : A)))

def encodedExhaustion (I : Type*) [Encodable I] (n : ℕ) : Finset I :=
  (Finset.range (n + 1)).preimage Encodable.encode
    (fun _ _ _ _ h => Encodable.encode_injective h)

@[simp] theorem mem_encodedExhaustion {I : Type*} [Encodable I] (i : I) (n : ℕ) :
    i ∈ encodedExhaustion I n ↔ Encodable.encode i ≤ n := by
  simp only [encodedExhaustion, Finset.mem_preimage, Finset.mem_range, Nat.lt_succ_iff]

theorem eventually_subset_encodedExhaustion {I : Type*} [Encodable I] (S : Finset I) :
    ∀ᶠ n in atTop, S ⊆ encodedExhaustion I n := by
  refine (eventually_all_finset S).mpr ?_
  intro i hi
  filter_upwards [eventually_ge_atTop (Encodable.encode i)] with n hn
  exact (mem_encodedExhaustion i n).mpr hn

/-- Countable-state-index Kolmogorov extension for compact metric values,
proved directly for the actual finite marginal family. -/
theorem exists_processLaw_of_compact_finite_marginals
    {I A : Type*} [Countable I] [MetricSpace A] [CompactSpace A]
    [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A] [Inhabited A]
    (P : ∀ S : Finset I, ProbabilityMeasure (S → A))
    (hP : ∀ (S T : Finset I) (h : S ⊆ T),
      Measure.map (finiteSubrestriction (A := A) h) (P T : Measure (T → A)) =
        (P S : Measure (S → A))) :
    ∃ Q : ProbabilityMeasure (I → A), ∀ S : Finset I,
      Measure.map (finiteRestriction (A := A) S) (Q : Measure (I → A)) = (P S : Measure (S → A)) := by
  letI : Encodable I := Encodable.ofCountable I
  letI : MetricSpace (I → A) := TopologicalSpace.metrizableSpaceMetric (I → A)
  let S := encodedExhaustion I
  let laws : ℕ → ProbabilityMeasure (I → A) := fun n =>
    (P (S n)).map (continuous_finitePadding (A := A) (S n)).measurable.aemeasurable
  obtain ⟨Q, r, hr, hconv⟩ := compact_probability_laws_subsequence laws
  refine ⟨Q, ?_⟩
  intro T
  have hTcont : Continuous (finiteRestriction (A := A) T) :=
    continuous_pi (fun i => continuous_apply i.val)
  have hmarg : ∀ᶠ n in atTop,
      Measure.map (finiteRestriction (A := A) T) (laws (r n) : Measure (I → A)) =
        (P T : Measure (T → A)) := by
    filter_upwards [hr.tendsto_atTop.eventually (eventually_subset_encodedExhaustion T)] with n hn
    change Measure.map (finiteRestriction (A := A) T)
      (Measure.map (finitePadding (A := A) (S (r n))) (P (S (r n)) : Measure (S (r n) → A))) = _
    rw [Measure.map_map hTcont.measurable (continuous_finitePadding (A := A) (S (r n))).measurable]
    have he : finiteRestriction (A := A) T ∘ finitePadding (A := A) (S (r n)) =
        finiteSubrestriction (A := A) hn := by
      funext x i
      dsimp only [Function.comp_apply, finiteRestriction, finitePadding, finiteSubrestriction]
      split_ifs with hi
      · rfl
      · exact False.elim (hi (hn i.property))
    rw [he]
    exact hP T (S (r n)) hn
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map hTcont.measurable.aemeasurable f.continuous.measurable.aestronglyMeasurable]
  have hweak := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hconv
    (f.compContinuous ⟨finiteRestriction (A := A) T, hTcont⟩)
  have hsame : ∀ᶠ n in atTop,
      (∫ x, f (finiteRestriction T x) ∂(laws (r n) : Measure (I → A))) =
        ∫ x, f x ∂(P T : Measure (T → A)) := by
    filter_upwards [hmarg] with n hn
    rw [← integral_map hTcont.measurable.aemeasurable
      f.continuous.measurable.aestronglyMeasurable, hn]
  exact tendsto_nhds_unique hweak (tendsto_const_nhds.congr' (hsame.mono (fun _ hx => hx.symm)))

end GaussianWave.BS
