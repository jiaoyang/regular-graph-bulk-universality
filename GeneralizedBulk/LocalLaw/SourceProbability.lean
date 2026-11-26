import SpectralConsequences.FullPaperTheorems
import LocalLaw.SourceTheorem42
import GeneralizedBulk.Graph.UniformSwitching

/-!
Unconditioning the checked local-law source on the genuine uniform ensemble.

The source spectral conclusions use the structural conditional law. Here a
fixed admissible structural scale is chosen, its complement is bounded by an
actual polynomial using the proved cycle and bicyclic-pattern counts, and
the conditional spectral conclusions are transferred to uniform graphs.
These statements retain the source's normalized adjacency and predicates;
they are not yet constructors of the bulk project's four HY records.
-/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology

namespace GeneralizedBulk.LocalLawBridge
open LocalLaw SpectralConsequences
local instance sourceProbabilityDecidable (p : Prop) : Decidable p := Classical.propDecidable p

private theorem uniform_eventMass_le_one {X : Type*} [Fintype X] [Nonempty X]
    (A : X → Prop) : eventMass (finiteUniformWeight X) A ≤ 1 := by
  apply (eventMass_mono _ finiteUniformWeight_nonneg (fun _ _ => True.intro)).trans
  simpa only [eventMass, if_true] using (finiteUniformWeight_total (Γ := X)).le

/-- The loss in removing conditioning is the actual structural complement.
The positive denominator premise excludes the totalized zero-ratio case. -/
theorem unconditional_failure_le_of_conditional {X : Type*} [Fintype X] [Nonempty X]
    (A F : X → Prop) (δ : ℝ) (hδ : 0 ≤ δ)
    (hA : 0 < eventMass (finiteUniformWeight X) A)
    (hconditional : eventMass (finiteUniformWeight X) (fun x => A x ∧ F x) /
      eventMass (finiteUniformWeight X) A ≤ δ) :
    eventMass (finiteUniformWeight X) F ≤
      eventMass (finiteUniformWeight X) (fun x => ¬A x) + δ := by
  classical
  have hnum := (div_le_iff₀ hA).mp hconditional
  have hnum' : eventMass (finiteUniformWeight X) (fun x => A x ∧ F x) ≤ δ :=
    hnum.trans ((mul_le_mul_of_nonneg_left (uniform_eventMass_le_one A) hδ).trans_eq
      (mul_one δ))
  have hcover : ∀ x, F x → ¬A x ∨ (A x ∧ F x) := by
    intro x hx
    by_cases ha : A x
    · exact Or.inr ⟨ha,hx⟩
    · exact Or.inl ha
  exact ((eventMass_mono _ finiteUniformWeight_nonneg hcover).trans
    (eventMass_union_le _ finiteUniformWeight_nonneg _ _)).trans
      (add_le_add_left hnum' _)

/-- Polynomial control of the complement of a fixed genuine structural event.
The estimate uses the original uniform ensemble, with no local-law premise. -/
theorem eventually_structural_failure_polynomial (d ω : ℕ) (hd : 3 ≤ d) (hω : 1 ≤ ω) :
    ∀ᶠ N : ℕ in atTop,
      eventMass (LocalLaw.RegularGraph.weight (N := N) (d := d))
        (fun g => ¬LocalLaw.RegularGraph.structural
          (logarithmicRadius ((1/4 : ℝ)/4) d N) ω ⌊(N : ℝ)^(1/4 : ℝ)⌋₊ g) ≤
        2*(N : ℝ)^(-(1/32 : ℝ)) := by
  classical
  let c : ℝ := 1/4
  let ρ := structuralRadiusCoefficient d c
  have hk : (1 : ℝ) < ((d-1 : ℕ) : ℝ) := by exact_mod_cast (show 1 < d-1 by omega)
  have hρ : 0 ≤ ρ := div_nonneg (by norm_num [c]) (Real.log_pos hk).le
  have hbudget₁ := eventually_pattern_switching_budget d (2*ρ) 1 (by omega)
    (by positivity) (by norm_num)
  have hbudget₂ := eventually_pattern_switching_budget d (4*ρ) 2 (by omega)
    (by positivity) (by norm_num)
  have hsmall₁ := eventually_const_mul_log_rpow_le (badCenterMomentConstant d c)
    2 (1/32) (by norm_num)
  have hsmall₂ := eventually_const_mul_log_rpow_le (bicyclicFamilyConstant d c)
    7 (23/32) (by norm_num)
  filter_upwards [hbudget₁,hbudget₂,hsmall₁,hsmall₂,eventually_log_ge_nat 1,
    Filter.eventually_ge_atTop 1] with N hbudget₁ hbudget₂ hsmall₁ hsmall₂ hlog hN
  let R := logarithmicRadius (c/4) d N
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hr : (R : ℝ) ≤ ρ*Real.log (N : ℝ) :=
    structuralRadius_le_log d N c hd (by norm_num [c]) hN
  have hK₁ : ((2*R+1 : ℕ) : ℝ) ≤ 2*ρ*Real.log (N : ℝ)+1 := by
    push_cast
    linarith
  have hK₂ : ((4*R+2 : ℕ) : ℝ) ≤ 4*ρ*Real.log (N : ℝ)+2 := by
    push_cast
    linarith
  have hball := LocalLaw.RegularGraph.ball_excess_two_mass_bound R
    (by omega : 0 < N) (by omega : 2 ≤ d) (hbudget₂ _ hK₂)
  have hbad := LocalLaw.RegularGraph.badCenters_strict_tail_bound R (2*R+1) hd le_rfl
    (by omega : 0 < N) (hbudget₁ _ hK₁) ((N : ℝ)^c) (Real.rpow_pos_of_pos hn c)
  have hnum₁ := badCenter_numerator_bound d N c hd (by norm_num [c]) hN hlog
  have hnum₂ := bicyclic_family_numerator_bound d N c hd (by norm_num [c]) hN hlog
  have hs₁ : badCenterMomentConstant d c * Real.log (N : ℝ)^2 ≤ (N : ℝ)^(1/32 : ℝ) := by
    simpa only [Real.rpow_two] using hsmall₁
  have hs₂ : bicyclicFamilyConstant d c * Real.log (N : ℝ)^7 ≤ (N : ℝ)^(23/32 : ℝ) := by
    rw [show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num,Real.rpow_natCast] at hsmall₂
    exact hsmall₂
  have hbad' : eventMass (LocalLaw.RegularGraph.weight (N := N) (d := d))
      (fun g => (N : ℝ)^c < ((nonTreeCenters g.graph R).card : ℝ)) ≤
      (N : ℝ)^(-(1/32 : ℝ)) := by
    apply hbad.trans
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hn c)).mpr
    calc
      _ ≤ badCenterMomentConstant d c * Real.log (N : ℝ)^2 * (N : ℝ)^(3*c/4) := hnum₁
      _ ≤ (N : ℝ)^(1/32 : ℝ) * (N : ℝ)^(3*c/4) :=
        mul_le_mul_of_nonneg_right hs₁ (Real.rpow_nonneg hn.le _)
      _ = (N : ℝ)^(-(1/32 : ℝ)) * (N : ℝ)^c := by
        rw [← Real.rpow_add hn, ← Real.rpow_add hn]
        norm_num [c]
  have hball' : eventMass (LocalLaw.RegularGraph.weight (N := N) (d := d))
      (fun g => ∃ o, 2 ≤ graphBallExcess g.graph o R) ≤
      (N : ℝ)^(-(1/32 : ℝ)) := by
    apply hball.trans
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hn).mpr
    calc
      _ ≤ bicyclicFamilyConstant d c * Real.log (N : ℝ)^7 * (N : ℝ)^c := hnum₂
      _ ≤ (N : ℝ)^(23/32 : ℝ) * (N : ℝ)^c :=
        mul_le_mul_of_nonneg_right hs₂ (Real.rpow_nonneg hn.le _)
      _ = (N : ℝ)^(-(1/32 : ℝ)) * (N : ℝ) := by
        calc
          _ = (N : ℝ)^(-(1/32 : ℝ)+1) := by rw [← Real.rpow_add hn]; norm_num [c]
          _ = _ := by rw [Real.rpow_add hn,Real.rpow_one]
  have hcover : ∀ g : LocalLaw.RegularGraph N d,
      ¬LocalLaw.RegularGraph.structural R ω ⌊(N : ℝ)^c⌋₊ g →
      (∃ o, 2 ≤ graphBallExcess g.graph o R) ∨
        (N : ℝ)^c < ((nonTreeCenters g.graph R).card : ℝ) := by
    intro g hnot
    by_cases hex : ∃ o, 2 ≤ graphBallExcess g.graph o R
    · exact Or.inl hex
    · right
      by_cases hle : ((nonTreeCenters g.graph R).card : ℝ) ≤ (N : ℝ)^c
      · exact False.elim (hnot ⟨fun o => (show graphBallExcess g.graph o R ≤ 1 by
          have hh : ¬2 ≤ graphBallExcess g.graph o R := fun h => hex ⟨o,h⟩
          omega).trans hω,(Nat.le_floor_iff (Real.rpow_nonneg hn.le c)).mpr hle⟩)
      · exact lt_of_not_ge hle
  have h := ((eventMass_mono _ LocalLaw.RegularGraph.weight_nonnegative hcover).trans
    (eventMass_union_le _ LocalLaw.RegularGraph.weight_nonnegative _ _)).trans
      (add_le_add hball' hbad')
  simpa only [c,R,two_mul] using h

/-- A polynomial conditional failure bound on the chosen source structural
event gives an unconditional polynomial bound on the original ensemble. -/
theorem eventually_unconditional_of_structural_conditional (d ω : ℕ)
    (hd : 3 ≤ d) (hω : 1 ≤ ω)
    (F : ∀ N, LocalLaw.RegularGraph N d → Prop)
    (hconditional : ∀ᶠ N : ℕ in atTop, Nonempty (LocalLaw.RegularGraph N d) →
      eventMass (LocalLaw.RegularGraph.weight (N := N) (d := d)) (fun g =>
        LocalLaw.RegularGraph.structural (logarithmicRadius ((1/4 : ℝ)/4) d N)
          ω ⌊(N : ℝ)^(1/4 : ℝ)⌋₊ g ∧ F N g) /
        eventMass (LocalLaw.RegularGraph.weight (N := N) (d := d))
          (LocalLaw.RegularGraph.structural (logarithmicRadius ((1/4 : ℝ)/4) d N)
            ω ⌊(N : ℝ)^(1/4 : ℝ)⌋₊) ≤ 1/(N : ℝ)) :
    ∀ᶠ N : ℕ in atTop, Nonempty (LocalLaw.RegularGraph N d) →
      eventMass (LocalLaw.RegularGraph.weight (N := N) (d := d)) (F N) ≤
        3*(N : ℝ)^(-(1/32 : ℝ)) := by
  filter_upwards [hconditional,eventually_structural_failure_polynomial d ω hd hω,
    eventually_original_structural_mass_half d ω (1/4) hd hω (by norm_num) (by norm_num),
    Filter.eventually_ge_atTop 1] with N hconditional hstruct hmass hN
  intro hnonempty
  letI := hnonempty
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmasspos : 0 < eventMass (LocalLaw.RegularGraph.weight (N := N) (d := d))
      (LocalLaw.RegularGraph.structural (logarithmicRadius ((1/4 : ℝ)/4) d N)
        ω ⌊(N : ℝ)^(1/4 : ℝ)⌋₊) := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/2) (hmass hnonempty)
  have hbound := unconditional_failure_le_of_conditional
    (LocalLaw.RegularGraph.structural (logarithmicRadius ((1/4 : ℝ)/4) d N)
      ω ⌊(N : ℝ)^(1/4 : ℝ)⌋₊) (F N) (1/(N : ℝ)) (by positivity)
    hmasspos (hconditional hnonempty)
  have hinv : 1/(N : ℝ) ≤ (N : ℝ)^(-(1/32 : ℝ)) := by
    rw [one_div,← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by norm_num)
  exact (hbound.trans (add_le_add hstruct hinv)).trans_eq (by ring)

/-- The actual source weak-rigidity predicate now holds under unconditioned
uniform regular graphs, with a proved positive rate and polynomial failure. -/
theorem uniform_source_weak_rigidity (d : ℕ) (hd : 3 ≤ d) :
    ∃ α : ℝ, 0 < α ∧ ∀ᶠ N : ℕ in atTop,
      Nonempty (LocalLaw.RegularGraph N d) →
        eventMass (LocalLaw.RegularGraph.weight (N := N) (d := d))
          (fun g => ¬PaperRigid hd α g) ≤ 3*(N : ℝ)^(-(1/32 : ℝ)) := by
  obtain ⟨α,hα,hprob⟩ := paper_theorem_1_2 d (finiteOmega d) (1/4) hd
    (finiteOmega_positive d hd) le_rfl (by norm_num) (by norm_num)
  refine ⟨α,hα,?_⟩
  apply eventually_unconditional_of_structural_conditional d (finiteOmega d) hd
    (finiteOmega_positive d hd) (fun _ g => ¬PaperRigid hd α g)
  simpa only [Real.rpow_one] using hprob 1

/-- The source homogeneous bound covers every vector in every complex
eigenspace under the original, unconditioned uniform graph ensemble. -/
theorem uniform_source_all_eigenvectors (d : ℕ) (hd : 3 ≤ d) :
    ∀ᶠ N : ℕ in atTop, Nonempty (LocalLaw.RegularGraph N d) →
      eventMass (LocalLaw.RegularGraph.weight (N := N) (d := d))
        (fun g => ¬PaperAllEigenvectors g) ≤ 3*(N : ℝ)^(-(1/32 : ℝ)) := by
  apply eventually_unconditional_of_structural_conditional d (finiteOmega d) hd
    (finiteOmega_positive d hd) (fun _ g => ¬PaperAllEigenvectors g)
  simpa only [Real.rpow_one] using paper_theorem_1_4_all_eigenvectors d (finiteOmega d)
    (1/4) hd (finiteOmega_positive d hd) le_rfl (by norm_num) (by norm_num) 1

/-- The checked source entrywise and averaged local law also holds on the
unconditioned ensemble, at fixed legal source parameters. -/
theorem uniform_source_local_law (d : ℕ) (hd : 3 ≤ d) :
    ∀ᶠ N : ℕ in atTop, Nonempty (LocalLaw.RegularGraph N d) →
      eventMass (LocalLaw.RegularGraph.weight (N := N) (d := d))
        (fun g => ¬∀ z : ℂ, 0 < z.im → Real.log (N : ℝ)^(300 : ℝ)/(N : ℝ) ≤ z.im →
          RealSourceLocalLawAt (by omega) 12 (logarithmicRadius (1/128) d N)
            (sourceUniformLawConstant d) z g) ≤ 3*(N : ℝ)^(-(1/32 : ℝ)) := by
  apply eventually_unconditional_of_structural_conditional d (finiteOmega d) hd
    (finiteOmega_positive d hd)
  simpa only [pow_one] using source_theorem_4_2 d 12 300 (1/4) (1/128) hd
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 1

/-- The structural event and the actual source local law hold together on
one unconditional polynomial-probability event. -/
theorem uniform_source_structural_local_law (d : ℕ) (hd : 3 ≤ d) :
    ∀ᶠ N : ℕ in atTop, Nonempty (LocalLaw.RegularGraph N d) →
      eventMass (LocalLaw.RegularGraph.weight (N := N) (d := d))
        (fun g => ¬(LocalLaw.RegularGraph.structural
          (logarithmicRadius ((1/4 : ℝ)/4) d N) (finiteOmega d)
            ⌊(N : ℝ)^(1/4 : ℝ)⌋₊ g ∧ SourceLocalLawGood g (by omega) (1/128))) ≤
        3*(N : ℝ)^(-(1/32 : ℝ)) := by
  apply eventually_unconditional_of_structural_conditional d (finiteOmega d) hd
    (finiteOmega_positive d hd)
  filter_upwards [source_theorem_4_2 d 12 300 (1/4) (1/128) hd
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 1]
    with N hprob
  intro hnonempty
  have heq : (fun g : LocalLaw.RegularGraph N d =>
      LocalLaw.RegularGraph.structural (logarithmicRadius ((1/4 : ℝ)/4) d N)
        (finiteOmega d) ⌊(N : ℝ)^(1/4 : ℝ)⌋₊ g ∧
          ¬(LocalLaw.RegularGraph.structural (logarithmicRadius ((1/4 : ℝ)/4) d N)
            (finiteOmega d) ⌊(N : ℝ)^(1/4 : ℝ)⌋₊ g ∧ SourceLocalLawGood g (by omega) (1/128))) =
      (fun g => LocalLaw.RegularGraph.structural (logarithmicRadius ((1/4 : ℝ)/4) d N)
        (finiteOmega d) ⌊(N : ℝ)^(1/4 : ℝ)⌋₊ g ∧
          ¬∀ z : ℂ, 0 < z.im → Real.log (N : ℝ)^(300 : ℝ)/(N : ℝ) ≤ z.im →
            RealSourceLocalLawAt (by omega) 12 (logarithmicRadius (1/128) d N)
              (sourceUniformLawConstant d) z g) := by
    funext g
    apply propext
    rw [show (300 : ℝ) = ((300 : ℕ) : ℝ) by norm_num,Real.rpow_natCast]
    simp only [SourceLocalLawGood]
    tauto
  rw [heq]
  simpa only [pow_one] using hprob hnonempty

/-- The finite source weights and the bulk project's actual uniform measure
give the same probability to every predicate. -/
theorem finiteUniform_real_eq_eventMass {X : Type*} [Fintype X]
    [MeasurableSpace X] [MeasurableSingletonClass X] (A : X → Prop) :
    (GeneralizedBulk.Graph.finiteUniform X {x | A x}).toReal =
      eventMass (finiteUniformWeight X) A := by
  classical
  have hset : {x | A x} = (Finset.univ.filter A : Set X) := by ext x; simp
  rw [hset,GeneralizedBulk.Graph.finiteUniform_finset_toReal]
  simp only [eventMass,finiteUniformWeight,← Finset.sum_filter,Finset.sum_const,
    nsmul_eq_mul,div_eq_mul_inv,one_mul]

/-- In particular, the two independently defined regular-graph uniform laws
agree exactly on all source predicates. -/
theorem regularGraphLaw_real_eq_eventMass (N d : ℕ)
    (A : LocalLaw.RegularGraph N d → Prop) :
    (GeneralizedBulk.Graph.regularGraphLaw N d {g | A g}).toReal =
      eventMass (LocalLaw.RegularGraph.weight (N := N) (d := d)) A := by
  exact finiteUniform_real_eq_eventMass (X := GeneralizedBulk.Graph.RegularGraph N d) A

/-- Weak source rigidity as a probability for the bulk project's graph law. -/
theorem regularGraphLaw_source_weak_rigidity (d : ℕ) (hd : 3 ≤ d) :
    ∃ α : ℝ, 0 < α ∧ ∀ᶠ N : ℕ in atTop,
      Nonempty (LocalLaw.RegularGraph N d) →
        (GeneralizedBulk.Graph.regularGraphLaw N d {g | ¬PaperRigid hd α g}).toReal ≤
          3*(N : ℝ)^(-(1/32 : ℝ)) := by
  obtain ⟨α,hα,hprob⟩ := uniform_source_weak_rigidity d hd
  refine ⟨α,hα,?_⟩
  simpa only [regularGraphLaw_real_eq_eventMass] using hprob

/-- All source eigenvector bounds as probabilities for the bulk graph law. -/
theorem regularGraphLaw_source_all_eigenvectors (d : ℕ) (hd : 3 ≤ d) :
    ∀ᶠ N : ℕ in atTop, Nonempty (LocalLaw.RegularGraph N d) →
      (GeneralizedBulk.Graph.regularGraphLaw N d {g | ¬PaperAllEigenvectors g}).toReal ≤
        3*(N : ℝ)^(-(1/32 : ℝ)) := by
  simpa only [regularGraphLaw_real_eq_eventMass] using uniform_source_all_eigenvectors d hd

/-- The source local law as a probability for the bulk project's graph law. -/
theorem regularGraphLaw_source_local_law (d : ℕ) (hd : 3 ≤ d) :
    ∀ᶠ N : ℕ in atTop, Nonempty (LocalLaw.RegularGraph N d) →
      (GeneralizedBulk.Graph.regularGraphLaw N d {g | ¬∀ z : ℂ, 0 < z.im →
        Real.log (N : ℝ)^(300 : ℝ)/(N : ℝ) ≤ z.im →
        RealSourceLocalLawAt (by omega) 12 (logarithmicRadius (1/128) d N)
          (sourceUniformLawConstant d) z g}).toReal ≤ 3*(N : ℝ)^(-(1/32 : ℝ)) := by
  simpa only [regularGraphLaw_real_eq_eventMass] using uniform_source_local_law d hd

/-- The simultaneous structural/local-law event for the bulk graph law. -/
theorem regularGraphLaw_source_structural_local_law (d : ℕ) (hd : 3 ≤ d) :
    ∀ᶠ N : ℕ in atTop, Nonempty (LocalLaw.RegularGraph N d) →
      (GeneralizedBulk.Graph.regularGraphLaw N d {g | ¬(LocalLaw.RegularGraph.structural
        (logarithmicRadius ((1/4 : ℝ)/4) d N) (finiteOmega d)
          ⌊(N : ℝ)^(1/4 : ℝ)⌋₊ g ∧ SourceLocalLawGood g (by omega) (1/128))}).toReal ≤
        3*(N : ℝ)^(-(1/32 : ℝ)) := by
  simpa only [regularGraphLaw_real_eq_eventMass] using uniform_source_structural_local_law d hd

end GeneralizedBulk.LocalLawBridge
