import Mathlib.MeasureTheory.Constructions.Projective

/-! Finite-dimensional laws determine actual function-space laws, including
a jointly retained base variable and an arbitrarily indexed field. -/
noncomputable section
open MeasureTheory
namespace GeneralizedBulk.Analysis
universe u

theorem measure_pi_eq_of_finite_marginals {ι : Type*} {Y : ι → Type*}
    [∀ i,MeasurableSpace (Y i)] (μ ν : Measure (∀ i,Y i)) [IsFiniteMeasure μ]
    (h : ∀ I : Finset ι,μ.map I.restrict=ν.map I.restrict) : μ=ν := by
  exact IsProjectiveLimit.unique (μ := μ) (ν := ν) (P := fun I : Finset ι => μ.map I.restrict)
    (fun I => rfl) (fun I => (h I).symm)

theorem measure_prod_pi_eq_of_finite_marginals {ι : Type*} {X : Type u} {Y : ι → Type u}
    [MeasurableSpace X] [∀ i,MeasurableSpace (Y i)]
    (μ ν : Measure (X × (∀ i,Y i))) [IsFiniteMeasure μ]
    (h : ∀ I : Finset ι,μ.map (fun z => (z.1,I.restrict z.2))=
      ν.map (fun z => (z.1,I.restrict z.2))) : μ=ν := by
  classical
  let A : Option ι → Type _ := fun o => o.elim X Y
  let spaces := fun i => (inferInstance : MeasurableSpace (Y i))
  let baseSpace := (inferInstance : MeasurableSpace X)
  letI (o : Option ι) : MeasurableSpace (A o) := by
    cases o with
    | none => exact baseSpace
    | some i => exact spaces i
  let encode : (X × (∀ i,Y i)) → (∀ o,A o) := fun z o =>
    match o with | none => z.1 | some i => z.2 i
  let decode : (∀ o,A o) → X × (∀ i,Y i) := fun z => (z none,fun i => z (some i))
  have hencode : Measurable encode := by
    apply measurable_pi_lambda
    intro o
    cases o with
    | none => exact measurable_fst
    | some i => exact (measurable_pi_apply i).comp measurable_snd
  have hdecode : Measurable decode := (measurable_pi_apply none).prodMk
    (measurable_pi_lambda _ (fun i => measurable_pi_apply (some i)))
  have hinverse : decode ∘ encode=id := by funext z; rfl
  have hencoded : μ.map encode=ν.map encode := by
    apply measure_pi_eq_of_finite_marginals
    intro I
    let S := I.eraseNone
    let project := fun z : X × (∀ i,Y i) => (z.1,S.restrict z.2)
    let finish : (X × (∀ i : S,Y i)) → (∀ j : I,A j.val) := fun z j =>
      match j with
      | ⟨none,hj⟩ => z.1
      | ⟨some i,hj⟩ => z.2 ⟨i,Finset.mem_eraseNone.mpr hj⟩
    have hp : Measurable project := measurable_fst.prodMk
      (measurable_pi_lambda _ (fun i => (measurable_pi_apply i.val).comp measurable_snd))
    have hf : Measurable finish := by
      apply measurable_pi_lambda
      rintro ⟨o,ho⟩
      cases o with
      | none => exact measurable_fst
      | some i => exact (measurable_pi_apply
          (⟨i,Finset.mem_eraseNone.mpr ho⟩ : S)).comp measurable_snd
    have hr : Measurable (fun z : ∀ o,A o => I.restrict z) :=
      measurable_pi_lambda _ (fun i => measurable_pi_apply i.val)
    have hfactor : I.restrict ∘ encode=finish ∘ project := by
      funext z j
      rcases j with ⟨o,ho⟩
      cases o <;> rfl
    simp only [Measure.map_map hr hencode]
    rw [hfactor,← Measure.map_map hf hp,← Measure.map_map hf hp,h S]
  have hh := congrArg (Measure.map decode) hencoded
  simpa only [Measure.map_map hdecode hencode,hinverse,Measure.map_id] using hh

theorem measure_prod_pi_eq_of_finite_joint_marginals {ι : Type*}
    {X Y : ι → Type*} [∀ i,MeasurableSpace (X i)] [∀ i,MeasurableSpace (Y i)]
    (μ ν : Measure ((∀ i,X i) × (∀ i,Y i))) [IsFiniteMeasure μ]
    (h : ∀ I : Finset ι,
      μ.map (fun z => fun i : I => (z.1 i,z.2 i)) =
      ν.map (fun z => fun i : I => (z.1 i,z.2 i))) : μ=ν := by
  let encode : ((∀ i,X i) × (∀ i,Y i)) → (∀ i,X i × Y i) :=
    fun z i => (z.1 i,z.2 i)
  let decode : (∀ i,X i × Y i) → ((∀ i,X i) × (∀ i,Y i)) :=
    fun z => (fun i => (z i).1,fun i => (z i).2)
  have he : Measurable encode := measurable_pi_lambda _ (fun i =>
    ((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd))
  have hd : Measurable decode :=
    (measurable_pi_lambda _ (fun i => measurable_fst.comp (measurable_pi_apply i))).prodMk
      (measurable_pi_lambda _ (fun i => measurable_snd.comp (measurable_pi_apply i)))
  have hh : μ.map encode=ν.map encode := by
    apply measure_pi_eq_of_finite_marginals
    intro I
    have hr : Measurable (fun z : ∀ i,X i × Y i => I.restrict z) :=
      measurable_pi_lambda _ (fun i => measurable_pi_apply i.val)
    simpa only [Measure.map_map hr he] using h I
  have hinverse : decode ∘ encode=id := by funext z; rfl
  have hh' := congrArg (Measure.map decode) hh
  simpa only [Measure.map_map hd he,hinverse,Measure.map_id] using hh'

end GeneralizedBulk.Analysis
