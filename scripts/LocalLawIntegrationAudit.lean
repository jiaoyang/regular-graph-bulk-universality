import GeneralizedBulk
import LocalLaw.Main
import SpectralConsequences.Main

/-! Audit exact source constructors and article endpoints. No BS/HY or
substitute Gaussianity/moment estimate may occur in the final theorem types.
Generic intermediate theorems remain available with their original inputs. -/
open Lean Elab Command

run_cmd do
  let inputs : Array Name := #[
    ``GeneralizedBulk.External.HYCoarseInput,
    ``GeneralizedBulk.External.HYMesoscopicInput,
    ``GeneralizedBulk.External.HYLocalStarInput,
    ``GeneralizedBulk.External.HYGeometryInput,
    ``GeneralizedBulk.External.BSQualitativeInput]
  let substitutes : Array Name := #[
    `GaussianWave.UniformBSOn, `GaussianWave.BSJointClassification,
    `GaussianWave.CenteredGaussianLaw,
    `GeneralizedBulk.External.CenteredGaussianLaw,
    `GaussianWave.RegularEigenData.OneEdgeQuadraticBound,
    `GaussianWave.TightInProbability,
    `SpectralConsequences.PaperRigid,
    `SpectralConsequences.PaperAllEigenvectors,
    `SpectralConsequences.SourceLocalLawGood,
    `LocalLaw.RealSourceLocalLawAt]
  let forbidden := inputs ++ substitutes
  let sourceEndpoints : Array Name := #[
    ``LocalLaw.source_theorem_4_2,
    ``SpectralConsequences.full_paper_theorem_1_2,
    ``SpectralConsequences.full_paper_theorem_1_4,
    ``GeneralizedBulk.LocalLawBridge.regularGraphLaw_source_weak_rigidity,
    ``GeneralizedBulk.LocalLawBridge.regularGraphLaw_source_all_eigenvectors,
    ``GeneralizedBulk.LocalLawBridge.regularGraphLaw_source_local_law,
    ``GeneralizedBulk.LocalLawBridge.regularGraphLaw_source_structural_local_law,
    ``GeneralizedBulk.External.RegularSpectralData.resolvent_eq_localLaw_green,
    ``GeneralizedBulk.External.RegularSpectralData.scalarResolvent_eq_localLaw_transform,
    ``GeneralizedBulk.External.RegularSpectralData.delocalization_of_localLaw]
  for endpoint in sourceEndpoints do
    let info ← getConstInfo endpoint
    unless info.isTheorem do
      throwError "Expected proved theorem: {endpoint}"
    for input in inputs do
      if (info.type.find? (·.isConstOf input)).isSome then
        throwError "Source/adapter theorem assumes a BS/HY record: {endpoint}: {input}"
    logInfo m!"Source/adapter theorem has no BS/HY-record premise: {endpoint}"
  let constructors : Array (Name × Name) := #[
    (`GeneralizedBulk.External.RegularSpectralData.provedHYCoarseInput,
      ``GeneralizedBulk.External.HYCoarseInput),
    (`GeneralizedBulk.External.RegularSpectralData.provedHYLocalStarInput,
      ``GeneralizedBulk.External.HYLocalStarInput),
    (`GeneralizedBulk.External.RegularSpectralData.provedHYMesoscopicInput,
      ``GeneralizedBulk.External.HYMesoscopicInput),
    (`GeneralizedBulk.External.RegularSpectralData.provedHYGeometryInput,
      ``GeneralizedBulk.External.HYGeometryInput)]
  for (name, expected) in constructors do
    let info ← getConstInfo name
    let mut target := info.type
    while target.isForall do
      let .forallE _ domain body _ := target | throwError "Expected a forall binder"
      for input in forbidden do
        if (domain.find? (·.isConstOf input)).isSome then
          throwError "Proved constructor assumes a substitute estimate: {name}: {input}"
      target := body
    unless target.getAppFn.isConstOf expected do
      throwError "Constructor does not produce its exact original HY record: {name}"
    logInfo m!"Exact proved constructor has no BS/HY/substitute estimate premise: {name} -> {expected}"
  let endpoints : Array Name := #[
    `GeneralizedBulk.External.RegularSpectralData.bulk_universality,
    `GeneralizedBulk.Graph.uniform_regular_graph_bulk_universality,
    `GeneralizedBulk.Graph.uniform_graph_star_wasserstein,
    `GeneralizedBulk.Graph.uniform_root_fourth_probability,
    `GeneralizedBulk.Graph.uniform_graph_mixed_fourth]
  for endpoint in endpoints do
    let info ← getConstInfo endpoint
    unless info.isTheorem do
      throwError "Expected proved article endpoint: {endpoint}"
    for input in forbidden do
      if (info.type.find? (·.isConstOf input)).isSome then
        throwError "Article endpoint retains BS/HY/substitute estimate: {endpoint}: {input}"
    logInfo m!"Article endpoint type contains no BS/HY/substitute estimate: {endpoint}"

#print axioms GeneralizedBulk.External.RegularSpectralData.provedHYCoarseInput
#print axioms GeneralizedBulk.External.RegularSpectralData.provedHYLocalStarInput
#print axioms GeneralizedBulk.External.RegularSpectralData.provedHYMesoscopicInput
#print axioms GeneralizedBulk.External.RegularSpectralData.provedHYGeometryInput
#print axioms GeneralizedBulk.External.RegularSpectralData.bulk_universality
#print axioms GeneralizedBulk.Graph.uniform_regular_graph_bulk_universality
#print axioms GeneralizedBulk.Graph.uniform_graph_star_wasserstein
#print axioms GeneralizedBulk.Graph.uniform_root_fourth_probability
#print axioms GeneralizedBulk.Graph.uniform_graph_mixed_fourth

#check GeneralizedBulk.External.RegularSpectralData.bulk_universality
#check GeneralizedBulk.Graph.uniform_regular_graph_bulk_universality
#check GeneralizedBulk.Graph.uniform_graph_star_wasserstein
#check GeneralizedBulk.Graph.uniform_graph_mixed_fourth
