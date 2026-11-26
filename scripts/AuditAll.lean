import GeneralizedBulk
import GaussianWave
import BourgadeHuang
import LocalLaw.Audit
import SpectralConsequences.Audit
import Lean.Util.CollectAxioms

/-! Audit every safe constant originating in any of the merged libraries or the
vendored characterization, irrespective of declaration namespace or privacy.
Source declarations are scanned separately by check_sources.py. -/
open Lean Elab Command

run_cmd do
  let roots : Array Name := #[`GeneralizedBulk, `GaussianWave, `BourgadeHuang, `LocalLaw, `SpectralConsequences]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← getEnv
  let localModule := fun m : Name => roots.any (fun root => root.isPrefixOf m)
  let localModules := env.allImportedModuleNames.filter localModule
  let mut counts : Array Nat := Array.replicate roots.size 0
  let mut theoremCounts : Array Nat := Array.replicate roots.size 0
  let mut skipped : Array Nat := Array.replicate roots.size 0
  let mut names : Array Name := #[]
  for (n, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let moduleName := env.header.moduleNames[idx.toNat]!
      for i in [:roots.size] do
        if roots[i]!.isPrefixOf moduleName then
          if !info.isUnsafe && !info.isPartial then
            names := names.push n
            counts := counts.modify i (· + 1)
            if info.isTheorem then
              theoremCounts := theoremCounts.modify i (· + 1)
          else
            skipped := skipped.modify i (· + 1)
  let collection : Lean.CollectAxioms.M Unit := names.forM Lean.CollectAxioms.collect
  let (_, state) := (collection.run env).run {}
  for a in state.axioms do
    unless allowed.contains a do
      throwError "Unexpected axiom in merged safe-constant dependencies: {a}"
  logInfo m!"Merged axiom audit passed for all {names.size} safe constants from {localModules.size} local modules."
  for i in [:roots.size] do
    logInfo m!"{roots[i]!}: {counts[i]!} safe constants ({theoremCounts[i]!} theorems); {skipped[i]!} generated implementation constants excluded."
  logInfo "Allowed foundations: propext, Classical.choice, Quot.sound."

run_cmd do
  let endpoints : Array Name := #[
    `GeneralizedBulk.External.RegularSpectralData.bulk_universality_of_HY,
    `GeneralizedBulk.External.RegularSpectralData.identify_bulk_scalar_limit_of_HY,
    `GeneralizedBulk.External.RegularSpectralData.bulk_universality_of_BS_HY,
    `GeneralizedBulk.External.RegularSpectralData.identify_bulk_scalar_limit_of_BS_HY]
  for endpoint in endpoints do
    let info ← getConstInfo endpoint
    if (info.type.find? (·.isConstOf ``GeneralizedBulk.External.BSQualitativeInput)).isSome then
      throwError "The final theorem type still contains a BSQualitativeInput hypothesis: {endpoint}"
    unless info.isTheorem do
      throwError "Expected a checked theorem at final endpoint: {endpoint}"
    logInfo m!"No BSQualitativeInput in final theorem type: {endpoint}"

run_cmd do
  let forbidden : Array Name := #[
    ``GeneralizedBulk.External.BSQualitativeInput,
    ``GeneralizedBulk.External.HYCoarseInput,
    ``GeneralizedBulk.External.HYLocalStarInput,
    ``GeneralizedBulk.External.HYMesoscopicInput,
    ``GeneralizedBulk.External.HYGeometryInput,
    `GaussianWave.UniformBSOn, `GaussianWave.BSJointClassification,
    `GaussianWave.CenteredGaussianLaw,
    `GeneralizedBulk.External.CenteredGaussianLaw,
    `GaussianWave.RegularEigenData.OneEdgeQuadraticBound,
    `GaussianWave.TightInProbability,
    `SpectralConsequences.PaperRigid, `SpectralConsequences.PaperAllEigenvectors,
    `SpectralConsequences.SourceLocalLawGood, `LocalLaw.RealSourceLocalLawAt]
  let endpoints : Array Name := #[
    `GeneralizedBulk.External.RegularSpectralData.bulk_universality,
    `GeneralizedBulk.Graph.uniform_regular_graph_bulk_universality,
    `GeneralizedBulk.Graph.uniform_graph_star_wasserstein,
    `GeneralizedBulk.Graph.uniform_root_fourth_probability,
    `GeneralizedBulk.Graph.uniform_graph_mixed_fourth,
    `GeneralizedBulk.Graph.uniform_regular_graph_bulk_universality_along_admissible_sizes,
    `GeneralizedBulk.Graph.uniform_graph_mixed_fourth_along_admissible_sizes,
    `GeneralizedBulk.Graph.article_polynomial_mixed_fourth,
    `GeneralizedBulk.Graph.regularGraph_nonempty_clique_blocks,
    `GeneralizedBulk.Graph.frequently_admissibleSize,
    `GeneralizedBulk.Graph.regularGraph_nonempty_of_arithmetic,
    `GeneralizedBulk.Graph.regularGraph_nonempty_iff_arithmetic,
    `GeneralizedBulk.Graph.admissibleSize_iff_arithmetic,
    `GeneralizedBulk.Graph.admissibleSizeFilter_eq_arithmetic,
    `GeneralizedBulk.Graph.arithmeticSizeFilter_neBot,
    `GeneralizedBulk.Graph.uniform_graph_star_wasserstein_sup,
    `GeneralizedBulk.Graph.measurable_fixedEnergyStarWassersteinSup,
    `GeneralizedBulk.Graph.fixedEnergyStarWassersteinSup_eq_zero_of_empty,
    `GeneralizedBulk.Graph.graphEigenCandidate_wassersteinTwoSquared_common_energy_le,
    `GeneralizedBulk.Graph.fixedEnergyStarWassersteinSup_le,
    `GeneralizedBulk.Graph.fixedEnergyStarWassersteinSup_lt_top,
    `GeneralizedBulk.Graph.ofReal_fixedEnergyStarWassersteinSupReal,
    `GeneralizedBulk.Graph.measurable_fixedEnergyStarWassersteinSupReal,
    `GeneralizedBulk.Graph.fixedEnergyStarWassersteinSupReal_eq_zero_of_empty,
    `GeneralizedBulk.Graph.uniform_graph_star_wasserstein_fixed_energy,
    `GeneralizedBulk.Graph.uniform_graph_star_wasserstein_fixed_energy_sup,
    `GeneralizedBulk.Graph.corollary_1_3,
    `GeneralizedBulk.Graph.corollary_1_3_real,
    `GeneralizedBulk.Graph.corollary_1_3_along_sizes,
    `GeneralizedBulk.Graph.corollary_1_3_real_along_sizes,
    `GeneralizedBulk.Graph.selected_graph_star_wasserstein,
    `GeneralizedBulk.Graph.selected_graph_star_wasserstein_common_energy]
  for endpoint in endpoints do
    let info ← getConstInfo endpoint
    unless info.isTheorem do
      throwError "Expected a checked article theorem at {endpoint}"
    for input in forbidden do
      if (info.type.find? (·.isConstOf input)).isSome then
        throwError "Unremoved BS/HY input in article theorem {endpoint}: {input}"
    logInfo m!"Complete article endpoint has no BS/HY hypothesis: {endpoint}"

#print axioms GeneralizedBulk.External.RegularSpectralData.bulk_universality_of_HY
#print axioms GeneralizedBulk.External.RegularSpectralData.identify_bulk_scalar_limit_of_HY
#print axioms GeneralizedBulk.External.RegularSpectralData.bulk_universality_of_BS_HY
#print axioms GeneralizedBulk.External.RegularSpectralData.identify_bulk_scalar_limit_of_BS_HY
#print axioms GaussianWave.BS.RRGClassificationEvents.eigenvectors_BSJointClassification
#print axioms GaussianWave.BS.RRGClassificationEvents.signals_BSJointClassification

#print axioms LocalLaw.source_theorem_4_2
#print axioms SpectralConsequences.full_paper_theorem_1_2
#print axioms SpectralConsequences.full_paper_theorem_1_4

#print axioms GeneralizedBulk.External.RegularSpectralData.bulk_universality
#print axioms GeneralizedBulk.Graph.uniform_regular_graph_bulk_universality
#print axioms GeneralizedBulk.Graph.uniform_graph_star_wasserstein
#print axioms GeneralizedBulk.Graph.uniform_graph_mixed_fourth

#print axioms GeneralizedBulk.Graph.uniform_root_fourth_probability

#print axioms GeneralizedBulk.Graph.uniform_graph_star_wasserstein_fixed_energy_sup
#print axioms GeneralizedBulk.Graph.corollary_1_3
#print axioms GeneralizedBulk.Graph.corollary_1_3_real
#print axioms GeneralizedBulk.Graph.corollary_1_3_along_sizes
#print axioms GeneralizedBulk.Graph.corollary_1_3_real_along_sizes
