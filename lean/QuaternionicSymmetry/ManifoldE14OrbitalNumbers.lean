import QuaternionicSymmetry.QuaternionicE14ClosedEvaluation
import QuaternionicSymmetry.QuaternionicSourceIntegralNonnegative
import QuaternionicSymmetry.QuaternionicRecoveredSourceComparison
import QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerGeometry

/-! Canonical nonnegative orbital-remainder numbers on actual PQK manifolds
in dimensions thirteen and fourteen. No orbital-sign or number inequality is
assumed: these are derived from the registered KSW and scalar Haar formula. -/
namespace QuaternionicSymmetry.ManifoldE14OrbitalNumbers
open Module QuaternionicE14ClosedEvaluation QuaternionicE14OrbitalSums
open QuaternionicWeylMatrixCoefficients QuaternionicCurvatureFiniteExpansion
open QuaternionicCurvatureOrbitalSign ManifoldQuaternionicKSWEq38Input
open ManifoldQuaternionicKSWScalarInput QuaternionicTracePositivity
open ManifoldClosedPolynomialRepresentative QuaternionicClosedSourceGenerators
open ManifoldEvenClosedEvaluation ManifoldE14OrbitalWeights
open QuaternionicSourceIntegralNonnegative QuaternionicRecoveredSourceComparison
open ManifoldIntegratedRecoveredCertificates ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicKSWScalarConstancyDerived
open scoped Manifold ContDiff
noncomputable section
variable {E M ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [Fintype ι]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem orbital13_pointwise_nonnegative
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hsp : KSWSp1CurvatureFormula S Q D) (hdecomp : KSWEq38Decomposition S Q D)
    (hn : S.quaternionicDimension = 13) (b : Basis ι ℝ E) (t : ℝ)
    (ht : ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      scalarRatio S Q D p y hy = t ^ 2)
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (F : CE E →ₗ[ℝ] ℝ)
    (hF : 0 ≤ F (embed (V := E) (QuaternionicFundamental.topForm S b))) :
    0 ≤ F (embed (V := E) (gradeValue p y
      (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap 13
      (closedRepresentative (generators S Q D t)
        H2WitnessThirteen.orbitalSum orbitalSum13_weighted))) := by
  obtain ⟨W, hW, hv⟩ := seven_generator_values S Q D hsp hdecomp b t ht p y hy
  rw [pointwise_representative_complex, hv]
  have h := orbitalSum13_nonnegative (β := Index S) hsource S b
    ((t^2 / Real.pi)^2) (sq_nonneg _) hn
  rw [← hn] at h
  simpa only [hn] using h _
    (fun a => (tangentSourceMatrixMap S (operatorBasis S a)).property) _
    (coefficientExterior_mem S W (HyperWeylFiber.mem_skewCentralizer S hW)
      b hW.1 hW.2.2.2.2.1) F hF

theorem orbital14_pointwise_nonnegative
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hsp : KSWSp1CurvatureFormula S Q D) (hdecomp : KSWEq38Decomposition S Q D)
    (hn : S.quaternionicDimension = 14) (b : Basis ι ℝ E) (t : ℝ)
    (ht : ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      scalarRatio S Q D p y hy = t ^ 2)
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (F : CE E →ₗ[ℝ] ℝ)
    (hF : 0 ≤ F (embed (V := E) (QuaternionicFundamental.topForm S b))) :
    0 ≤ F (embed (V := E) (gradeValue p y
      (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap 14
      (closedRepresentative (generators S Q D t)
        H2WitnessFourteen.orbitalSum orbitalSum14_weighted))) := by
  obtain ⟨W, hW, hv⟩ := seven_generator_values S Q D hsp hdecomp b t ht p y hy
  rw [pointwise_representative_complex, hv]
  have h := orbitalSum14_nonnegative (β := Index S) hsource S b
    ((t^2 / Real.pi)^2) (sq_nonneg _) hn
  rw [← hn] at h
  simpa only [hn] using h _
    (fun a => (tangentSourceMatrixMap S (operatorBasis S a)).property) _
    (coefficientExterior_mem S W (HyperWeylFiber.mem_skewCentralizer S hW)
      b hW.1 hW.2.2.2.2.1) F hF

variable [MeasurableSpace E] [BorelSpace E]
  [Nonempty M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
variable (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))

theorem orbital13_recovered_nonnegative
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hsp : KSWLemma310OnModel (E := E) (M := M))
    (heq38 : KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 13)
    (hdim : 52 = Module.finrank ℝ E) :
    0 ≤ sevenCandidateNumber P.tangent P.connection 13 12 hdim
      H2WitnessThirteen.orbitalSum := by
  have hn2 : 2 ≤ S.quaternionicDimension := by omega
  let hd := decomposition_of_KSWEq38OnModel S P.tangent heq38
    P.toPositiveScalarTangentGeometry hn2
  obtain ⟨t, _htpos, ht⟩ := exists_global_parameter_of_eq38 S P.tangent
    P.toPositiveScalarTangentGeometry hd hn2 P.connected
  have h := sourcePolynomialNumber_nonnegative S P.tangent P.connection
    (Module.finBasis ℝ E) t 12 hdim H2WitnessThirteen.orbitalSum orbitalSum13_weighted
    (orbital13_pointwise_nonnegative S P.tangent P.connection hsource
      (formula_of_KSWLemma310OnModel S P.tangent hsp
        P.toPositiveScalarTangentGeometry hn2)
      hd hn (Module.finBasis ℝ E) t (fun p y hy => (ht p y hy).symm))
  rw [sourceNumber_eq_sevenCandidate S P.tangent P.connection, hn] at h
  exact h

theorem orbital14_recovered_nonnegative
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hsp : KSWLemma310OnModel (E := E) (M := M))
    (heq38 : KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 14)
    (hdim : 56 = Module.finrank ℝ E) :
    0 ≤ sevenCandidateNumber P.tangent P.connection 14 13 hdim
      H2WitnessFourteen.orbitalSum := by
  have hn2 : 2 ≤ S.quaternionicDimension := by omega
  let hd := decomposition_of_KSWEq38OnModel S P.tangent heq38
    P.toPositiveScalarTangentGeometry hn2
  obtain ⟨t, _htpos, ht⟩ := exists_global_parameter_of_eq38 S P.tangent
    P.toPositiveScalarTangentGeometry hd hn2 P.connected
  have h := sourcePolynomialNumber_nonnegative S P.tangent P.connection
    (Module.finBasis ℝ E) t 13 hdim H2WitnessFourteen.orbitalSum orbitalSum14_weighted
    (orbital14_pointwise_nonnegative S P.tangent P.connection hsource
      (formula_of_KSWLemma310OnModel S P.tangent hsp
        P.toPositiveScalarTangentGeometry hn2)
      hd hn (Module.finBasis ℝ E) t (fun p y hy => (ht p y hy).symm))
  rw [sourceNumber_eq_sevenCandidate S P.tangent P.connection, hn] at h
  exact h

end
end QuaternionicSymmetry.ManifoldE14OrbitalNumbers
