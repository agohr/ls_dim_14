import QuaternionicSymmetry.ManifoldTwistorBWW66ReductiveTransformationSource
import QuaternionicSymmetry.ManifoldTwistorORSWNormalizedSeed
import QuaternionicSymmetry.ManifoldTwistorBKKPositivePicardLieReductionRescaled

/-! Actual intrinsic metric symmetry of every positive seed geometry with
quaternionic dimension two through seven. Scalar normalization, contact
homogeneity, twistor simple connectedness and metric transport are internal.
Only the explicitly registered general literature clauses remain premises. -/
namespace QuaternionicSymmetry.ManifoldTwistorORSWSeedMetricSymmetry

open GeneralContactFanoORSWSource GeneralContactFanoPicardUniquenessSource
open GeneralHolomorphicFullAutomorphismLieSource
open ManifoldTwistorORSWSeedApplication ManifoldTwistorORSWCompactRealFormApplication
open ManifoldTwistorNTContactInfinitesimalSource
open ManifoldTwistorBKKPicardUniquenessApplication
open ManifoldTwistorUniqueContactFullEquiv ManifoldTwistorUniqueContactFullLieTransfer
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorContactAutomorphisms ManifoldTwistorFullAutomorphisms
open ManifoldTwistorLineCoreClasses ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSpanSymmetry ManifoldQuaternionicTorusAction
open HolomorphicLineCoreAmpleFiniteMap HolomorphicLineCoreSheafPicardGenerator
open HolomorphicLineSheafClasses HolomorphicLineSheafClassGroup
open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open ManifoldTwistorORSWSeedFromSources
open ManifoldTwistorPositiveRicciInput ManifoldTwistorPositiveContactAmple
open GeneralContactFanoPicardHomogeneitySource
open ManifoldTwistorBKKAnalyticPicardApplication
open ManifoldTwistorFullAutHomogeneityGeneration
open GeneralHolomorphicTransitiveOrbitSource
open ManifoldTwistorORSWPicardSeed ManifoldSWEquation22SourceContract
open ManifoldTwistorORSWNormalizedSeed
open ManifoldPositiveQuaternionicKahlerHomothety
open ManifoldTwistorHomogeneousContactSymmetrySource
open ManifoldTwistorPositiveAnticanonicalSimplyConnected
open GeneralPositiveAnticanonicalSimplyConnectedSource
open ManifoldRiemannianIntrinsicSymmetry ManifoldMetricHomothety
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

/-- Intrinsic symmetry of the original metric, with the seed geometry
selected internally from the general sources. -/
theorem intrinsicSymmetric_seed_from_sources
    (hORSW : AnalyticCompactRealFormRankHomogeneity)
    (hUnique : AnalyticContactPicardGeneratorPreservesDistribution)
    (hAutSource : ManifoldTwistorBWW66ReductiveTransformationSource.FullAutReductiveTransformationSource)
    (hNT : NTContactInfinitesimalComplexificationSource)
    (hNTU : GeneralUniqueContactHamiltonianSource.UniqueContactHamiltonianBijection)
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    (S : QuaternionicStructure E)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (hn : 2 ≤ S.quaternionicDimension) (hn7 : S.quaternionicDimension ≤ 7)
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (hT1 : NormalizedPositiveRicciContactExistence)
    (hKodaira : HolomorphicPositiveLineKodairaSource.PositiveHermitianLineAmpleTheorem.{0,0,0})
    (hBKK : AnalyticContactPicardOrHomogeneousCorollary)
    (hLeeOrbit : LeeHolomorphicTransitiveOrbitSubmersion)
    (hGeneral : GeneralComplexContactData.GeneralContactCanonicalTheorem.{0,0,0})
    (hEquation : SWEquation22Source.{1})
    (hCohom : SWCohomologicalSource.{0,0,1})
    (hTorus : CompactLieTorusInputs.MaximalTorusSource.{0,0})
    (hRankOne : CompactLieTorusInputs.CompactRankOneDimensionSource.{0,0})
    (hBallmann : BallmannPositiveAnticanonicalSimplyConnected)
    (hWolfLeBrun : HomogeneousContactTwistorSymmetryCorollary) :
    IsRiemannianSymmetric P.tangent := by
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  obtain ⟨s, hs, hScalar⟩ := exists_normalized_scalar S P heq38 hn
  let R := rescaleCompact P s hs
  obtain ⟨A,C,_hAmple,_hGen,hContact,_hFull⟩ :=
    exists_normalized_homogeneous_generated_ample_seed
      hORSW hUnique hAutSource hNT hNTU hR3 hClosed hImm hLee S R hn hn7
      hsource hsp heq38 hT1 hKodaira hBKK hLeeOrbit hGeneral hEquation
      hCohom hTorus hRankOne hScalar
  have hSC := normalized_twistor_simplyConnected
    hBallmann hT1 R S.quaternionicDimension hn S.real_finrank hScalar
  have hSym := intrinsicSymmetric_of_contactAutomorphisms_transitive
    hWolfLeBrun R S.quaternionicDimension hn S.real_finrank A C hSC hContact
  change IsRiemannianSymmetric
    (ManifoldQuaternionicHomothetyReduction.rescaleMetric
      P.tangent s (ne_of_gt hs)) at hSym
  exact (isRiemannianSymmetric_iff_metricHomothety
    (rescaleHomothety P.tangent s hs)).mpr hSym

end
end QuaternionicSymmetry.ManifoldTwistorORSWSeedMetricSymmetry
