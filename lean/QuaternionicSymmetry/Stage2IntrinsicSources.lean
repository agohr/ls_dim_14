import QuaternionicSymmetry.ManifoldQuaternionicIsometryCompactness
import QuaternionicSymmetry.Stage2ActualInduction
import QuaternionicSymmetry.ManifoldPositiveQuaternionicBWWExtremeOccurrence
import QuaternionicSymmetry.ManifoldTwistorSelectedPicardExtremalRootBound
import QuaternionicSymmetry.GeneralContactFanoORSWRecognitionSource
import QuaternionicSymmetry.TorusCharacterFromMathlib
import QuaternionicSymmetry.CompactTorusEigenbasisFromMathlib
import QuaternionicSymmetry.ManifoldQuaternionicKSWScalarFromDecomposition
import QuaternionicSymmetry.ManifoldQuaternionicKSWEq38Derived
import QuaternionicSymmetry.ManifoldQuaternionicFixedComponentFromCompactAction
import QuaternionicSymmetry.ManifoldRiemannianOneJetFromCompactAction
import QuaternionicSymmetry.EmbeddedCodomainRestrictionFromMathlib
import QuaternionicSymmetry.FiniteHolomorphicMapDimensionFromMathlib
import QuaternionicSymmetry.EquivariantImmersionFromMathlib
import QuaternionicSymmetry.RealAdjointDifferentialFromMathlib
import QuaternionicSymmetry.HolomorphicTransitiveOrbitFromMathlib
import QuaternionicSymmetry.ManifoldRiemannianFixedTotalGeodesyFromMathlib
import QuaternionicSymmetry.ComplexSubmanifoldFromMathlib
import QuaternionicSymmetry.HolomorphicLineFiniteSectionsFromMathlib
import QuaternionicSymmetry.MaximalTorusFromCorrespondence
import QuaternionicSymmetry.MaximalTorusLieFromClosedEmbedding
import QuaternionicSymmetry.QuaternionicSubmanifoldFromMathlib
import QuaternionicSymmetry.UniqueContactHamiltonianFromMathlib

/-! Explicit literature inputs for induction on actual manifolds. The
model-dependent curvature and fixed-manifold statements are quantified over
all supported carriers, so applying induction to an induced fixed component
requires no new geometric or classification premise. Each field is a named
source proposition; the final statement report unfolds every field. This
record asserts no source proposition by itself and introduces no axiom. -/

namespace QuaternionicSymmetry.Stage2IntrinsicSources

open scoped Manifold ContDiff

/-- The C12 literature boundary, without the additional Amann sign input. -/
structure Sources : Prop where
  orswRecognition : GeneralContactFanoORSWRecognitionSource.AnalyticCompactRealFormExtremalRecognition
  bwwRestriction : GeneralBWWAnalyticExtremalSource.AnalyticExtremalRestrictionAndSmallSections
  bwwReductive : ManifoldTwistorBWW66ReductiveTransformationSource.FullAutReductiveTransformationSource
  unique : GeneralContactFanoPicardUniquenessSource.AnalyticContactPicardGeneratorPreservesDistribution
  ntComplexification : ManifoldTwistorNTContactInfinitesimalSource.NTContactInfinitesimalComplexificationSource
  isometryLie : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0}
  closedEmbedding : GeneralClosedSubgroupLieSource.LeeClosedEmbeddingTheorem
  orbital : OrbitalInterleavedBridge.LiteralInterleavedFormula
  positiveContact : ManifoldTwistorNittaTakeuchiPositiveRicciInput.PositiveRicciContactExistence
  kodaira : HolomorphicPositiveLineKodairaSource.PositiveHermitianLineAmpleTheorem.{0,0,0}
  picardAlternative : GeneralContactFanoPicardHomogeneitySource.AnalyticContactPicardOrHomogeneousCorollary
  swEquation : ManifoldSWEquation22SourceContract.SWEquation22Source.{1}
  swCohomology : ManifoldTwistorLeBrunComplexAtlas.SWCohomologicalSource.{0,0,1}
  ballmann : GeneralPositiveAnticanonicalSimplyConnectedSource.BallmannPositiveAnticanonicalSimplyConnected
  wolfLeBrun : ManifoldTwistorHomogeneousContactSymmetrySource.HomogeneousContactTwistorSymmetryCorollary



/-- The former BG-T2 field is now proved from mathlib. The argument is retained
only to preserve the source-record API used by the induction modules. -/
theorem Sources.eigenbasis (_s : Sources) :
    CompactTorusEigenbasisSource.KnappTorusEigenbasis :=
  CompactTorusEigenbasisFromMathlib.torusEigenbasisSource

/-- The former BG-T1 field is now proved from mathlib. -/
theorem Sources.circleCharacters (_s : Sources) : TorusCharacterInput.CircleCharacterSource :=
  TorusCharacterFromMathlib.circleCharacterSource

/-- BG-D3 follows from mathlib's inverse function theorem. -/
theorem Sources.embeddedRestriction (_s : Sources) :
    GeneralSmoothMapSource.LeeEmbeddedCodomainRestrictionTheorem :=
  EmbeddedCodomainRestrictionFromMathlib.embeddedCodomainRestriction

/-- Finite fibers force the dimension inequality by the proved local rank argument. -/
theorem Sources.finiteMapDimension (_s : Sources) :
    HolomorphicFiniteMapDimensionSource.FiniteHolomorphicMapDimensionTheorem.{0,0} :=
  FiniteHolomorphicMapDimensionFromMathlib.finiteHolomorphicMapDimension

/-- Injective equivariant maps are immersions by the proved local rank argument. -/
theorem Sources.equivariantImmersion (_s : Sources) :
    GeneralSmoothMapSource.LeeEquivariantImmersionTheorem :=
  EquivariantImmersionFromMathlib.equivariantImmersion

/-- The genuine adjoint differential is the Lie bracket, by the chart calculation. -/
theorem Sources.adjointDifferential (_s : Sources) :
    GeneralRealAdjointDifferentialSource.LeeRealAdjointDifferentialSource :=
  RealAdjointDifferentialFromMathlib.realAdjointDifferential

/-- Open orbit maps and the proved rank theorem give the literal submersion theorem. -/
theorem Sources.orbitSubmersion (_s : Sources) :
    GeneralHolomorphicTransitiveOrbitSource.LeeHolomorphicTransitiveOrbitSubmersion :=
  HolomorphicTransitiveOrbitFromMathlib.holomorphicTransitiveOrbitSubmersion

/-- Invariant real tangent spaces give holomorphic graph charts by the inverse
function theorem and the proved Cauchy–Riemann criterion. -/
theorem Sources.complexSubmanifold (_s : Sources) :
    ComplexSubmanifoldInput.ClosedComplexTangentSubmanifoldTheorem :=
  ComplexSubmanifoldFromMathlib.closedComplexTangentSubmanifold

/-- Local Schwarz estimates make evaluation on finitely many sample points
injective on the genuine holomorphic section space. -/
theorem Sources.finiteSections (_s : Sources) :
    HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness :=
  HolomorphicLineFiniteSectionsFromMathlib.compactHolomorphicLineSectionFiniteness

/-- Quaternionic Gram-Schmidt, the projected connection and the internally
proved curvature decomposition give the original induced positive geometry. -/
theorem Sources.quaternionicSubmanifold (_s : Sources) :
    ManifoldQuaternionicSubmanifoldInput.PositiveQuaternionicSubmanifoldSource :=
  QuaternionicSubmanifoldFromMathlib.positiveQuaternionicSubmanifold

/-- Holomorphic flows realize all vector fields in the actual full automorphism
Lie algebra; kernel preservation and the proved contact correspondence give
the original canonical Hamiltonian bijection. -/
theorem Sources.ntHamiltonian (s : Sources) :
    GeneralUniqueContactHamiltonianSource.UniqueContactHamiltonianBijection :=
  UniqueContactHamiltonianFromMathlib.uniqueContactHamiltonian s.closedEmbedding

section DerivedGeometry
variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

/-- The supplied smooth quaternionic isometric inclusion is internally totally geodesic. -/
theorem Sources.fixedTotalGeodesy (_s : Sources) :
    ManifoldRiemannianFixedTotalGeodesyInput.FixedComponentTotalGeodesyOnModel (E := E) (M := M) :=
  ManifoldRiemannianFixedTotalGeodesyFromMathlib.fixedComponentTotalGeodesy

/-- The algebraic Riemann identities and quaternionic normalizer equations
prove the full KSW scalar/Weyl decomposition of the actual tangent curvature. -/
theorem Sources.kswDecomposition (_s : Sources) :
    ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M) :=
  ManifoldQuaternionicKSWEq38Derived.onModel

/-- KSW Lemma 3.10 is a projection of the internally proved Equation (3.8). -/
theorem Sources.kswSp1 (s : Sources) :
    ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M) :=
  ManifoldQuaternionicKSWScalarFromDecomposition.kswSp1_of_kswDecomposition
    s.kswDecomposition

/-- Compact-action averaging proves the fixed-component interface on compact bases. -/
theorem Sources.fixedComponents (s : Sources) [CompactSpace M] [PreconnectedSpace M] [Nonempty M] :
    ManifoldRiemannianFixedComponentInput.RiemannianFixedComponentOnModel (E := E) (M := M) :=
  ManifoldQuaternionicFixedComponentFromCompactAction.fixedComponents s.isometryLie s.closedEmbedding

/-- One-jet rigidity follows from the proved compact-action fixed-component theorem. -/
theorem Sources.oneJet (s : Sources) [CompactSpace M] :
    ManifoldRiemannianOneJetInput.RiemannianOneJetRigidityOnModel (E := E) (M := M) :=
  ManifoldRiemannianOneJetFromCompactAction.oneJet s.isometryLie s.closedEmbedding
end DerivedGeometry

/-- The original maximal-torus Lie correspondence is proved using only the
retained closed-subgroup atlas theorem and internal compact Lie theory. -/
theorem Sources.torusLie (s : Sources) :
    CompactLieMaximalTorusTangentSource.MaximalTorusLieCorrespondenceSource :=
  MaximalTorusLieFromClosedEmbedding.maximalTorusLieCorrespondence s.closedEmbedding

/-- Maximal embedded tori exist by bounded dimension; the internally proved Lie
correspondence supplies the positive-rank clause. -/
theorem Sources.maximalTorus (s : Sources) : CompactLieTorusInputs.MaximalTorusSource.{0,0} :=
  MaximalTorusFromCorrespondence.maximalTorusSource s.closedEmbedding s.torusLie

/-- Internally derived compactness, available to the Cartan/root chain. -/
theorem Sources.isometryCompactness (s : Sources) :
    ManifoldQuaternionicIsometryCompactness.QuaternionicIsometryCompactness :=
  ManifoldQuaternionicIsometryCompactness.compactness_of_isometryLie s.isometryLie

/-- The separately disclosed E14 sign source; absent from `Sources` and C12. -/
def AmannInput : Prop :=
  ∀ {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    [Nonempty M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M],
    ManifoldAmannIntersectionInput.AmannKrainesRayInput (E := E) (M := M)

end QuaternionicSymmetry.Stage2IntrinsicSources
