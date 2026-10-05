import QuaternionicSymmetry.Stage2IntrinsicSources
import QuaternionicSymmetry.ManifoldPositiveQuaternionicBWWExtremeIsolation
import QuaternionicSymmetry.ManifoldTwistorSelectedExtremalRestrictionUpper
import QuaternionicSymmetry.ManifoldQuaternionicIsometryLieFromSources
import QuaternionicSymmetry.SelectedTorusEmbeddedLieAtlas

/-! Actual normalized Picard-branch extremal isolation. The caller supplies
only named general literature sources, actual geometry/contact/Picard data,
the SAME maximal torus and lower-dimensional homogeneity. Real/full/contact
Lie atlases, the embedded torus atlas, unpowered vertex occurrence, integral
character span, centre zero and root bounds are constructed internally.
The BWW occurrence argument is upstream of centre/root calculations. -/

namespace QuaternionicSymmetry.ManifoldTwistorNormalizedPicardIsolation

open Stage2IntrinsicSources Stage2ActualInduction
open ManifoldPositiveQuaternionicKahlerGeometry ManifoldQuaternionicScalarCurvature
open ManifoldQuaternionicSpanSymmetry ManifoldQuaternionicTorusAction
open ManifoldQuaternionicMaximalTorusAction ManifoldQuaternionicActualWeightHull
open ManifoldQuaternionicVerticalCircleCharacter ManifoldQuaternionicVerticalWeightKernel
open ManifoldQuaternionicTorusFixedComplexComponent
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorLineCoreClasses HolomorphicLineCoreClasses
open HolomorphicLineSheafClasses HolomorphicLineSheafClassGroup
open HolomorphicLineCoreSheafPicardGenerator HolomorphicLineCoreAmpleFiniteMap
open ManifoldTwistorSelectedPicardExtremalRootBound
open ManifoldTwistorSelectedExtremalRestrictionUpper
open ManifoldPositiveQuaternionicBWWExtremeOccurrence
open ManifoldPositiveQuaternionicBWWExtremeIsolation
open ManifoldTwistorUniqueContactFullEquiv ManifoldTwistorUniqueContactFullLieTransfer
open ManifoldTwistorContactAutomorphisms ManifoldTwistorFullAutomorphisms
open ManifoldRiemannianFixedComponentInput ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicHomothetyReduction ManifoldQuaternionicHomothetyConnection
open CompactLieTorusInputs
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem normalized_picard_extrema_are_points
    (src : Sources)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
    (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)
    (hAmple : letI := A.charts; letI := A.complexManifold
      AmpleCore 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore P.tangent P.connection C.contact.line))
    (hFullPic : letI := A.charts; letI := A.complexManifold
      Function.Bijective (fun k : ℤ =>
        (classMulEquiv 𝓘(ℂ,ComplexTwistorModel n)
          (contactClass P.tangent P.connection C.contact.line) :
          SheafClass (B := SphereBundleTotal P.tangent)
            𝓘(ℂ,ComplexTwistorModel n)) ^ k))
    (hScalar : ∀ p y (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      localScalarCurvature P.tangent P.connection p y hy =
        16 * (n : ℝ) * ((n : ℝ) + 2))
    {r : ℕ} (T : TorusEmbedding (QuaternionicIsometries P.tangent) r)
    (hMax : T.IsMaximal (QuaternionicIsometries P.tangent)) (hr : 2 ≤ r)
    (hLower : ∀ m, 2 ≤ m → m < n → NormalizedContactHomogeneity m) :
    letI : CompactSpace M := ⟨P.compact⟩
    letI : PreconnectedSpace M := ⟨P.connected⟩
    letI := A.charts
    ∀ (z : SphereBundleTotal P.tangent)
      (hz : ∀ t, (actionOfEmbedding P.tangent T).representation t • z = z)
      (μ : Fin r → ℤ),
      (∀ t, torusVerticalCircleCharacter P.tangent src.isometryLie
        (actionOfEmbedding P.tangent T) z hz t = weightCharacter μ t) →
      (fun i => (μ i : ℝ)) ∈
        (convexHull ℝ (actualRealWeights P.tangent src.isometryLie
          (actionOfEmbedding P.tangent T))).extremePoints ℝ →
      (component P.tangent (actionOfEmbedding P.tangent T) z).Subsingleton := by
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  letI : T3Space M := inferInstance
  letI : LocallyCompactSpace M := inferInstance
  have hTwistorFixed :=
    ManifoldQuaternionicTwistorFixedFromCompactAction.liftedFixedComponents
      P.tangent src.isometryLie src.closedEmbedding
  letI := A.charts
  letI := A.complexManifold
  have hCorePic := (core_zpow_bijective_iff_analyticPicard
    𝓘(ℂ,ComplexTwistorModel n)
    (contactLineCore P.tangent P.connection C.contact.line)).mpr hFullPic
  have hVertices := selected_extremal_vertices_occur_of_fixedpoint_occurrence
    src.isometryLie P n A C T (by
      intro z hz μ hchar hExtreme
      apply normalized_extreme_selectedSectionWeightSpace_ne_bot
        src.bwwRestriction src.positiveContact src.kodaira
        src.isometryLie src.finiteSections src.eigenbasis src.circleCharacters
        src.quaternionicSubmanifold src.oneJet src.fixedComponents src.fixedTotalGeodesy
        src.orbitSubmersion src.bwwReductive
        P hTwistorFixed src.complexSubmanifold src.embeddedRestriction
        n hn hDim A C hAmple hCorePic hScalar T hr z hz μ hchar hExtreme
      intro m hm hmn C₀
      letI : NeZero (4*m) := ⟨by omega⟩
      letI := C₀.charts
      letI := C₀.manifold
      intro R hR
      letI : Nonempty (FixedComponent P.tangent
          ((actionOfEmbedding P.tangent T).connectedKernelImage P.tangent μ) z.1) :=
        ⟨⟨z.1, mem_connectedComponentIn
          (base_mem_connectedKernelFixedSet P.tangent (actionOfEmbedding P.tangent T) z hz μ)⟩⟩
      exact exists_rescaled_fullAut_transitive m hm (hLower m hm hmn) R
        (by simp) src.kswDecomposition)
  obtain ⟨VR,hNormR,hSpaceR,hFiniteR,hRealChart,hRealManifold,hRealLie⟩ :=
    ManifoldQuaternionicIsometryLieFromSources.exists_real_lie_atlas
      P.toPositiveQuaternionicKahlerGeometry n hn hDim
      src.closedEmbedding src.isometryLie
  letI : NormedAddCommGroup VR := hNormR
  letI : NormedSpace ℝ VR := hSpaceR
  letI : FiniteDimensional ℝ VR := hFiniteR
  letI : ChartedSpace VR (QuaternionicIsometries P.tangent) := hRealChart
  letI : IsManifold 𝓘(ℝ,VR) ∞ (QuaternionicIsometries P.tangent) := hRealManifold
  letI : LieGroup 𝓘(ℝ,VR) ∞ (QuaternionicIsometries P.tangent) := hRealLie
  letI : CompactSpace (QuaternionicIsometries P.tangent) :=
    src.isometryCompactness
      P.toPositiveQuaternionicKahlerGeometry n hn hDim
  letI : SecondCountableTopology (QuaternionicIsometries P.tangent) :=
    ChartedSpace.secondCountable_of_sigmaCompact VR _
  obtain ⟨d,⟨g⟩⟩ := SelectedTorusEmbeddedLieAtlas.exists_selected_embedded_atlas
    (V := VR) T src.closedEmbedding
  obtain ⟨hPreserve,V,hNorm,hSpace,hFinite,hChart,hManifold,hLie,hJoint,
      hRad,hConj,hCartan,hCenter,hRoot⟩ :=
    exists_selected_picard_extremal_root_bound
      src.bwwReductive src.unique src.ntComplexification
      src.ntHamiltonian src.adjointDifferential src.isometryLie
      src.isometryCompactness src.torusLie
      src.closedEmbedding src.equivariantImmersion src.embeddedRestriction
      src.finiteSections src.eigenbasis src.circleCharacters
      P n hn hDim A C hAmple hFullPic hRealChart hRealManifold hRealLie
      T hMax g hVertices
  letI : NormedAddCommGroup V := hNorm
  letI : NormedSpace ℂ V := hSpace
  letI : FiniteDimensional ℂ V := hFinite
  letI : ChartedSpace V (TwistorHolomorphicAutomorphisms P.tangent P.connection A) := hChart
  letI : IsManifold 𝓘(ℂ,V) ∞ (TwistorHolomorphicAutomorphisms P.tangent P.connection A) := hManifold
  letI : LieGroup 𝓘(ℂ,V) ∞ (TwistorHolomorphicAutomorphisms P.tangent P.connection A) := hLie
  have hContactWeight := contactWeight_bound_of_selected_root_bound P n A C T hRoot
  intro z hz μ hchar hExtreme
  apply normalized_extreme_component_is_point_of_weight_bound
    src.bwwRestriction src.positiveContact src.kodaira
    src.isometryLie src.finiteSections src.eigenbasis src.circleCharacters
    src.quaternionicSubmanifold src.oneJet src.fixedComponents src.fixedTotalGeodesy
    src.orbitSubmersion src.bwwReductive
    P hTwistorFixed src.complexSubmanifold src.embeddedRestriction
    n hn hDim A C.contact hAmple hCorePic hScalar
    (actionOfEmbedding P.tangent T) (actionOfEmbedding_faithful P.tangent T) hr
    hContactWeight z hz μ hchar hExtreme
  intro m hm hmn C₀
  letI : NeZero (4*m) := ⟨by omega⟩
  letI := C₀.charts
  letI := C₀.manifold
  intro R hR
  letI : Nonempty (FixedComponent P.tangent
      ((actionOfEmbedding P.tangent T).connectedKernelImage P.tangent μ) z.1) :=
    ⟨⟨z.1, mem_connectedComponentIn
      (base_mem_connectedKernelFixedSet P.tangent (actionOfEmbedding P.tangent T) z hz μ)⟩⟩
  exact exists_rescaled_fullAut_transitive m hm (hLower m hm hmn) R
    (by simp) src.kswDecomposition

end
end QuaternionicSymmetry.ManifoldTwistorNormalizedPicardIsolation
