import QuaternionicSymmetry.ManifoldPositiveQuaternionicHigherExtremeComponent
import QuaternionicSymmetry.ManifoldQuaternionicFixedComplexDimensionBound
import QuaternionicSymmetry.ConnectedChartedSpaceDimension

/-! The literal normalized extremal full-torus fixed component has genuine
real and complex embedded atlases. It is either a point, has positive complex
dimension at most three over a four-real-dimensional kernel component, or
lies over a strictly smaller induced positive quaternionic-Kähler component
of quaternionic dimension at least two. The small branch uses no four-
dimensional positive-geometry source. -/

namespace QuaternionicSymmetry.ManifoldPositiveQuaternionicExtremeFixedComplexDimensionAlternative

open ManifoldPositiveQuaternionicHigherExtremeComponent
open ManifoldPositiveQuaternionicKahlerGeometry ManifoldQuaternionicScalarCurvature
open ManifoldQuaternionicTorusAction ManifoldQuaternionicActualWeightHull
open ManifoldQuaternionicActualWeightVertical ManifoldQuaternionicVerticalCircleCharacter
open ManifoldQuaternionicTorusFixedComplexComponent
open ManifoldQuaternionicTwistorLiftedFixedSet
open ManifoldQuaternionicTwistorComplexFixedAtlas
open ManifoldQuaternionicFixedComplexDimensionBound
open ManifoldRiemannianFixedComponentInput ManifoldRiemannianFixedComponentGenericInput
open ManifoldRiemannianIsometryLieInput
open ManifoldQuaternionicSubmanifoldInput ManifoldTwistorSphereCore
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorPositiveRicciInput HolomorphicPositiveLineKodairaSource
open ProjectiveAnalyticAlgebraicSources CompactTorusEigenbasisSource TorusCharacterInput
open QuaternionicSymmetry.GeneralSmoothMapSource
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T3Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

private abbrev J := (𝓘(ℝ,E)).prod (𝓡 2)
private abbrev V := E × EuclideanSpace ℝ (Fin 2)

/-- The three actual extreme-component alternatives, with the same literal
full-torus fixed component and its constructed compatible complex atlas in
every branch. The `m=1` branch is only a small-component statement. -/
theorem normalized_extreme_component_point_or_small_or_higher
    (hT1 : NormalizedPositiveRicciContactExistence)
    (hKodaira : PositiveHermitianLineAmpleTheorem.{0,0,0})
    (hR3 : IsometryLieSource.{0,0})
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (hEigen : KnappTorusEigenbasis) (hCircle : CircleCharacterSource)
    (hT4 : PositiveQuaternionicSubmanifoldSource)
    (hjet : ManifoldRiemannianOneJetInput.RiemannianOneJetRigidityOnModel
      (E := E) (M := M))
    (hfixedSource : RiemannianFixedComponentOnModel (E := E) (M := M))
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (hTwistorFixed : ManifoldQuaternionicTwistorFixedFromCompactAction.LiftedFixedComponents P.tangent)
    (hComplex : ComplexSubmanifoldInput.ClosedComplexTangentSubmanifoldTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
    (B₀ : CompatibleComplexAtlas P.tangent P.connection n)
    (hScalar : ∀ p y (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      localScalarCurvature P.tangent P.connection p y hy =
        16 * (n : ℝ) * ((n : ℝ) + 2))
    {r : ℕ} (A : ContinuousTorusAction P.tangent r)
    (hA : A.Faithful) (hr : 2 ≤ r) :
    letI : CompactSpace M := ⟨P.compact⟩
    letI : PreconnectedSpace M := ⟨P.connected⟩
    letI := B₀.charts
    ∀ (z : SphereBundleTotal P.tangent)
      (hz : ∀ t, A.representation t • z = z) (μ : Fin r → ℤ),
      (∀ t, torusVerticalCircleCharacter P.tangent hR3 A z hz t = weightCharacter μ t) →
      (fun i => (μ i : ℝ)) ∈
        (convexHull ℝ (actualRealWeights P.tangent hR3 A)).extremePoints ℝ →
      ∃ k : ℕ, ∃ H : FixedComponentAtlas (J (E := E))
        (liftedSet P.tangent A.imageSubgroup) z k,
        ∃ b : ℕ, ∃ B : ComplexSubmanifoldInput.CompatibleComplexAtlas
          (realEmbeddedAtlas P.tangent P.connection B₀ A.imageSubgroup H) b,
          k = 2*b ∧
          ((component P.tangent A z).Subsingleton ∨
            (∃ C : FixedComponentAtlas P.tangent
              (A.connectedKernelImage P.tangent μ) z.1 4,
              0 < b ∧ b ≤ 3) ∨
            (∃ m : ℕ, ∃ hm : 2 ≤ m, m < n ∧
              ∃ C : FixedComponentAtlas P.tangent
                (A.connectedKernelImage P.tangent μ) z.1 (4*m),
                letI : NeZero (4*m) := ⟨by omega⟩
                letI := C.charts
                letI := C.manifold
                ∃ R : CompactConnectedPositiveQuaternionicKahlerGeometry
                    (E := EuclideanSpace ℝ (Fin (4*m)))
                    (M := FixedComponent P.tangent
                      (A.connectedKernelImage P.tangent μ) z.1),
                  IsInducedQuaternionicGeometry
                    P.toPositiveQuaternionicKahlerGeometry
                    R.toPositiveQuaternionicKahlerGeometry Subtype.val)) := by
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  letI := B₀.charts
  intro z hz μ hchar hextreme
  obtain ⟨k,H,b,B,hkb,_⟩ := exists_complexComponentAtlas
    P.tangent A P.connection B₀ hTwistorFixed hComplex z hz
  refine ⟨k,H,b,B,hkb,?_⟩
  by_cases hpoint : (component P.tangent A z).Subsingleton
  · exact Or.inl hpoint
  have halt := normalized_extreme_component_higher_alternative
    hT1 hKodaira hR3 hFinite hEigen hCircle
    hT4 hjet hfixedSource P n hn hDim hScalar A hA hr z hz μ hchar hextreme
  rcases halt with hpoint' | ⟨m,hmpos,hmLt,C,hone | ⟨hm2,R,hR⟩⟩
  · exact False.elim (hpoint hpoint')
  · right; left
    subst m
    have hsmall := complex_dimension_le_three_of_four_base
      P.tangent A z hz μ P.connection B₀ H B (by simpa using C) hLee
    letI : ChartedSpace (EuclideanSpace ℂ (Fin b))
      ↥(component P.tangent A z) := B.charts
    letI : PreconnectedSpace ↥(component P.tangent A z) :=
      Subtype.preconnectedSpace isPreconnected_connectedComponentIn
    have hnontrivial : (component P.tangent A z).Nontrivial :=
      Set.not_subsingleton_iff.mp hpoint
    letI : Nontrivial ↥(component P.tangent A z) := hnontrivial.coe_sort
    exact ⟨C, ConnectedChartedSpaceDimension.complex_dimension_pos
      (X := ↥(component P.tangent A z)) b, hsmall⟩
  · right; right
    exact ⟨m,hm2,hmLt,C,R,hR⟩

end
end QuaternionicSymmetry.ManifoldPositiveQuaternionicExtremeFixedComplexDimensionAlternative
