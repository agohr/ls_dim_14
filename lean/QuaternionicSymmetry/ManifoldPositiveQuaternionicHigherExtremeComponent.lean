import QuaternionicSymmetry.ManifoldPositiveQuaternionicWeightHull
import QuaternionicSymmetry.ManifoldQuaternionicTorusHigherComponentAlternative

/-!
For every actual extremal torus-fixed twistor component, the normalized
antipodal weight theorem supplies a nonzero vertical weight. The resulting
component alternative uses only a dimension-one exception, not a source for
four-dimensional positive Einstein–Weyl geometry. The higher branch retains
the actual induced positive quaternionic-Kähler geometry.
-/

namespace QuaternionicSymmetry.ManifoldPositiveQuaternionicHigherExtremeComponent

open ManifoldPositiveQuaternionicWeightHull
open ManifoldPositiveQuaternionicKahlerGeometry ManifoldQuaternionicScalarCurvature
open ManifoldQuaternionicTorusAction ManifoldQuaternionicActualWeightHull
open ManifoldQuaternionicActualWeightVertical ManifoldQuaternionicVerticalCircleCharacter
open ManifoldQuaternionicTorusHigherComponentAlternative
open ManifoldQuaternionicTorusFixedComplexComponent
open ManifoldRiemannianFixedComponentInput ManifoldRiemannianIsometryLieInput
open ManifoldQuaternionicSubmanifoldInput ManifoldTwistorSphereCore
open ManifoldTwistorPositiveRicciInput HolomorphicPositiveLineKodairaSource
open ProjectiveAnalyticAlgebraicSources CompactTorusEigenbasisSource TorusCharacterInput
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T3Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

/-- The literal full-torus component at an extreme weight is a point, has a
four-real-dimensional connected kernel base, or has a strictly smaller
induced positive quaternionic-Kähler kernel base. No `hT4four` premise. -/
theorem normalized_extreme_component_higher_alternative
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
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
    (hScalar : ∀ p y (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      localScalarCurvature P.tangent P.connection p y hy =
        16 * (n : ℝ) * ((n : ℝ) + 2))
    {r : ℕ} (A : ContinuousTorusAction P.tangent r)
    (hA : A.Faithful) (hr : 2 ≤ r) :
    letI : CompactSpace M := ⟨P.compact⟩
    letI : PreconnectedSpace M := ⟨P.connected⟩
    ∀ (z : SphereBundleTotal P.tangent)
      (hz : ∀ t, A.representation t • z = z) (μ : Fin r → ℤ),
      (∀ t, torusVerticalCircleCharacter P.tangent hR3 A z hz t = weightCharacter μ t) →
      (fun i => (μ i : ℝ)) ∈
        (convexHull ℝ (actualRealWeights P.tangent hR3 A)).extremePoints ℝ →
      (component P.tangent A z).Subsingleton ∨
        ∃ m : ℕ, 0 < m ∧ m < n ∧
          ∃ C : FixedComponentAtlas P.tangent
            (A.connectedKernelImage P.tangent μ) z.1 (4*m),
            m = 1 ∨
              (∃ hm : 2 ≤ m,
                letI : NeZero (4*m) := ⟨by omega⟩
                letI := C.charts
                letI := C.manifold
                ∃ R : CompactConnectedPositiveQuaternionicKahlerGeometry
                    (E := EuclideanSpace ℝ (Fin (4*m)))
                    (M := FixedComponent P.tangent
                      (A.connectedKernelImage P.tangent μ) z.1),
                  IsInducedQuaternionicGeometry
                    P.toPositiveQuaternionicKahlerGeometry
                    R.toPositiveQuaternionicKahlerGeometry Subtype.val) := by
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  intro z hz μ hchar hextreme
  have hhull := normalized_actual_weight_hull_from_sources
    hT1 hKodaira hR3 hFinite hEigen hCircle
    P n hn hDim hScalar A hA (by omega)
  have hμ : μ ≠ 0 := by
    intro hzero
    apply hhull.2.2.2.1 _ hextreme
    funext i
    simp [hzero]
  exact component_subsingleton_or_four_dimension_or_higher_induced_geometry
    P.toPositiveQuaternionicKahlerGeometry n hn hDim
    hR3 hT4 hjet hfixedSource A hA hr z hz μ hμ
    (hasVerticalWeight_of_character P.tangent hR3 A z hz μ hchar)

end
end QuaternionicSymmetry.ManifoldPositiveQuaternionicHigherExtremeComponent
