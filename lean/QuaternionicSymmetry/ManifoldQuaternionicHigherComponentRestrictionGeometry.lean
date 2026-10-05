import QuaternionicSymmetry.ManifoldPositiveQuaternionicExtremeFixedComplexDimensionAlternative
import QuaternionicSymmetry.ManifoldQuaternionicKernelQTriviality
import QuaternionicSymmetry.ManifoldQuaternionicInducedTwistorMap
import QuaternionicSymmetry.ManifoldRiemannianFixedTotalGeodesyInput

/-! The actual higher fixed component supplies the base range, quaternionic
coefficient triviality, total geodesy, and a lift of the selected ambient
twistor point. These are the geometric hypotheses of the established
intrinsic-to-ambient contact-line restriction theorem. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicHigherComponentRestrictionGeometry

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicInducedTwistorMap
open ManifoldQuaternionicTorusAction
open ManifoldQuaternionicActualWeightVertical
open ManifoldQuaternionicVerticalCircleCharacter
open ManifoldQuaternionicVerticalWeightKernel
open ManifoldQuaternionicKernelQTriviality
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometryCoefficients
open ManifoldRiemannianFixedComponentInput
open ManifoldRiemannianFixedTotalGeodesyInput
open ManifoldTwistorSphereCore
open ManifoldRiemannianIsometryLieInput
open TorusCharacterInput
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T3Space M] [SecondCountableTopology M] [Nonempty M]
  [CompactSpace M] [PreconnectedSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))

/-- The higher-branch induced geometry is based on the *literal* connected
fixed component. The selected ambient point has a preimage in the induced
twistor sphere; no identification of the full-torus component with that
sphere bundle is made. -/
theorem higher_component_restriction_geometry
    (hR3 : IsometryLieSource.{0,0})
    (hBG : FixedComponentTotalGeodesyOnModel (E := E) (M := M))
    {r : ℕ} (T : ContinuousTorusAction P.tangent r)
    (z : SphereBundleTotal P.tangent)
    (hz : ∀ t, T.representation t • z = z)
    (μ : Fin r → ℤ)
    (hchar : ∀ t, torusVerticalCircleCharacter P.tangent hR3 T z hz t =
      weightCharacter μ t)
    (m : ℕ) (hm : 2 ≤ m)
    (C : FixedComponentAtlas P.tangent
      (T.connectedKernelImage P.tangent μ) z.1 (4*m)) :
    letI : NeZero (4*m) := ⟨by omega⟩
    letI := C.charts
    letI := C.manifold
    ∀ (R : CompactConnectedPositiveQuaternionicKahlerGeometry
        (E := EuclideanSpace ℝ (Fin (4*m)))
        (M := FixedComponent P.tangent
          (T.connectedKernelImage P.tangent μ) z.1))
      (hR : IsInducedQuaternionicGeometry
        P.toPositiveQuaternionicKahlerGeometry
        R.toPositiveQuaternionicKahlerGeometry Subtype.val),
      ∃ zR : SphereBundleTotal R.tangent,
        sphereTotalMap P.toPositiveQuaternionicKahlerGeometry
          R.toPositiveQuaternionicKahlerGeometry Subtype.val
          C.inclusion_injective_derivative hR zR = z ∧
        Set.range (Subtype.val : FixedComponent P.tangent
          (T.connectedKernelImage P.tangent μ) z.1 → M) =
          connectedComponentIn (fixedPoints P.tangent
            (T.connectedKernelImage P.tangent μ)) zR.1.1 ∧
        (∀ x ∈ Set.range (Subtype.val : FixedComponent P.tangent
          (T.connectedKernelImage P.tangent μ) z.1 → M),
          ∀ f ∈ T.connectedKernelImage P.tangent μ,
          ∀ a : Fin 3 → ℝ, coefficientAction P.tangent f x a = a) ∧
        ManifoldQuaternionicInducedTotalGeodesy.IsTotallyGeodesic
          P.toPositiveQuaternionicKahlerGeometry
          R.toPositiveQuaternionicKahlerGeometry Subtype.val
          P.connection R.connection := by
  letI : NeZero (4*m) := ⟨by omega⟩
  letI := C.charts
  letI := C.manifold
  intro R hR
  have hweight := hasVerticalWeight_of_character P.tangent hR3 T z hz μ hchar
  have hOne := connectedKernel_coefficient_trivial P.tangent T z hz μ hweight
  have hQ := connectedKernel_coefficientAction_everywhere P.tangent hR3 T μ z.1
    (base_mem_connectedKernelFixedSet P.tangent T z hz μ) hOne
  let xR : FixedComponent P.tangent
      (T.connectedKernelImage P.tangent μ) z.1 :=
    ⟨z.1, mem_connectedComponentIn
      (base_mem_connectedKernelFixedSet P.tangent T z hz μ)⟩
  obtain ⟨aR, haR⟩ := sphereTotalMap_fiber_surjective
    P.toPositiveQuaternionicKahlerGeometry
    R.toPositiveQuaternionicKahlerGeometry Subtype.val
    C.inclusion_injective_derivative hR xR z.2
  refine ⟨⟨xR,aR⟩, ?_, ?_, ?_, ?_⟩
  · simpa [xR] using haR
  · change Set.range (Subtype.val : FixedComponent P.tangent
        (T.connectedKernelImage P.tangent μ) z.1 → M) =
        connectedComponentIn (fixedPoints P.tangent
          (T.connectedKernelImage P.tangent μ)) z.1
    exact Subtype.range_val
  · intro x hx f hf a
    obtain ⟨y,rfl⟩ := hx
    exact hQ y f hf a
  · exact fixedComponent_totallyGeodesic_of_source hBG
      P.toPositiveQuaternionicKahlerGeometry
      (T.connectedKernelImage P.tangent μ) z.1 (4*m) C
      R.toPositiveQuaternionicKahlerGeometry hR P.connection R.connection

end
end QuaternionicSymmetry.ManifoldQuaternionicHigherComponentRestrictionGeometry
