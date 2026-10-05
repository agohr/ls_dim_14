import QuaternionicSymmetry.ManifoldQuaternionicFixedWeightComponents
import QuaternionicSymmetry.ManifoldQuaternionicActualWeightVertical
import QuaternionicSymmetry.ManifoldTwistorPositiveContactAmple

/-! On a normalized actual positive quaternionic-Kähler manifold, one
integral vertical character at a fixed point is the character at every
point of its genuine connected full-torus fixed component. The complete
section eigenbasis and ample generating power are constructed internally
from precisely registered general source inputs. -/
namespace QuaternionicSymmetry.ManifoldPositiveQuaternionicComponentWeights

open ManifoldQuaternionicFixedWeightComponents
open ManifoldQuaternionicTorusAction ManifoldQuaternionicVerticalCircleCharacter
open ManifoldQuaternionicTorusFixedComplexComponent ManifoldQuaternionicTwistorLiftedFixedSet
open ManifoldQuaternionicActualWeightVertical ManifoldQuaternionicVerticalWeightKernel
open ManifoldPositiveQuaternionicKahlerGeometry ManifoldQuaternionicScalarCurvature
open ManifoldTwistorPositiveContactAmple ManifoldTwistorPositiveRicciInput
open HolomorphicPositiveLineKodairaSource CompactTorusEigenbasisSource TorusCharacterInput
open ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T3Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem normalized_component_weight_from_sources
    (hT1 : NormalizedPositiveRicciContactExistence)
    (hKodaira : PositiveHermitianLineAmpleTheorem.{0,0,0})
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (hEigen : KnappTorusEigenbasis) (hCircle : CircleCharacterSource)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
    (hScalar : ∀ p y (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      localScalarCurvature P.tangent P.connection p y hy =
        16 * (n : ℝ) * ((n : ℝ) + 2))
    {r : ℕ} (T : ContinuousTorusAction P.tangent r) :
    letI : CompactSpace M := ⟨P.compact⟩
    letI : PreconnectedSpace M := ⟨P.connected⟩
    ∀ (z : SphereBundleTotal P.tangent)
      (hz : ∀ t, T.representation t • z = z) (ν : Fin r → ℤ),
      (∀ t, torusVerticalCircleCharacter P.tangent hR3 T z hz t = weightCharacter ν t) →
      ∀ w ∈ component P.tangent T z,
        ∃ hw : ∀ t, T.representation t • w = w,
          (∀ t, torusVerticalCircleCharacter P.tangent hR3 T w hw t = weightCharacter ν t) ∧
            HasVerticalWeight P.tangent T w hw ν := by
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  obtain ⟨B,C,hAmple⟩ := exists_normalized_ample_contact_core
    hT1 hKodaira P n hn hDim hScalar
  intro z hz ν hν w hwComponent
  have hw : ∀ t, T.representation t • w = w :=
    (mem_fixedSpherePoints_iff_torus P.tangent T w).mp
      (connectedComponentIn_subset _ _ hwComponent)
  have hchar : ∀ t,
      torusVerticalCircleCharacter P.tangent hR3 T w hw t = weightCharacter ν t := by
    intro t
    exact (character_eq_on_component_of_ample P.tangent hR3 hCircle T
      hFinite hEigen P.connection B C.contact hAmple z hz w hwComponent hw t).trans (hν t)
  exact ⟨hw,hchar,hasVerticalWeight_of_character P.tangent hR3 T w hw ν hchar⟩

end
end QuaternionicSymmetry.ManifoldPositiveQuaternionicComponentWeights
