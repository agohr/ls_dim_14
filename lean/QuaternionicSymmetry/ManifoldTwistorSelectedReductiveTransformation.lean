import QuaternionicSymmetry.ManifoldTwistorBWW66ReductiveTransformationSource
import QuaternionicSymmetry.ManifoldTwistorSelectedPositiveRicciContactAmple

/-! A normalized actual positive twistor: retain the same T1-selected
complex/contact atlas and positive-Ricci witness, derive contact ampleness,
and apply the sourced full-automorphism transformation conclusion there. -/

namespace QuaternionicSymmetry.ManifoldTwistorSelectedReductiveTransformation

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorPositiveRicciInput
open ManifoldTwistorBWW66ReductiveTransformationSource
open ManifoldTwistorFullAutReductiveTransformationTarget
open ManifoldTwistorSelectedPositiveRicciContactAmple
open HolomorphicLineCoreAmpleFiniteMap HolomorphicPositiveLineKodairaSource
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

/-- Source-selected actual complex/contact atlas with both an ample
contact line and a single reductive, jointly holomorphic full-automorphism
Lie transformation atlas. The two conclusions concern identical `A,C`. -/
theorem exists_normalized_ample_reductive_fullAut_transformation
    (hT1 : NormalizedPositiveRicciContactExistence)
    (hKodaira : PositiveHermitianLineAmpleTheorem.{0,0,0})
    (hBWW : FullAutReductiveTransformationSource)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
    (hScalar : ∀ p y (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      ManifoldQuaternionicScalarCurvature.localScalarCurvature
        P.tangent P.connection p y hy =
        16 * (n : ℝ) * ((n : ℝ) + 2)) :
    ∃ A : CompatibleComplexAtlas P.tangent P.connection n,
      ∃ C : NondegenerateHolomorphicContactData P.tangent P.connection n A,
        (letI := A.charts
         letI := A.complexManifold
         AmpleCore 𝓘(ℂ,ComplexTwistorModel n)
           (ManifoldTwistorLineCoreClasses.contactLineCore
             P.tangent P.connection C.contact.line)) ∧
        FullAutReductiveTransformationConclusion P.tangent P.connection A := by
  obtain ⟨A,C,m,hm⟩ := hT1 P n hn hDim hScalar
  exact ⟨A,C,
    ample_contact_core_of_selected_positiveRicci hKodaira P A C m hm,
    hBWW P n hn hDim A⟩

end
end QuaternionicSymmetry.ManifoldTwistorSelectedReductiveTransformation
