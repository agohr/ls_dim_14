import QuaternionicSymmetry.ManifoldTwistorPositiveContactFromDeterminant
import QuaternionicSymmetry.ManifoldTwistorPositiveRicciInput
import QuaternionicSymmetry.ManifoldTwistorCompactHausdorff
import QuaternionicSymmetry.HolomorphicLineHermitianGaugeCurvature
import QuaternionicSymmetry.HolomorphicPositiveLineKodairaSource

/-! Positive Ricci on LeBrun's *selected* complex/contact twistor gives
ampleness of its actual represented contact quotient line. The chain is
internal apart from the positive-Hermitian Kodaira embedding theorem.
The contact-line metric is constructed using the proved determinant-square gauge.
No contact-line ampleness or Hilbert value is passed as a premise. -/

namespace QuaternionicSymmetry.ManifoldTwistorPositiveContactAmple

open ManifoldTwistorPositiveRicciInput ManifoldTwistorLineCoreClasses
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldPositiveQuaternionicKahlerGeometry ManifoldQuaternionicScalarCurvature
open HolomorphicLineCoreClasses HolomorphicLineTensorPowerClasses
open HolomorphicLineHermitianMetric HolomorphicLineHermitianPositiveRoot
open HolomorphicLineHermitianGauge HolomorphicLineHermitianGaugeCurvature
open HolomorphicPositiveLineKodairaSource HolomorphicLineCoreAmpleFiniteMap
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

/-- On the same T1-selected complex twistor/contact data, positive
anticanonical curvature transfers through the genuine determinant-square gauge,
descends to the positive `(n+1)`-st root, and then Kodaira yields actual
complete-linear-system ampleness of the contact quotient line. -/
theorem exists_normalized_ample_contact_core
    (hT1 : NormalizedPositiveRicciContactExistence)
    (hKodaira : PositiveHermitianLineAmpleTheorem.{0,0,0})
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
    (hScalar : ∀ p y (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      localScalarCurvature P.tangent P.connection p y hy =
        16 * (n : ℝ) * ((n : ℝ) + 2)) :
    ∃ A : CompatibleComplexAtlas P.tangent P.connection n,
      ∃ C : NondegenerateHolomorphicContactData P.tangent P.connection n A,
      letI := A.charts
      letI := A.complexManifold
      AmpleCore 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore P.tangent P.connection C.contact.line) := by
  obtain ⟨A,C,mAnti,hAnti⟩ :=
    exists_positive_anticanonical hT1 P n hn hDim hScalar
  letI := A.charts
  letI := A.complexManifold
  letI : CompactSpace M := ⟨P.compact⟩
  let L := contactLineCore P.tangent P.connection C.contact.line
  let K := anticanonicalLineCore P.tangent P.connection A
  obtain ⟨mL,hmL⟩ :=
    ManifoldTwistorPositiveContactFromDeterminant.exists_positive_contact_metric
      P.tangent P.connection C mAnti hAnti
  exact ⟨A,C,ampleCore_of_positiveHermitian hKodaira L mL hmL⟩

end
end QuaternionicSymmetry.ManifoldTwistorPositiveContactAmple
