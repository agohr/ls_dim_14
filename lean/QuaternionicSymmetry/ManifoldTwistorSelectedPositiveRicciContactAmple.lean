import QuaternionicSymmetry.ManifoldTwistorPositiveContactAmple

/-!
# Ampleness from a retained positive-Ricci tangent metric

The published T1 source selects one complex/contact twistor and a positive
Chern-Ricci Hermitian tangent metric. This helper retains that *same*
metric and atlas while deriving ampleness of its contact quotient line:
positive determinant curvature, the internally proved contact determinant-square
isomorphism, a positive root metric, and general Kodaira. It does not
identify separately selected Lie-group atlases or assert reductivity.
-/

namespace QuaternionicSymmetry.ManifoldTwistorSelectedPositiveRicciContactAmple

open ManifoldTwistorPositiveRicciInput ManifoldTwistorLineCoreClasses
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldPositiveQuaternionicKahlerGeometry
open HolomorphicVectorHermitianMetric
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

/-- A positive-Chern-Ricci tangent metric on one actual selected twistor
produces an ample contact line on that identical complex/contact atlas. -/
theorem ample_contact_core_of_selected_positiveRicci
    (hKodaira : PositiveHermitianLineAmpleTheorem.{0,0,0})
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    {n : ℕ} (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)
    (m :
      letI := A.charts
      HermitianBundleMetric (E := ComplexTwistorModel n)
        (A.complexTangentCore P.tangent P.connection))
    (hm :
      letI := A.charts
      m.PositiveChernRicci
        (A.complexTangentCore P.tangent P.connection)) :
    letI := A.charts
    letI := A.complexManifold
    AmpleCore 𝓘(ℂ,ComplexTwistorModel n)
      (contactLineCore P.tangent P.connection C.contact.line) := by
  letI := A.charts
  letI := A.complexManifold
  letI : CompactSpace M := ⟨P.compact⟩
  let Z := A.complexTangentCore P.tangent P.connection
  let hZ := A.complexTangentCore_holomorphic P.tangent P.connection
  let L := contactLineCore P.tangent P.connection C.contact.line
  let K := anticanonicalLineCore P.tangent P.connection A
  let mAnti := m.determinantMetric Z hZ
  have hAnti : mAnti.PositiveChernCurvature K :=
    m.determinantMetric_positive Z hZ hm
  obtain ⟨mL,hmL⟩ :=
    ManifoldTwistorPositiveContactFromDeterminant.exists_positive_contact_metric
      P.tangent P.connection C mAnti hAnti
  exact ampleCore_of_positiveHermitian hKodaira L mL hmL

end
end QuaternionicSymmetry.ManifoldTwistorSelectedPositiveRicciContactAmple
