import QuaternionicSymmetry.ManifoldTwistorNittaTakeuchiPositiveRicciInput
import QuaternionicSymmetry.ManifoldTwistorPositiveContactAmple

/-! For the unnormalized positive-scale Nitta–Takeuchi twistor input,
the existing internal determinant, contact determinant-square gauge, positive-root,
and Kodaira chain proves ampleness of the *same selected* contact quotient.
There is no second complex/contact selection and no unnormalized geometry
comparison assumption. -/

namespace QuaternionicSymmetry.ManifoldTwistorNittaTakeuchiPositiveContactAmple

open ManifoldTwistorNittaTakeuchiPositiveRicciInput
open ManifoldTwistorLineCoreClasses ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorSphereCore ManifoldPositiveQuaternionicKahlerGeometry
open HolomorphicVectorHermitianMetric HolomorphicLineHermitianMetric
open HolomorphicLineCoreClasses HolomorphicLineTensorPowerClasses
open HolomorphicLineHermitianPositiveRoot HolomorphicLineHermitianGauge
open HolomorphicLineHermitianGaugeCurvature
open HolomorphicPositiveLineKodairaSource HolomorphicLineCoreAmpleFiniteMap
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

/-- Positive Chern Ricci on the source-selected actual tangent metric
induces positive curvature of its actual anticanonical determinant line. -/
theorem exists_positive_anticanonical
    (hNT : PositiveRicciContactExistence)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n) :
    ∃ A : CompatibleComplexAtlas P.tangent P.connection n,
      ∃ _C : NondegenerateHolomorphicContactData P.tangent P.connection n A,
      letI := A.charts
      ∃ m : HermitianLineMetric (anticanonicalLineCore P.tangent P.connection A),
        m.PositiveChernCurvature := by
  obtain ⟨A,C,m,hm⟩ := hNT P n hn hDim
  letI := A.charts
  let Z := A.complexTangentCore P.tangent P.connection
  let hZ := A.complexTangentCore_holomorphic P.tangent P.connection
  exact ⟨A,C,m.determinantMetric Z hZ,m.determinantMetric_positive Z hZ hm⟩

/-- Positive actual contact-line ampleness for the *unnormalized* positive
geometry, with the same existential A and C throughout the Ricci,
determinant-square, positive-root, and Kodaira steps. -/
theorem exists_actual_ample_contact_core
    (hNT : PositiveRicciContactExistence)
    (hKodaira : PositiveHermitianLineAmpleTheorem.{0,0,0})
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n) :
    ∃ A : CompatibleComplexAtlas P.tangent P.connection n,
      ∃ C : NondegenerateHolomorphicContactData P.tangent P.connection n A,
      letI := A.charts
      letI := A.complexManifold
      AmpleCore 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore P.tangent P.connection C.contact.line) := by
  obtain ⟨A,C,mAnti,hAnti⟩ :=
    exists_positive_anticanonical hNT P n hn hDim
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
end QuaternionicSymmetry.ManifoldTwistorNittaTakeuchiPositiveContactAmple
