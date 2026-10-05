import QuaternionicSymmetry.ManifoldTwistorBKKPositivePicardUniqueness
import QuaternionicSymmetry.ManifoldTwistorPositiveAnticanonicalSimplyConnected
import QuaternionicSymmetry.ManifoldTwistorHomogeneousContactSymmetrySource

/-!
# Normalized actual twistor: Picard uniqueness or intrinsic metric symmetry

This is the exceptional-metric exit of the reviewed general BKK dichotomy.
On the homogeneous-contact branch, the checked actual twistor simple
connectedness and the separately registered Wolf–LeBrun general
correspondence give a global Riemannian point symmetry for the *same*
positive quaternionic-Kähler metric. The other branch retains both full
analytic Picard generation and the BKK uniqueness conclusion on the same
contact distribution. No concrete Wolf model or extra model-geometry
premise occurs here.
-/

namespace QuaternionicSymmetry.ManifoldTwistorBKKPositivePicardSymmetricExit

open GeneralContactFanoPicardHomogeneitySource
open GeneralContactFanoPicardUniquenessSource
open GeneralPositiveAnticanonicalSimplyConnectedSource
open ManifoldTwistorPositiveRicciInput
open ManifoldTwistorPositiveAnticanonicalSimplyConnected
open ManifoldTwistorBKKPositivePicardUniqueness
open ManifoldTwistorHomogeneousContactSymmetrySource
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorLineCoreClasses
open ManifoldTwistorUniqueContactFullEquiv
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicScalarCurvature
open ManifoldRiemannianIntrinsicSymmetry
open HolomorphicLineSheafClasses HolomorphicLineSheafClassGroup
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

/-- A normalized actual compact positive geometry has either analytic
contact-line Picard generation with full biholomorphic preservation of that
contact structure, or intrinsic Riemannian symmetry of its original metric.
The general literature clauses remain explicit arguments. -/
theorem exists_normalized_analyticPicard_unique_or_intrinsicSymmetric
    (hT1 : NormalizedPositiveRicciContactExistence)
    (hKodaira : HolomorphicPositiveLineKodairaSource.PositiveHermitianLineAmpleTheorem.{0,0,0})
    (hBKK : AnalyticContactPicardOrHomogeneousCorollary)
    (hUnique : AnalyticContactPicardGeneratorPreservesDistribution)
    (hBallmann : BallmannPositiveAnticanonicalSimplyConnected)
    (hWolfLeBrun : HomogeneousContactTwistorSymmetryCorollary)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
    (hScalar : ∀ p y (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      localScalarCurvature P.tangent P.connection p y hy =
        16 * (n : ℝ) * ((n : ℝ) + 2)) :
    (∃ A : CompatibleComplexAtlas P.tangent P.connection n,
      ∃ C : NondegenerateHolomorphicContactData P.tangent P.connection n A,
        letI := A.charts
        letI := A.complexManifold
        Function.Bijective (fun r : ℤ =>
          (classMulEquiv 𝓘(ℂ,ComplexTwistorModel n)
            (contactClass P.tangent P.connection C.contact.line) :
            SheafClass (B := SphereBundleTotal P.tangent)
              𝓘(ℂ,ComplexTwistorModel n)) ^ r) ∧
        FullPreservesContact P.tangent P.connection A C.contact.line) ∨
    IsRiemannianSymmetric P.tangent := by
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  have hSC : SimplyConnectedSpace (SphereBundleTotal P.tangent) :=
    normalized_twistor_simplyConnected hBallmann hT1 P n hn hDim hScalar
  obtain ⟨A, C, hPicOrHom⟩ :=
    exists_normalized_analyticPicard_unique_or_contactAut_transitive
      hT1 hKodaira hBKK hUnique P n hn hDim hScalar
  rcases hPicOrHom with hPic | hHom
  · exact Or.inl ⟨A, C, hPic⟩
  · exact Or.inr <|
      intrinsicSymmetric_of_contactAutomorphisms_transitive
        hWolfLeBrun P n hn hDim A C hSC hHom

end
end QuaternionicSymmetry.ManifoldTwistorBKKPositivePicardSymmetricExit
