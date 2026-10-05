import QuaternionicSymmetry.ManifoldTwistorPositiveContactAmple
import QuaternionicSymmetry.ManifoldTwistorBKKAnalyticPicardApplication
import QuaternionicSymmetry.ManifoldTwistorBKKPicardUniquenessApplication
import QuaternionicSymmetry.ManifoldTwistorPicardContactLieAction
import QuaternionicSymmetry.ManifoldTwistorPositiveAnticanonicalSimplyConnected
import QuaternionicSymmetry.ManifoldTwistorHomogeneousContactSymmetrySource

/-!
# Same-atlas positive-twistor Picard/Lie reduction or intrinsic symmetry

The selected actual contact atlas, contact form, and ampleness witness are
retained together. Hence the analytic Picard-generator branch can apply
reviewed BKK uniqueness and the general Kobayashi full-automorphism theorem
to this very contact group, giving a finite-dimensional complex Lie atlas
with jointly holomorphic action. On the homogeneous-contact branch, actual
twistor simple connectedness and Wolf–LeBrun give intrinsic symmetry of the
original positive quaternionic-Kähler metric. No atlas or ampleness is
supplied as an actual-model premise and no second contact structure is
selected after the dichotomy.
-/

namespace QuaternionicSymmetry.ManifoldTwistorBKKPositivePicardLieReduction

open GeneralContactFanoPicardHomogeneitySource
open GeneralContactFanoPicardUniquenessSource
open GeneralHolomorphicFullAutomorphismLieSource
open GeneralPositiveAnticanonicalSimplyConnectedSource
open ManifoldTwistorPositiveContactAmple ManifoldTwistorPositiveRicciInput
open ManifoldTwistorBKKAnalyticPicardApplication
open ManifoldTwistorBKKPicardUniquenessApplication
open ManifoldTwistorPicardContactLieAction
open ManifoldTwistorPositiveAnticanonicalSimplyConnected
open ManifoldTwistorHomogeneousContactSymmetrySource
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorLineCoreClasses ManifoldTwistorUniqueContactFullEquiv
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicScalarCurvature
open ManifoldRiemannianIntrinsicSymmetry
open HolomorphicLineCoreAmpleFiniteMap
open HolomorphicLineSheafClasses HolomorphicLineSheafClassGroup
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

/-- The normalized actual positive-PQK twistor either retains one selected
ample contact line which generates full analytic Picard and carries the
actual finite-dimensional holomorphic contact Lie action, or the original
metric is globally Riemannian symmetric. Full distribution preservation is
recorded on the Picard branch for contact/full-group transport. -/
theorem exists_normalized_analyticPicard_contactLie_or_intrinsicSymmetric
    (hT1 : NormalizedPositiveRicciContactExistence)
    (hKodaira : HolomorphicPositiveLineKodairaSource.PositiveHermitianLineAmpleTheorem.{0,0,0})
    (hBKK : AnalyticContactPicardOrHomogeneousCorollary)
    (hUnique : AnalyticContactPicardGeneratorPreservesDistribution)
    (hKob : KobayashiCompactAutomorphismTransformation)
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
        AmpleCore 𝓘(ℂ,ComplexTwistorModel n)
          (contactLineCore P.tangent P.connection C.contact.line) ∧
        Function.Bijective (fun r : ℤ =>
          (classMulEquiv 𝓘(ℂ,ComplexTwistorModel n)
            (contactClass P.tangent P.connection C.contact.line) :
            SheafClass (B := SphereBundleTotal P.tangent)
              𝓘(ℂ,ComplexTwistorModel n)) ^ r) ∧
        FullPreservesContact P.tangent P.connection A C.contact.line ∧
        ContactLieActionConclusion P A C) ∨
    IsRiemannianSymmetric P.tangent := by
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  have hSC : SimplyConnectedSpace (SphereBundleTotal P.tangent) :=
    normalized_twistor_simplyConnected hBallmann hT1 P n hn hDim hScalar
  obtain ⟨A, C, hAmple⟩ := exists_normalized_ample_contact_core
    hT1 hKodaira P n hn hDim hScalar
  rcases analyticPicard_generator_or_contactAut_transitive
      hBKK P n (by omega) A C hAmple with hPic | hHom
  · have hFull := fullPreservesContact_of_analyticPicard_generator
      hUnique P n (by omega) A C hAmple hPic
    have hLie := contact_lie_action_of_analyticPicard_generator
      hUnique hKob P n (by omega) A C hAmple hPic
    exact Or.inl ⟨A, C, hAmple, hPic, hFull, hLie⟩
  · exact Or.inr <|
      intrinsicSymmetric_of_contactAutomorphisms_transitive
        hWolfLeBrun P n hn hDim A C hSC hHom

end
end QuaternionicSymmetry.ManifoldTwistorBKKPositivePicardLieReduction
