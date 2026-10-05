import QuaternionicSymmetry.ManifoldTwistorBKKPositivePicardHomogeneity
import QuaternionicSymmetry.ManifoldTwistorFullAutHomogeneityGeneration

/-! On the same normalized actual positive twistor, the reviewed derived
BKK alternative and the compact-complex transformation theorem yield an
analytic Picard generator or global generation of the genuine contact line.
The homogeneous branch uses contact-automorphism *transitivity* but the
holomorphic atlas/action of the full biholomorphism group. -/

namespace QuaternionicSymmetry.ManifoldTwistorBKKPositiveGeneration

open GeneralContactFanoPicardHomogeneitySource
open GeneralHolomorphicTransitiveOrbitSource
open GeneralHolomorphicFullAutomorphismLieSource
open ManifoldTwistorBKKPositivePicardHomogeneity
open ManifoldTwistorFullAutHomogeneityGeneration
open ManifoldTwistorPositiveRicciInput
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorLineCoreClasses
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicScalarCurvature
open HolomorphicLineCorePullback
open HolomorphicLineSheafClasses HolomorphicLineSheafClassGroup
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

/-- Same actual twistor/contact line in both branches. The accepted general
inputs are passed explicitly; no contact-group Lie atlas, Hamiltonian
identification, or project-specific generation premise is supplied. -/
theorem exists_normalized_analyticPicard_generator_or_contactLine_generated
    (hT1 : NormalizedPositiveRicciContactExistence)
    (hKodaira : HolomorphicPositiveLineKodairaSource.PositiveHermitianLineAmpleTheorem.{0,0,0})
    (hBKK : AnalyticContactPicardOrHomogeneousCorollary)
    (hLee : LeeHolomorphicTransitiveOrbitSubmersion)
    (hKob : KobayashiCompactAutomorphismTransformation)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
    (hScalar : ∀ p y (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      localScalarCurvature P.tangent P.connection p y hy =
        16 * (n : ℝ) * ((n : ℝ) + 2)) :
    ∃ A : CompatibleComplexAtlas P.tangent P.connection n,
      ∃ C : NondegenerateHolomorphicContactData P.tangent P.connection n A,
        letI := A.charts
        letI := A.complexManifold
        Function.Bijective (fun r : ℤ =>
          (classMulEquiv 𝓘(ℂ,ComplexTwistorModel n)
            (contactClass P.tangent P.connection C.contact.line) :
            SheafClass (B := SphereBundleTotal P.tangent)
              𝓘(ℂ,ComplexTwistorModel n)) ^ r) ∨
        GloballyGenerated 𝓘(ℂ,ComplexTwistorModel n)
          (contactLineCore P.tangent P.connection C.contact.line) := by
  obtain ⟨A, C, hAlt⟩ :=
    exists_normalized_analyticPicard_generator_or_contactAut_transitive
      hT1 hKodaira hBKK P n hn hDim hScalar
  refine ⟨A, C, ?_⟩
  rcases hAlt with hPic | hTrans
  · exact Or.inl hPic
  · exact Or.inr
      (actual_contactLine_generated_of_contactAut_transitive hLee hKob
        P A C hTrans)

end
end QuaternionicSymmetry.ManifoldTwistorBKKPositiveGeneration
