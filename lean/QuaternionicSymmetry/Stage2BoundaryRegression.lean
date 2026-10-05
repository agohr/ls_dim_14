import QuaternionicSymmetry.Stage2IntrinsicClassification

/-! Interface regressions at the actual seed, induction, source and metric
boundaries. Literal real dimensions exercise the ofHigher/ofFour adapters.
C12 signatures contain no Amann argument; E14 exposes its extra sign source.
The generation checks require the original metric/contact line, with no
normalization scalar, replacement manifold or caller generation hypothesis. -/
namespace QuaternionicSymmetry.Stage2BoundaryRegression

open Stage2IntrinsicClassification Stage2IntrinsicSources Stage2IntrinsicGeometry
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldPositiveTwistorCompatibleFourGeometry
open ManifoldFourDerdzinskiIntrinsicSymmetry ManifoldRiemannianIntrinsicSymmetry
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorLineCoreClasses
open HolomorphicLineCorePullback HolomorphicLineCoreAmpleFiniteMap
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

/-- The separate four-dimensional convention reaches the original metric. -/
theorem four_original_metric (sources : Sources) (hFour : DerdzinskiFourSymmetrySource)
    (P : CompactConnectedPositiveTwistorCompatibleFourGeometry (E := E) (M := M)) :
    IsRiemannianSymmetric P.tangent :=
  intrinsicSymmetric_c12 sources hFour (ofFour P) (by omega)

/-- First seed boundary: real dimension eight. -/
theorem c12_dimension_two (sources : Sources) (hFour : DerdzinskiFourSymmetrySource)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (hDim : Module.finrank ℝ E = 8) : IsRiemannianSymmetric P.tangent :=
  intrinsicSymmetric_c12 sources hFour
    (ofHigher (n := 2) (by omega) P (by omega)) (by omega)

/-- Last seed boundary: real dimension twenty-eight. -/
theorem c12_dimension_seven (sources : Sources) (hFour : DerdzinskiFourSymmetrySource)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (hDim : Module.finrank ℝ E = 28) : IsRiemannianSymmetric P.tangent :=
  intrinsicSymmetric_c12 sources hFour
    (ofHigher (n := 7) (by omega) P (by omega)) (by omega)

/-- First induction boundary: real dimension thirty-two. -/
theorem c12_dimension_eight (sources : Sources) (hFour : DerdzinskiFourSymmetrySource)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (hDim : Module.finrank ℝ E = 32) : IsRiemannianSymmetric P.tangent :=
  intrinsicSymmetric_c12 sources hFour
    (ofHigher (n := 8) (by omega) P (by omega)) (by omega)

/-- Last C12 boundary: no Amann source is supplied. -/
theorem c12_dimension_twelve (sources : Sources) (hFour : DerdzinskiFourSymmetrySource)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (hDim : Module.finrank ℝ E = 48) : IsRiemannianSymmetric P.tangent :=
  intrinsicSymmetric_c12 sources hFour
    (ofHigher (n := 12) (by omega) P (by omega)) (by omega)

/-- First dimension requiring the disclosed extra sign source. -/
theorem e14_dimension_thirteen (sources : Sources) (hFour : DerdzinskiFourSymmetrySource)
    (hAmann : AmannInput)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (hDim : Module.finrank ℝ E = 52) : IsRiemannianSymmetric P.tangent :=
  intrinsicSymmetric_e14 sources hFour hAmann
    (ofHigher (n := 13) (by omega) P (by omega)) (by omega)

/-- Last E14 boundary: the given fifty-six-dimensional metric. -/
theorem e14_dimension_fourteen (sources : Sources) (hFour : DerdzinskiFourSymmetrySource)
    (hAmann : AmannInput)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (hDim : Module.finrank ℝ E = 56) : IsRiemannianSymmetric P.tangent :=
  intrinsicSymmetric_e14 sources hFour hAmann
    (ofHigher (n := 14) (by omega) P (by omega)) (by omega)

/-- Original-metric generation at the C12 boundary, without the sign source. -/
theorem c12_original_contact_line (sources : Sources)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (hDim : Module.finrank ℝ E = 48) :
    ∃ A : CompatibleComplexAtlas P.tangent P.connection 12,
      ∃ C : NondegenerateHolomorphicContactData P.tangent P.connection 12 A,
        letI := A.charts
        letI := A.complexManifold
        GloballyGenerated 𝓘(ℂ,ComplexTwistorModel 12)
          (contactLineCore P.tangent P.connection C.contact.line) ∧
        AmpleCore 𝓘(ℂ,ComplexTwistorModel 12)
          (contactLineCore P.tangent P.connection C.contact.line) :=
  exists_generated_ample_contact_c12 sources 12 (by omega) (by omega) P (by omega)

/-- Both properties concern one literal original-metric line at E14. -/
theorem e14_original_contact_line (sources : Sources) (hAmann : AmannInput)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (hDim : Module.finrank ℝ E = 56) :
    ∃ A : CompatibleComplexAtlas P.tangent P.connection 14,
      ∃ C : NondegenerateHolomorphicContactData P.tangent P.connection 14 A,
        letI := A.charts
        letI := A.complexManifold
        GloballyGenerated 𝓘(ℂ,ComplexTwistorModel 14)
          (contactLineCore P.tangent P.connection C.contact.line) ∧
        AmpleCore 𝓘(ℂ,ComplexTwistorModel 14)
          (contactLineCore P.tangent P.connection C.contact.line) :=
  exists_generated_ample_contact_e14 sources hAmann 14 (by omega) (by omega) P (by omega)

end
end QuaternionicSymmetry.Stage2BoundaryRegression
