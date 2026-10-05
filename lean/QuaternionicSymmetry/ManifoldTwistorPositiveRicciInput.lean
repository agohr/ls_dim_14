import QuaternionicSymmetry.HolomorphicVectorHermitianMetric
import QuaternionicSymmetry.ManifoldTwistorLeBrunExistenceInput
import QuaternionicSymmetry.ManifoldTwistorLineCoreClasses

/-! The positive-Ricci metric part of LeBrun 1995, Theorem 2.1 (p.10
of the author PDF). The theorem supplies a Kähler–Einstein twistor metric
of scalar curvature `8(n+1)(2n+1)` for a base normalized to `16n(n+2)`.
We retain its weaker positive Chern Ricci conclusion, on an actual smooth
positive-definite Hermitian tangent metric. Demailly VIII §6, Definition
(6.6) and equation (6.7), p.378, identify that form in holomorphic frames
as `-i∂∂̄log det(gram)`. For a Kähler metric this is the Ricci form.

The contact line is not declared positive or ample in this source. Its
canonical-power identification, metric transport, positive root and the
general Kodaira theorem must still be applied internally. -/

namespace QuaternionicSymmetry.ManifoldTwistorPositiveRicciInput

open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorLineCoreClasses
open ManifoldPositiveQuaternionicKahlerGeometry ManifoldQuaternionicScalarCurvature
open ManifoldPositiveQuaternionicKahlerHomothety ManifoldQuaternionicKSWEq38Input
open HolomorphicVectorHermitianMetric HolomorphicLineHermitianMetric
open scoped Manifold ContDiff
noncomputable section

/-- The literal positive Kähler–Einstein twistor existence theorem,
weakened only to its positive Ricci consequence. All metric entries,
overlaps and Ricci Hessians refer to the genuine complex tangent core. -/
def NormalizedPositiveRicciContactExistence : Prop :=
  ∀ {E M : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Nontrivial E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ), 2 ≤ n → Module.finrank ℝ E = 4*n →
    (∀ p y (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      localScalarCurvature P.tangent P.connection p y hy =
        16 * (n : ℝ) * ((n : ℝ) + 2)) →
    ∃ A : CompatibleComplexAtlas P.tangent P.connection n,
      ∃ _C : NondegenerateHolomorphicContactData P.tangent P.connection n A,
      letI := A.charts
      ∃ m : HermitianBundleMetric (E := ComplexTwistorModel n)
          (A.complexTangentCore P.tangent P.connection),
        m.PositiveChernRicci (A.complexTangentCore P.tangent P.connection)

/-- The metric part and the complex/contact part use the same T1-selected
geometry; no second independent existence theorem is required. -/
theorem complexContactExistence_of_positiveRicci
    (hT1 : NormalizedPositiveRicciContactExistence) :
    NormalizedComplexContactExistence.{0,0} := by
  intro E M _ _ _ _ _ _ _ _ _ _ P n hn hDim hScalar
  obtain ⟨A,C,m,hm⟩ := hT1 P n hn hDim hScalar
  exact ⟨A,⟨C⟩⟩

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

/-- Derive a positive metric on the actual anticanonical determinant line
from the source-selected genuine positive-Ricci tangent metric. -/
theorem exists_positive_anticanonical
    (hT1 : NormalizedPositiveRicciContactExistence)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
    (hScalar : ∀ p y (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      localScalarCurvature P.tangent P.connection p y hy =
        16 * (n : ℝ) * ((n : ℝ) + 2)) :
    ∃ A : CompatibleComplexAtlas P.tangent P.connection n,
      ∃ _C : NondegenerateHolomorphicContactData P.tangent P.connection n A,
      letI := A.charts
      ∃ m : HermitianLineMetric (anticanonicalLineCore P.tangent P.connection A),
        m.PositiveChernCurvature := by
  obtain ⟨A,C,m,hm⟩ := hT1 P n hn hDim hScalar
  letI := A.charts
  let Z := A.complexTangentCore P.tangent P.connection
  let hZ := A.complexTangentCore_holomorphic P.tangent P.connection
  exact ⟨A,C,m.determinantMetric Z hZ,m.determinantMetric_positive Z hZ hm⟩

/-- Apply the same literal positive-Ricci source to an arbitrary positive
input after the already checked actual metric homothety. -/
theorem exists_rescaled_positive_anticanonical
    (hT1 : NormalizedPositiveRicciContactExistence)
    (S : QuaternionicStructure E)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (heq38 : KSWEq38OnModel (E := E) (M := M))
    (hn : 2 ≤ S.quaternionicDimension) :
    ∃ s : ℝ, ∃ hs : 0 < s,
      ∃ A : CompatibleComplexAtlas
        (rescaleCompact P s hs).tangent (rescaleCompact P s hs).connection
        S.quaternionicDimension,
      ∃ _C : NondegenerateHolomorphicContactData
        (rescaleCompact P s hs).tangent (rescaleCompact P s hs).connection
        S.quaternionicDimension A,
      letI := A.charts
      ∃ m : HermitianLineMetric (anticanonicalLineCore
          (rescaleCompact P s hs).tangent (rescaleCompact P s hs).connection A),
        m.PositiveChernCurvature := by
  obtain ⟨s,hs,hScalar⟩ := exists_normalized_scalar S P heq38 hn
  obtain ⟨A,C,m,hm⟩ := exists_positive_anticanonical hT1
    (rescaleCompact P s hs) S.quaternionicDimension hn S.real_finrank hScalar
  exact ⟨s,hs,A,C,m,hm⟩

end
end QuaternionicSymmetry.ManifoldTwistorPositiveRicciInput
