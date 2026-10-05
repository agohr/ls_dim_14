import QuaternionicSymmetry.ManifoldTwistorPositiveRicciInput

/-! Nitta–Takeuchi, *Contact structures on twistor spaces*, J. Math. Soc.
Japan 39 (1987), §2, pp. 149–151, construct the complex twistor and its
horizontal complex-contact structure for nonzero scalar curvature. Their
(2.10) makes the natural Einstein pseudo-Kähler metric positive Kähler when
the scalar curvature is positive; p. 151 computes the auxiliary metric's
Ricci form as `2(n+1)` times its Kähler form, and hence gives positive Ricci
for the positive rescaled metric. Unlike the scalar-specific formulation of
LeBrun's Theorem 2.1, this statement does not choose a numerical scale.

The input below retains only positive Chern Ricci for the source-selected
actual tangent Hermitian metric. It neither supplies ampleness directly nor
asserts positivity for an arbitrary compatible atlas or contact datum. -/

namespace QuaternionicSymmetry.ManifoldTwistorNittaTakeuchiPositiveRicciInput

open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorLineCoreClasses
open ManifoldPositiveQuaternionicKahlerGeometry ManifoldQuaternionicScalarCurvature
open HolomorphicVectorHermitianMetric
open scoped Manifold ContDiff
noncomputable section

/-- Unnormalized positive-scalar complex/contact/Kähler–Einstein twistor
existence, retaining its positive Chern Ricci consequence on the same
selected actual complex/contact data. Nitta–Takeuchi (1987), §2,
pp. 149–151, especially (2.9), (2.10), and the positive Ricci computation
on p. 151. -/
def PositiveRicciContactExistence : Prop :=
  ∀ {E M : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Nontrivial E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ), 2 ≤ n → Module.finrank ℝ E = 4*n →
    ∃ A : CompatibleComplexAtlas P.tangent P.connection n,
      ∃ _C : NondegenerateHolomorphicContactData P.tangent P.connection n A,
      letI := A.charts
      ∃ m : HermitianBundleMetric (E := ComplexTwistorModel n)
          (A.complexTangentCore P.tangent P.connection),
        m.PositiveChernRicci (A.complexTangentCore P.tangent P.connection)

/-- The all-positive-scale input specializes to the existing normalized
LeBrun interface without changing the selected geometric data. -/
theorem normalized_of_positive (h : PositiveRicciContactExistence) :
    ManifoldTwistorPositiveRicciInput.NormalizedPositiveRicciContactExistence := by
  intro E M _ _ _ _ _ _ _ _ _ _ P n hn hDim _
  exact h P n hn hDim

end
end QuaternionicSymmetry.ManifoldTwistorNittaTakeuchiPositiveRicciInput
