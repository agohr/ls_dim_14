import QuaternionicSymmetry.ManifoldTwistorGeneralContactInstantiation
import QuaternionicSymmetry.GeneralComplexContactSections
import QuaternionicSymmetry.ManifoldTwistorContactContraction

/-! The general contact-geometry section construction is literally the
actual LeBrun quotient-form contraction on the selected twistor. -/

namespace QuaternionicSymmetry.ManifoldTwistorGeneralContractionMatch

open GeneralComplexContactData
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorContactContraction
open HolomorphicVectorFieldPushforward
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
  {n : ℕ} (B : CompatibleComplexAtlas Q D n)
  (C : NondegenerateHolomorphicContactData Q D n B)

theorem general_sectionOfTangent_eq_contraction
    (X : letI := B.charts; letI := B.complexManifold
      Fields (V := ComplexTwistorModel n) (Z := SphereBundleTotal Q)) :
    letI := B.charts
    letI := B.complexManifold
    C.toGeneralContactGeometry.sectionOfTangent X =
      contraction Q D B C.contact X := by
  letI := B.charts
  letI := B.complexManifold
  apply ContMDiffSection.ext
  intro z
  rfl

end
end QuaternionicSymmetry.ManifoldTwistorGeneralContractionMatch
