import QuaternionicSymmetry.FourDimensionalHalfSpinHopfHomeomorph
import QuaternionicSymmetry.ManifoldQuaternionicFourHodgeFiberHomeomorphism

/-! The local projective negative-half-spin line is homeomorphic to the
literal reversed-Q-oriented negative-Hodge unit sphere on an actual tangent
fiber.  Both sides retain their independently constructed topologies.  This
is pointwise and chart-indexed, not yet an SO(4)-associated total bundle. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHodgeFiberHomeomorph

open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinHopfHomeomorph
open ManifoldQuaternionicMetric
  ManifoldQuaternionicFourNegativeHodgeSphere
  ManifoldQuaternionicFourHodgeFiberEquiv
  ManifoldQuaternionicFourHodgeFiberTopology
  ManifoldQuaternionicFourHodgeFiberHomeomorphism
open ManifoldTwistorSphereBundle
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (hdim : Module.finrank ℝ E = 4)

private abbrev TangentHodgeSphere (x : M) :=
  {α : FourDimensionalExteriorHodge.TwoForm
      (TangentSpace 𝓘(ℝ,E) x) //
    α ∈ negativeTangentUnitHalf Q hdim x}

/-- The existing coefficient-to-Hodge formula is a homeomorphism for
the independent canonical exterior topology. -/
def coefficientHodgeHomeomorph (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i) :
    letI := negativeTangentUnitHalfTopology Q hdim x
    coefficientSphere ≃ₜ TangentHodgeSphere Q hdim x := by
  letI := negativeTangentUnitHalfTopology Q hdim x
  exact {
    toEquiv := {
      toFun := localHodgeSphereMap Q hdim i x hi
      invFun := localHodgeSphereInverse Q hdim i x hi
      left_inv := localHodgeSphereInverse_left Q hdim i x hi
      right_inv := localHodgeSphereInverse_right Q hdim i x hi }
    continuous_toFun := localHodgeSphereMap_continuous Q hdim i x hi
    continuous_invFun := localHodgeSphereInverse_continuous Q hdim i x hi }

/-- Explicit projective-spinor to actual tangent negative-Hodge fiber
homeomorphism, with no transported topology on either side. -/
def projectiveHodgeFiberHomeomorph (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i) :
    letI := negativeTangentUnitHalfTopology Q hdim x
    ProjectiveSpinor ≃ₜ TangentHodgeSphere Q hdim x := by
  letI := negativeTangentUnitHalfTopology Q hdim x
  exact projectiveHopfHomeomorph.trans
    (coefficientHodgeHomeomorph Q hdim i x hi)

theorem projectiveHodgeFiberHomeomorph_apply (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i) (p : ProjectiveSpinor) :
    (projectiveHodgeFiberHomeomorph Q hdim i x hi p).1 =
      (localHodgeSphereMap Q hdim i x hi
        (FourDimensionalHalfSpinHopfProjectiveDescent.projectiveHopf p)).1 := rfl

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHodgeFiberHomeomorph
