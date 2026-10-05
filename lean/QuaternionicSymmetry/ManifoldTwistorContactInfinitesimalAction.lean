import QuaternionicSymmetry.HolomorphicFamilyInfinitesimalLinear
import QuaternionicSymmetry.HolomorphicVectorFieldPushforward
import QuaternionicSymmetry.ManifoldTwistorContactAutomorphisms
import QuaternionicSymmetry.ManifoldTwistorContactAutomorphismTopology
import Mathlib.Geometry.Manifold.GroupLieAlgebra

/-! Differentiate a genuine jointly holomorphic contact-automorphism
action in its supplied complex Lie atlas. The result lands in actual
holomorphic tangent fields and is complex-linear. This proves only the
infinitesimal-action map and its pointwise derivative formula; it does
not assert the contact Hamiltonian contraction is bijective. -/

namespace QuaternionicSymmetry.ManifoldTwistorContactInfinitesimalAction

open HolomorphicFamilyInfinitesimalLinear
open HolomorphicVectorFieldPushforward
open ManifoldTwistorContactAutomorphisms
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section

variable {E M V : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
  {n : ℕ} (B : CompatibleComplexAtlas Q D n)
  (L : HolomorphicContactLine Q D n B)

/-- The true infinitesimal contact action, without any NT theorem:
holomorphicity follows by differentiating the actual holomorphic joint
evaluation; linearity follows from linearity of its mfderiv. -/
def contactInfinitesimalActionLinear
    [ChartedSpace V (ContactAutomorphisms Q D B L)]
    [IsManifold 𝓘(ℂ,V) ∞ (ContactAutomorphisms Q D B L)]
    (hJoint :
      letI := B.charts
      letI := B.complexManifold
      ContMDiff (𝓘(ℂ,V).prod 𝓘(ℂ,ComplexTwistorModel n))
        𝓘(ℂ,ComplexTwistorModel n) ∞
        (fun p : ContactAutomorphisms Q D B L × SphereBundleTotal Q =>
          p.1.1 p.2)) :
    letI := B.charts
    letI := B.complexManifold
    GroupLieAlgebra 𝓘(ℂ,V) (ContactAutomorphisms Q D B L) →ₗ[ℂ]
      Fields (V := ComplexTwistorModel n) (Z := SphereBundleTotal Q) := by
  letI := B.charts
  letI := B.complexManifold
  exact infinitesimalActionLinear
    (fun p : ContactAutomorphisms Q D B L × SphereBundleTotal Q => p.1.1 p.2)
    1 hJoint (by intro z; rfl)

theorem contactInfinitesimalActionLinear_apply
    [ChartedSpace V (ContactAutomorphisms Q D B L)]
    [IsManifold 𝓘(ℂ,V) ∞ (ContactAutomorphisms Q D B L)]
    (hJoint :
      letI := B.charts
      letI := B.complexManifold
      ContMDiff (𝓘(ℂ,V).prod 𝓘(ℂ,ComplexTwistorModel n))
        𝓘(ℂ,ComplexTwistorModel n) ∞
        (fun p : ContactAutomorphisms Q D B L × SphereBundleTotal Q =>
          p.1.1 p.2))
    (v : GroupLieAlgebra 𝓘(ℂ,V) (ContactAutomorphisms Q D B L))
    (z : SphereBundleTotal Q) :
    letI := B.charts
    letI := B.complexManifold
    contactInfinitesimalActionLinear (V := V) Q D B L hJoint v z =
      (mfderiv 𝓘(ℂ,V) 𝓘(ℂ,ComplexTwistorModel n)
        (fun f : ContactAutomorphisms Q D B L => f.1 z) 1) v := by
  letI := B.charts
  letI := B.complexManifold
  exact infinitesimalActionLinear_apply
    (fun p : ContactAutomorphisms Q D B L × SphereBundleTotal Q => p.1.1 p.2)
    1 hJoint (by intro y; rfl) v z

end
end QuaternionicSymmetry.ManifoldTwistorContactInfinitesimalAction
