import QuaternionicSymmetry.ManifoldTwistorUniqueContactFullLieTransfer
import QuaternionicSymmetry.ManifoldTwistorContactInfinitesimalAction
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-! The conditional contact/full group homeomorphism, with its transported
complex atlas, has a genuine invertible complex derivative. Its derivative
intertwines the actual orbit-derived holomorphic vector fields. -/

namespace QuaternionicSymmetry.ManifoldTwistorContactFullLieDerivative

open ManifoldTwistorUniqueContactFullEquiv
open ManifoldTwistorUniqueContactFullLieTransfer
open ManifoldTwistorContactInfinitesimalAction
open ManifoldTwistorContactAutomorphisms
open ManifoldTwistorFullAutomorphisms
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
  (hPreserve : FullPreservesContact Q D B L)

/-- Invertibility is internal to the transported complex manifold structure,
not an additional automorphism-group source premise. -/
theorem contactFull_mfderiv_bijective
    [ChartedSpace V (TwistorHolomorphicAutomorphisms Q D B)]
    [IsManifold 𝓘(ℂ,V) ∞ (TwistorHolomorphicAutomorphisms Q D B)] :
    letI := contactCharts (V := V) Q D B L hPreserve
    Function.Bijective
      (mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V)
        (contactFullHomeomorph Q D B L hPreserve)
        (1 : ContactAutomorphisms Q D B L)) := by
  letI := contactCharts (V := V) Q D B L hPreserve
  letI := contactManifold (V := V) Q D B L hPreserve
  let e := contactFullHomeomorph Q D B L hPreserve
  let Φ : Diffeomorph 𝓘(ℂ,V) 𝓘(ℂ,V)
      (ContactAutomorphisms Q D B L)
      (TwistorHolomorphicAutomorphisms Q D B) ∞ := {
    toEquiv := e.toEquiv
    contMDiff_toFun := ComplexHomeomorphLieAtlasTransfer.holomorphic_toFun e
    contMDiff_invFun := ComplexHomeomorphLieAtlasTransfer.holomorphic_invFun e }
  exact (Φ.mfderivToContinuousLinearEquiv (by simp)
    (1 : ContactAutomorphisms Q D B L)).bijective

/-- Chain-rule naturality for the literal contact/full point action. -/
theorem contact_orbit_derivative_eq_full
    [ChartedSpace V (TwistorHolomorphicAutomorphisms Q D B)]
    [IsManifold 𝓘(ℂ,V) ∞ (TwistorHolomorphicAutomorphisms Q D B)]
    (hFullJoint :
      letI := B.charts
      letI := B.complexManifold
      ContMDiff (𝓘(ℂ,V).prod 𝓘(ℂ,ComplexTwistorModel n))
        𝓘(ℂ,ComplexTwistorModel n) ∞
        (fun p : TwistorHolomorphicAutomorphisms Q D B × SphereBundleTotal Q =>
          p.1.1 p.2))
    (v : letI := contactCharts (V := V) Q D B L hPreserve
      GroupLieAlgebra 𝓘(ℂ,V) (ContactAutomorphisms Q D B L))
    (z : SphereBundleTotal Q) :
    letI := B.charts
    letI := B.complexManifold
    letI := contactCharts (V := V) Q D B L hPreserve
    letI := contactManifold (V := V) Q D B L hPreserve
    contactInfinitesimalActionLinear (V := V) Q D B L
      (contact_joint_holomorphic_of_full (V := V)
        Q D B L hPreserve hFullJoint) v z =
      (mfderiv 𝓘(ℂ,V) 𝓘(ℂ,ComplexTwistorModel n)
        (fun f : TwistorHolomorphicAutomorphisms Q D B => f.1 z) 1)
        ((mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V)
          (contactFullHomeomorph Q D B L hPreserve)
          (1 : ContactAutomorphisms Q D B L)) v) := by
  letI := B.charts
  letI := B.complexManifold
  letI := contactCharts (V := V) Q D B L hPreserve
  letI := contactManifold (V := V) Q D B L hPreserve
  let e := contactFullHomeomorph Q D B L hPreserve
  have heOne : e (1 : ContactAutomorphisms Q D B L) =
      (1 : TwistorHolomorphicAutomorphisms Q D B) := by rfl
  have hFullOrbit : ContMDiff 𝓘(ℂ,V) 𝓘(ℂ,ComplexTwistorModel n) ∞
      (fun f : TwistorHolomorphicAutomorphisms Q D B => f.1 z) :=
    hFullJoint.comp (contMDiff_id.prodMk contMDiff_const)
  have hTo : ContMDiff 𝓘(ℂ,V) 𝓘(ℂ,V) ∞ e :=
    ComplexHomeomorphLieAtlasTransfer.holomorphic_toFun e
  have hChain := mfderiv_comp (1 : ContactAutomorphisms Q D B L)
    (hFullOrbit.mdifferentiable (by simp) (e 1))
    (hTo.mdifferentiable (by simp) (1 : ContactAutomorphisms Q D B L))
  rw [heOne] at hChain
  have hOrbitEq :
      (fun f : ContactAutomorphisms Q D B L => f.1 z) =
        (fun f : TwistorHolomorphicAutomorphisms Q D B => f.1 z) ∘ e := rfl
  rw [contactInfinitesimalActionLinear_apply, hOrbitEq, hChain]
  rfl

end
end QuaternionicSymmetry.ManifoldTwistorContactFullLieDerivative
