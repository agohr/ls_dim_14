import QuaternionicSymmetry.ComplexHomeomorphLieAtlasTransfer
import QuaternionicSymmetry.ManifoldTwistorUniqueContactFullEquiv

/-! Conditional transport of the *same* full-automorphism complex Lie
structure to the actual contact group, when every biholomorphism preserves
the selected contact distribution. Joint holomorphicity is transported
only when supplied for the full-automorphism action in that same atlas. -/

namespace QuaternionicSymmetry.ManifoldTwistorUniqueContactFullLieTransfer

open ManifoldTwistorUniqueContactFullEquiv
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

def contactCharts [ChartedSpace V (TwistorHolomorphicAutomorphisms Q D B)] :
    ChartedSpace V (ContactAutomorphisms Q D B L) :=
  ComplexHomeomorphLieAtlasTransfer.charts
    (contactFullHomeomorph Q D B L hPreserve)

def contactManifold [ChartedSpace V (TwistorHolomorphicAutomorphisms Q D B)]
    [IsManifold 𝓘(ℂ,V) ∞ (TwistorHolomorphicAutomorphisms Q D B)] :
    letI := contactCharts (V := V) Q D B L hPreserve
    IsManifold 𝓘(ℂ,V) ∞ (ContactAutomorphisms Q D B L) :=
  ComplexHomeomorphLieAtlasTransfer.manifold
    (contactFullHomeomorph Q D B L hPreserve)

def contactLieGroup [ChartedSpace V (TwistorHolomorphicAutomorphisms Q D B)]
    [LieGroup 𝓘(ℂ,V) ∞ (TwistorHolomorphicAutomorphisms Q D B)] :
    letI := contactCharts (V := V) Q D B L hPreserve
    LieGroup 𝓘(ℂ,V) ∞ (ContactAutomorphisms Q D B L) := by
  apply ComplexHomeomorphLieAtlasTransfer.lieGroup
    (contactFullHomeomorph Q D B L hPreserve)
  · intro f g
    rfl
  · intro f
    rfl

/-- Holomorphic joint evaluation on full Aut descends to the contact group
through the literal contact/full homeomorphism and transported atlas. -/
theorem contact_joint_holomorphic_of_full
    [ChartedSpace V (TwistorHolomorphicAutomorphisms Q D B)]
    [IsManifold 𝓘(ℂ,V) ∞ (TwistorHolomorphicAutomorphisms Q D B)]
    (hJoint :
      letI := B.charts
      letI := B.complexManifold
      ContMDiff (𝓘(ℂ,V).prod 𝓘(ℂ,ComplexTwistorModel n))
        𝓘(ℂ,ComplexTwistorModel n) ∞
        (fun p : TwistorHolomorphicAutomorphisms Q D B × SphereBundleTotal Q =>
          p.1.1 p.2)) :
    letI := B.charts
    letI := B.complexManifold
    letI := contactCharts (V := V) Q D B L hPreserve
    ContMDiff (𝓘(ℂ,V).prod 𝓘(ℂ,ComplexTwistorModel n))
      𝓘(ℂ,ComplexTwistorModel n) ∞
      (fun p : ContactAutomorphisms Q D B L × SphereBundleTotal Q =>
        p.1.1 p.2) := by
  letI := B.charts
  letI := B.complexManifold
  letI := contactCharts (V := V) Q D B L hPreserve
  letI := contactManifold (V := V) Q D B L hPreserve
  have hForget : ContMDiff 𝓘(ℂ,V) 𝓘(ℂ,V) ∞
      (contactFullHomeomorph Q D B L hPreserve) :=
    ComplexHomeomorphLieAtlasTransfer.holomorphic_toFun
      (contactFullHomeomorph Q D B L hPreserve)
  have hPair : ContMDiff
      (𝓘(ℂ,V).prod 𝓘(ℂ,ComplexTwistorModel n))
      (𝓘(ℂ,V).prod 𝓘(ℂ,ComplexTwistorModel n)) ∞
      (fun p : ContactAutomorphisms Q D B L × SphereBundleTotal Q =>
        (contactFullHomeomorph Q D B L hPreserve p.1, p.2)) :=
    (hForget.comp contMDiff_fst).prodMk contMDiff_snd
  convert hJoint.comp hPair using 1

end
end QuaternionicSymmetry.ManifoldTwistorUniqueContactFullLieTransfer
