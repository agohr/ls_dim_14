import QuaternionicSymmetry.ManifoldTwistorHolomorphicMapCriterion

/-! Any two actual compatible complex atlases for the same quaternionic
metric and connection have a holomorphic identity comparison. The proof
uses their independently checked smooth-real maps and identical twistor
almost-complex tensor, rather than assuming atlas uniqueness. -/

namespace QuaternionicSymmetry.ManifoldTwistorCompatibleAtlasIdentity
open ManifoldTwistorSphereCore ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorHolomorphicMapCriterion
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem holomorphic_identity {n : ℕ}
    (A B : CompatibleComplexAtlas Q D n) :
    @ContMDiff ℂ _ _ _ _ _ _ 𝓘(ℂ,ComplexTwistorModel n)
      (SphereBundleTotal Q) _ B.charts
      _ _ _ _ _ 𝓘(ℂ,ComplexTwistorModel n)
      (SphereBundleTotal Q) _ A.charts ∞
      (id : SphereBundleTotal Q → SphereBundleTotal Q) := by
  letI := B.charts
  letI := B.realManifold
  letI := B.complexManifold
  exact contMDiff_complex_of_twistor_tensor Q D A
    (id : SphereBundleTotal Q → SphereBundleTotal Q)
    B.smoothToExisting B.tangentI

end
end QuaternionicSymmetry.ManifoldTwistorCompatibleAtlasIdentity
