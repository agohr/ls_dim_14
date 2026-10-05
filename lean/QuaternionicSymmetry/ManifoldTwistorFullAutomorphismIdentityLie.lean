import QuaternionicSymmetry.ManifoldTwistorFullAutomorphismLieTarget
import QuaternionicSymmetry.ManifoldTwistorFullAutomorphismLift
import QuaternionicSymmetry.ComplexIdentityComponentLie

/-! The full twistor automorphism identity component acquires the inherited
complex Lie atlas once the full group's explicit Lie-structure target is
discharged. This transfer is internal; no BWW source conclusion is inserted. -/

namespace QuaternionicSymmetry.ManifoldTwistorFullAutomorphismIdentityLie

open ManifoldTwistorFullAutomorphisms
open ManifoldTwistorFullAutomorphismLieTarget
open ManifoldTwistorFullAutomorphismLift
open IdentityComponentLie
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T2Space M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
  {n : ℕ} (B : CompatibleComplexAtlas Q D n)

theorem identityComponent_hasComplexLieAtlas
    (hFull : FullAutComplexLieConclusion Q D B) :
    letI := B.charts
    letI := B.complexManifold
    ∃ (V : Type) (hNorm : NormedAddCommGroup V),
      letI : NormedAddCommGroup V := hNorm
      ∃ (hSpace : NormedSpace ℂ V),
        letI : NormedSpace ℂ V := hSpace
        ∃ (hFinite : FiniteDimensional ℂ V)
          (hChart : ChartedSpace V (TwistorHolomorphicAutomorphisms Q D B)),
          letI : FiniteDimensional ℂ V := hFinite
          letI : ChartedSpace V (TwistorHolomorphicAutomorphisms Q D B) := hChart
          let G := TwistorHolomorphicAutomorphisms Q D B
          let hCompChart := ComplexIdentityComponentLie.charts V G
          letI : ChartedSpace V (Component G) := hCompChart
          IsManifold 𝓘(ℂ,V) ∞ (Component G) ∧
          LieGroup 𝓘(ℂ,V) ∞ (Component G) ∧
          ContMDiff 𝓘(ℂ,V) 𝓘(ℂ,V) ∞
            (Subtype.val : Component G → G) := by
  letI := B.charts
  letI := B.complexManifold
  obtain ⟨V,hNorm,hSpace,hFinite,hChart,hManifold,hLie⟩ := hFull
  letI : NormedAddCommGroup V := hNorm
  letI : NormedSpace ℂ V := hSpace
  letI : FiniteDimensional ℂ V := hFinite
  letI : ChartedSpace V (TwistorHolomorphicAutomorphisms Q D B) := hChart
  letI : IsManifold 𝓘(ℂ,V) ∞ (TwistorHolomorphicAutomorphisms Q D B) := hManifold
  letI : LieGroup 𝓘(ℂ,V) ∞ (TwistorHolomorphicAutomorphisms Q D B) := hLie
  refine ⟨V,hNorm,hSpace,hFinite,hChart,?_,?_,?_⟩
  · exact ComplexIdentityComponentLie.manifold V
      (TwistorHolomorphicAutomorphisms Q D B)
  · exact ComplexIdentityComponentLie.lieGroup V
      (TwistorHolomorphicAutomorphisms Q D B)
  · exact ComplexIdentityComponentLie.inclusion_holomorphic V
      (TwistorHolomorphicAutomorphisms Q D B)

end
end QuaternionicSymmetry.ManifoldTwistorFullAutomorphismIdentityLie
