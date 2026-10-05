import QuaternionicSymmetry.ManifoldTwistorFullAutomorphismIdentityComponent
import QuaternionicSymmetry.OpenSubgroupComplexLie
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-! Typed, non-opaque complex Lie-structure target for the *actual full*
twistor biholomorphism group. BWW 6.5 treats this group as a complex Lie
group; no source application or complexification is claimed in this file. -/

namespace QuaternionicSymmetry.ManifoldTwistorFullAutomorphismLieTarget

open ManifoldTwistorFullAutomorphisms
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
  {n : ℕ} (B : CompatibleComplexAtlas Q D n)

/-- An atlas on the already constructed compact-open full automorphism
group, with genuinely complex-smooth multiplication and inverse. -/
def FullAutComplexLieConclusion : Prop :=
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
        IsManifold 𝓘(ℂ,V) ∞ (TwistorHolomorphicAutomorphisms Q D B) ∧
        LieGroup 𝓘(ℂ,V) ∞ (TwistorHolomorphicAutomorphisms Q D B)

end
end QuaternionicSymmetry.ManifoldTwistorFullAutomorphismLieTarget
