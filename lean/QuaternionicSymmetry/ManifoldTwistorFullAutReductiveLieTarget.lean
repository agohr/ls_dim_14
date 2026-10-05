import QuaternionicSymmetry.ManifoldTwistorFullAutomorphismLieTarget
import Mathlib.Geometry.Manifold.GroupLieAlgebra
import Mathlib.Algebra.Lie.Semisimple.Defs

/-! A mathematically literal reductivity target for BWW Theorem 6.6:
the radical of the *actual tangent Lie algebra* of the full twistor
automorphism group is central. This is only a target Prop, not a sourced
proof of the theorem or an algebraic-group comparison. -/

namespace QuaternionicSymmetry.ManifoldTwistorFullAutReductiveLieTarget

open ManifoldTwistorFullAutomorphisms
open ManifoldTwistorFullAutomorphismLieTarget
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

def FullAutReductiveLieConclusion : Prop :=
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
        ∃ hLie : LieGroup 𝓘(ℂ,V) ∞ (TwistorHolomorphicAutomorphisms Q D B),
          letI : LieGroup 𝓘(ℂ,V) ∞
              (TwistorHolomorphicAutomorphisms Q D B) := hLie
          letI : CompleteSpace V := FiniteDimensional.complete ℂ V
          letI : ENat.LEInfty (minSmoothness ℂ 3) := by
            simpa only [minSmoothness_of_isRCLikeNormedField] using
              (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))
          letI : LieGroup 𝓘(ℂ,V) (minSmoothness ℂ 3)
              (TwistorHolomorphicAutomorphisms Q D B) :=
            LieGroup.of_le (ENat.LEInfty.out)
          LieAlgebra.HasCentralRadical ℂ
            (GroupLieAlgebra 𝓘(ℂ,V)
              (TwistorHolomorphicAutomorphisms Q D B))

theorem fullAutComplexLie_of_reductive
    (h : FullAutReductiveLieConclusion Q D B) :
    FullAutComplexLieConclusion Q D B := by
  obtain ⟨V,hNorm,hSpace,hFinite,hChart,hManifold,hLie,_⟩ := h
  exact ⟨V,hNorm,hSpace,hFinite,hChart,hManifold,hLie⟩

end
end QuaternionicSymmetry.ManifoldTwistorFullAutReductiveLieTarget
