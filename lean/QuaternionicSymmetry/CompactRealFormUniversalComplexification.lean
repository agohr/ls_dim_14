import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Analysis.Complex.Basic

/-! A group-level, rather than merely tangent-space, universal property for
the complexification of a compact real Lie group. Holomorphic extension to
every finite-dimensional complex Lie group is unique. This is a target for
BWW 6.5; no group is asserted to satisfy it here. -/

namespace QuaternionicSymmetry.CompactRealFormUniversalComplexification

open scoped Manifold ContDiff
noncomputable section

variable {K G VC : Type} [Group K] [TopologicalSpace K]
  [Group G] [TopologicalSpace G]
  [NormedAddCommGroup VC] [NormedSpace ℂ VC]
  [ChartedSpace VC G] [LieGroup 𝓘(ℂ,VC) ∞ G]

/-- The actual homomorphism is injective and continuous, and every
continuous compact-real-group homomorphism to a complex Lie group extends
uniquely to a holomorphic homomorphism on `G`. The compactness/Lie
properties of `K` are supplied at application sites, not hidden in this
definition. The target is finite-dimensional, Hausdorff and second-countable;
its `IsManifold` instance is inherited from `LieGroup`. -/
def IsUniversalComplexification (ι : K →* G) : Prop :=
  Continuous ι ∧ Function.Injective ι ∧
  ∀ {W H : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W]
    [TopologicalSpace H] [T2Space H] [SecondCountableTopology H]
    [ChartedSpace W H] [Group H]
    [LieGroup 𝓘(ℂ,W) ∞ H],
    ∀ f : K →* H, Continuous f →
      ∃! Φ : G →* H,
        ContMDiff 𝓘(ℂ,VC) 𝓘(ℂ,W) ∞ Φ ∧ Φ.comp ι = f

end
end QuaternionicSymmetry.CompactRealFormUniversalComplexification
