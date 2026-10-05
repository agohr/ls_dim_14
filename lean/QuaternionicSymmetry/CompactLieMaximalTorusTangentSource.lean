import QuaternionicSymmetry.CompactLieTorusInputs
import Mathlib.Geometry.Manifold.GroupLieAlgebra

/-! A narrow BG-L1 (Knapp IV.5 Proposition 4.30) interface for the
*same* selected maximal torus. Its Lie algebra is expressed intrinsically
using velocities of smooth curves lying in that torus's actual image.
Thus no smoothness of the chosen continuous parametrization is silently
assumed. The source assertion is the maximal-abelian correspondence, not
a new classification or complexification hypothesis. -/

namespace QuaternionicSymmetry.CompactLieMaximalTorusTangentSource

open CompactLieTorusInputs
open scoped Manifold ContDiff
noncomputable section

variable {V G : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [Group G] [TopologicalSpace G] [ChartedSpace V G]
  [LieGroup 𝓘(ℝ,V) ∞ G]

/-- Intrinsic real tangent vectors to smooth curves contained in the
image of the given maximal torus. We use the image, not a derivative of
its merely continuous chosen parametrization. -/
def torusCurveVelocities {r : ℕ} (T : TorusEmbedding G r) :
    Set (GroupLieAlgebra 𝓘(ℝ,V) G) :=
  {v | ∃ c : ℝ → G,
    c 0 = 1 ∧ (∀ s : ℝ, c s ∈ T.hom.range) ∧
    ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,V) ∞ c ∧
    mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,V) c 0 (1 : ℝ) = v}

def torusLieSpan {r : ℕ} (T : TorusEmbedding G r) :
    Submodule ℝ (GroupLieAlgebra 𝓘(ℝ,V) G) :=
  Submodule.span ℝ (torusCurveVelocities T)

/-- Exact selected-torus consequence of BG-L1's maximal-torus/maximal-
abelian-Lie-subalgebra correspondence. The hypotheses explicitly require
an actual compact connected finite-dimensional real Lie group. -/
def MaximalTorusLieCorrespondenceOnModel : Prop :=
  ∀ [FiniteDimensional ℝ V] [CompactSpace G] [ConnectedSpace G]
    [T2Space G] [SecondCountableTopology G],
    ∀ {r : ℕ} (T : TorusEmbedding G r), T.IsMaximal G →
      (∀ (x : GroupLieAlgebra 𝓘(ℝ,V) G), x ∈ torusLieSpan (V := V) T →
        ∀ (y : GroupLieAlgebra 𝓘(ℝ,V) G),
          y ∈ torusLieSpan (V := V) T → ⁅x,y⁆ = 0) ∧
      (∀ x : GroupLieAlgebra 𝓘(ℝ,V) G,
        (∀ (y : GroupLieAlgebra 𝓘(ℝ,V) G),
          y ∈ torusLieSpan (V := V) T → ⁅x,y⁆ = 0) →
        x ∈ torusLieSpan (V := V) T)

/-- Uniformly registered BG-L1 correspondence, to be instantiated at the
actual BG-R3 isometry Lie atlas. This is the part of Knapp IV.5,
Proposition 4.30 not retained by the earlier existence-only projection. -/
def MaximalTorusLieCorrespondenceSource : Prop :=
  ∀ (W H : Type) [NormedAddCommGroup W] [NormedSpace ℝ W]
    [Group H] [TopologicalSpace H] [ChartedSpace W H]
    [LieGroup 𝓘(ℝ,W) ∞ H],
    MaximalTorusLieCorrespondenceOnModel (V := W) (G := H)

end
end QuaternionicSymmetry.CompactLieMaximalTorusTangentSource
