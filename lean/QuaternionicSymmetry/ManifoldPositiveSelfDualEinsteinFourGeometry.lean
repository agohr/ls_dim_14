import QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerGeometry
import QuaternionicSymmetry.ManifoldQuaternionicRiemannSymmetry

/-!
The four-dimensional base case has a different geometric input from the
higher-dimensional quaternionic-Kähler holonomy condition. Here Einstein and
self-duality are equations on the curvature of the actual metric, torsion-free
tangent connection. The quaternionic triple fixes the orientation: its three
Kähler forms span the self-dual two-forms. The `selfDualWeyl` field says the
Weyl curvature endomorphism has image in precisely that three-dimensional
span, equivalently that its anti-self-dual half vanishes under the Einstein
equation. No twistor Kähler or classification conclusion is included.

Orientation warning: this condition must not be used to assert integrability
of the existing `S(Q)` construction. With Q identified with the self-dual
half, that twistor requires the Weyl curvature on Q to vanish, whereas this
structure puts the Weyl image in Q. The four-dimensional twistor bridge must
use the opposite half or an explicitly compatible curvature condition.
See LeBrun, *Twistors, Self-Duality, and Spin^c Structures* (2021), Section 1,
Figure 1 and the paragraph immediately following it.
-/

namespace QuaternionicSymmetry.ManifoldPositiveSelfDualEinsteinFourGeometry
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicScalarCurvature
open VectorBundleFrameTransitions
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

/-- The real four-dimensional, positive Einstein and self-dual geometric
input for the Hitchin base case. The corrected curvature in `selfDualWeyl`
is `R - (scalar/12) (w ↦ ⟨v,w⟩u - ⟨u,w⟩v)` in the sign convention where a
positive space form has positive Ricci curvature. -/
structure PositiveSelfDualEinsteinFourGeometry extends
    PositiveQuaternionicKahlerGeometry (E := E) (M := M) where
  realDimension : Module.finrank ℝ E = 4
  einstein : ∀ (p : M) (y : E)
      (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (v w : E),
      localRicci tangent connection p y hy v w =
        (localScalarCurvature tangent connection p y hy / 4) * inner ℝ v w
  selfDualWeyl : ∀ (p : M) (y : E)
      (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (u v : E),
      ∃ a : Fin 3 → ℝ, ∀ w : E,
        adaptedCurvature tangent connection p y hy u v w -
          (localScalarCurvature tangent connection p y hy / 12) •
            ((inner ℝ v w) • u - (inner ℝ u w) • v) =
          (QuaternionicFrameReduction.synth
            (tangent.reduction.Q (achart E p)) a) w

theorem PositiveSelfDualEinsteinFourGeometry.quaternionicDimension_one
    (P : PositiveSelfDualEinsteinFourGeometry (E := E) (M := M))
    (i : atlas E M) :
    (P.tangent.reduction.Q i).quaternionicDimension = 1 := by
  have h := (P.tangent.reduction.Q i).real_finrank
  rw [P.realDimension] at h
  omega

end
end QuaternionicSymmetry.ManifoldPositiveSelfDualEinsteinFourGeometry
