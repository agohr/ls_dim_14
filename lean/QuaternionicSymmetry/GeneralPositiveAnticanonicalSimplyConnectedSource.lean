import QuaternionicSymmetry.HolomorphicVectorHermitianMetric
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
Ballmann, *Lectures on Kähler Manifolds*, Proposition 3.21 and (3.22),
Appendix A (A.33)-(A.35), §5.4 around (5.59), Theorem 6.12,
Corollary 7.3, and the Fano paragraph following it: a compact connected
complex manifold with positive anticanonical line is simply connected.
Positive curvature of the actual Hermitian anticanonical metric gives a
positive closed `(1,1)` representative and hence a Kähler metric; Calabi–Yau
then gives a (possibly different) positive-Ricci Kähler metric. The latter
is what Kobayashi's theorem consumes. No assertion that the original
Hermitian metric has positive Riemannian Ricci is made here.

The anticanonical core below is the determinant of the actual holomorphic
tangent-bundle core, not an unrelated positive line.
The actual local metric/Levi-Hessian type and this derived input were
reviewed against the cited author copy on 28 September 2026 (BG-C8).
This is a disclosed derived monograph input, not an internal proof of the
Chern-Weil, Calabi-Yau or Kobayashi theorems.
-/

namespace QuaternionicSymmetry.GeneralPositiveAnticanonicalSimplyConnectedSource

open HolomorphicVectorHermitianMetric HolomorphicLineHermitianMetric
open HolomorphicLineCoreClasses HolomorphicDeterminantLine
open scoped Manifold ContDiff
noncomputable section

/-- The genuine generic complex anticanonical determinant line. -/
def anticanonicalLineCore {B F : Type}
    [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [FiniteDimensional ℂ F] [ChartedSpace F B]
    [IsManifold 𝓘(ℂ,F) ∞ B] :
    LineCore.{0} (B := B) 𝓘(ℂ,F) := by
  letI : IsManifold 𝓘(ℂ,F) (∞ + 1) B := by simpa using
    (inferInstance : IsManifold 𝓘(ℂ,F) ∞ B)
  let Z := tangentBundleCore 𝓘(ℂ,F) B
  letI : Z.IsContMDiff 𝓘(ℂ,F) ∞ := tangentBundleCore.isContMDiff
  exact ⟨atlas F B, determinantCore Z, inferInstance⟩

/-- General published positive-anticanonical simply-connectedness theorem,
expressed on the determinant of the *actual* holomorphic tangent core.
This is a literature premise, not a proof of Ballmann/Kobayashi/Calabi–Yau. -/
def BallmannPositiveAnticanonicalSimplyConnected : Prop :=
  ∀ {B F : Type}
    [TopologicalSpace B] [T2Space B] [SecondCountableTopology B]
    [CompactSpace B] [PreconnectedSpace B] [Nonempty B]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    [ChartedSpace F B] [IsManifold 𝓘(ℂ,F) ∞ B]
    (m : HermitianLineMetric (anticanonicalLineCore (B := B) (F := F))),
    m.PositiveChernCurvature → SimplyConnectedSpace B

end
end QuaternionicSymmetry.GeneralPositiveAnticanonicalSimplyConnectedSource
