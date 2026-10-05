import QuaternionicSymmetry.CompactSymplecticMatrixUnits
import QuaternionicSymmetry.GeneralClosedSubgroupLieSource
import Mathlib.Geometry.Manifold.SmoothEmbedding

/-!
The exact general background boundary for the first concrete compact
symplectic model: Lee, *Introduction to Smooth Manifolds*, 2nd ed.,
Theorem 20.12 (Closed Subgroup Theorem), printed pp.523–525, PDF p.540.
The theorem says that a closed subgroup of a real Lie group has a real
embedded Lie-subgroup structure. It does not supply a quotient metric,
quaternionic atlas, or Wolf-space classification.

Our ambient `Units (Matrix ... ℂ)` is Mathlib's actual real Lie group, and
`toMatrixUnits_closedEmbedding` proves that the actual compact symplectic
matrix group is a closed subgroup of it. The only source-facing premise
below is the resulting real embedded Lie atlas. The dimension is existential;
no desired quaternionic-projective dimension is supplied.
-/

namespace QuaternionicSymmetry.CompactSymplecticClosedSubgroupSource

open CompactSymplecticMatrixUnits Topology Manifold
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)
private abbrev Mat (n : ℕ) :=
  Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℂ

/-- The full geometric conclusion of the closed-subgroup theorem for the
actual compact symplectic matrix group. The inclusion is required to be a
smooth embedding, not merely a continuous monomorphism. -/
structure EmbeddedRealLieAtlas (n d : ℕ) where
  charts : ChartedSpace (Fin d → ℝ) (G n)
  manifold : letI := charts
    IsManifold 𝓘(ℝ, Fin d → ℝ) ∞ (G n)
  lieGroup : letI := charts
    LieGroup 𝓘(ℝ, Fin d → ℝ) ∞ (G n)
  smoothEmbedding : letI := charts
    IsSmoothEmbedding 𝓘(ℝ, Fin d → ℝ)
      𝓘(ℝ, Mat n) ∞ (toMatrixUnits n)

/-- The literal Lee 20.12 application to the checked closed subgroup of
matrix units. This is a source premise, not a custom axiom or a model
classification statement. -/
def LeeClosedSubgroupForCompactSymplectic : Prop :=
  ∀ n : ℕ, ∃ d : ℕ, Nonempty (EmbeddedRealLieAtlas n d)

/-- The checked matrix-unit inclusion satisfies every geometric
hypothesis in the general Lee 20.12 source interface. -/
theorem leeClosedSubgroupForCompactSymplectic_of_general
    (hLee : GeneralClosedSubgroupLieSource.LeeClosedEmbeddingTheorem) :
    LeeClosedSubgroupForCompactSymplectic := by
  intro n
  letI : SecondCountableTopology (Mat n)ˣ :=
    Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
  obtain ⟨d, ⟨a⟩⟩ := hLee (E := Mat n) (A := G n) (B := (Mat n)ˣ)
    (toMatrixUnits n)
    (toMatrixUnits_closedEmbedding n)
  exact ⟨d, ⟨{
    charts := a.charts
    manifold := a.manifold
    lieGroup := a.lieGroup
    smoothEmbedding := a.smoothEmbedding
  }⟩⟩

end
end QuaternionicSymmetry.CompactSymplecticClosedSubgroupSource
