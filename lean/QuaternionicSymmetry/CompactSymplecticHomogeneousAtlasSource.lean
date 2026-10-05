import QuaternionicSymmetry.CompactSymplecticClosedSubgroupSource
import QuaternionicSymmetry.CompactSymplecticProjectorOrbitQuotient
import QuaternionicSymmetry.GeneralLieHomogeneousSpaceSource

/-!
Lee, *Introduction to Smooth Manifolds*, 2nd ed., Theorem 20.12,
printed pp.523–525, gives a real embedded Lie atlas to the checked closed
projector stabilizer inside an already equipped compact symplectic Lie group.
Theorem 21.17, printed pp.551–552, then gives a smooth quotient atlas,
submersive quotient map, smooth transitive left action, and dimension
subtraction. This file records precisely that general-source boundary for
the actual matrix stabilizer and coset quotient. It assumes neither an
invariant metric nor a quaternionic-projective/Wolf identification.
-/

namespace QuaternionicSymmetry.CompactSymplecticHomogeneousAtlasSource

open CompactSymplecticProjectiveQuotient
open CompactSymplecticClosedSubgroupSource
open Manifold Topology
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)
private abbrev K (n : ℕ) := firstPairStabilizer n
private abbrev C (n : ℕ) := ProjectiveCarrier n
private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev Mat (n : ℕ) :=
  Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℂ

/-- The algebraically canonical left action on the actual coset quotient. -/
def leftCosetAction (n : ℕ) (u : G n) (q : C n) : C n := by
  exact GeneralLieHomogeneousSpaceSource.leftCosetAction (K n) u q

/-- The same general Lee closed-subgroup premise applies a second time to
the actual closed projector stabilizer inside the now-equipped compact
symplectic Lie group. Thus its Lie atlas is not separately stipulated in
the quotient source. -/
theorem exists_stabilizer_atlas_of_general
    (hLee : GeneralClosedSubgroupLieSource.LeeClosedEmbeddingTheorem)
    (n d : ℕ) (g : EmbeddedRealLieAtlas n d) :
    letI := g.charts
    ∃ e : ℕ, Nonempty
      (GeneralClosedSubgroupLieSource.EmbeddedRealLieAtlas
        (RModel d) (K n) (G n) (K n).subtype e) := by
  letI := g.charts
  letI := g.manifold
  letI := g.lieGroup
  letI : SecondCountableTopology (Mat n)ˣ :=
    Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology (G n) :=
    (CompactSymplecticMatrixUnits.toMatrixUnits_closedEmbedding n).isEmbedding.secondCountableTopology
  have hClosed : IsClosedEmbedding ((K n).subtype : K n →* G n) := by
    change IsClosedEmbedding (Subtype.val : K n → G n)
    exact (isClosed_firstPairStabilizer n).isClosedEmbedding_subtypeVal
  exact hLee (E := RModel d) (A := K n) (B := G n)
    (K n).subtype hClosed

/-- The exact smooth outputs on the already constructed closed matrix
stabilizer and genuine topological coset quotient. Dimensions remain
existential until the actual stabilizer Lie algebra is computed. -/
structure SmoothHomogeneousAtlas (n d e q : ℕ)
    (g : EmbeddedRealLieAtlas n d) where
  stabilizerCharts : ChartedSpace (RModel e) (K n)
  stabilizerManifold : letI := stabilizerCharts
    IsManifold 𝓘(ℝ, RModel e) ∞ (K n)
  stabilizerLieGroup : letI := stabilizerCharts
    LieGroup 𝓘(ℝ, RModel e) ∞ (K n)
  stabilizerSmoothEmbedding : letI := stabilizerCharts
    letI := g.charts
    IsSmoothEmbedding 𝓘(ℝ, RModel e) 𝓘(ℝ, RModel d) ∞
      (Subtype.val : K n → G n)
  quotientCharts : ChartedSpace (RModel q) (C n)
  quotientManifold : letI := quotientCharts
    IsManifold 𝓘(ℝ, RModel q) ∞ (C n)
  quotientSmooth : letI := g.charts
    letI := quotientCharts
    ContMDiff 𝓘(ℝ, RModel d) 𝓘(ℝ, RModel q) ∞
      (fun u : G n => (u : C n))
  quotientSubmersive : letI := g.charts
    letI := quotientCharts
    ∀ u : G n, Function.Surjective
      (mfderiv 𝓘(ℝ, RModel d) 𝓘(ℝ, RModel q)
        (fun v : G n => (v : C n)) u)
  actionSmooth : letI := g.charts
    letI := quotientCharts
    ContMDiff (𝓘(ℝ, RModel d).prod 𝓘(ℝ, RModel q))
      𝓘(ℝ, RModel q) ∞ (fun p : G n × C n => leftCosetAction n p.1 p.2)
  dimension : q + e = d

/-- The literal Lee 20.12+21.17 source application, conditional on the
real Lie atlas furnished by Lee 20.12 for the ambient compact symplectic
matrix subgroup. All groups, subgroup membership, quotient topology, and
closedness in this signature are actual checked objects. -/
def LeeHomogeneousSpaceForProjectorStabilizer : Prop :=
  ∀ (n d : ℕ) (g : EmbeddedRealLieAtlas n d),
    ∃ e q : ℕ, Nonempty (SmoothHomogeneousAtlas n d e q g)

/-- Both general Lee source premises apply to the actual closed matrix
subgroup and then to its actual closed projector stabilizer. The result
therefore has no specialized homogeneous-space source assumption. -/
theorem leeHomogeneousSpaceForProjectorStabilizer_of_general
    (hClosed : GeneralClosedSubgroupLieSource.LeeClosedEmbeddingTheorem)
    (hQuot : GeneralLieHomogeneousSpaceSource.LeeHomogeneousSpaceTheorem) :
    LeeHomogeneousSpaceForProjectorStabilizer := by
  intro n d g
  letI := g.charts
  letI := g.manifold
  letI := g.lieGroup
  letI : SecondCountableTopology (Mat n)ˣ :=
    Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology (G n) :=
    (CompactSymplecticMatrixUnits.toMatrixUnits_closedEmbedding n).isEmbedding.secondCountableTopology
  obtain ⟨e, ⟨k⟩⟩ := exists_stabilizer_atlas_of_general hClosed n d g
  obtain ⟨q, ⟨a⟩⟩ := hQuot (G := G n) d (K n)
    (isClosed_firstPairStabilizer n) e k
  exact ⟨e, q, ⟨{
    stabilizerCharts := k.charts
    stabilizerManifold := k.manifold
    stabilizerLieGroup := k.lieGroup
    stabilizerSmoothEmbedding := k.smoothEmbedding
    quotientCharts := a.charts
    quotientManifold := a.manifold
    quotientSmooth := a.quotientSmooth
    quotientSubmersive := a.quotientSubmersive
    actionSmooth := a.actionSmooth
    dimension := a.dimension
  }⟩⟩

end
end QuaternionicSymmetry.CompactSymplecticHomogeneousAtlasSource
