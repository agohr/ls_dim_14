import QuaternionicSymmetry.CompactAbelianLieLattice
import QuaternionicSymmetry.FullLatticeCirclePresentation

/-! A compact connected finite-dimensional abelian Lie group is a literal
circle-power torus. Only the retained closed-subgroup input is used, for
automatic smoothness of the internally constructed one-parameter subgroups. -/
namespace QuaternionicSymmetry.CompactAbelianLieTorus
open Module Function CompactLieTorusInputs
open CompactAbelianLieCover CompactAbelianLieKernel CompactAbelianLieLattice
open GeneralClosedSubgroupLieSource
open scoped Manifold ContDiff
noncomputable section
variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CommGroup G] [TopologicalSpace G] [ChartedSpace E G]
  [IsManifold 𝓘(ℝ,E) ∞ G] [LieGroup 𝓘(ℝ,E) ∞ G]
  [CompactSpace G] [T2Space G] [SecondCountableTopology G] [PreconnectedSpace G]

theorem exists_torus (hClosed : LeeClosedEmbeddingTheorem)
    {d : ℕ} (b : Basis (Fin d) ℝ (GroupLieAlgebra 𝓘(ℝ,E) G)) :
    ∃ T : TorusEmbedding G d, Surjective T.hom := by
  let L := (kernel b).toIntSubmodule
  letI : DiscreteTopology L := kernel_discrete b hClosed
  letI : IsZLattice ℝ L := kernel_isZLattice b hClosed
  exact FullLatticeCirclePresentation.exists_torus_presentation L (coordinateHom b)
    (coordinateMap_smooth b hClosed).continuous (coordinateMap_surjective b hClosed)
    (fun _ => Iff.rfl)

include E in
theorem isTorus_top (hClosed : LeeClosedEmbeddingTheorem) :
    IsTorusSubgroup G (⊤ : Subgroup G) := by
  letI : FiniteDimensional ℝ (GroupLieAlgebra 𝓘(ℝ,E) G) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (GroupLieAlgebra 𝓘(ℝ,E) G)
  obtain ⟨T,hT⟩ := exists_torus hClosed b
  refine ⟨_,T,?_⟩
  exact MonoidHom.range_eq_top.mpr hT

end
end QuaternionicSymmetry.CompactAbelianLieTorus
