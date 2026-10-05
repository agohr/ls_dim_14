import QuaternionicSymmetry.CompactAbelianLieKernel
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Topology.Baire.LocallyCompactRegular

/-! Compactness forces the discrete kernel of the coordinate cover to span
the entire real coordinate space. Thus it is a genuine full lattice. -/
namespace QuaternionicSymmetry.CompactAbelianLieLattice
open Module Set Function CompactAbelianLieCover CompactAbelianLieKernel
open GeneralClosedSubgroupLieSource
open scoped Manifold ContDiff Topology
noncomputable section
variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CommGroup G] [TopologicalSpace G] [ChartedSpace E G]
  [IsManifold 𝓘(ℝ,E) ∞ G] [LieGroup 𝓘(ℝ,E) ∞ G]
  [CompactSpace G] [T2Space G] [SecondCountableTopology G] [PreconnectedSpace G]
  {d : ℕ} (b : Basis (Fin d) ℝ (GroupLieAlgebra 𝓘(ℝ,E) G))

theorem kernel_span_top (hClosed : LeeClosedEmbeddingTheorem) :
    Submodule.span ℝ (kernel b : Set (Fin d → ℝ)) = ⊤ := by
  classical
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℝ,E) ∞
  have hs := coordinateMap_surjective b hClosed
  have hc := (coordinateMap_smooth b hClosed).continuous
  have ho : IsOpenMap (coordinateMap b) :=
    (coordinateHom b).isOpenMap_of_sigmaCompact hs hc
  have hq := ho.isQuotientMap hc hs
  by_contra htop
  obtain ⟨φ,hφ,hker⟩ := (Submodule.span ℝ (kernel b : Set (Fin d → ℝ))).exists_le_ker_of_lt_top
    (lt_top_iff_ne_top.mpr htop)
  have hconst (x y : Fin d → ℝ) (hxy : coordinateMap b x = coordinateMap b y) : φ x = φ y := by
    have hn : coordinateMap b (-y) = (coordinateMap b y)⁻¹ :=
      map_inv (coordinateHom b) (Multiplicative.ofAdd y)
    have hz : x-y ∈ kernel b := by
      change coordinateMap b (x-y) = 1
      rw [sub_eq_add_neg, coordinateMap_add, hn, hxy, mul_inv_cancel]
    have he := hker (Submodule.subset_span hz)
    change φ (x-y) = 0 at he
    rw [map_sub, sub_eq_zero] at he
    exact he
  let g : G → ℝ := fun y => φ (surjInv hs y)
  have hcomp : g ∘ coordinateMap b = φ := by
    funext x
    exact hconst _ _ (surjInv_eq hs (coordinateMap b x))
  have hg : Continuous g := hq.continuous_iff.mpr (by
    rw [hcomp]
    exact φ.continuous_of_finiteDimensional)
  obtain ⟨x,hx⟩ := DFunLike.ne_iff.mp hφ
  have hx' : φ x ≠ 0 := by simpa using hx
  have hgSurj : Surjective g := by
    intro r
    refine ⟨coordinateMap b ((r / φ x) • x),?_⟩
    change (g ∘ coordinateMap b) ((r / φ x) • x) = r
    rw [hcomp, map_smul]
    change r / φ x * φ x = r
    exact div_mul_cancel₀ r hx'
  have hcompact := isCompact_range hg
  rw [Set.range_eq_univ.mpr hgSurj] at hcompact
  exact noncompact_univ ℝ hcompact

theorem kernel_isZLattice (hClosed : LeeClosedEmbeddingTheorem) :
    letI : DiscreteTopology (kernel b).toIntSubmodule := kernel_discrete b hClosed
    IsZLattice ℝ (kernel b).toIntSubmodule := by
  letI : DiscreteTopology (kernel b).toIntSubmodule := kernel_discrete b hClosed
  exact ⟨kernel_span_top b hClosed⟩

end
end QuaternionicSymmetry.CompactAbelianLieLattice
