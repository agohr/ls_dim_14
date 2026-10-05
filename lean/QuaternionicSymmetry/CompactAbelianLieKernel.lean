import QuaternionicSymmetry.CompactAbelianLieCover
import QuaternionicSymmetry.ManifoldLocalDiffeomorphism
import Mathlib.Topology.Algebra.Group.Basic

/-! The real coordinate cover of a compact abelian Lie group has a discrete
kernel. The proof uses the actual coordinate derivative and inverse function
theorem, without a lattice or torus classification assumption. -/
namespace QuaternionicSymmetry.CompactAbelianLieKernel
open Module Set CompactAbelianLieCover GeneralClosedSubgroupLieSource
open scoped Manifold ContDiff Topology
noncomputable section
variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CommGroup G] [TopologicalSpace G] [ChartedSpace E G]
  [IsManifold 𝓘(ℝ,E) ∞ G] [LieGroup 𝓘(ℝ,E) ∞ G]
  [CompactSpace G] [T2Space G] [SecondCountableTopology G]
  {d : ℕ} (b : Basis (Fin d) ℝ (GroupLieAlgebra 𝓘(ℝ,E) G))

theorem locally_injective (hClosed : LeeClosedEmbeddingTheorem) :
    ∃ U : Set (Fin d → ℝ), IsOpen U ∧ 0 ∈ U ∧ InjOn (coordinateMap b) U := by
  let φ := writtenInExtChartAt 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,E) 0 (coordinateMap b)
  let D : (Fin d → ℝ) ≃L[ℝ] E := b.equivFun.symm.toContinuousLinearEquiv
  have hD : mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,E) (coordinateMap b) 0 =
      (D : (Fin d → ℝ) →L[ℝ] E) := by
    apply ContinuousLinearMap.coe_injective
    exact derivative_eq b hClosed
  have hf := (coordinateMap_smooth b hClosed).contMDiffAt (x := 0)
  have hcd : ContDiffAt ℝ ∞ φ 0 := by
    simpa [φ] using (contMDiffAt_iff.mp hf).2
  have hd : HasFDerivAt φ (D : (Fin d → ℝ) →L[ℝ] E) 0 := by
    simpa [φ, hD] using (hf.mdifferentiableAt (by simp)).hasMFDerivAt.2
  let e := hcd.toOpenPartialHomeomorph φ hd (by simp)
  refine ⟨e.source,e.open_source,hcd.mem_toOpenPartialHomeomorph_source hd (by simp),?_⟩
  intro x hx y hy hxy
  apply e.injOn hx hy
  change φ x = φ y
  simpa [φ, writtenInExtChartAt, hxy]

def kernel : AddSubgroup (Fin d → ℝ) where
  carrier := {x | coordinateMap b x = 1}
  zero_mem' := coordinateMap_zero b
  add_mem' hx hy := by
    dsimp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [coordinateMap_add, hx, hy, one_mul]
  neg_mem' {x} hx := by
    dsimp only [Set.mem_setOf_eq] at hx ⊢
    have he := coordinateMap_add b x (-x)
    simpa [hx] using he.symm

theorem kernel_discrete (hClosed : LeeClosedEmbeddingTheorem) : DiscreteTopology (kernel b) := by
  obtain ⟨U,hU,h0,hInj⟩ := locally_injective b hClosed
  apply discreteTopology_iff_isOpen_singleton_zero.mpr
  have he : (Subtype.val : kernel b → (Fin d → ℝ)) ⁻¹' U = {0} := by
    ext x
    constructor
    · intro hx
      have hz := hInj hx h0 (x.property.trans (coordinateMap_zero b).symm)
      exact Set.mem_singleton_iff.mpr (Subtype.ext hz)
    · intro hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact h0
  rw [← he]
  exact hU.preimage continuous_subtype_val

end
end QuaternionicSymmetry.CompactAbelianLieKernel
