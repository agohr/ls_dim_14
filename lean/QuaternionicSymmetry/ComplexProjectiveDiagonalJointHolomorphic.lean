import QuaternionicSymmetry.ComplexTorusCharacterHolomorphic
import QuaternionicSymmetry.ComplexProjectiveDiagonalHolomorphic
import QuaternionicSymmetry.ComplexProjectiveLinearEquivHolomorphic
import Mathlib.Geometry.Manifold.Algebra.Structures

/-! Joint holomorphicity of the literal diagonal complex-torus action on
complex projective space. The proof uses the genuine complex-torus open
manifold and fixed projective affine charts. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalJointHolomorphic

open ComplexProjectiveTopology ComplexProjectiveDiagonalAction
open ComplexProjectiveLinearEquivHolomorphic
open ComplexTorusCharacterHolomorphic TorusLaurentRepresentation
open scoped Manifold ContDiff LinearAlgebra.Projectivization
noncomputable section

variable {r d : ℕ} (μ : Fin (d + 1) → Fin r → ℤ)

private abbrev IT (r : ℕ) := 𝓘(ℂ, Fin r → ℂ)
private abbrev IP (d : ℕ) := 𝓘(ℂ, Fin d → ℂ)

theorem localRepresentative_contMDiff (i : Fin (d + 1)) :
    ContMDiff ((IT r).prod (IP d)) 𝓘(ℂ, Coord d) ∞
      (fun q : ComplexTorus r × (Fin d → ℂ) =>
        diagonalEquiv μ q.1 (homogeneousVector d i q.2)) := by
  apply contMDiff_pi_space.mpr
  intro j
  have hχ : ContMDiff ((IT r).prod (IP d)) 𝓘(ℂ,ℂ) ∞
      (fun q : ComplexTorus r × (Fin d → ℂ) =>
        (complexWeightCharacter (μ j) q.1 : ℂ)) :=
    (complexWeightCharacter_holomorphic (μ j)).comp contMDiff_fst
  have hh : ContMDiff ((IT r).prod (IP d)) 𝓘(ℂ,ℂ) ∞
      (fun q : ComplexTorus r × (Fin d → ℂ) =>
        homogeneousVector d i q.2 j) := by
    have hcomponent : ContDiff ℂ ∞
        (fun w : Fin d → ℂ => homogeneousVector d i w j) :=
      (contDiff_apply ℂ ℂ j).comp (contDiff_homogeneousVector i)
    exact hcomponent.contMDiff.comp contMDiff_snd
  convert hχ.mul hh using 1

theorem localAction_contMDiff (i : Fin (d + 1)) :
    ContMDiff ((IT r).prod (IP d)) (IP d) ∞
      (fun q : ComplexTorus r × (Fin d → ℂ) =>
        projectivize d (diagonalEquiv μ q.1 (homogeneousVector d i q.2))) := by
  have hrep := localRepresentative_contMDiff μ i
  have hmap : Set.MapsTo
      (fun q : ComplexTorus r × (Fin d → ℂ) =>
        diagonalEquiv μ q.1 (homogeneousVector d i q.2))
      Set.univ {v : Coord d | v ≠ 0} := by
    intro q hq
    exact (diagonalEquiv μ q.1).map_ne_zero_iff.mpr
      (homogeneousVector_ne_zero d i q.2)
  exact contMDiffOn_univ.mp
    ((contMDiffOn_projectivize_nonzero d).comp hrep.contMDiffOn hmap)

theorem jointAction_contMDiffOn_chart (i : Fin (d + 1)) :
    ContMDiffOn ((IT r).prod (IP d)) (IP d) ∞
      (fun q : ComplexTorus r × Space d => projectiveAction μ q.1 q.2)
      (Set.univ ×ˢ affineDomain d i) := by
  have he : projectiveChart d i ∈
      (contDiffGroupoid ∞ (IP d)).maximalAtlas (Space d) :=
    (StructureGroupoid.subset_maximalAtlas
      (G := contDiffGroupoid ∞ (IP d))) ⟨i, rfl⟩
  have hchart : ContMDiffOn ((IT r).prod (IP d))
      ((IT r).prod (IP d)) ∞
      (Prod.map id (projectiveChart d i))
      (Set.univ ×ˢ affineDomain d i) :=
    (contMDiff_id : ContMDiff (IT r) (IT r) ∞
      (id : ComplexTorus r → ComplexTorus r)).contMDiffOn.prodMap
      ((contMDiffOn_of_mem_maximalAtlas he).mono (by
        simp [projectiveChart_source] : affineDomain d i ⊆
          (projectiveChart d i).source))
  have hcomp := (localAction_contMDiff μ i).comp_contMDiffOn hchart
  apply hcomp.congr
  intro q hq
  have hp : q.2 ∈ affineDomain d i := hq.2
  have hpoint : (projectiveChart d i).symm (projectiveChart d i q.2) = q.2 :=
    (projectiveChart d i).left_inv (by
      simpa [projectiveChart_source] using hp)
  rw [projectiveChart_symm_apply] at hpoint
  change projectiveAction μ q.1 q.2 =
    projectivize d
      (diagonalEquiv μ q.1
        (homogeneousVector d i (projectiveChart d i q.2)))
  conv_lhs => rw [← hpoint]
  rw [euclideanPoint, projectiveAction_mk]
  exact (projectivize_of_ne_zero d _
    ((diagonalEquiv μ q.1).map_ne_zero_iff.mpr
      (homogeneousVector_ne_zero d i (projectiveChart d i q.2)))).symm

theorem jointAction_contMDiff :
    ContMDiff ((IT r).prod (IP d)) (IP d) ∞
      (fun q : ComplexTorus r × Space d => projectiveAction μ q.1 q.2) := by
  apply contMDiffOn_univ.mp
  apply contMDiffOn_of_locally_contMDiffOn
  intro q hq
  obtain ⟨i, hi⟩ := exists_mem_affineDomain d q.2
  refine ⟨Set.univ ×ˢ affineDomain d i,
    isOpen_univ.prod (isOpen_affineDomain d i), ⟨Set.mem_univ _, hi⟩, ?_⟩
  exact (jointAction_contMDiffOn_chart μ i).mono Set.inter_subset_right

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalJointHolomorphic
