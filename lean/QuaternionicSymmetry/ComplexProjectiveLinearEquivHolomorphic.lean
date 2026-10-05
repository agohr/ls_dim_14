import QuaternionicSymmetry.ComplexProjectiveQuotientHolomorphic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-! Projectivizations of invertible complex-linear coordinate changes are
holomorphic for the literal projective affine atlases. -/

namespace QuaternionicSymmetry.ComplexProjectiveLinearEquivHolomorphic

open ComplexProjectiveTopology
open scoped Manifold ContDiff LinearAlgebra.Projectivization
noncomputable section

variable {d e : ℕ} (A : Coord d ≃ₗ[ℂ] Coord e)

def projectiveMap : Space d → Space e :=
  Projectivization.map A.toLinearMap A.injective

theorem projectiveMap_mk (v : Coord d) (hv : v ≠ 0) :
    projectiveMap A (Projectivization.mk ℂ v hv) =
      Projectivization.mk ℂ (A v) (A.map_ne_zero_iff.mpr hv) := rfl

theorem projectiveMap_euclideanPoint (i : Fin (d + 1))
    (w : Fin d → ℂ) :
    projectiveMap A (euclideanPoint d i w) =
      projectivize e (A (homogeneousVector d i w)) := by
  rw [euclideanPoint, projectiveMap_mk]
  exact (projectivize_of_ne_zero e _
    (A.map_ne_zero_iff.mpr (homogeneousVector_ne_zero d i w))).symm

theorem contDiff_homogeneousVector (i : Fin (d + 1)) :
    ContDiff ℂ ∞ (homogeneousVector d i) := by
  apply contDiff_pi.mpr
  intro j
  by_cases hij : j = i
  · subst j
    simpa [homogeneousVector] using
      (contDiff_const : ContDiff ℂ ∞ (fun _ : Fin d → ℂ => (1 : ℂ)))
  · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij
    rw [← hk]
    simpa [homogeneousVector, Fin.insertNth_apply_succAbove] using
      (contDiff_apply ℂ ℂ k : ContDiff ℂ ∞ (fun w : Fin d → ℂ => w k))

theorem contDiff_localRepresentative (i : Fin (d + 1)) :
    ContDiff ℂ ∞ (fun w : Fin d → ℂ => A (homogeneousVector d i w)) := by
  exact (A.toLinearMap.toContinuousLinearMap.contDiff).comp
    (contDiff_homogeneousVector i)

theorem contMDiffOn_projectiveMap_chart (i : Fin (d + 1)) :
    ContMDiffOn 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin e → ℂ) ∞
      (projectiveMap A) (affineDomain d i) := by
  have he : projectiveChart d i ∈
      (contDiffGroupoid ∞ 𝓘(ℂ, Fin d → ℂ)).maximalAtlas (Space d) :=
    (StructureGroupoid.subset_maximalAtlas
      (G := contDiffGroupoid ∞ 𝓘(ℂ, Fin d → ℂ))) ⟨i, rfl⟩
  have hsource : affineDomain d i ⊆ (projectiveChart d i).source := by
    simp [projectiveChart_source]
  have hcoord : ContMDiffOn 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Coord e) ∞
      (fun p : Space d => A (homogeneousVector d i (projectiveChart d i p)))
      (affineDomain d i) := by
    have hself := StructureGroupoid.chart_mem_maximalAtlas
      (contDiffGroupoid ∞ 𝓘(ℂ, Coord e)) (0 : Coord e)
    apply (contMDiffOn_iff_of_mem_maximalAtlas' he hself hsource
      (by intro p hp; simp)).mpr
    apply (contDiff_localRepresentative A i).contDiffOn.congr
    intro w hw
    have ht : w ∈ (projectiveChart d i).target := by
      rw [projectiveChart_target]
      trivial
    simp only [Function.comp_def, OpenPartialHomeomorph.extend_coe,
      OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, chartAt_self_eq, id_eq]
    rw [(projectiveChart d i).right_inv ht]
    rfl
  have hne : Set.MapsTo
      (fun p : Space d => A (homogeneousVector d i (projectiveChart d i p)))
      (affineDomain d i) {v : Coord e | v ≠ 0} := by
    intro p hp
    exact A.map_ne_zero_iff.mpr
      (homogeneousVector_ne_zero d i (projectiveChart d i p))
  have hcomp := ContMDiffOn.comp
    (contMDiffOn_projectivize_nonzero e) hcoord hne
  apply hcomp.congr
  intro p hp
  have hchart : (projectiveChart d i).symm (projectiveChart d i p) = p := by
    exact (projectiveChart d i).left_inv (by
      simpa [projectiveChart_source] using hp)
  rw [projectiveChart_symm_apply] at hchart
  change projectiveMap A p =
    projectivize e (A (homogeneousVector d i (projectiveChart d i p)))
  conv_lhs => rw [← hchart]
  exact projectiveMap_euclideanPoint A i (projectiveChart d i p)

theorem contMDiff_projectiveMap :
    ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin e → ℂ) ∞
      (projectiveMap A) := by
  apply contMDiffOn_univ.mp
  apply contMDiffOn_of_locally_contMDiffOn
  intro p hp
  obtain ⟨i, hi⟩ := exists_mem_affineDomain d p
  refine ⟨affineDomain d i, isOpen_affineDomain d i, hi, ?_⟩
  exact (contMDiffOn_projectiveMap_chart A i).mono Set.inter_subset_right

end
end QuaternionicSymmetry.ComplexProjectiveLinearEquivHolomorphic
