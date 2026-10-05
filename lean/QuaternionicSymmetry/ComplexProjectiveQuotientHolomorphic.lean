import QuaternionicSymmetry.ComplexProjectiveManifold
import Mathlib.Geometry.Manifold.ContMDiff.Defs

/-! Holomorphicity of projectivizing a nonzero homogeneous coordinate vector. -/

namespace QuaternionicSymmetry.ComplexProjectiveTopology

open scoped Manifold ContDiff LinearAlgebra.Projectivization

/-- A total extension of projectivization, used only away from zero. -/
noncomputable def projectivize (d : ℕ) (v : Coord d) : Space d :=
  if hv : v ≠ 0 then Projectivization.mk ℂ v hv
  else euclideanPoint d (0 : Fin (d + 1)) 0

theorem projectivize_of_ne_zero (d : ℕ) (v : Coord d) (hv : v ≠ 0) :
    projectivize d v = Projectivization.mk ℂ v hv := by
  simp [projectivize, hv]

def coordinateNonzero (d : ℕ) (i : Fin (d + 1)) : Set (Coord d) :=
  {v | v i ≠ 0}

theorem isOpen_coordinateNonzero (d : ℕ) (i : Fin (d + 1)) :
    IsOpen (coordinateNonzero d i) :=
  isOpen_ne.preimage (continuous_apply i)

theorem exists_coordinateNonzero_of_ne_zero (d : ℕ) (v : Coord d)
    (hv : v ≠ 0) : ∃ i : Fin (d + 1), v ∈ coordinateNonzero d i := by
  by_contra h
  have hz : v = 0 := by
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  exact hv hz

theorem coordinateNonzero_subset_ne_zero (d : ℕ) (i : Fin (d + 1)) :
    coordinateNonzero d i ⊆ {v | v ≠ 0} := by
  intro v hv hz
  exact hv (by simp [hz])

theorem projectivize_mem_chart (d : ℕ) (i : Fin (d + 1))
    {v : Coord d} (hv : v ∈ coordinateNonzero d i) :
    projectivize d v ∈ (projectiveChart d i).source := by
  rw [projectiveChart_source, projectivize_of_ne_zero d v
    (coordinateNonzero_subset_ne_zero d i hv)]
  exact (mem_affineDomain_mk d i v _).2 hv

/-- The ordinary rational coordinates of a nonzero homogeneous vector. -/
noncomputable def coordinateRatio (d : ℕ) (i : Fin (d + 1))
    (v : Coord d) : Fin d → ℂ :=
  fun k => v (i.succAbove k) / v i

theorem contDiffOn_coordinateRatio (d : ℕ) (i : Fin (d + 1)) :
    ContDiffOn ℂ ∞ (coordinateRatio d i) (coordinateNonzero d i) := by
  apply contDiffOn_pi.mpr
  intro k
  have hnum := (contDiff_apply ℂ ℂ (i.succAbove k) :
    ContDiff ℂ ∞ (fun v : Coord d => v (i.succAbove k))).contDiffOn
      (s := coordinateNonzero d i)
  have hden := (contDiff_apply ℂ ℂ i :
    ContDiff ℂ ∞ (fun v : Coord d => v i)).contDiffOn
      (s := coordinateNonzero d i)
  have hne : ∀ v ∈ coordinateNonzero d i, v i ≠ 0 := fun _ hv => hv
  convert hnum.mul (hden.inv hne) using 1

theorem projectiveChart_projectivize (d : ℕ) (i : Fin (d + 1))
    {v : Coord d} (hv : v ∈ coordinateNonzero d i) :
    projectiveChart d i (projectivize d v) = coordinateRatio d i v := by
  rw [projectiveChart_apply d i _ (by
    rw [← projectiveChart_source]
    exact projectivize_mem_chart d i hv)]
  funext k
  change affineRatio d i
    ⟨projectivize d v, (by
      simpa only [projectiveChart_source] using projectivize_mem_chart d i hv :
      projectivize d v ∈ affineDomain d i)⟩ (i.succAbove k) =
      v (i.succAbove k) / v i
  have hne := coordinateNonzero_subset_ne_zero d i hv
  simpa only [projectivize_of_ne_zero d v hne] using
    (affineRatio_mk d i (i.succAbove k) v hne hv)

theorem contMDiffOn_projectivize_coordinate (d : ℕ) (i : Fin (d + 1)) :
    ContMDiffOn 𝓘(ℂ, Coord d) 𝓘(ℂ, Fin d → ℂ) ∞
      (projectivize d) (coordinateNonzero d i) := by
  have he := StructureGroupoid.chart_mem_maximalAtlas
    (contDiffGroupoid ∞ 𝓘(ℂ, Coord d)) (0 : Coord d)
  have he' : projectiveChart d i ∈
      (contDiffGroupoid ∞ 𝓘(ℂ, Fin d → ℂ)).maximalAtlas (Space d) :=
    (StructureGroupoid.subset_maximalAtlas
      (G := contDiffGroupoid ∞ 𝓘(ℂ, Fin d → ℂ))) ⟨i, rfl⟩
  have hs : coordinateNonzero d i ⊆ (chartAt (Coord d) (0 : Coord d)).source := by
    intro v hv
    simp
  have hmap : Set.MapsTo (projectivize d) (coordinateNonzero d i)
      (projectiveChart d i).source := by
    intro v hv
    exact projectivize_mem_chart d i hv
  apply (contMDiffOn_iff_of_mem_maximalAtlas' he he' hs hmap).mpr
  have hcomp : ContDiffOn ℂ ∞
      (fun v : Coord d => projectiveChart d i (projectivize d v))
      (coordinateNonzero d i) :=
    (contDiffOn_coordinateRatio d i).congr
      (fun v hv => projectiveChart_projectivize d i hv)
  simpa [chartAt_self_eq] using hcomp

/-- Projectivizing a nonzero vector is holomorphic for the standard complex
projective manifold structure, as follows from the rational affine charts. -/
theorem contMDiffOn_projectivize_nonzero (d : ℕ) :
    ContMDiffOn 𝓘(ℂ, Coord d) 𝓘(ℂ, Fin d → ℂ) ∞
      (projectivize d) {v | v ≠ 0} := by
  apply contMDiffOn_of_locally_contMDiffOn
  intro v hv
  obtain ⟨i, hi⟩ := exists_coordinateNonzero_of_ne_zero d v hv
  refine ⟨coordinateNonzero d i, isOpen_coordinateNonzero d i, hi, ?_⟩
  exact (contMDiffOn_projectivize_coordinate d i).mono (Set.inter_subset_right)

end QuaternionicSymmetry.ComplexProjectiveTopology
