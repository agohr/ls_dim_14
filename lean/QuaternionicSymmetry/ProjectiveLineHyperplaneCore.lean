import QuaternionicSymmetry.ProjectiveLineTangentDeterminant
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-! The standard hyperplane line O(1) on CP¹, represented by its actual
homogeneous-coordinate transitions on the two projective affine charts.
No degree classification is built into this definition. -/

namespace QuaternionicSymmetry.ProjectiveLineHyperplaneCore

open scoped Manifold ContDiff
open ComplexProjectiveTopology FourDimensionalHalfSpinProjective
open HolomorphicLineCoreClasses
noncomputable section

def hyperplaneTransition (i j : Fin 2) (p : ProjectiveSpinor) : ℂ :=
  p.rep i / p.rep j

theorem projectiveChart_coordinate (j : Fin 2) (p : ProjectiveSpinor)
    (hp : p ∈ affineDomain 1 j) :
    (projectiveChart 1 j p) 0 = p.rep (j.succAbove 0) / p.rep j := by
  rw [projectiveChart_apply 1 j p hp]
  rfl

theorem hyperplaneTransition_holomorphic (i j : Fin 2) :
    ContMDiffOn 𝓘(ℂ,Fin 1 → ℂ) 𝓘(ℂ,ℂ) ∞ (hyperplaneTransition i j)
      (affineDomain 1 i ∩ affineDomain 1 j) := by
  by_cases hij : i = j
  · subst j
    apply (contMDiffOn_const (c := (1 : ℂ))).congr
    intro p hp
    exact div_self hp.1
  · have he : projectiveChart 1 j ∈
        (contDiffGroupoid ∞ 𝓘(ℂ,Fin 1 → ℂ)).maximalAtlas ProjectiveSpinor :=
      (StructureGroupoid.subset_maximalAtlas
        (G := contDiffGroupoid ∞ 𝓘(ℂ,Fin 1 → ℂ))) ⟨j,rfl⟩
    have hc := contMDiffOn_of_mem_maximalAtlas he
    have hv := (ContinuousLinearMap.proj (0 : Fin 1) :
      (Fin 1 → ℂ) →L[ℂ] ℂ).contMDiff.comp_contMDiffOn hc
    apply (hv.mono (by
      intro p hp
      simpa only [projectiveChart_source] using hp.2)).congr
    intro p hp
    change hyperplaneTransition i j p = (projectiveChart 1 j p) 0
    rw [projectiveChart_coordinate j p hp.2]
    have hi : j.succAbove 0 = i := by
      fin_cases i <;> fin_cases j <;> simp_all
    rw [hi]
    rfl

def hyperplaneCore : VectorBundleCore ℂ ProjectiveSpinor ℂ (Fin 2) where
  baseSet := affineDomain 1
  isOpen_baseSet := isOpen_affineDomain 1
  indexAt p := Classical.choose (exists_mem_affineDomain 1 p)
  mem_baseSet_at p := Classical.choose_spec (exists_mem_affineDomain 1 p)
  coordChange i j p := hyperplaneTransition i j p • ContinuousLinearMap.id ℂ ℂ
  coordChange_self i p hp v := by
    change (p.rep i / p.rep i) * v = v
    rw [div_self hp, one_mul]
  continuousOn_coordChange i j :=
    (hyperplaneTransition_holomorphic i j).continuousOn.smul continuousOn_const
  coordChange_comp i j k p hp v := by
    change (p.rep j / p.rep k) * ((p.rep i / p.rep j) * v) =
      (p.rep i / p.rep k) * v
    have hj : p.rep j ≠ 0 := hp.1.2
    have hk : p.rep k ≠ 0 := hp.2
    field_simp [hj,hk]

instance hyperplaneCore_holomorphic : hyperplaneCore.IsContMDiff 𝓘(ℂ,Fin 1 → ℂ) ∞ where
  contMDiffOn_coordChange i j :=
    (hyperplaneTransition_holomorphic i j).smul contMDiffOn_const

def hyperplaneLineCore : LineCore.{0} (B := ProjectiveSpinor) 𝓘(ℂ,Fin 1 → ℂ) where
  Index := Fin 2
  core := hyperplaneCore
  holomorphic := inferInstance

end
end QuaternionicSymmetry.ProjectiveLineHyperplaneCore
