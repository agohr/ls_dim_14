import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! Pull a genuine manifold atlas across a fixed homeomorphism. This is the
first source-free step in transporting BG-R3's full metric-isometry atlas to
the actual quaternionic-isometry group. -/

namespace QuaternionicSymmetry.HomeomorphLieAtlasTransfer

open Manifold
open scoped Manifold ContDiff
noncomputable section

variable {V X Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace V Y]

def charts (e : X ≃ₜ Y) : ChartedSpace V X where
  atlas := (fun c : OpenPartialHomeomorph Y V =>
    e.toOpenPartialHomeomorph ≫ₕ c) '' atlas V Y
  chartAt x := e.toOpenPartialHomeomorph ≫ₕ chartAt V (e x)
  mem_chart_source x := by simp
  chart_mem_atlas x := ⟨chartAt V (e x), chart_mem_atlas V (e x), rfl⟩

def manifold (e : X ≃ₜ Y) [IsManifold 𝓘(ℝ,V) ∞ Y] :
    letI := charts (V := V) e
    IsManifold 𝓘(ℝ,V) ∞ X := by
  letI := charts (V := V) e
  haveI : HasGroupoid X (contDiffGroupoid ∞ 𝓘(ℝ,V)) := ⟨by
    intro c c' hc hc'
    obtain ⟨d, hd, rfl⟩ := hc
    obtain ⟨d', hd', rfl⟩ := hc'
    have heq :
        (e.toOpenPartialHomeomorph ≫ₕ d).symm ≫ₕ
          (e.toOpenPartialHomeomorph ≫ₕ d') = d.symm ≫ₕ d' := by
      rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
      conv_lhs =>
        rw [← OpenPartialHomeomorph.trans_assoc]
        arg 1
        rw [OpenPartialHomeomorph.trans_assoc]
      rw [← Homeomorph.symm_toOpenPartialHomeomorph,
        ← Homeomorph.trans_toOpenPartialHomeomorph, e.symm_trans_self]
      simp
    rw [heq]
    exact HasGroupoid.compatible hd hd'
  ⟩
  exact IsManifold.mk' 𝓘(ℝ,V) ∞ X

theorem smooth_toFun (e : X ≃ₜ Y) [IsManifold 𝓘(ℝ,V) ∞ Y] :
    letI := charts (V := V) e
    ContMDiff 𝓘(ℝ,V) 𝓘(ℝ,V) ∞ e := by
  letI := charts (V := V) e
  letI := manifold (V := V) e
  apply (contMDiff_iff).2
  constructor
  · exact e.continuous
  intro x y
  have hGroupoid :
      (chartAt V x).symm ≫ₕ e.toOpenPartialHomeomorph ≫ₕ chartAt V y ∈
        contDiffGroupoid ∞ 𝓘(ℝ,V) := by
    change (e.toOpenPartialHomeomorph ≫ₕ chartAt V (e x)).symm ≫ₕ
      e.toOpenPartialHomeomorph ≫ₕ chartAt V y ∈ _
    have hcancel :
        (e.toOpenPartialHomeomorph ≫ₕ chartAt V (e x)).symm ≫ₕ
          e.toOpenPartialHomeomorph ≫ₕ chartAt V y =
          (chartAt V (e x)).symm ≫ₕ chartAt V y := by
      rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
      conv_lhs =>
        rw [← OpenPartialHomeomorph.trans_assoc]
        arg 1
        rw [OpenPartialHomeomorph.trans_assoc]
      rw [← Homeomorph.symm_toOpenPartialHomeomorph,
        ← Homeomorph.trans_toOpenPartialHomeomorph, e.symm_trans_self]
      simp
    rw [hcancel]
    exact HasGroupoid.compatible (chart_mem_atlas V (e x)) (chart_mem_atlas V y)
  have hSmooth := contMDiffOn_of_mem_contDiffGroupoid hGroupoid
  simpa only [modelWithCornersSelf_coe, mfld_simps] using hSmooth.contDiffOn

theorem smooth_invFun (e : X ≃ₜ Y) [IsManifold 𝓘(ℝ,V) ∞ Y] :
    letI := charts (V := V) e
    ContMDiff 𝓘(ℝ,V) 𝓘(ℝ,V) ∞ e.symm := by
  letI := charts (V := V) e
  letI := manifold (V := V) e
  apply (contMDiff_iff).2
  constructor
  · exact e.symm.continuous
  intro y x
  have hGroupoid :
      (chartAt V y).symm ≫ₕ e.symm.toOpenPartialHomeomorph ≫ₕ chartAt V x ∈
        contDiffGroupoid ∞ 𝓘(ℝ,V) := by
    change (chartAt V y).symm ≫ₕ e.symm.toOpenPartialHomeomorph ≫ₕ
      (e.toOpenPartialHomeomorph ≫ₕ chartAt V (e x)) ∈ _
    have hcancel :
        (chartAt V y).symm ≫ₕ e.symm.toOpenPartialHomeomorph ≫ₕ
          (e.toOpenPartialHomeomorph ≫ₕ chartAt V (e x)) =
          (chartAt V y).symm ≫ₕ chartAt V (e x) := by
      simp only [← OpenPartialHomeomorph.trans_assoc]
      conv_lhs =>
        arg 1
        rw [OpenPartialHomeomorph.trans_assoc]
      rw [← Homeomorph.trans_toOpenPartialHomeomorph, e.symm_trans_self]
      simp
    rw [hcancel]
    exact HasGroupoid.compatible (chart_mem_atlas V y) (chart_mem_atlas V (e x))
  have hSmooth := contMDiffOn_of_mem_contDiffGroupoid hGroupoid
  simpa only [modelWithCornersSelf_coe, mfld_simps] using hSmooth.contDiffOn

/-- Transport genuine smooth group operations, not merely the atlas, across
a topological group isomorphism. -/
def lieGroup [Group X] [Group Y] (e : X ≃ₜ Y)
    (hMul : ∀ x y : X, e (x * y) = e x * e y)
    (hInv : ∀ x : X, e x⁻¹ = (e x)⁻¹)
    [LieGroup 𝓘(ℝ,V) ∞ Y] :
    letI := charts (V := V) e
    LieGroup 𝓘(ℝ,V) ∞ X := by
  letI := charts (V := V) e
  letI := manifold (V := V) e
  have he := smooth_toFun (V := V) e
  have he' := smooth_invFun (V := V) e
  refine { toIsManifold := inferInstance, contMDiff_mul := ?_, contMDiff_inv := ?_ }
  · have hY : ContMDiff (𝓘(ℝ,V).prod 𝓘(ℝ,V)) 𝓘(ℝ,V) ∞
        (fun p : X × X => e p.1 * e p.2) :=
      (he.comp contMDiff_fst).mul (he.comp contMDiff_snd)
    have hX := he'.comp hY
    convert hX using 1
    funext p
    change p.1 * p.2 = e.symm (e p.1 * e p.2)
    rw [← hMul p.1 p.2]
    exact (e.symm_apply_apply _).symm
  · have hY : ContMDiff 𝓘(ℝ,V) 𝓘(ℝ,V) ∞
        (fun x : X => (e x)⁻¹) := he.inv
    have hX := he'.comp hY
    convert hX using 1
    funext x
    change x⁻¹ = e.symm ((e x)⁻¹)
    rw [← hInv x]
    exact (e.symm_apply_apply _).symm

end
end QuaternionicSymmetry.HomeomorphLieAtlasTransfer
