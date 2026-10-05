import Mathlib.Geometry.Manifold.Diffeomorph

/-! Transport a manifold atlas across a homeomorphism without changing the target topology. -/

namespace QuaternionicSymmetry.HomeomorphTransportedManifold

open Manifold OpenPartialHomeomorph
open scoped Manifold ContDiff

noncomputable section

section General

variable {H X Y : Type*} [TopologicalSpace H] [TopologicalSpace X]
  [TopologicalSpace Y] [ChartedSpace H X]

/-- The preferred source chart precomposed with the inverse homeomorphism. -/
def transportedChart (e : X ≃ₜ Y) (y : Y) : OpenPartialHomeomorph Y H :=
  e.symm.transOpenPartialHomeomorph (chartAt H (e.symm y))

/-- The target retains its given topology; only its charts are transported. -/
def chartedSpace (e : X ≃ₜ Y) : ChartedSpace H Y where
  atlas := {c | ∃ d ∈ atlas H X, c = e.symm.transOpenPartialHomeomorph d}
  chartAt := transportedChart e
  mem_chart_source y := by
    change y ∈ (e.symm.transOpenPartialHomeomorph (chartAt H (e.symm y))).source
    simp only [Homeomorph.transOpenPartialHomeomorph_source, Set.mem_preimage]
    exact mem_chart_source H (e.symm y)
  chart_mem_atlas y := ⟨chartAt H (e.symm y), chart_mem_atlas H _, rfl⟩

theorem transition_eq (e : X ≃ₜ Y) (d d' : OpenPartialHomeomorph X H) :
    (e.symm.transOpenPartialHomeomorph d).symm ≫ₕ
      (e.symm.transOpenPartialHomeomorph d') = d.symm ≫ₕ d' := by
  simp only [Homeomorph.transOpenPartialHomeomorph_eq_trans,
    OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.trans_assoc]
  change d.symm ≫ₕ e.toOpenPartialHomeomorph ≫ₕ
    e.symm.toOpenPartialHomeomorph ≫ₕ d' = d.symm ≫ₕ d'
  simp only [← OpenPartialHomeomorph.trans_assoc,
    ← Homeomorph.trans_toOpenPartialHomeomorph,
    Homeomorph.self_trans_symm, Homeomorph.refl_toOpenPartialHomeomorph,
    OpenPartialHomeomorph.refl_trans]

theorem hasGroupoid (e : X ≃ₜ Y) (G : StructureGroupoid H)
    [HasGroupoid X G] :
    @HasGroupoid H _ Y _ (chartedSpace e) G := by
  letI : ChartedSpace H Y := chartedSpace e
  refine { compatible := ?_ }
  rintro c c' ⟨d, hd, rfl⟩ ⟨d', hd', rfl⟩
  rw [transition_eq]
  exact G.compatible hd hd'

theorem isManifold {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (I : ModelWithCorners 𝕜 E H) (n : WithTop ℕ∞)
    [IsManifold I n X] (e : X ≃ₜ Y) :
    @IsManifold 𝕜 _ E _ _ H _ I n Y _ (chartedSpace e) := by
  letI : ChartedSpace H Y := chartedSpace e
  letI : HasGroupoid Y (contDiffGroupoid n I) := hasGroupoid e _
  exact IsManifold.mk' I n Y

def structomorph (e : X ≃ₜ Y) (G : StructureGroupoid H)
    [HasGroupoid X G] :
    @Structomorph H _ G X Y _ _ _ (chartedSpace e) := by
  letI : ChartedSpace H Y := chartedSpace e
  refine { e with mem_groupoid := ?_ }
  intro c c' hc hc'
  obtain ⟨d, hd, rfl⟩ := hc'
  rw [Homeomorph.transOpenPartialHomeomorph_eq_trans]
  change c.symm ≫ₕ e.toOpenPartialHomeomorph ≫ₕ
    e.symm.toOpenPartialHomeomorph ≫ₕ d ∈ G
  simp only [← OpenPartialHomeomorph.trans_assoc,
    ← Homeomorph.trans_toOpenPartialHomeomorph,
    Homeomorph.self_trans_symm, Homeomorph.refl_toOpenPartialHomeomorph,
    OpenPartialHomeomorph.refl_trans]
  exact G.compatible hc hd

end General

section SelfModel

variable {𝕜 H X Y : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup H] [NormedSpace 𝕜 H]
  [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace H X]

theorem contMDiff_toFun (e : X ≃ₜ Y)
    [IsManifold 𝓘(𝕜,H) ∞ X] :
    letI := chartedSpace (H := H) e
    letI := isManifold 𝓘(𝕜,H) ∞ e
    ContMDiff 𝓘(𝕜,H) 𝓘(𝕜,H) ∞ e := by
  letI := chartedSpace (H := H) e
  letI := isManifold 𝓘(𝕜,H) ∞ e
  intro x
  rw [contMDiffAt_iff]
  refine ⟨e.continuous.continuousAt, ?_⟩
  let c := chartAt H x
  have hc : c x ∈ c.target := mem_chart_target H x
  have hmodel : ContDiffWithinAt 𝕜 ∞ (id : H → H) (Set.range 𝓘(𝕜,H))
      (extChartAt 𝓘(𝕜,H) x x) := contDiffWithinAt_id
  have hchart : (chartAt H (e x) : OpenPartialHomeomorph Y H) =
      e.symm.transOpenPartialHomeomorph c := by
    change e.symm.transOpenPartialHomeomorph (chartAt H (e.symm (e x))) = _
    simp only [e.symm_apply_apply]
    rfl
  apply hmodel.congr_of_eventuallyEq
  · filter_upwards [mem_nhdsWithin_of_mem_nhds (c.open_target.mem_nhds hc)] with y hy
    rw [extChartAt_coe, hchart]
    simp only [Function.comp_apply, extChartAt_coe_symm, extChartAt_coe,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, id]
    change c (e.symm (e (c.symm y))) = y
    rw [e.symm_apply_apply]
    exact c.right_inv hy
  · rw [extChartAt_coe, hchart]
    simp only [Function.comp_apply, extChartAt_coe_symm, extChartAt_coe,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, id]
    rw [c.left_inv (mem_chart_source H x)]
    change c (e.symm (e x)) = c x
    rw [e.symm_apply_apply]

theorem contMDiff_invFun (e : X ≃ₜ Y)
    [IsManifold 𝓘(𝕜,H) ∞ X] :
    letI := chartedSpace (H := H) e
    letI := isManifold 𝓘(𝕜,H) ∞ e
    ContMDiff 𝓘(𝕜,H) 𝓘(𝕜,H) ∞ e.symm := by
  letI := chartedSpace (H := H) e
  letI := isManifold 𝓘(𝕜,H) ∞ e
  intro y
  rw [contMDiffAt_iff]
  refine ⟨e.symm.continuous.continuousAt, ?_⟩
  let x := e.symm y
  let c := chartAt H x
  have hchart : (chartAt H y : OpenPartialHomeomorph Y H) =
      e.symm.transOpenPartialHomeomorph c := rfl
  have hc : (chartAt H y) y ∈ c.target := by
    rw [hchart]
    exact mem_chart_target H y
  have hmodel : ContDiffWithinAt 𝕜 ∞ (id : H → H) (Set.range 𝓘(𝕜,H))
      (extChartAt 𝓘(𝕜,H) y y) := contDiffWithinAt_id
  apply hmodel.congr_of_eventuallyEq
  · filter_upwards [mem_nhdsWithin_of_mem_nhds (c.open_target.mem_nhds hc)] with z hz
    rw [extChartAt_coe]
    simp only [Function.comp_apply, extChartAt_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, id]
    rw [hchart]
    change c (e.symm (e (c.symm z))) = z
    rw [e.symm_apply_apply]
    exact c.right_inv hz
  · rw [extChartAt_coe]
    simp only [Function.comp_apply, extChartAt_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, id]
    rw [hchart]
    change c (e.symm (e (c.symm (c x)))) = c x
    rw [c.left_inv (mem_chart_source H x), e.symm_apply_apply]

/-- A homeomorphism is a genuine complex (or real) diffeomorphism for
the transported atlas on its target, with the target's original topology. -/
def diffeomorph (e : X ≃ₜ Y) [IsManifold 𝓘(𝕜,H) ∞ X] :
    letI := chartedSpace (H := H) e
    letI := isManifold 𝓘(𝕜,H) ∞ e
    X ≃ₘ⟮𝓘(𝕜,H), 𝓘(𝕜,H)⟯ Y := by
  letI := chartedSpace (H := H) e
  letI := isManifold 𝓘(𝕜,H) ∞ e
  exact { e.toEquiv with
    contMDiff_toFun := contMDiff_toFun e
    contMDiff_invFun := contMDiff_invFun e }

end SelfModel

end

end QuaternionicSymmetry.HomeomorphTransportedManifold
