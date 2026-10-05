import QuaternionicSymmetry.OpenSubgroupLieTangentIdentity
import QuaternionicSymmetry.CompactLieTorusMaximalTransfer
import QuaternionicSymmetry.CompactLieMaximalTorusTangentSource

/-! The selected torus has the same intrinsic curve-velocity span in the
full Lie group and its inherited-atlas open identity component. -/

namespace QuaternionicSymmetry.IdentityComponentTorusTangentSpan

open IdentityComponentLie CompactLieTorusMaximalTransfer
open CompactLieTorusInputs CompactLieMaximalTorusTangentSource
open OpenSubgroupLie OpenSubgroupLieTangentIdentity
open TopologicalSpace Set
open scoped Manifold ContDiff Topology
noncomputable section

variable {V G : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace V G] [LieGroup 𝓘(ℝ,V) ∞ G]

theorem component_curve_velocity_mem_full {r : ℕ} (T : TorusEmbedding G r) :
    letI := IdentityComponentLie.charts V G
    letI := IdentityComponentLie.lieGroup V G
    torusCurveVelocities (V := V) (G := Component G) (liftToComponent G T) ⊆
      torusCurveVelocities (V := V) (G := G) T := by
  letI := IdentityComponentLie.charts V G
  letI := IdentityComponentLie.lieGroup V G
  intro v hv
  obtain ⟨c,hc0,hcr,hcSmooth,hcv⟩ := hv
  refine ⟨(Subtype.val : Component G → G) ∘ c, ?_, ?_, ?_, ?_⟩
  · simpa [Function.comp_apply] using congrArg Subtype.val hc0
  · intro s
    obtain ⟨t,ht⟩ := hcr s
    exact ⟨t, congrArg Subtype.val ht⟩
  · exact (IdentityComponentLie.inclusion_smooth V G).comp hcSmooth
  · have hchain := mfderiv_comp (0 : ℝ)
      ((IdentityComponentLie.inclusion_smooth V G).mdifferentiableAt (by simp))
      (hcSmooth.mdifferentiableAt (by simp))
    rw [hc0, mfderiv_inclusion_one_eq_id (Component G)
      (IdentityComponentLie.isOpen_component V G)] at hchain
    have hpoint := congrArg (fun A : ℝ →L[ℝ] V => A (1 : ℝ)) hchain
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hpoint
    exact hpoint.trans hcv

theorem full_curve_velocity_mem_component {r : ℕ} (T : TorusEmbedding G r) :
    letI := IdentityComponentLie.charts V G
    letI := IdentityComponentLie.lieGroup V G
    torusCurveVelocities (V := V) (G := G) T ⊆
      torusCurveVelocities (V := V) (G := Component G) (liftToComponent G T) := by
  letI := IdentityComponentLie.charts V G
  letI := IdentityComponentLie.lieGroup V G
  intro v hv
  obtain ⟨c,hc0,hcr,hcSmooth,hcv⟩ := hv
  have hcComponent (s : ℝ) : c s ∈ Component G := by
    obtain ⟨t,ht⟩ := hcr s
    rw [← ht]
    exact torus_range_le_component G T ⟨t,rfl⟩
  let cC : ℝ → Component G := fun s => ⟨c s, hcComponent s⟩
  have hcCsmooth : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,V) ∞ cC :=
    OpenSubgroupLie.contMDiff_codRestrict_opens
      (U := (⟨Component G, IdentityComponentLie.isOpen_component V G⟩ : Opens G))
      hcSmooth hcComponent
  refine ⟨cC, ?_, ?_, hcCsmooth, ?_⟩
  · apply Subtype.ext
    exact hc0
  · intro s
    obtain ⟨t,ht⟩ := hcr s
    exact ⟨t, Subtype.ext ht⟩
  · have hchain := mfderiv_comp (0 : ℝ)
      ((IdentityComponentLie.inclusion_smooth V G).mdifferentiableAt (by simp))
      (hcCsmooth.mdifferentiableAt (by simp))
    have hfun : ((Subtype.val : Component G → G) ∘ cC) = c := rfl
    have hcC0 : cC 0 = 1 := by
      apply Subtype.ext
      exact hc0
    rw [hfun, hcC0, mfderiv_inclusion_one_eq_id (Component G)
      (IdentityComponentLie.isOpen_component V G)] at hchain
    have hpoint := congrArg (fun A : ℝ →L[ℝ] V => A (1 : ℝ)) hchain
    simp at hpoint
    exact hpoint.symm.trans hcv

theorem torusLieSpan_liftToComponent_eq {r : ℕ} (T : TorusEmbedding G r) :
    letI := IdentityComponentLie.charts V G
    letI := IdentityComponentLie.lieGroup V G
    torusLieSpan (V := V) (G := Component G) (liftToComponent G T) =
      torusLieSpan (V := V) (G := G) T := by
  letI := IdentityComponentLie.charts V G
  letI := IdentityComponentLie.lieGroup V G
  apply congrArg (Submodule.span ℝ)
  exact Set.Subset.antisymm (component_curve_velocity_mem_full T)
    (full_curve_velocity_mem_component T)

end
end QuaternionicSymmetry.IdentityComponentTorusTangentSpan
