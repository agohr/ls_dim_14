import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-! Open subgroups inherit the actual Lie atlas without a new source
premise. This will be used for the identity component of full isometries. -/

namespace QuaternionicSymmetry.OpenSubgroupLie

open TopologicalSpace
open scoped Manifold ContDiff
noncomputable section

theorem contMDiff_codRestrict_opens
    {E H V X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace X] [ChartedSpace H X]
    [TopologicalSpace Y] [ChartedSpace V Y]
    {U : Opens Y} {f : X → Y}
    (hf : ContMDiff I 𝓘(ℝ,V) ∞ f) (hU : ∀ x, f x ∈ U) :
    ContMDiff I 𝓘(ℝ,V) ∞ (fun x => (⟨f x,hU x⟩ : U)) := by
  intro x
  have h := contMDiffAt_iff.mp (hf x)
  apply contMDiffAt_iff.mpr
  exact ⟨tendsto_subtype_rng.mpr h.1,h.2⟩

variable {V G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [Group G] [TopologicalSpace G] [ChartedSpace V G]
  (S : Subgroup G) (hS : IsOpen (S : Set G))

def charts : ChartedSpace V S := by
  let U : Opens G := ⟨S,hS⟩
  change ChartedSpace V U
  infer_instance

def manifold [IsManifold 𝓘(ℝ,V) ∞ G] :
    letI := charts (V := V) S hS
    IsManifold 𝓘(ℝ,V) ∞ S := by
  let U : Opens G := ⟨S,hS⟩
  change IsManifold 𝓘(ℝ,V) ∞ U
  infer_instance

theorem inclusion_smooth :
    letI := charts (V := V) S hS
    ContMDiff 𝓘(ℝ,V) 𝓘(ℝ,V) ∞ (Subtype.val : S → G) := by
  let U : Opens G := ⟨S,hS⟩
  change ContMDiff 𝓘(ℝ,V) 𝓘(ℝ,V) ∞ (Subtype.val : U → G)
  exact contMDiff_subtype_val

def lieGroup [LieGroup 𝓘(ℝ,V) ∞ G] :
    letI := charts (V := V) S hS
    LieGroup 𝓘(ℝ,V) ∞ S := by
  letI := charts (V := V) S hS
  letI := manifold (V := V) S hS
  let U : Opens G := ⟨S,hS⟩
  have hval := inclusion_smooth (V := V) S hS
  refine { toIsManifold := inferInstance, contMDiff_mul := ?_, contMDiff_inv := ?_ }
  · have hmul : ContMDiff (𝓘(ℝ,V).prod 𝓘(ℝ,V)) 𝓘(ℝ,V) ∞
        (fun p : S × S => (p.1 : G) * (p.2 : G)) :=
      (hval.comp contMDiff_fst).mul (hval.comp contMDiff_snd)
    exact contMDiff_codRestrict_opens (U := U) hmul
      (fun p => S.mul_mem p.1.2 p.2.2)
  · exact contMDiff_codRestrict_opens (U := U) hval.inv
      (fun p => S.inv_mem p.2)

end
end QuaternionicSymmetry.OpenSubgroupLie
