import QuaternionicSymmetry.OpenSubgroupLie
import Mathlib.Analysis.Complex.Basic

/-! Complex analogue of the checked real open-subgroup atlas transfer.
Once the full automorphism group has a compatible complex Lie atlas,
its open identity component inherits that atlas internally. -/

namespace QuaternionicSymmetry.OpenSubgroupComplexLie

open TopologicalSpace
open scoped Manifold ContDiff
noncomputable section

theorem contMDiff_codRestrict_opens
    {E H V X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace H] {I : ModelWithCorners ℂ E H}
    [TopologicalSpace X] [ChartedSpace H X]
    [TopologicalSpace Y] [ChartedSpace V Y]
    {U : Opens Y} {f : X → Y}
    (hf : ContMDiff I 𝓘(ℂ,V) ∞ f) (hU : ∀ x, f x ∈ U) :
    ContMDiff I 𝓘(ℂ,V) ∞ (fun x => (⟨f x,hU x⟩ : U)) := by
  intro x
  have h := contMDiffAt_iff.mp (hf x)
  apply contMDiffAt_iff.mpr
  exact ⟨tendsto_subtype_rng.mpr h.1,h.2⟩

variable {V G : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [Group G] [TopologicalSpace G] [ChartedSpace V G]
  (S : Subgroup G) (hS : IsOpen (S : Set G))

def charts : ChartedSpace V S := by
  let U : Opens G := ⟨S,hS⟩
  change ChartedSpace V U
  infer_instance

def manifold [IsManifold 𝓘(ℂ,V) ∞ G] :
    letI := charts (V := V) S hS
    IsManifold 𝓘(ℂ,V) ∞ S := by
  let U : Opens G := ⟨S,hS⟩
  change IsManifold 𝓘(ℂ,V) ∞ U
  infer_instance

theorem inclusion_holomorphic :
    letI := charts (V := V) S hS
    ContMDiff 𝓘(ℂ,V) 𝓘(ℂ,V) ∞ (Subtype.val : S → G) := by
  let U : Opens G := ⟨S,hS⟩
  change ContMDiff 𝓘(ℂ,V) 𝓘(ℂ,V) ∞ (Subtype.val : U → G)
  exact contMDiff_subtype_val

def lieGroup [LieGroup 𝓘(ℂ,V) ∞ G] :
    letI := charts (V := V) S hS
    LieGroup 𝓘(ℂ,V) ∞ S := by
  letI := charts (V := V) S hS
  letI := manifold (V := V) S hS
  let U : Opens G := ⟨S,hS⟩
  have hval := inclusion_holomorphic (V := V) S hS
  refine { toIsManifold := inferInstance, contMDiff_mul := ?_, contMDiff_inv := ?_ }
  · have hmul : ContMDiff (𝓘(ℂ,V).prod 𝓘(ℂ,V)) 𝓘(ℂ,V) ∞
        (fun p : S × S => (p.1 : G) * (p.2 : G)) :=
      (hval.comp contMDiff_fst).mul (hval.comp contMDiff_snd)
    exact contMDiff_codRestrict_opens (U := U) hmul
      (fun p => S.mul_mem p.1.2 p.2.2)
  · exact contMDiff_codRestrict_opens (U := U) hval.inv
      (fun p => S.inv_mem p.2)

end
end QuaternionicSymmetry.OpenSubgroupComplexLie
