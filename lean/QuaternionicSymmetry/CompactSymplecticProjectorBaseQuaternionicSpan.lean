import QuaternionicSymmetry.CompactSymplecticProjectorBaseImaginaryRank

/-! The genuine rank-three imaginary tangent plane is exactly the real
span of the three checked actual quaternionic tangent operators. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorBaseQuaternionicSpan

open Manifold
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorBaseQuaternionic
open CompactSymplecticProjectorBaseQuaternionAction
open CompactSymplecticProjectorBaseImaginaryPlane
open CompactSymplecticClosedSubgroupSource
open CompactSymplecticHomogeneousAtlasSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section
set_option maxHeartbeats 5000000

private abbrev RModel (d : ℕ) := Fin d → ℝ

def baseGeneratorSpan
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n) :
    letI := a.quotientCharts
    Submodule ℝ (Module.End ℝ
      (TangentSpace 𝓘(ℝ, RModel q) (baseCoset n))) := by
  letI := a.quotientCharts
  exact Submodule.span ℝ
    ({(baseI hDesc hImm n d e q g a hq).toLinearMap,
      (baseJ hDesc hImm n d e q g a hq).toLinearMap,
      (baseK hDesc hImm n d e q g a hq).toLinearMap} :
      Set (Module.End ℝ (TangentSpace 𝓘(ℝ, RModel q) (baseCoset n))))

theorem baseImaginaryPlane_eq_generatorSpan
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n) :
    letI := a.quotientCharts
    baseImaginaryPlane hDesc hImm n d e q g a hq =
      baseGeneratorSpan hDesc hImm n d e q g a hq := by
  letI := a.quotientCharts
  let I := (baseI hDesc hImm n d e q g a hq).toLinearMap
  let J := (baseJ hDesc hImm n d e q g a hq).toLinearMap
  let K := (baseK hDesc hImm n d e q g a hq).toLinearMap
  apply le_antisymm
  · intro S hS
    obtain ⟨r, hr, hSr⟩ := Submodule.mem_map.mp hS
    have hr0 : r.re = 0 := LinearMap.mem_ker.mp hr
    have hdecomp : baseQuaternionAction hDesc hImm n d e q g a hq r =
        r.imI • I + r.imJ • J + r.imK • K := by
      ext v
      simp [I, J, K, baseQuaternionAction_apply, hr0, add_assoc]
    rw [← hSr]
    change baseQuaternionAction hDesc hImm n d e q g a hq r ∈
      baseGeneratorSpan hDesc hImm n d e q g a hq
    rw [hdecomp]
    apply Submodule.add_mem
    · apply Submodule.add_mem
      · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp [I]))
      · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp [J]))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp [K]))
  · apply Submodule.span_le.mpr
    intro S hS
    rcases hS with rfl | rfl | rfl
    · have hI : I = baseQuaternionAction hDesc hImm n d e q g a hq
          (⟨0, 1, 0, 0⟩ : ℍ) := by
        ext v
        simp [I, baseQuaternionAction_apply]
      change I ∈ baseImaginaryPlane hDesc hImm n d e q g a hq
      rw [hI]
      exact action_imaginary_mem hDesc hImm n d e q g a hq _ rfl
    · have hJ : J = baseQuaternionAction hDesc hImm n d e q g a hq
          (⟨0, 0, 1, 0⟩ : ℍ) := by
        ext v
        simp [J, baseQuaternionAction_apply]
      change J ∈ baseImaginaryPlane hDesc hImm n d e q g a hq
      rw [hJ]
      exact action_imaginary_mem hDesc hImm n d e q g a hq _ rfl
    · have hK : K = baseQuaternionAction hDesc hImm n d e q g a hq
          (⟨0, 0, 0, 1⟩ : ℍ) := by
        ext v
        simp [K, baseQuaternionAction_apply]
      change K ∈ baseImaginaryPlane hDesc hImm n d e q g a hq
      rw [hK]
      exact action_imaginary_mem hDesc hImm n d e q g a hq _ rfl

end
end QuaternionicSymmetry.CompactSymplecticProjectorBaseQuaternionicSpan
