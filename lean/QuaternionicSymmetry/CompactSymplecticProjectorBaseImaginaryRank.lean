import QuaternionicSymmetry.CompactSymplecticProjectorComplementQuaternionAction
import Mathlib.RingTheory.SimpleRing.Basic

/-! In positive quaternionic dimension, the checked imaginary tangent
endomorphism plane has actual real dimension three. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorBaseImaginaryRank

open Manifold
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorBaseQuaternionAction
open CompactSymplecticProjectorBaseImaginaryPlane
open CompactSymplecticClosedSubgroupSource
open CompactSymplecticHomogeneousAtlasSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section
set_option maxHeartbeats 1000000

private abbrev RModel (d : ℕ) := Fin d → ℝ

private theorem imaginaryQuaternion_finrank :
    Module.finrank ℝ (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)).ker = 3 := by
  let f := QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)
  have hsurj : Function.Surjective f := by
    intro x
    exact ⟨(x : ℍ), rfl⟩
  have hrange : Module.finrank ℝ (LinearMap.range f) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj]
    simp
  have h := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, QuaternionAlgebra.finrank_eq_four] at h
  change 1 + Module.finrank ℝ (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)).ker = 4 at h
  omega

theorem baseQuaternionAction_injective
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (atlas : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) :
    letI := atlas.quotientCharts
    Function.Injective (baseQuaternionAction hDesc hImm n d e q g atlas hq) := by
  letI := atlas.quotientCharts
  have hqpos : 0 < q := by omega
  letI : Nonempty (Fin q) := ⟨⟨0, hqpos⟩⟩
  letI : Nontrivial (TangentSpace 𝓘(ℝ, RModel q) (baseCoset n)) := by
    change Nontrivial (RModel q)
    infer_instance
  letI : Nontrivial (Module.End ℝ
      (TangentSpace 𝓘(ℝ, RModel q) (baseCoset n))) := inferInstance
  exact (baseQuaternionAction hDesc hImm n d e q g atlas hq).toRingHom.injective

/-- The pure-imaginary plane is genuinely rank three on every actual
projector model with positive quaternionic dimension. -/
theorem baseImaginaryPlane_finrank
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (atlas : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) :
    letI := atlas.quotientCharts
    Module.finrank ℝ (baseImaginaryPlane hDesc hImm n d e q g atlas hq) = 3 := by
  letI := atlas.quotientCharts
  let f := (baseQuaternionAction hDesc hImm n d e q g atlas hq).toLinearMap
  let K := (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)).ker
  let fk : K →ₗ[ℝ] Module.End ℝ
      (TangentSpace 𝓘(ℝ, RModel q) (baseCoset n)) := f.comp K.subtype
  have hfk : Function.Injective fk :=
    (baseQuaternionAction_injective hDesc hImm n d e q g atlas hq hn).comp
      Subtype.val_injective
  have hrange : LinearMap.range fk = baseImaginaryPlane hDesc hImm n d e q g atlas hq := by
    ext S
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨r.1, r.2, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨⟨r, hr⟩, rfl⟩
  rw [← hrange, LinearMap.finrank_range_of_inj hfk]
  exact imaginaryQuaternion_finrank

end
end QuaternionicSymmetry.CompactSymplecticProjectorBaseImaginaryRank
