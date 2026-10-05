import QuaternionicSymmetry.CompactSymplecticProjectorStabilizerTangentEquiv
import QuaternionicSymmetry.CompactSymplecticProjectorFullIsotropyPlane

/-! The rank-three imaginary plane is fixed by conjugation with every
genuine tangent automorphism induced by an actual projector stabilizer. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStabilizerPlane

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorBaseImaginaryPlane
open CompactSymplecticProjectorBaseImaginaryRank
open CompactSymplecticProjectorStabilizerTangentFactor
open CompactSymplecticProjectorStabilizerTangentEquiv
open CompactSymplecticProjectorFullIsotropyPlane
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 1000000

private abbrev RModel (d : ℕ) := Fin d → ℝ

theorem stabilizer_conj_preserves_imaginary
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (atlas : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (u : firstPairStabilizer n) :
    letI := atlas.quotientCharts
    (baseImaginaryPlane hDesc hImm n d e q g atlas hq).map
      (((stabilizerTangentEquiv n d e q g atlas u).toLinearEquiv.conjAlgEquiv ℝ).toLinearMap) =
      baseImaginaryPlane hDesc hImm n d e q g atlas hq := by
  letI := atlas.quotientCharts
  let T := (stabilizerTangentEquiv n d e q g atlas u).toLinearEquiv
  let Q := baseImaginaryPlane hDesc hImm n d e q g atlas hq
  have hle : Q.map (T.conjAlgEquiv ℝ).toLinearMap ≤ Q := by
    intro S hS
    obtain ⟨R, hR, rfl⟩ := Submodule.mem_map.mp hS
    obtain ⟨R', hcomm⟩ :=
      fullStabilizer_preserves_imaginary hDesc hImm n d e q g atlas hq u ⟨R, hR⟩
    have hTeq : T.toLinearMap = stabilizerTangentEnd n d e q g atlas u :=
      stabilizerTangentEquiv_toLinearMap n d e q g atlas u
    have hconj : (T.conjAlgEquiv ℝ) R = R'.1 := by
      apply LinearMap.ext
      intro v
      have hv := congrArg
        (fun F : Module.End ℝ (TangentSpace 𝓘(ℝ, RModel q) (baseCoset n)) =>
          F (T.symm v)) hcomm
      change T (R (T.symm v)) = R'.1 v
      calc
        T (R (T.symm v)) = R'.1 (T (T.symm v)) := by
          simpa only [Module.End.mul_apply, ← hTeq] using hv
        _ = R'.1 v := congrArg R'.1 (T.apply_symm_apply v)
    change (T.conjAlgEquiv ℝ) R ∈ Q
    rw [hconj]
    exact R'.2
  haveI : FiniteDimensional ℝ Q :=
    .of_finrank_eq_succ (by simpa using
      (baseImaginaryPlane_finrank hDesc hImm n d e q g atlas hq hn :
        Module.finrank ℝ Q = 3))
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [baseImaginaryPlane_finrank hDesc hImm n d e q g atlas hq hn]
  let f := (T.conjAlgEquiv ℝ).toLinearMap
  let fk : Q →ₗ[ℝ] Module.End ℝ
      (TangentSpace 𝓘(ℝ, RModel q) (baseCoset n)) := f.comp Q.subtype
  have hfk : Function.Injective fk :=
    (T.conjAlgEquiv ℝ).injective.comp Subtype.val_injective
  have hrange : LinearMap.range fk = Q.map f := by
    ext S
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨r.1, r.2, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨⟨r, hr⟩, rfl⟩
  rw [← hrange, LinearMap.finrank_range_of_inj hfk]
  exact baseImaginaryPlane_finrank hDesc hImm n d e q g atlas hq hn

end
end QuaternionicSymmetry.CompactSymplecticProjectorStabilizerPlane
