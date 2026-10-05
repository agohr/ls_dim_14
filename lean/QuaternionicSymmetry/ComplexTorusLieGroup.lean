import QuaternionicSymmetry.ComplexTorusCharacterHolomorphic
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! The existing open-submanifold complex torus is a genuine complex Lie
group. Its multiplication and inverse are checked in the fixed ambient
coordinate chart, without a new manifold structure. -/

namespace QuaternionicSymmetry.ComplexTorusLieGroup

open TorusLaurentRepresentation ComplexTorusHolomorphicStructure
open ComplexTorusCharacterHolomorphic
open scoped Manifold ContDiff
noncomputable section

variable (r : ℕ)

theorem multiplication_holomorphic :
    ContMDiff (𝓘(ℂ, Fin r → ℂ).prod 𝓘(ℂ, Fin r → ℂ))
      𝓘(ℂ, Fin r → ℂ) ∞
      (fun p : ComplexTorus r × ComplexTorus r => torusVal r (p.1 * p.2)) := by
  apply contMDiff_pi_space.mpr
  intro i
  have hleft : ContMDiff
      (𝓘(ℂ, Fin r → ℂ).prod 𝓘(ℂ, Fin r → ℂ)) 𝓘(ℂ,ℂ) ∞
      (fun p : ComplexTorus r × ComplexTorus r => ((p.1 i : ℂ))) :=
    ((contDiff_apply ℂ ℂ i).contMDiff).comp
      ((contMDiff_torusVal r).comp contMDiff_fst)
  have hright : ContMDiff
      (𝓘(ℂ, Fin r → ℂ).prod 𝓘(ℂ, Fin r → ℂ)) 𝓘(ℂ,ℂ) ∞
      (fun p : ComplexTorus r × ComplexTorus r => ((p.2 i : ℂ))) :=
    ((contDiff_apply ℂ ℂ i).contMDiff).comp
      ((contMDiff_torusVal r).comp contMDiff_snd)
  simpa [torusVal] using hleft.mul hright

theorem inverse_holomorphic :
    ContMDiff 𝓘(ℂ, Fin r → ℂ) 𝓘(ℂ, Fin r → ℂ) ∞
      (fun z : ComplexTorus r => torusVal r z⁻¹) := by
  apply contMDiff_pi_space.mpr
  intro i
  have hAmb : ContMDiffOn 𝓘(ℂ, Fin r → ℂ) 𝓘(ℂ,ℂ) ∞
      (fun x : Fin r → ℂ => x i ^ (-1 : ℤ)) (allNonzero r) :=
    (contDiffOn_coord_zpow i (-1)).contMDiffOn
  have hmap : Set.MapsTo (torusVal r) Set.univ (allNonzero r) := by
    intro z hz j
    exact (z j).ne_zero
  have hcomp := hAmb.comp (contMDiff_torusVal r).contMDiffOn hmap
  have hwhole := contMDiffOn_univ.mp hcomp
  simpa [torusVal, zpow_neg_one] using hwhole

noncomputable instance : LieGroup 𝓘(ℂ, Fin r → ℂ) ∞ (ComplexTorus r) where
  contMDiff_mul := by
    apply ContMDiff.of_comp_isOpenEmbedding (torusVal_isOpenEmbedding r)
    exact multiplication_holomorphic r
  contMDiff_inv := by
    apply ContMDiff.of_comp_isOpenEmbedding (torusVal_isOpenEmbedding r)
    exact inverse_holomorphic r

end
end QuaternionicSymmetry.ComplexTorusLieGroup
