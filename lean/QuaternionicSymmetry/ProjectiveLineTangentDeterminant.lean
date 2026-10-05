import QuaternionicSymmetry.ComplexProjectiveManifold
import QuaternionicSymmetry.FourDimensionalHalfSpinProjective
import QuaternionicSymmetry.HolomorphicRankOneDeterminant
import QuaternionicSymmetry.HolomorphicLineCoreClasses
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-! The actual tangent determinant line of CP¹, with transitions obtained
from derivatives of the standard complex projective atlas. -/

namespace QuaternionicSymmetry.ProjectiveLineTangentDeterminant

open scoped Manifold ContDiff
open FourDimensionalHalfSpinProjective HolomorphicDeterminantLine
open HolomorphicLineCoreClasses
noncomputable section

abbrev Model := Fin 1 → ℂ

def tangentCore : VectorBundleCore ℂ ProjectiveSpinor Model
    (atlas Model ProjectiveSpinor) :=
  tangentBundleCore 𝓘(ℂ,Model) ProjectiveSpinor

instance tangentCore_holomorphic : tangentCore.IsContMDiff 𝓘(ℂ,Model) ∞ := by
  letI : IsManifold 𝓘(ℂ,Model) (∞ + 1) ProjectiveSpinor := by
    simpa using (inferInstance : IsManifold 𝓘(ℂ,Model) ∞ ProjectiveSpinor)
  exact tangentBundleCore.isContMDiff

def tangentLineCore : LineCore.{0} (B := ProjectiveSpinor) 𝓘(ℂ,Model) where
  Index := atlas Model ProjectiveSpinor
  core := determinantCore tangentCore
  holomorphic := inferInstance

theorem tangentLineSection_contMDiffOn (U : Set ProjectiveSpinor)
    (s : ∀ x : ProjectiveSpinor, TangentSpace 𝓘(ℂ,Model) x)
    (hs : ContMDiffOn 𝓘(ℂ,Model) (𝓘(ℂ,Model)).tangent ∞
      (fun x => (⟨x,s x⟩ : TangentBundle 𝓘(ℂ,Model) ProjectiveSpinor)) U) :
    letI := tangentLineCore.holomorphic
    ContMDiffOn 𝓘(ℂ,Model) ((𝓘(ℂ,Model)).prod 𝓘(ℂ,ℂ)) ∞
      (fun x => (⟨x,s x 0⟩ : Bundle.TotalSpace ℂ tangentLineCore.core.Fiber)) U := by
  exact HolomorphicRankOneDeterminant.determinantSection_contMDiffOn
    𝓘(ℂ,Model) tangentCore U s hs

end
end QuaternionicSymmetry.ProjectiveLineTangentDeterminant
