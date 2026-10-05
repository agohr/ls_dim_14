import QuaternionicSymmetry.FourDimensionalHalfSpinHopfAffineDerivative
import QuaternionicSymmetry.FourDimensionalHalfSpinHopfAffineSphere
import QuaternionicSymmetry.ManifoldTwistorVerticalTangent

/-! Convert the checked affine quaternion derivative to the genuine
round-sphere tangent derivative, using the independent sphere inclusion. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfAffineSphereDerivative

open scoped Quaternion Matrix Manifold ContDiff Topology
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinHopfNormalizedConnection
  FourDimensionalHalfSpinHopfAffineDerivative
  FourDimensionalHalfSpinHopfScalarDerivative
  FourDimensionalHalfSpinHopfAffineSphere
  FourDimensionalHalfSpinHopfNormalization
  FourDimensionalHalfSpinHopfSphere
  FourDimensionalHalfSpinProjectiveConnection
  ManifoldTwistorCoefficientSphere
  ManifoldTwistorVerticalComplex
  ManifoldTwistorSphereBundle
  QuaternionicUnitScalarIsometries
  ManifoldQuaternionicAdjointConnection
  ComplexProjectiveTopology

noncomputable section

local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

private def imaginaryCoords : ℍ →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun q := ![q.imI,q.imJ,q.imK]
  map_add' p q := by ext j; fin_cases j <;> simp
  map_smul' r q := by ext j; fin_cases j <;> simp

def imaginaryEuclidean : ℍ →L[ℝ] EuclideanThree :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.comp
    imaginaryCoords.toContinuousLinearMap

theorem imaginaryEuclidean_pureScalar (a : Fin 3 → ℝ) :
    imaginaryEuclidean (pureScalar a) = toEuclidean a := by
  apply (EuclideanSpace.equiv (Fin 3) ℝ).injective
  ext j
  fin_cases j <;> simp [imaginaryEuclidean, imaginaryCoords,
    pureScalar, toEuclidean]

def firstAffineSphere (z : ℂ) : geometricSphere := affineSphere 0 ![z]

theorem firstAffineSphere_coe (z : ℂ) :
    (firstAffineSphere z : EuclideanThree) =
      imaginaryEuclidean (normalizedSpinorHopf (affineSpinorLift z)) := by
  have hs : affineSpinorLift z ≠ 0 := by simp [affineSpinorLift]
  have hvec : homogeneousVector 1 (0 : Fin 2) ![z] = affineSpinorLift z := by
    ext j; fin_cases j <;> simp [affineSpinorLift, homogeneousVector]
  rw [firstAffineSphere, affineSphere_eq_hopf]
  have hhopf : hopfSphere (homogeneousVector 1 (0 : Fin 2) ![z])
      (homogeneousVector_ne_zero 1 0 ![z]) =
      hopfSphere (affineSpinorLift z) hs := by
    simpa only [hvec]
  rw [hhopf]
  change toEuclidean (hopfSphere (affineSpinorLift z) _).1 = _
  rw [← imaginaryEuclidean_pureScalar,
    pureScalar_hopfSphere]
  congr 1
  simpa only [normalizedSpinorHopf, hopfQuaternion_eq_ratio]

private def finOneLinear : ℂ →L[ℝ] (Fin 1 → ℂ) :=
  ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id ℝ ℂ)

theorem firstAffineSphere_mdifferentiableAt (z : ℂ) :
    MDifferentiableAt 𝓘(ℝ,ℂ) (𝓡 2) firstAffineSphere z := by
  have h := (contMDiff_affineSphere 0).mdifferentiableAt
    (x := finOneLinear z) (by simp)
  have hc : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 1 → ℂ) ∞ finOneLinear :=
    finOneLinear.contDiff.contMDiff
  have hf : MDifferentiableAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 1 → ℂ)
      finOneLinear z :=
    hc.mdifferentiableAt (by simp)
  convert h.comp z hf using 1 <;> rfl

theorem firstAffineSphere_tangent_fderiv (z w : ℂ) :
    sphereTangentMap (firstAffineSphere z)
      (mfderiv 𝓘(ℝ,ℂ) (𝓡 2) firstAffineSphere z w) =
      imaginaryEuclidean
        (fderiv ℝ (normalizedSpinorHopf ∘ affineSpinorLift) z w) := by
  let ι : geometricSphere → EuclideanThree := Subtype.val
  have hι : MDifferentiableAt (𝓡 2) 𝓘(ℝ,EuclideanThree)
      ι (firstAffineSphere z) :=
    (contMDiff_coe_sphere (n := 2) (m := ∞)).mdifferentiableAt (by simp)
  have hchain := mfderiv_comp z hι (firstAffineSphere_mdifferentiableAt z)
  have hfun : ι ∘ firstAffineSphere =
      imaginaryEuclidean ∘ normalizedSpinorHopf ∘ affineSpinorLift := by
    funext t; exact firstAffineSphere_coe t
  have hdiff : DifferentiableAt ℝ
      (normalizedSpinorHopf ∘ affineSpinorLift) z := by
    exact (normalizedSpinorHopf_differentiableAt ![1,z] (by simp)).comp
      z (by
        let L : ℂ →L[ℝ] Spinor := ContinuousLinearMap.pi (fun j : Fin 2 =>
          if j = 0 then 0 else ContinuousLinearMap.id ℝ ℂ)
        have hfun : affineSpinorLift = fun t => ![1,0] + L t := by
          funext t; ext j; fin_cases j <;>
            simp [affineSpinorLift, L]
        rw [hfun]
        exact ((hasFDerivAt_const (𝕜 := ℝ) (![1,0] : Spinor) z).add
          L.hasFDerivAt).differentiableAt)
  have hderiv : fderiv ℝ (ι ∘ firstAffineSphere) z =
      imaginaryEuclidean.comp
        (fderiv ℝ (normalizedSpinorHopf ∘ affineSpinorLift) z) := by
    rw [hfun]
    simpa only [ContinuousLinearMap.fderiv] using
      (fderiv_comp z imaginaryEuclidean.differentiableAt hdiff)
  have hv := congrArg (fun L : ℂ →L[ℝ] EuclideanThree => L w) hchain
  rw [mfderiv_eq_fderiv, hderiv] at hv
  simpa only [sphereTangentMap, ContinuousLinearMap.comp_apply,
    Function.comp_apply] using hv.symm

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfAffineSphereDerivative
