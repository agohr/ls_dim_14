import QuaternionicSymmetry.FourDimensionalHalfSpinHopfSecondHorizontal
import QuaternionicSymmetry.FourDimensionalHalfSpinHopfAffineSphereDerivative

/-! Convert the independently checked second affine spinor derivative
to the true tangent derivative of the geometric sphere. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfSecondSphereDerivative

open scoped Quaternion Matrix Manifold ContDiff Topology
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinHopfSecondHorizontal
  FourDimensionalHalfSpinHopfAffineSphereDerivative
  FourDimensionalHalfSpinHopfAffineSphere
  FourDimensionalHalfSpinHopfNormalization
  FourDimensionalHalfSpinHopfNormalizedConnection
  FourDimensionalHalfSpinHopfScalarDerivative
  FourDimensionalHalfSpinHopfSphere
  FourDimensionalHalfSpinProjectiveSecondTensor
  ManifoldTwistorCoefficientSphere
  ManifoldTwistorVerticalComplex
  ManifoldTwistorSphereBundle
  QuaternionicUnitScalarIsometries
  ManifoldQuaternionicAdjointConnection
  ComplexProjectiveTopology

noncomputable section

local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

def secondAffineSpinorLift (z : ℂ) : Spinor := ![z,1]

private def secondAffineSpinorLinear : ℂ →L[ℝ] Spinor :=
  ContinuousLinearMap.pi (fun j : Fin 2 =>
    if j = 0 then ContinuousLinearMap.id ℝ ℂ else 0)

private theorem secondAffineSpinorLift_eq (z : ℂ) :
    secondAffineSpinorLift z = ![0,1] + secondAffineSpinorLinear z := by
  ext j
  fin_cases j <;> simp [secondAffineSpinorLift, secondAffineSpinorLinear]

private theorem secondAffineSpinorLift_hasFDerivAt (z : ℂ) :
    HasFDerivAt secondAffineSpinorLift secondAffineSpinorLinear z := by
  convert (hasFDerivAt_const (𝕜 := ℝ) (![0,1] : Spinor) z).add
    secondAffineSpinorLinear.hasFDerivAt using 1
  · funext w; exact secondAffineSpinorLift_eq w
  · simp

private theorem secondAffineSpinorLift_fderiv (z w : ℂ) :
    fderiv ℝ secondAffineSpinorLift z w = ![w,0] := by
  rw [(secondAffineSpinorLift_hasFDerivAt z).fderiv]
  ext j
  fin_cases j <;> simp [secondAffineSpinorLinear]

def secondAffineSphere (z : ℂ) : geometricSphere := affineSphere 1 ![z]

theorem secondAffineSphere_coe (z : ℂ) :
    (secondAffineSphere z : EuclideanThree) =
      imaginaryEuclidean
        (normalizedSpinorHopf (secondAffineSpinorLift z)) := by
  have hs : secondAffineSpinorLift z ≠ 0 := by simp [secondAffineSpinorLift]
  have hvec : homogeneousVector 1 (1 : Fin 2) ![z] =
      secondAffineSpinorLift z := by
    ext j; fin_cases j <;>
      simp [secondAffineSpinorLift, homogeneousVector,
        Fin.insertNth, Fin.succAboveCases]
  rw [secondAffineSphere, affineSphere_eq_hopf]
  have hhopf : hopfSphere (homogeneousVector 1 (1 : Fin 2) ![z])
      (homogeneousVector_ne_zero 1 1 ![z]) =
      hopfSphere (secondAffineSpinorLift z) hs := by
    simpa only [hvec]
  rw [hhopf]
  change toEuclidean (hopfSphere (secondAffineSpinorLift z) _).1 = _
  rw [← imaginaryEuclidean_pureScalar,
    pureScalar_hopfSphere]
  congr 1
  simpa only [normalizedSpinorHopf, hopfQuaternion_eq_ratio]

private def finOneLinear : ℂ →L[ℝ] (Fin 1 → ℂ) :=
  ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id ℝ ℂ)

theorem secondAffineSphere_mdifferentiableAt (z : ℂ) :
    MDifferentiableAt 𝓘(ℝ,ℂ) (𝓡 2) secondAffineSphere z := by
  have h := (contMDiff_affineSphere 1).mdifferentiableAt
    (x := finOneLinear z) (by simp)
  have hc : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 1 → ℂ) ∞ finOneLinear :=
    finOneLinear.contDiff.contMDiff
  have hf : MDifferentiableAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 1 → ℂ)
      finOneLinear z := hc.mdifferentiableAt (by simp)
  convert h.comp z hf using 1 <;> rfl

theorem secondAffineSphere_tangent_fderiv (z w : ℂ) :
    sphereTangentMap (secondAffineSphere z)
      (mfderiv 𝓘(ℝ,ℂ) (𝓡 2) secondAffineSphere z w) =
      imaginaryEuclidean
        (fderiv ℝ (normalizedSpinorHopf ∘ secondAffineSpinorLift) z w) := by
  let ι : geometricSphere → EuclideanThree := Subtype.val
  have hι : MDifferentiableAt (𝓡 2) 𝓘(ℝ,EuclideanThree)
      ι (secondAffineSphere z) :=
    (contMDiff_coe_sphere (n := 2) (m := ∞)).mdifferentiableAt (by simp)
  have hchain := mfderiv_comp z hι (secondAffineSphere_mdifferentiableAt z)
  have hfun : ι ∘ secondAffineSphere =
      imaginaryEuclidean ∘ normalizedSpinorHopf ∘ secondAffineSpinorLift := by
    funext t; exact secondAffineSphere_coe t
  have hdiff : DifferentiableAt ℝ
      (normalizedSpinorHopf ∘ secondAffineSpinorLift) z :=
    (normalizedSpinorHopf_differentiableAt ![z,1] (by simp)).comp
      z (secondAffineSpinorLift_hasFDerivAt z).differentiableAt
  have hderiv : fderiv ℝ (ι ∘ secondAffineSphere) z =
      imaginaryEuclidean.comp
        (fderiv ℝ (normalizedSpinorHopf ∘ secondAffineSpinorLift) z) := by
    rw [hfun]
    simpa only [ContinuousLinearMap.fderiv] using
      (fderiv_comp z imaginaryEuclidean.differentiableAt hdiff)
  have hv := congrArg (fun L : ℂ →L[ℝ] EuclideanThree => L w) hchain
  rw [mfderiv_eq_fderiv, hderiv] at hv
  simpa only [sphereTangentMap, ContinuousLinearMap.comp_apply,
    Function.comp_apply] using hv.symm

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem secondAffineSphere_horizontal_mfderiv
    (p : M) (y u : ℍ)
    (hy : y ∈ (extChartAt 𝓘(ℝ, ℍ) p).target) (z : ℂ) :
    sphereTangentMap (secondAffineSphere z)
      (mfderiv 𝓘(ℝ,ℂ) (𝓡 2) secondAffineSphere z
        (-(secondLocalConnectionGenerator Q D p y z u))) =
      -toEuclidean (inducedForm Q D p y u
        (hopfSphere ![z,1] (by simp)).1) := by
  rw [secondAffineSphere_tangent_fderiv]
  have hcomp := fderiv_comp z
    (by simpa [secondAffineSpinorLift] using
      normalizedSpinorHopf_differentiableAt ![z,1] (by simp))
    (secondAffineSpinorLift_hasFDerivAt z).differentiableAt
  have hv := congrArg (fun L : ℂ →L[ℝ] ℍ =>
    L (-(secondLocalConnectionGenerator Q D p y z u))) hcomp
  simp only [ContinuousLinearMap.comp_apply, secondAffineSpinorLift_fderiv] at hv
  rw [hv]
  change imaginaryEuclidean
    ((fderiv ℝ normalizedSpinorHopf ![z,1])
      ![-(secondLocalConnectionGenerator Q D p y z u),0]) = _
  rw [normalizedSpinorHopf_second_horizontal Q D p y u hy z,
    map_neg, imaginaryEuclidean_pureScalar]

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfSecondSphereDerivative
