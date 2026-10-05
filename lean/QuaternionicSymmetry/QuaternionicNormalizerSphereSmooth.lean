import QuaternionicSymmetry.QuaternionicNormalizerCrossCovariance
import QuaternionicSymmetry.ManifoldTwistorVerticalTangent

/-! The fixed-model normalizer's independently defined action on the
geometric Euclidean sphere is smooth. Its actual manifold differential is
the restriction of the linear coefficient rotation. -/

namespace QuaternionicSymmetry.QuaternionicNormalizerSphereSmooth

open scoped Manifold ContDiff
open QuaternionicIsometryNormalizer
  QuaternionicNormalizerRotationAxes
  FourDimensionalTwistorNormalizerQuotient
  ManifoldTwistorCoefficientSphere
  ManifoldTwistorVerticalComplex
  ManifoldTwistorSphereBundle

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  (S : QuaternionicStructure E)

local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

def euclideanRotation (g : normalizer S) :
    EuclideanThree →L[ℝ] EuclideanThree :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.comp
    ((rotationLinear S g).toContinuousLinearMap.comp
      (EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap)

def geometricAction (g : normalizer S) :
    geometricSphere → geometricSphere :=
  fun u => coefficientSphereHomeomorph
    (act S g (coefficientSphereHomeomorph.symm u))

theorem geometricAction_coe (g : normalizer S) (u : geometricSphere) :
    (geometricAction S g u : EuclideanThree) = euclideanRotation S g u.1 := rfl

theorem geometricAction_smooth (g : normalizer S) :
    ContMDiff (𝓡 2) (𝓡 2) ∞ (geometricAction S g) := by
  let R := euclideanRotation S g
  have hR : ContMDiff (𝓡 2) 𝓘(ℝ, EuclideanThree) ∞
      (fun u : geometricSphere => R u.1) :=
    R.contMDiff.comp contMDiff_coe_sphere
  have hsphere : ∀ u : geometricSphere,
      R u.1 ∈ Metric.sphere (0 : EuclideanThree) 1 := by
    intro u
    have hu := (mem_geometricSphere _).1 u.2
    apply (mem_geometricSphere _).2
    change squareNorm (rotationLinear S g
      (EuclideanSpace.equiv (Fin 3) ℝ u.1)) = 1
    rw [show squareNorm (rotationLinear S g
      (EuclideanSpace.equiv (Fin 3) ℝ u.1)) =
      squareNorm (EuclideanSpace.equiv (Fin 3) ℝ u.1) from
        rotation_dot S g _ _]
    simpa [EuclideanSpace.equiv] using hu
  exact (hR.codRestrict_sphere (n := 2) hsphere).congr (by
    intro u
    apply Subtype.ext
    exact (geometricAction_coe S g u).symm)

theorem sphereTangentMap_geometricAction
    (g : normalizer S) (u : geometricSphere)
    (v : TangentSpace (𝓡 2) u) :
    sphereTangentMap (geometricAction S g u)
      (mfderiv (𝓡 2) (𝓡 2) (geometricAction S g) u v) =
      euclideanRotation S g (sphereTangentMap u v) := by
  let R := euclideanRotation S g
  let a := geometricAction S g
  let ι : geometricSphere → EuclideanThree := Subtype.val
  have hfun : ι ∘ a = R ∘ ι := by
    funext w
    exact geometricAction_coe S g w
  have hderiv := congrArg
    (fun F : geometricSphere → EuclideanThree =>
      mfderiv (𝓡 2) 𝓘(ℝ, EuclideanThree) F u v) hfun
  have hιa : MDifferentiableAt (𝓡 2) 𝓘(ℝ, EuclideanThree) ι (a u) :=
    (contMDiff_coe_sphere (n := 2) (m := ∞)).mdifferentiableAt (by simp)
  have ha : MDifferentiableAt (𝓡 2) (𝓡 2) a u :=
    (geometricAction_smooth S g).mdifferentiableAt (by simp)
  have hRsmooth : ContMDiff 𝓘(ℝ, EuclideanThree)
      𝓘(ℝ, EuclideanThree) ∞ R := R.contMDiff
  have hR : MDifferentiableAt 𝓘(ℝ, EuclideanThree) 𝓘(ℝ, EuclideanThree)
      R (ι u) := hRsmooth.mdifferentiableAt (by simp)
  have hι : MDifferentiableAt (𝓡 2) 𝓘(ℝ, EuclideanThree) ι u :=
    (contMDiff_coe_sphere (n := 2) (m := ∞)).mdifferentiableAt (by simp)
  change mfderiv (𝓡 2) 𝓘(ℝ, EuclideanThree) (ι ∘ a) u v =
    mfderiv (𝓡 2) 𝓘(ℝ, EuclideanThree) (R ∘ ι) u v at hderiv
  rw [mfderiv_comp u hιa ha, mfderiv_comp u hR hι] at hderiv
  change sphereTangentMap (a u)
      (mfderiv (𝓡 2) (𝓡 2) a u v) =
    (mfderiv 𝓘(ℝ, EuclideanThree) 𝓘(ℝ, EuclideanThree) R (ι u))
      (sphereTangentMap u v) at hderiv
  simpa only [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv] using hderiv

end
end QuaternionicSymmetry.QuaternionicNormalizerSphereSmooth
