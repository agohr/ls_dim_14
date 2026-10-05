import QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorSphereSmooth
import QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorOrientation
import QuaternionicSymmetry.ManifoldTwistorVerticalTangent

/-! The literal base-fiber preferred-coordinate sphere rotation has a
complex-linear manifold derivative for the actual vertical twistor complex
structure. This uses its checked cross-product law, not an orientation
premise. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorVerticalComplex

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorStrongBaseTwistorCoordinateLinear
open CompactSymplecticProjectorStrongBaseTwistorSphereSmooth
open CompactSymplecticProjectorStrongBaseTwistorOrientation
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldTwistorCoefficientSphere
open ManifoldTwistorSphereBundle
open ManifoldTwistorVerticalComplex
open scoped Quaternion Matrix Matrix.Norms.Operator Manifold ContDiff

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

theorem sphereTangentMap_preferredBaseSphereMap
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) [NeZero q] (u : geometricSphere)
    (v : TangentSpace (𝓡 2) u) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    sphereTangentMap (preferredBaseGeometricSphereMap hLee hDesc hImm n d e q g a hq hn u)
      (mfderiv (𝓡 2) (𝓡 2)
        (preferredBaseGeometricSphereMap hLee hDesc hImm n d e q g a hq hn) u v) =
      preferredBaseGeometricLinear hLee hDesc hImm n d e q g a hq hn
        (sphereTangentMap u v) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  let R := (preferredBaseGeometricLinear hLee hDesc hImm n d e q g a hq hn).toContinuousLinearMap
  let f := preferredBaseGeometricSphereMap hLee hDesc hImm n d e q g a hq hn
  let ι : geometricSphere → EuclideanThree := Subtype.val
  have hfun : ι ∘ f = R ∘ ι := rfl
  have hd := congrArg
    (fun F : geometricSphere → EuclideanThree =>
      mfderiv (𝓡 2) 𝓘(ℝ, EuclideanThree) F u v) hfun
  have hιf : MDifferentiableAt (𝓡 2) 𝓘(ℝ, EuclideanThree) ι (f u) :=
    (contMDiff_coe_sphere (n := 2) (m := ∞)).mdifferentiableAt (by simp)
  have hf : MDifferentiableAt (𝓡 2) (𝓡 2) f u :=
    (preferredBaseGeometricSphereMap_smooth hLee hDesc hImm n d e q g a hq hn)
      |>.mdifferentiableAt (by simp)
  have hRsmooth : ContMDiff 𝓘(ℝ, EuclideanThree)
      𝓘(ℝ, EuclideanThree) ∞ R := R.contMDiff
  have hR : MDifferentiableAt 𝓘(ℝ, EuclideanThree) 𝓘(ℝ, EuclideanThree)
      R (ι u) := hRsmooth.mdifferentiableAt (by simp)
  have hι : MDifferentiableAt (𝓡 2) 𝓘(ℝ, EuclideanThree) ι u :=
    (contMDiff_coe_sphere (n := 2) (m := ∞)).mdifferentiableAt (by simp)
  change mfderiv (𝓡 2) 𝓘(ℝ, EuclideanThree) (ι ∘ f) u v =
    mfderiv (𝓡 2) 𝓘(ℝ, EuclideanThree) (R ∘ ι) u v at hd
  rw [mfderiv_comp u hιf hf, mfderiv_comp u hR hι] at hd
  change sphereTangentMap (f u) (mfderiv (𝓡 2) (𝓡 2) f u v) =
    (mfderiv 𝓘(ℝ, EuclideanThree) 𝓘(ℝ, EuclideanThree) R (ι u))
      (sphereTangentMap u v) at hd
  simpa only [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv] using hd

theorem sphereVerticalCoefficient_preferredBaseSphereMap
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) [NeZero q] (z : coefficientSphere)
    (v : TangentSpace (𝓡 2) (coefficientSphereHomeomorph z)) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    let f := preferredBaseGeometricSphereMap hLee hDesc hImm n d e q g a hq hn
    let b := coefficientSphereHomeomorph.symm (f (coefficientSphereHomeomorph z))
    ((sphereTangentVerticalEquiv b)
      (mfderiv (𝓡 2) (𝓡 2) f (coefficientSphereHomeomorph z) v)).1 =
      preferredBaseCoefficientLinear hLee hDesc hImm n d e q g a hq hn
        ((sphereTangentVerticalEquiv z v).1) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  let f := preferredBaseGeometricSphereMap hLee hDesc hImm n d e q g a hq hn
  let b := coefficientSphereHomeomorph.symm (f (coefficientSphereHomeomorph z))
  change (EuclideanSpace.equiv (Fin 3) ℝ)
      (sphereTangentMap (f (coefficientSphereHomeomorph z))
        (mfderiv (𝓡 2) (𝓡 2) f (coefficientSphereHomeomorph z) v)) =
    preferredBaseCoefficientLinear hLee hDesc hImm n d e q g a hq hn
      ((EuclideanSpace.equiv (Fin 3) ℝ)
        (sphereTangentMap (coefficientSphereHomeomorph z) v))
  rw [sphereTangentMap_preferredBaseSphereMap]
  rfl

private theorem tangentVerticalEquiv_complex (z : coefficientSphere)
    (v : TangentSpace (𝓡 2) (coefficientSphereHomeomorph z)) :
    sphereTangentVerticalEquiv z (sphereVerticalComplex z v) =
      verticalComplex z (sphereTangentVerticalEquiv z v) := by
  simp [sphereVerticalComplex]

/-- The actual preferred-coordinate change on the base twistor sphere has
a complex-linear vertical manifold derivative. -/
theorem preferredBaseSphereMap_mfderiv_complex
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) [NeZero q] (z : coefficientSphere)
    (v : TangentSpace (𝓡 2) (coefficientSphereHomeomorph z)) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    let f := preferredBaseGeometricSphereMap hLee hDesc hImm n d e q g a hq hn
    let b := coefficientSphereHomeomorph.symm (f (coefficientSphereHomeomorph z))
    mfderiv (𝓡 2) (𝓡 2) f (coefficientSphereHomeomorph z)
      (sphereVerticalComplex z v) =
      sphereVerticalComplex b
        (mfderiv (𝓡 2) (𝓡 2) f (coefficientSphereHomeomorph z) v) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  let f := preferredBaseGeometricSphereMap hLee hDesc hImm n d e q g a hq hn
  let b := coefficientSphereHomeomorph.symm (f (coefficientSphereHomeomorph z))
  let P := preferredBaseCoefficientLinear hLee hDesc hImm n d e q g a hq hn
  apply (sphereTangentVerticalEquiv b).injective
  apply Subtype.ext
  rw [sphereVerticalCoefficient_preferredBaseSphereMap hLee hDesc hImm
    n d e q g a hq hn z (sphereVerticalComplex z v),
    tangentVerticalEquiv_complex z,
    tangentVerticalEquiv_complex b]
  change P (z.1 ⨯₃ (sphereTangentVerticalEquiv z v).1) =
    b.1 ⨯₃
      (sphereTangentVerticalEquiv b
        (mfderiv (𝓡 2) (𝓡 2) f (coefficientSphereHomeomorph z) v)).1
  rw [sphereVerticalCoefficient_preferredBaseSphereMap hLee hDesc hImm
    n d e q g a hq hn z v]
  have hb : b.1 = P z.1 := rfl
  rw [hb]
  exact preferredBaseCoefficientLinear_cross hLee hDesc hImm
    n d e q g a hq hn z.1 (sphereTangentVerticalEquiv z v).1

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorVerticalComplex
