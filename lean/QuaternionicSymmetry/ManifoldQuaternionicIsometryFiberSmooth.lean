import QuaternionicSymmetry.ManifoldQuaternionicIsometryOrientation
import QuaternionicSymmetry.ManifoldTwistorCoefficientSphere
import QuaternionicSymmetry.ManifoldTwistorVerticalTangent

/-! Smoothness of the genuine derivative-induced quaternionic-isometry action
on each individual geometric twistor two-sphere. The base-dependent total
space lift requires a separate fixed-chart theorem. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicIsometryFiberSmooth

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometryCoefficients
open ManifoldTwistorSphereBundle
open ManifoldTwistorCoefficientSphere
open ManifoldTwistorVerticalComplex
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

/-- The coefficient rotation as a bounded linear map on Euclidean 3-space. -/
def euclideanCoefficientAction (f : QuaternionicIsometries Q) (x : M) :
    EuclideanThree →L[ℝ] EuclideanThree :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.comp
    ((coefficientAction Q f x).toContinuousLinearMap.comp
      (EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap)

theorem euclideanCoefficientAction_apply (f : QuaternionicIsometries Q)
    (x : M) (u : EuclideanThree) :
    euclideanCoefficientAction Q f x u =
      toEuclidean (coefficientAction Q f x
        (EuclideanSpace.equiv (Fin 3) ℝ u)) := rfl

theorem euclideanCoefficientAction_sphere (f : QuaternionicIsometries Q)
    (x : M) (u : geometricSphere) :
    euclideanCoefficientAction Q f x u.1 ∈
      Metric.sphere (0 : EuclideanThree) 1 := by
  rw [euclideanCoefficientAction_apply]
  apply (mem_geometricSphere _).2
  rw [coefficientAction_squareNorm]
  exact (mem_geometricSphere _).1 u.2

/-- Actual fixed-base action of a quaternionic isometry on the smooth
geometric two-sphere representing that twistor fiber. -/
def geometricFiberAction (f : QuaternionicIsometries Q) (x : M) :
    geometricSphere → geometricSphere :=
  fun u => coefficientSphereHomeomorph
    (coefficientSphereAction Q f x (coefficientSphereHomeomorph.symm u))

theorem geometricFiberAction_smooth (f : QuaternionicIsometries Q)
    (x : M) :
    ContMDiff (𝓡 2) (𝓡 2) ∞ (geometricFiberAction Q f x) := by
  let R := euclideanCoefficientAction Q f x
  have hR : ContMDiff (𝓡 2) 𝓘(ℝ, EuclideanThree) ∞
      (fun u : geometricSphere => R u.1) :=
    R.contMDiff.comp contMDiff_coe_sphere
  have hsphere : ∀ u : geometricSphere,
      R u.1 ∈ Metric.sphere (0 : EuclideanThree) 1 :=
    euclideanCoefficientAction_sphere Q f x
  have h := hR.codRestrict_sphere (n := 2) hsphere
  exact h.congr (by
    intro u
    apply Subtype.ext
    rfl)

/-- The actual sphere differential is the restriction of the Euclidean
coefficient rotation to the tangent plane. -/
theorem sphereTangentMap_geometricFiberAction
    (f : QuaternionicIsometries Q) (x : M)
    (u : geometricSphere) (v : TangentSpace (𝓡 2) u) :
    sphereTangentMap (geometricFiberAction Q f x u)
      (mfderiv (𝓡 2) (𝓡 2) (geometricFiberAction Q f x) u v) =
        euclideanCoefficientAction Q f x (sphereTangentMap u v) := by
  let R := euclideanCoefficientAction Q f x
  let g := geometricFiberAction Q f x
  let ι : geometricSphere → EuclideanThree := Subtype.val
  have hfun : ι ∘ g = R ∘ ι := by
    funext w
    rfl
  have hderiv := congrArg
    (fun F : geometricSphere → EuclideanThree =>
      mfderiv (𝓡 2) 𝓘(ℝ,EuclideanThree) F u v) hfun
  change mfderiv (𝓡 2) 𝓘(ℝ,EuclideanThree) (ι ∘ g) u v =
    mfderiv (𝓡 2) 𝓘(ℝ,EuclideanThree) (R ∘ ι) u v at hderiv
  have hιg : MDifferentiableAt (𝓡 2) 𝓘(ℝ,EuclideanThree) ι (g u) :=
    (contMDiff_coe_sphere (n := 2) (m := ∞)).mdifferentiable
      (by simp) (g u)
  have hg : MDifferentiableAt (𝓡 2) (𝓡 2) g u :=
    (geometricFiberAction_smooth Q f x).mdifferentiable (by simp) u
  have hRsmooth : ContMDiff 𝓘(ℝ,EuclideanThree) 𝓘(ℝ,EuclideanThree)
      ∞ R := R.contMDiff
  have hR : MDifferentiableAt 𝓘(ℝ,EuclideanThree) 𝓘(ℝ,EuclideanThree)
      R (ι u) := hRsmooth.mdifferentiable (by simp) (ι u)
  have hι : MDifferentiableAt (𝓡 2) 𝓘(ℝ,EuclideanThree) ι u :=
    (contMDiff_coe_sphere (n := 2) (m := ∞)).mdifferentiable
      (by simp) u
  rw [mfderiv_comp u hιg hg, mfderiv_comp u hR hι] at hderiv
  change sphereTangentMap (g u)
      (mfderiv (𝓡 2) (𝓡 2) g u v) =
    (mfderiv 𝓘(ℝ,EuclideanThree) 𝓘(ℝ,EuclideanThree) R (ι u))
      (sphereTangentMap u v) at hderiv
  simpa only [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv] using hderiv

end
end QuaternionicSymmetry.ManifoldQuaternionicIsometryFiberSmooth
