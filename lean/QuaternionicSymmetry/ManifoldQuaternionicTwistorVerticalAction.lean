import QuaternionicSymmetry.ManifoldQuaternionicTwistorIsometryAction
import QuaternionicSymmetry.ManifoldQuaternionicIsometryOrientation
import QuaternionicSymmetry.ManifoldTwistorVerticalLine

/-! Naturality of the actual vertical tangent kernel under a differentiable
quaternionic-isometry lift. Smoothness of the derivative-defined lift is a
separate local-frame theorem; it is not assumed as part of the isometry
definition. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicTwistorVerticalAction

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometryCoefficients
open ManifoldQuaternionicIsometryOrientation
open ManifoldQuaternionicIntrinsicTwistorComparison
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldTwistorSphereCore
open ManifoldTwistorSphereBundle
open ManifoldTwistorSphereManifold
open ManifoldTwistorGlobalAlmostComplex
open ManifoldTwistorVerticalComplex
open ManifoldTwistorCoefficientSphere
open ManifoldQuaternionicConnection
open ManifoldQuaternionicMetric
open scoped Manifold ContDiff Matrix
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

private abbrev I := (𝓘(ℝ,E)).prod (𝓡 2)

/-- The derivative of a smooth lifted quaternionic isometry preserves the
vertical kernel of the genuine twistor projection. -/
theorem mfderiv_sphereTotalMap_mem_vertical
    (f : QuaternionicIsometries Q)
    (hf : ContMDiff (I (E := E)) (I (E := E)) ∞ (sphereTotalMap Q f))
    (z : SphereBundleTotal Q)
    (v : TangentSpace (I (E := E)) z)
    (hv : v ∈ verticalTangentSubmodule Q z) :
    mfderiv (I (E := E)) (I (E := E)) (sphereTotalMap Q f) z v ∈
      verticalTangentSubmodule Q (sphereTotalMap Q f z) := by
  rw [verticalTangentSubmodule_eq_projection_ker] at hv ⊢
  rw [LinearMap.mem_ker] at hv ⊢
  have hπ := sphereProjection_smooth Q
  have h₁ := mfderiv_comp z
    (hπ.contMDiffAt.mdifferentiableAt (by simp))
    (hf.contMDiffAt.mdifferentiableAt (by simp))
  have h₂ := mfderiv_comp z
    (f.1.contMDiff.mdifferentiable (by simp) z.1)
    (hπ.contMDiffAt.mdifferentiableAt (by simp))
  have hfun : (fun w : SphereBundleTotal Q => w.1) ∘ sphereTotalMap Q f =
      (f.1 : M → M) ∘ (fun w : SphereBundleTotal Q => w.1) := by
    funext w
    exact sphereTotalMap_base Q f w
  have hderiv := congrArg
    (fun F : SphereBundleTotal Q → M =>
      mfderiv (I (E := E)) 𝓘(ℝ,E) F z v) hfun
  change mfderiv (I (E := E)) 𝓘(ℝ,E)
      ((fun w : SphereBundleTotal Q => w.1) ∘ sphereTotalMap Q f) z v =
    mfderiv (I (E := E)) 𝓘(ℝ,E)
      ((f.1 : M → M) ∘ (fun w : SphereBundleTotal Q => w.1)) z v at hderiv
  rw [h₁, h₂] at hderiv
  change mfderiv (I (E := E)) 𝓘(ℝ,E)
    (fun w : SphereBundleTotal Q => w.1) (sphereTotalMap Q f z)
      (mfderiv (I (E := E)) (I (E := E)) (sphereTotalMap Q f) z v) = 0
  change mfderiv (I (E := E)) 𝓘(ℝ,E)
      (fun w : SphereBundleTotal Q => w.1) (sphereTotalMap Q f z)
        (mfderiv (I (E := E)) (I (E := E)) (sphereTotalMap Q f) z v) =
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f.1 : M → M) z.1
      (mfderiv (I (E := E)) 𝓘(ℝ,E)
        (fun w : SphereBundleTotal Q => w.1) z v) at hderiv
  change mfderiv (I (E := E)) 𝓘(ℝ,E)
    (fun w : SphereBundleTotal Q => w.1) z v = 0 at hv
  rw [hv, map_zero] at hderiv
  exact hderiv

/-- The chart identification of the actual vertical tangent line transports
its global complex structure to cross-product rotation on coefficients. -/
theorem verticalTangentEquiv_complex
    (D : CompatibleTangentConnection Q) (z : SphereBundleTotal Q)
    (v : verticalTangentSubmodule Q z) :
    verticalTangentEquiv Q z (verticalTangentComplex Q D z v) =
      verticalComplex (coefficientSphereHomeomorph.symm z.2)
        (verticalTangentEquiv Q z v) := by
  apply Subtype.ext
  have hv : (preferredTangentEquiv Q z v.1).1 = 0 :=
    (mem_verticalTangentSubmodule_iff Q z v.1).mp v.2
  change (preferredTangentEquiv Q z (tangentComplex Q D z v.1)).2 =
    (coefficientSphereHomeomorph.symm z.2).1 ⨯₃
      (preferredTangentEquiv Q z v.1).2.1
  simp [tangentComplex, ManifoldTwistorLocalAlmostComplex.localTwistorComplex,
    ManifoldTwistorLocalAlmostComplex.chartSplitComplex,
    ManifoldTwistorHorizontalConnection.connectionSplit, hv]
  rfl

/-- The preferred sphere coordinate of the lifted point is exactly the
derivative-induced SO(3) coefficient action. -/
theorem sphereTotalMap_coefficient
    (f : QuaternionicIsometries Q) (z : SphereBundleTotal Q) :
    coefficientSphereHomeomorph.symm (sphereTotalMap Q f z).2 =
      coefficientSphereAction Q f z.1 (coefficientSphereHomeomorph.symm z.2) := by
  have hz : toOriginalSphere Q z =
      preferredPoint Q z.1 (coefficientSphereHomeomorph.symm z.2) := rfl
  change coefficientSphereHomeomorph.symm
    (coefficientSphereHomeomorph
      (localCoordinate Q (Q.frames.adaptedCore.indexAt
        (projection Q (twistorMap Q f (toOriginalSphere Q z))))
        (twistorMap Q f (toOriginalSphere Q z))
        (Q.frames.adaptedCore.mem_baseSet_at _))) = _
  rw [coefficientSphereHomeomorph.symm_apply_apply, hz,
    twistorMap_preferredPoint]
  simpa only [preferredPoint, projection_pointOfLocal] using
    (localCoordinate_pointOfLocal Q (Q.frames.adaptedCore.indexAt (f • z.1))
      (f • z.1) (Q.frames.adaptedCore.mem_baseSet_at (f • z.1))
      (coefficientSphereAction Q f z.1 (coefficientSphereHomeomorph.symm z.2)))

/-- The derivative-induced coefficient map, with its codomain rewritten to
the preferred coefficient at the actual image twistor point. -/
def coefficientVerticalCastMap (f : QuaternionicIsometries Q)
    (z : SphereBundleTotal Q) :
    verticalSubmodule (coefficientSphereHomeomorph.symm z.2) →ₗ[ℝ]
      verticalSubmodule (coefficientSphereHomeomorph.symm
        (sphereTotalMap Q f z).2) :=
  (sphereTotalMap_coefficient Q f z).symm ▸
    coefficientVerticalAction Q f z.1
      (coefficientSphereHomeomorph.symm z.2)

/-- The vertical-line map obtained by transporting the genuine quaternionic
SO(3) coefficient action through the actual total-space tangent charts.
Identification with the ambient derivative is a further smoothness theorem. -/
def verticalLineAction (f : QuaternionicIsometries Q)
    (z : SphereBundleTotal Q) :
    verticalTangentSubmodule Q z →ₗ[ℝ]
      verticalTangentSubmodule Q (sphereTotalMap Q f z) :=
  (verticalTangentEquiv Q (sphereTotalMap Q f z)).symm.toLinearMap.comp
    ((coefficientVerticalCastMap Q f z).comp
      (verticalTangentEquiv Q z).toLinearMap)

end
end QuaternionicSymmetry.ManifoldQuaternionicTwistorVerticalAction
