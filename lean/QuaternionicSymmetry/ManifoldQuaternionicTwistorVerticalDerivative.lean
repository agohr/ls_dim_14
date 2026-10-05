import QuaternionicSymmetry.ManifoldQuaternionicTwistorLiftSmooth
import QuaternionicSymmetry.ManifoldQuaternionicTwistorVerticalAction
import QuaternionicSymmetry.ManifoldQuaternionicIsometryFiberSmooth
import QuaternionicSymmetry.ManifoldQuaternionicLocalCoefficientComparison
import QuaternionicSymmetry.ManifoldTwistorPreferredChartDerivative

/-! The actual smooth derivative-induced lift acts on genuine vertical tangent
planes, without any extra smoothness premise. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicTwistorVerticalDerivative

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicTwistorLiftSmooth
open ManifoldQuaternionicTwistorVerticalAction
open ManifoldQuaternionicIsometryFiberSmooth
open ManifoldQuaternionicLocalCoefficientComparison
open ManifoldQuaternionicLocalSphereActionSmooth
open ManifoldTwistorSphereCore
open ManifoldTwistorCoefficientSphere
open ManifoldTwistorGlobalAlmostComplex
open ManifoldTwistorVerticalComplex
open ManifoldQuaternionicIsometryCoefficients
open ManifoldTwistorGlobalAlmostComplex
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

private abbrev J := (𝓘(ℝ,E)).prod (𝓡 2)

local instance (x : M) : ChartedSpace (EuclideanSpace ℝ (Fin 2))
    ((sphereCore Q).Fiber x) := by
  change ChartedSpace (EuclideanSpace ℝ (Fin 2)) geometricSphere
  infer_instance

/-- On a fixed base fiber, the smooth total-chart formula reduces exactly to
the independently constructed geometric sphere action. -/
theorem localSphereAction_fixedFiber
    (f : QuaternionicIsometries Q) (p : M) (u : geometricSphere) :
    localSphereAction Q f p (p,u) = geometricFiberAction Q f p u := by
  apply Subtype.ext
  change localSphereAmbient Q f p (p,u) =
    (geometricFiberAction Q f p u : EuclideanThree)
  rw [localSphereAmbient, if_pos
    (show p ∈ (chartAt E p).source ∧
      f • p ∈ (chartAt E (f • p)).source from
      ⟨mem_chart_source E p, mem_chart_source E (f • p)⟩)]
  rw [localCoefficientRotation_center Q f p]
  rfl

/-- The derivative of the local total action in a pure fiber direction is
the derivative of the actual fixed-fiber geometric sphere action. -/
theorem localProductAction_vertical_mfderiv
    (f : QuaternionicIsometries Q) (p : M)
    (u : geometricSphere) (v : TangentSpace (𝓡 2) u) :
    mfderiv (J (E := E)) (J (E := E))
      (ManifoldQuaternionicTwistorLiftSmooth.localProductAction Q f p)
      (p,u) (0,v) =
        (0, mfderiv (𝓡 2) (𝓡 2)
          (geometricFiberAction Q f p) u v) := by
  let S : geometricSphere → M × geometricSphere := fun t => (p,t)
  let F := ManifoldQuaternionicTwistorLiftSmooth.localProductAction Q f p
  let G : geometricSphere → M × geometricSphere :=
    fun t => (f • p, geometricFiberAction Q f p t)
  have hfun : F ∘ S = G := by
    funext t
    apply Prod.ext
    · rfl
    · exact localSphereAction_fixedFiber Q f p t
  have hS : MDifferentiableAt (𝓡 2) (J (E := E)) S u :=
    mdifferentiableAt_const.prodMk mdifferentiableAt_id
  have hF : MDifferentiableAt (J (E := E)) (J (E := E)) F (S u) :=
    (ManifoldQuaternionicTwistorLiftSmooth.localProductAction_smoothAt_center
      Q f p u).mdifferentiableAt (by simp)
  have hG : MDifferentiableAt (𝓡 2) (𝓡 2)
      (geometricFiberAction Q f p) u :=
    (geometricFiberAction_smooth Q f p).mdifferentiable (by simp) u
  have hd := congrArg
    (fun H : geometricSphere → M × geometricSphere =>
      mfderiv (𝓡 2) (J (E := E)) H u v) hfun
  change mfderiv (𝓡 2) (J (E := E)) (F ∘ S) u v =
    mfderiv (𝓡 2) (J (E := E)) G u v at hd
  rw [mfderiv_comp u hF hS] at hd
  have hSd : mfderiv (𝓡 2) (J (E := E)) S u v = (0,v) := by
    rw [show S = (fun t : geometricSphere => (p,t)) from rfl,
      mfderiv_prod_right]
    rfl
  change (mfderiv (J (E := E)) (J (E := E)) F (S u))
      ((mfderiv (𝓡 2) (J (E := E)) S u) v) =
    (mfderiv (𝓡 2) (J (E := E)) G u) v at hd
  rw [hSd] at hd
  have hGd : mfderiv (𝓡 2) (J (E := E)) G u v =
      (0, mfderiv (𝓡 2) (𝓡 2)
        (geometricFiberAction Q f p) u v) := by
    rw [show G = (fun t : geometricSphere =>
        (f • p, geometricFiberAction Q f p t)) from rfl,
      mfderiv_prodMk mdifferentiableAt_const hG, mfderiv_const]
    rfl
  exact hd.trans hGd

/-- The actual lifted point's preferred geometric-sphere coordinate agrees
with the fixed-fiber SO(3) action. -/
theorem sphereTotalMap_fiber
    (f : QuaternionicIsometries Q) (z : SphereBundleTotal Q) :
    (sphereTotalMap Q f z).2 = geometricFiberAction Q f z.1 z.2 := by
  apply coefficientSphereHomeomorph.symm.injective
  exact sphereTotalMap_coefficient Q f z

/-- The genuine sphere-fiber differential has exactly the SO(3) weight of
derivative conjugation on quaternionic coefficients. -/
theorem sphereFiber_mfderiv_coefficient
    (f : QuaternionicIsometries Q) (p : M)
    (u : geometricSphere) (v : TangentSpace (𝓡 2) u) :
    EuclideanSpace.equiv (Fin 3) ℝ
      (sphereTangentMap (geometricFiberAction Q f p u)
        (mfderiv (𝓡 2) (𝓡 2) (geometricFiberAction Q f p) u v)) =
      coefficientAction Q f p
        (EuclideanSpace.equiv (Fin 3) ℝ (sphereTangentMap u v)) := by
  rw [sphereTangentMap_geometricFiberAction]
  rfl

/-- In the preferred product tangent charts at source and target, the
derivative of the actual total-space lift is the derivative of its smooth
fixed-chart formula. -/
theorem sphereTotalMap_mfderiv_eq_local
    (f : QuaternionicIsometries Q) (z : SphereBundleTotal Q) :
    mfderiv (J (E := E)) (J (E := E)) (sphereTotalMap Q f) z =
      mfderiv (J (E := E)) (J (E := E))
        (ManifoldQuaternionicTwistorLiftSmooth.localProductAction Q f z.1)
        (z.1,z.2) := by
  let p := z.1
  let w := sphereTotalMap Q f z
  let C := chartAt (M × geometricSphere) z
  let D := chartAt (M × geometricSphere) w
  let F := ManifoldQuaternionicTwistorLiftSmooth.localProductAction Q f p
  have hC : MDifferentiableAt (J (E := E)) (J (E := E))
      (C : SphereBundleTotal Q → M × geometricSphere) z :=
    (ManifoldQuaternionicSphereChartSmooth.preferredLocalTriv_smoothAt Q z).mdifferentiableAt
      (by simp)
  have hD : MDifferentiableAt (J (E := E)) (J (E := E))
      (D : SphereBundleTotal Q → M × geometricSphere) w :=
    (ManifoldQuaternionicSphereChartSmooth.preferredLocalTriv_smoothAt Q w).mdifferentiableAt
      (by simp)
  have hF : MDifferentiableAt (J (E := E)) (J (E := E)) F (C z) := by
    change MDifferentiableAt (J (E := E)) (J (E := E)) F
      (p,(C z).2)
    exact (ManifoldQuaternionicTwistorLiftSmooth.localProductAction_smoothAt_center
      Q f p (C z).2).mdifferentiableAt (by simp)
  have hLift : MDifferentiableAt (J (E := E)) (J (E := E))
      (sphereTotalMap Q f) z :=
    (sphereTotalMap_contMDiff Q f).mdifferentiable (by simp) z
  have hbase : Continuous (fun y : SphereBundleTotal Q => y.1) :=
    (ManifoldTwistorSphereManifold.sphereProjection_smooth Q).continuous
  have hf : Continuous (f.1 : M → M) := f.1.contMDiff.continuous
  have h₁ : ∀ᶠ y in nhds z, y.1 ∈ (chartAt E p).source :=
    (((chartAt E p).open_source).preimage hbase).mem_nhds
      (mem_chart_source E p)
  have h₂ : ∀ᶠ y in nhds z,
      f • y.1 ∈ (chartAt E (f • p)).source :=
    (((chartAt E (f • p)).open_source).preimage (hf.comp hbase)).mem_nhds
      (mem_chart_source E (f • p))
  have heq : (fun y : SphereBundleTotal Q => D (sphereTotalMap Q f y)) =ᶠ[nhds z]
      (fun y => F (C y)) := by
    filter_upwards [h₁, h₂] with y hy₁ hy₂
    exact (ManifoldQuaternionicTwistorLiftSmooth.localProductAction_eq_chart
      Q f p y hy₁ hy₂).symm
  have hd := heq.mfderiv_eq (I := J (E := E)) (I' := J (E := E))
  change mfderiv (J (E := E)) (J (E := E))
      (D ∘ sphereTotalMap Q f) z =
    mfderiv (J (E := E)) (J (E := E)) (F ∘ C) z at hd
  rw [mfderiv_comp z hD hLift, mfderiv_comp z hF hC] at hd
  have hdC : mfderiv (J (E := E)) (J (E := E))
      (C : SphereBundleTotal Q → M × geometricSphere) z =
        ContinuousLinearMap.id ℝ _ := preferredTriv_mfderiv Q z
  have hdD : mfderiv (J (E := E)) (J (E := E))
      (D : SphereBundleTotal Q → M × geometricSphere) w =
        ContinuousLinearMap.id ℝ _ := preferredTriv_mfderiv Q w
  have hDw : D w = (w.1,w.2) := by
    apply Prod.ext
    · rfl
    · change ((sphereCore Q).localTriv (achart E w.1) w).2 = w.2
      rw [(sphereCore Q).localTriv_apply]
      exact euclideanSphereCoordChange_self Q (achart E w.1) w.1
        (mem_chart_source E w.1) w.2
  rw [hdC, hdD] at hd
  rw [hDw] at hd
  simp only [ContinuousLinearMap.comp_id] at hd
  have hCz : C z = (p,z.2) := by
    apply Prod.ext
    · rfl
    · change ((sphereCore Q).localTriv (achart E p) z).2 = z.2
      rw [(sphereCore Q).localTriv_apply]
      exact euclideanSphereCoordChange_self Q (achart E p) p
        (mem_chart_source E p) z.2
  apply ContinuousLinearMap.ext
  intro v
  have hdv := congrArg
    (fun L : TangentSpace (J (E := E)) z →L[ℝ]
        TangentSpace (J (E := E)) w => L v) hd
  change (mfderiv (J (E := E)) (J (E := E))
      (sphereTotalMap Q f) z) v =
    (mfderiv (J (E := E)) (J (E := E)) F (C z)) v at hdv
  rw [hCz] at hdv
  exact hdv

/-- The actual derivative in a pure sphere-fiber direction is the fixed-fiber
sphere differential, in the preferred tangent coordinates. -/
theorem sphereTotalMap_vertical_mfderiv_snd
    (f : QuaternionicIsometries Q) (z : SphereBundleTotal Q)
    (v : TangentSpace (𝓡 2) (z.2 : geometricSphere)) :
    (mfderiv (J (E := E)) (J (E := E))
      (sphereTotalMap Q f) z (0,v)).2 =
        mfderiv (𝓡 2) (𝓡 2)
          (geometricFiberAction Q f z.1) (z.2 : geometricSphere) v := by
  rw [sphereTotalMap_mfderiv_eq_local Q f z]
  exact congrArg Prod.snd
    (localProductAction_vertical_mfderiv Q f z.1 z.2 v)

/-- The derivative of every actual lifted isometry preserves the genuine
vertical tangent plane of the sphere-bundle projection. -/
theorem mfderiv_sphereTotalMap_mem_vertical
    (f : QuaternionicIsometries Q) (z : SphereBundleTotal Q)
    (v : TangentSpace (J (E := E)) z)
    (hv : v ∈ verticalTangentSubmodule Q z) :
    mfderiv (J (E := E)) (J (E := E)) (sphereTotalMap Q f) z v ∈
      verticalTangentSubmodule Q (sphereTotalMap Q f z) :=
  ManifoldQuaternionicTwistorVerticalAction.mfderiv_sphereTotalMap_mem_vertical
    Q f (sphereTotalMap_contMDiff Q f) z v hv

/-- The genuine vertical tangent derivative has the exact quaternionic
coefficient SO(3) weight, expressed as equality of finite coordinate
vectors so no dependent fiber transport appears in the conclusion. -/
theorem vertical_mfderiv_coefficient
    (f : QuaternionicIsometries Q) (z : SphereBundleTotal Q)
    (v : verticalTangentSubmodule Q z) :
    ((verticalTangentEquiv Q (sphereTotalMap Q f z))
      ⟨mfderiv (J (E := E)) (J (E := E))
        (sphereTotalMap Q f) z v.1,
        mfderiv_sphereTotalMap_mem_vertical Q f z v.1 v.2⟩).1 =
      coefficientAction Q f z.1 ((verticalTangentEquiv Q z v).1) := by
  have hv0 : v.1.1 = 0 :=
    (mem_verticalTangentSubmodule_iff Q z v.1).mp v.2
  have hv : v.1 = (0,v.1.2) := Prod.ext hv0 rfl
  change EuclideanSpace.equiv (Fin 3) ℝ
      (sphereTangentMap (sphereTotalMap Q f z).2
        (mfderiv (J (E := E)) (J (E := E))
          (sphereTotalMap Q f) z v.1).2) =
    coefficientAction Q f z.1
      (EuclideanSpace.equiv (Fin 3) ℝ (sphereTangentMap z.2 v.1.2))
  rw [hv]
  rw [sphereTotalMap_vertical_mfderiv_snd Q f z v.1.2]
  rw [sphereTotalMap_fiber Q f z]
  exact sphereFiber_mfderiv_coefficient Q f z.1 z.2 v.1.2

end
end QuaternionicSymmetry.ManifoldQuaternionicTwistorVerticalDerivative
