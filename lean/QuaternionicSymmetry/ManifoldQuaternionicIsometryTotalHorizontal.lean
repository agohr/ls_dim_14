import QuaternionicSymmetry.ManifoldQuaternionicIsometryHorizontalAction
import QuaternionicSymmetry.ManifoldQuaternionicTwistorVerticalDerivative
import QuaternionicSymmetry.ManifoldTwistorContactSplitting

/-! Transport of the rank-three horizontal distribution by the genuine
smooth isometry lift on the associated twistor sphere bundle. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicIsometryTotalHorizontal

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometryHorizontalAction
open ManifoldQuaternionicTwistorVerticalDerivative
open ManifoldQuaternionicTwistorLiftSmooth
open ManifoldQuaternionicConnectionIsometrySolder
open ManifoldQuaternionicLocalDerivativeEquivariance
open ManifoldTwistorCoefficientSphere
open ManifoldTwistorSphereCore
open ManifoldTwistorVerticalComplex
open ManifoldTwistorGlobalAlmostComplex
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

private abbrev J := (𝓘(ℝ,E)).prod (𝓡 2)
local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩
local instance (x : M) : ChartedSpace (EuclideanSpace ℝ (Fin 2))
    ((sphereCore Q).Fiber x) := by
  change ChartedSpace (EuclideanSpace ℝ (Fin 2)) geometricSphere
  infer_instance

/-- In centered source and target charts, the local raw derivative is the
actual manifold differential of the isometry. -/
  theorem localRawDerivative_center_eq_mfderiv
    (f : QuaternionicIsometries Q) (p : M) :
    localRawDerivative Q f p p =
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f.1 : M → M) p := by
  unfold localRawDerivative
  ext v
  simp only [ContinuousLinearMap.comp_apply]
  rw [(tangentBundleCore 𝓘(ℝ,E) M).coordChange_self
    (achart E (f • p)) (f • p) (mem_chart_source E (f • p))]
  change (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f.1 : M → M) p)
    (((tangentBundleCore 𝓘(ℝ,E) M).coordChange
      (achart E p) (achart E p) p) v) = _
  rw [(tangentBundleCore 𝓘(ℝ,E) M).coordChange_self
    (achart E p) p (mem_chart_source E p)]
  rfl

theorem localIsometryChartMap_fderiv_center_eq_mfderiv
    (f : QuaternionicIsometries Q) (p : M) :
    fderiv ℝ (localIsometryChartMap Q f p)
      (extChartAt 𝓘(ℝ,E) p p) =
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f.1 : M → M) p := by
  rw [localIsometryChartMap_fderiv Q f p p
    (mem_chart_source E p) (mem_chart_source E (f • p)),
    localRawDerivative_center_eq_mfderiv]

theorem localIsometryChartMap_center
    (f : QuaternionicIsometries Q) (p : M) :
    localIsometryChartMap Q f p (extChartAt 𝓘(ℝ,E) p p) =
      extChartAt 𝓘(ℝ,E) (f • p) (f • p) := by
  simp only [localIsometryChartMap,
    (extChartAt 𝓘(ℝ,E) p).left_inv (mem_extChartAt_source p)]

/-- The pointwise total-sphere differential has the actual base isometry
derivative as its first block and the joint sphere-action differential as
its second block. -/
theorem sphereTotalMap_mfderiv_blocks
    (f : QuaternionicIsometries Q) (z : SphereBundleTotal Q)
    (v : E) (w : TangentSpace (𝓡 2) z.2) :
    mfderiv (J (E := E)) (J (E := E))
      (ManifoldQuaternionicTwistorIsometryAction.sphereTotalMap Q f)
      z (v,w) =
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f.1 : M → M) z.1 v,
        mfderiv (J (E := E)) (𝓡 2)
          (ManifoldQuaternionicLocalSphereActionSmooth.localSphereAction Q f z.1)
          (z.1,z.2) (v,w)) := by
  rw [sphereTotalMap_mfderiv_eq_local Q f z]
  have hb : MDifferentiableAt (J (E := E)) 𝓘(ℝ,E)
      (fun q : M × geometricSphere => f • q.1) (z.1,z.2) :=
    (f.1.contMDiff.contMDiffAt.comp (z.1,z.2) contMDiffAt_fst).mdifferentiableAt
      (by simp)
  have hs : MDifferentiableAt (J (E := E)) (𝓡 2)
      (ManifoldQuaternionicLocalSphereActionSmooth.localSphereAction Q f z.1)
      (z.1,z.2) :=
    (ManifoldQuaternionicLocalSphereActionSmooth.localSphereAction_smoothAt_center
      Q f z.1 z.2).mdifferentiableAt (by simp)
  change mfderiv (J (E := E)) (J (E := E))
      (fun q : M × geometricSphere =>
        (f • q.1,
          ManifoldQuaternionicLocalSphereActionSmooth.localSphereAction Q f z.1 q))
      (z.1,z.2) (v,w) = _
  rw [mfderiv_prodMk hb hs]
  have hf : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E)
      (f.1 : M → M) z.1 := f.1.contMDiff.mdifferentiable (by simp) z.1
  have hfst : MDifferentiableAt (J (E := E)) 𝓘(ℝ,E)
      (Prod.fst : M × geometricSphere → M) (z.1,z.2) :=
    mdifferentiableAt_fst
  have hcomp := mfderiv_comp (z.1,z.2) hf hfst
  change mfderiv (J (E := E)) 𝓘(ℝ,E)
      (fun q : M × geometricSphere => f • q.1) (z.1,z.2) = _ at hcomp
  rw [hcomp, mfderiv_fst]
  rfl

/-- Membership in the actual horizontal tangent plane, stated in the
ambient quaternionic coefficient coordinates of the genuine sphere tangent. -/
theorem mem_horizontal_iff_coefficient
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    (z : SphereBundleTotal Q) (t : TangentSpace (J (E := E)) z) :
    t ∈ horizontalTangentSubmodule Q D z ↔
      EuclideanSpace.equiv (Fin 3) ℝ (sphereTangentMap z.2 t.2) =
        -(ManifoldQuaternionicAdjointConnection.inducedForm Q D z.1
          (extChartAt 𝓘(ℝ,E) z.1 z.1) t.1
          (ManifoldQuaternionicIsometrySphereDerivative.sphereCoefficients z.2)) := by
  rw [mem_horizontalTangentSubmodule_iff]
  constructor
  · intro h
    have hv := congrArg Subtype.val h
    change EuclideanSpace.equiv (Fin 3) ℝ (sphereTangentMap z.2 t.2) +
      ManifoldQuaternionicAdjointConnection.inducedForm Q D z.1
        (extChartAt 𝓘(ℝ,E) z.1 z.1) t.1
        (ManifoldQuaternionicIsometrySphereDerivative.sphereCoefficients z.2) = 0 at hv
    exact (add_eq_zero_iff_eq_neg).mp hv
  · intro h
    apply Subtype.ext
    change EuclideanSpace.equiv (Fin 3) ℝ (sphereTangentMap z.2 t.2) +
      ManifoldQuaternionicAdjointConnection.inducedForm Q D z.1
        (extChartAt 𝓘(ℝ,E) z.1 z.1) t.1
        (ManifoldQuaternionicIsometrySphereDerivative.sphereCoefficients z.2) = 0
    exact (add_eq_zero_iff_eq_neg).mpr h

/-- The smooth derivative-induced isometry lift preserves the actual
horizontal tangent submodule of the compatible Levi-Civita connection. -/
theorem sphereTotalMap_maps_horizontal
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    (f : QuaternionicIsometries Q) (z : SphereBundleTotal Q)
    (t : TangentSpace (J (E := E)) z)
    (ht : t ∈ horizontalTangentSubmodule Q D z) :
    (mfderiv (J (E := E)) (J (E := E))
      (ManifoldQuaternionicTwistorIsometryAction.sphereTotalMap Q f) z t) ∈
      horizontalTangentSubmodule Q D
        (ManifoldQuaternionicTwistorIsometryAction.sphereTotalMap Q f z) := by
  have hsrc := (mem_horizontal_iff_coefficient Q D z t).mp ht
  have hhor := localSphereAction_horizontal_mfderiv_center Q D f z.1 z.2
    t.1 t.2 hsrc
  have hbase := localIsometryChartMap_fderiv_center_eq_mfderiv Q f z.1
  have hcenter := localIsometryChartMap_center Q f z.1
  have hfiber := localSphereAction_fixedFiber Q f z.1 z.2
  have hpoint := sphereTotalMap_fiber Q f z
  have hpointBase := ManifoldQuaternionicTwistorIsometryAction.sphereTotalMap_base Q f z
  rw [mem_horizontal_iff_coefficient]
  have hblocks := sphereTotalMap_mfderiv_blocks Q f z t.1 t.2
  change mfderiv (J (E := E)) (J (E := E))
      (ManifoldQuaternionicTwistorIsometryAction.sphereTotalMap Q f)
      z t = _ at hblocks
  rw [hblocks, hpointBase, hpoint]
  rw [← hfiber]
  simpa only [hcenter, hbase] using hhor

end
end QuaternionicSymmetry.ManifoldQuaternionicIsometryTotalHorizontal
