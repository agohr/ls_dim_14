import QuaternionicSymmetry.ManifoldQuaternionicSphereSmoothAt
import QuaternionicSymmetry.ManifoldQuaternionicLocalDerivativeEquivariance
import QuaternionicSymmetry.ManifoldQuaternionicTwistorLocalAction

/-! Local smooth sphere coordinate of the actual derivative-induced twistor
action. Outside the fixed-chart overlap it is extended by the identity. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicLocalSphereActionSmooth

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometryLocalDerivative
open ManifoldQuaternionicLocalDerivativeEquivariance
open ManifoldQuaternionicSphereSmoothAt
open ManifoldQuaternionicTwistorLocalAction
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldTwistorSphereBundle
open ManifoldTwistorCoefficientSphere
open ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

private abbrev J := (𝓘(ℝ,E)).prod (𝓡 2)
local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

/-- A globally sphere-valued extension of the actual fixed-chart formula. -/
def localSphereAmbient (f : QuaternionicIsometries Q) (p : M)
    (q : M × geometricSphere) : EuclideanThree := by
  classical
  exact if q.1 ∈ (chartAt E p).source ∧
      f • q.1 ∈ (chartAt E (f • p)).source then
    toEuclidean (localCoefficientRotation Q f p q.1
      (EuclideanSpace.equiv (Fin 3) ℝ q.2.1))
  else q.2.1

theorem localSphereAmbient_mem_sphere
    (f : QuaternionicIsometries Q) (p : M)
    (q : M × geometricSphere) :
    localSphereAmbient Q f p q ∈ Metric.sphere (0 : EuclideanThree) 1 := by
  classical
  by_cases hq : q.1 ∈ (chartAt E p).source ∧
      f • q.1 ∈ (chartAt E (f • p)).source
  · rw [localSphereAmbient, if_pos hq]
    apply (mem_geometricSphere _).2
    rw [localCoefficientRotation_squareNorm_on_overlap Q f p q.1 hq.1 hq.2]
    exact (mem_geometricSphere _).1 q.2.2
  · simpa only [localSphereAmbient, if_neg hq] using q.2.2

/-- The local formula as a genuine map between geometric two-sphere fibers. -/
def localSphereAction (f : QuaternionicIsometries Q) (p : M) :
    M × geometricSphere → geometricSphere :=
  Set.codRestrict (localSphereAmbient Q f p)
    (Metric.sphere (0 : EuclideanThree) 1)
    (localSphereAmbient_mem_sphere Q f p)

theorem localSphereAmbient_smoothAt_center
    (f : QuaternionicIsometries Q) (p : M) (u : geometricSphere) :
    ContMDiffAt (J (E := E)) 𝓘(ℝ,EuclideanThree) ∞
      (localSphereAmbient Q f p) (p,u) := by
  classical
  let P := (𝓘(ℝ,E)).prod 𝓘(ℝ,Fin 3 → ℝ)
  have hfst : ContMDiffAt (J (E := E)) 𝓘(ℝ,E) ∞
      (Prod.fst : M × geometricSphere → M) (p,u) := contMDiffAt_fst
  have hsnd : ContMDiffAt (J (E := E)) (𝓡 2) ∞
      (Prod.snd : M × geometricSphere → geometricSphere) (p,u) :=
    contMDiffAt_snd
  have hcoe : ContMDiffAt (J (E := E)) 𝓘(ℝ,EuclideanThree) ∞
      (fun q : M × geometricSphere => (q.2 : EuclideanThree)) (p,u) :=
    (contMDiff_coe_sphere (n := 2) (E := EuclideanThree)).contMDiffAt.comp
      (p,u) hsnd
  have hcoeff : ContMDiffAt (J (E := E)) 𝓘(ℝ,Fin 3 → ℝ) ∞
      (fun q : M × geometricSphere =>
        EuclideanSpace.equiv (Fin 3) ℝ (q.2 : EuclideanThree)) (p,u) :=
    ((EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap.contMDiff).contMDiffAt.comp
      (p,u) hcoe
  have hpair : ContMDiffAt (J (E := E)) P ∞
      (fun q : M × geometricSphere =>
        (q.1, EuclideanSpace.equiv (Fin 3) ℝ (q.2 : EuclideanThree)))
      (p,u) := hfst.prodMk hcoeff
  have hrot := (localCoefficientRotation_jointSmoothAt Q f p
    (EuclideanSpace.equiv (Fin 3) ℝ (u : EuclideanThree))).comp (p,u) hpair
  have hambient : ContMDiffAt (J (E := E)) 𝓘(ℝ,EuclideanThree) ∞
      (fun q : M × geometricSphere =>
        toEuclidean (localCoefficientRotation Q f p q.1
          (EuclideanSpace.equiv (Fin 3) ℝ q.2.1))) (p,u) :=
    ((EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.contMDiff).contMDiffAt.comp
      (p,u) hrot
  have hopen : IsOpen {q : M × geometricSphere |
      q.1 ∈ (chartAt E p).source ∧
        f • q.1 ∈ (chartAt E (f • p)).source} := by
    have hf : Continuous (f.1 : M → M) := f.1.contMDiff.continuous
    exact ((chartAt E p).open_source.inter
      ((chartAt E (f • p)).open_source.preimage hf)).preimage continuous_fst
  have hmem : (p,u) ∈ {q : M × geometricSphere |
      q.1 ∈ (chartAt E p).source ∧
        f • q.1 ∈ (chartAt E (f • p)).source} :=
    ⟨mem_chart_source E p, mem_chart_source E (f • p)⟩
  apply hambient.congr_of_eventuallyEq
  filter_upwards [hopen.mem_nhds hmem] with q hq
  simp only [localSphereAmbient, if_pos hq]

theorem localSphereAction_smoothAt_center
    (f : QuaternionicIsometries Q) (p : M) (u : geometricSphere) :
    ContMDiffAt (J (E := E)) (𝓡 2) ∞
      (localSphereAction Q f p) (p,u) :=
  contMDiffAt_codRestrict_sphere
    (localSphereAmbient_smoothAt_center Q f p u)
    (localSphereAmbient_mem_sphere Q f p)

/-- The locally smooth sphere formula is exactly the target fiber coordinate
of any point-level lift of the actual derivative action. -/
theorem localSphereAction_eq_lift_chart
    (f : QuaternionicIsometries Q) (p : M)
    (z w : SphereBundleTotal Q)
    (hx : z.1 ∈ (chartAt E p).source)
    (hy : f • z.1 ∈ (chartAt E (f • p)).source)
    (hw : w.1 ∈ (sphereCore Q).baseSet (achart E (f • p)))
    (hbase : w.1 = f • z.1)
    (horig : toOriginalSphere Q w =
      twistorMap Q f (toOriginalSphere Q z)) :
    localSphereAction Q f p
      (z.1, ((sphereCore Q).localTriv (achart E p) z).2) =
      ((sphereCore Q).localTriv (achart E (f • p)) w).2 := by
  classical
  let i := achart E p
  let j := achart E (f • p)
  have hcoeff := sphereChartCoefficient_of_lift Q f p z w hx hy hw hbase horig
  change (EuclideanSpace.equiv (Fin 3) ℝ)
      (((sphereCore Q).localTriv j w).2 : EuclideanThree) =
    localCoefficientRotation Q f p z.1
      ((EuclideanSpace.equiv (Fin 3) ℝ)
        (((sphereCore Q).localTriv i z).2 : EuclideanThree)) at hcoeff
  apply Subtype.ext
  change localSphereAmbient Q f p
      (z.1, ((sphereCore Q).localTriv i z).2) =
    (((sphereCore Q).localTriv j w).2 : EuclideanThree)
  rw [localSphereAmbient, if_pos ⟨hx, hy⟩]
  have h := congrArg toEuclidean hcoeff.symm
  simpa only [toEuclidean, LinearEquiv.symm_apply_apply] using h

end
end QuaternionicSymmetry.ManifoldQuaternionicLocalSphereActionSmooth
