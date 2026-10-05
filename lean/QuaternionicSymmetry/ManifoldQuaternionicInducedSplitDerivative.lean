import QuaternionicSymmetry.ManifoldQuaternionicInducedSphereDerivative
import QuaternionicSymmetry.ManifoldQuaternionicInducedTwistorDerivative
import QuaternionicSymmetry.ManifoldTwistorContactSplitting

/-! The actual induced twistor differential in Levi-Civita connection
coordinates; this module relates the local sphere formula to the global
horizontal distribution. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicInducedSplitDerivative
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicInducedTwistorMap
open ManifoldQuaternionicInducedTwistorSmooth
open ManifoldQuaternionicInducedTwistorDerivative
open ManifoldQuaternionicInducedSphereDerivative
open ManifoldQuaternionicInducedLocalSphereSmooth
open ManifoldQuaternionicInducedConnectionCovariance
open ManifoldQuaternionicAdaptedRectangularSmooth
open ManifoldQuaternionicInducedTotalGeodesy
open ManifoldQuaternionicInducedCoefficientMap
open ManifoldQuaternionicInducedLocalIntertwining
open ManifoldTwistorSphereBundle
open ManifoldQuaternionicIsometrySphereDerivative
open ManifoldTwistorGlobalAlmostComplex
open ManifoldTwistorCoefficientSphere
open ManifoldTwistorVerticalComplex
open ManifoldQuaternionicAdjointConnection
open scoped Manifold ContDiff
noncomputable section

variable {E F M N : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [FiniteDimensional ℝ F] [Nontrivial F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
variable (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
  (R : PositiveQuaternionicKahlerGeometry (E := F) (M := N))
  (ι : N → M)
  (hSmooth : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ ι)
  (hι : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x))
  (hR : IsInducedQuaternionicGeometry P R ι)

private abbrev JF := 𝓘(ℝ,F).prod (𝓡 2)
private abbrev JE := 𝓘(ℝ,E).prod (𝓡 2)
local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩
local instance (x : N) : ChartedSpace (EuclideanSpace ℝ (Fin 2))
    ((ManifoldTwistorSphereCore.sphereCore R.tangent).Fiber x) := by
  change ChartedSpace (EuclideanSpace ℝ (Fin 2)) geometricSphere
  infer_instance

include hSmooth in
theorem localBaseMap_fderiv_center (c : N) :
    fderiv ℝ (localBaseMap (E := E) (F := F) (M := M) (N := N)
      ι c (ι c))
      (extChartAt 𝓘(ℝ,F) c c) =
    mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι c := by
  have h := (hSmooth.mdifferentiable (by simp) c).mfderiv
  rw [ModelWithCorners.range_eq_univ (𝓘(ℝ,F)),
    fderivWithin_univ] at h
  exact h.symm

theorem localCoefficientInChart_center (c : N) (a : Fin 3 → ℝ) :
    localCoefficientInChart P R ι hι hR c
      (extChartAt 𝓘(ℝ,F) c c) a =
    coefficientMap P R ι hι hR c a := by
  change localCoefficientMap P R ι hι hR
    (achart F c) (achart E (ι c))
      ((extChartAt 𝓘(ℝ,F) c).symm
        (extChartAt 𝓘(ℝ,F) c c)) a = _
  rw [(extChartAt 𝓘(ℝ,F) c).left_inv (mem_extChartAt_source c)]
  change P.tangent.reduction.rankThreeCoordChange
      (achart E (ι c)) (achart E (ι c)) (ι c)
      (coefficientMap P R ι hι hR c
        (R.tangent.reduction.rankThreeCoordChange
          (achart F c) (achart F c) c a)) = _
  rw [R.tangent.reduction.rankThreeCoordChange_self
      (achart F c) c (mem_chart_source F c),
    P.tangent.reduction.rankThreeCoordChange_self
      (achart E (ι c)) (ι c) (mem_chart_source E (ι c))]

theorem localBaseMap_center (c : N) :
    localBaseMap ι c (ι c) (extChartAt 𝓘(ℝ,F) c c) =
      extChartAt 𝓘(ℝ,E) (ι c) (ι c) := by
  change (extChartAt 𝓘(ℝ,E) (ι c))
    (ι ((extChartAt 𝓘(ℝ,F) c).symm
      (extChartAt 𝓘(ℝ,F) c c))) = _
  rw [(extChartAt 𝓘(ℝ,F) c).left_inv (mem_extChartAt_source c)]

theorem sphereTotalMap_center_coefficients
    (z : ManifoldTwistorSphereCore.SphereBundleTotal R.tangent) :
    sphereCoefficients (sphereTotalMap P R ι hι hR z).2 =
      coefficientMap P R ι hι hR z.1 (sphereCoefficients z.2) := by
  rfl

theorem sphereTotalMap_center_localSphereMap
    (z : ManifoldTwistorSphereCore.SphereBundleTotal R.tangent) :
    (sphereTotalMap P R ι hι hR z).2 =
      localSphereMap P R ι hι hR z.1 (z.1,z.2) := by
  rw [ManifoldQuaternionicInducedTwistorDerivative.sphereTotalMap_fiber]
  exact (localSphereMap_fixedFiber P R ι hι hR z.1 z.2).symm

include hSmooth in
theorem sphereTotalMap_mfderiv_snd
    (z : ManifoldTwistorSphereCore.SphereBundleTotal R.tangent)
    (t : TangentSpace (JF (F := F)) z) :
    (mfderiv (JF (F := F)) (JE (E := E))
      (sphereTotalMap P R ι hι hR) z t).2 =
    mfderiv (JF (F := F)) (𝓡 2)
      (localSphereMap P R ι hι hR z.1) (z.1,z.2) t := by
  rw [sphereTotalMap_mfderiv_eq_local P R ι hSmooth hι hR z]
  have hb : MDifferentiableAt (JF (F := F)) 𝓘(ℝ,E)
      (fun q : N × geometricSphere => ι q.1) (z.1,z.2) :=
    hSmooth.mdifferentiableAt (by simp) |>.comp (z.1,z.2)
      mdifferentiableAt_fst
  have hs : MDifferentiableAt (JF (F := F)) (𝓡 2)
      (localSphereMap P R ι hι hR z.1) (z.1,z.2) :=
    (localSphereMap_smoothAt_center P R ι hSmooth hι hR z.1 z.2)
      |>.mdifferentiableAt (by simp)
  change (mfderiv (JF (F := F)) (JE (E := E))
    (fun q : N × geometricSphere =>
      (ι q.1, localSphereMap P R ι hι hR z.1 q))
      (z.1,z.2) t).2 = _
  rw [mfderiv_prodMk hb hs]
  rfl

include hSmooth in
theorem connectionTangentEquiv_mfderiv_fst
    (DP : ManifoldQuaternionicConnection.CompatibleTangentConnection P.tangent)
    (DR : ManifoldQuaternionicConnection.CompatibleTangentConnection R.tangent)
    (z : ManifoldTwistorSphereCore.SphereBundleTotal R.tangent)
    (t : TangentSpace (JF (F := F)) z) :
    (connectionTangentEquiv P.tangent DP
      (sphereTotalMap P R ι hι hR z)
      (mfderiv (JF (F := F)) (JE (E := E))
        (sphereTotalMap P R ι hι hR) z t)).1 =
      mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι z.1
        (connectionTangentEquiv R.tangent DR z t).1 := by
  change (mfderiv (JF (F := F)) (JE (E := E))
    (sphereTotalMap P R ι hι hR) z t).1 =
      mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι z.1 t.1
  exact sphereTotalMap_mfderiv_fst P R ι hSmooth hι hR z t

include hSmooth in
/-- The complete second block of the genuine induced twistor differential
is the intrinsic coefficient isometry after Levi-Civita splitting. -/
theorem connectionTangentEquiv_mfderiv_snd_coefficients
    (DP : ManifoldQuaternionicConnection.CompatibleTangentConnection P.tangent)
    (DR : ManifoldQuaternionicConnection.CompatibleTangentConnection R.tangent)
    (hTot : IsTotallyGeodesic P R ι DP DR)
    (z : ManifoldTwistorSphereCore.SphereBundleTotal R.tangent)
    (t : TangentSpace (JF (F := F)) z) :
    ((connectionTangentEquiv P.tangent DP
      (sphereTotalMap P R ι hι hR z)
      (mfderiv (JF (F := F)) (JE (E := E))
        (sphereTotalMap P R ι hι hR) z t)).2).1 =
    coefficientMap P R ι hι hR z.1
      ((connectionTangentEquiv R.tangent DR z t).2).1 := by
  let y := extChartAt 𝓘(ℝ,F) z.1 z.1
  let a := sphereCoefficients z.2
  let b := EuclideanSpace.equiv (Fin 3) ℝ (sphereTangentMap z.2 t.2)
  let C := coefficientMap P R ι hι hR z.1
  let B := inducedForm R.tangent DR z.1 y t.1 a
  let B' := inducedForm P.tangent DP (ι z.1)
    (extChartAt 𝓘(ℝ,E) (ι z.1) (ι z.1))
    (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι z.1 t.1) (C a)
  let d := (fderiv ℝ (localCoefficientInChart P R ι hι hR z.1) y t.1) a
  have ha : C B = B' + d := by
    have h := induced_connection_covariance_at_center
      P R ι hSmooth hι hR DP DR hTot z.1 t.1 a
    dsimp only at h
    rw [localBaseMap_center (ι := ι) z.1,
      localBaseMap_fderiv_center ι hSmooth z.1,
      localCoefficientInChart_center P R ι hι hR z.1 a,
      localCoefficientInChart_center P R ι hι hR z.1 B] at h
    exact h.symm.trans (add_comm _ _)
  have hder := localSphereMap_mfderiv_coefficients_center
    P R ι hSmooth hι hR z.1 z.2 t.1 t.2
  change EuclideanSpace.equiv (Fin 3) ℝ
      (sphereTangentMap (localSphereMap P R ι hι hR z.1 (z.1,z.2))
        (mfderiv (JF (F := F)) (𝓡 2)
          (localSphereMap P R ι hι hR z.1) (z.1,z.2) (t.1,t.2))) =
      d + localCoefficientInChart P R ι hι hR z.1 y b at hder
  rw [localCoefficientInChart_center P R ι hι hR z.1 b] at hder
  have hder' : EuclideanSpace.equiv (Fin 3) ℝ
      (sphereTangentMap (localSphereMap P R ι hι hR z.1 (z.1,z.2))
        (mfderiv (JF (F := F)) (𝓡 2)
          (localSphereMap P R ι hι hR z.1) (z.1,z.2) t)) = d + C b := by
    simpa only [Prod.mk.eta] using hder
  have hpoint := sphereTotalMap_center_localSphereMap P R ι hι hR z
  have hcoeff := sphereTotalMap_center_coefficients P R ι hι hR z
  have hblocks := sphereTotalMap_mfderiv_snd
    P R ι hSmooth hι hR z t
  have hbase := sphereTotalMap_mfderiv_fst
    P R ι hSmooth hι hR z t
  have hpointBase := sphereTotalMap_base P R ι hι hR z
  change EuclideanSpace.equiv (Fin 3) ℝ
      (sphereTangentMap (sphereTotalMap P R ι hι hR z).2
        (mfderiv (JF (F := F)) (JE (E := E))
          (sphereTotalMap P R ι hι hR) z t).2) +
      inducedForm P.tangent DP (sphereTotalMap P R ι hι hR z).1
        (extChartAt 𝓘(ℝ,E) (sphereTotalMap P R ι hι hR z).1
          (sphereTotalMap P R ι hι hR z).1)
        (mfderiv (JF (F := F)) (JE (E := E))
          (sphereTotalMap P R ι hι hR) z t).1
        (sphereCoefficients (sphereTotalMap P R ι hι hR z).2) =
    C (b + B)
  rw [hblocks, hbase, hpointBase, hcoeff, hpoint]
  rw [hder', map_add, ha]
  abel

include hSmooth in
/-- The genuine induced twistor differential sends the source
Levi-Civita horizontal distribution into the ambient one. -/
theorem sphereTotalMap_mfderiv_preserves_horizontal
    (DP : ManifoldQuaternionicConnection.CompatibleTangentConnection P.tangent)
    (DR : ManifoldQuaternionicConnection.CompatibleTangentConnection R.tangent)
    (hTot : IsTotallyGeodesic P R ι DP DR)
    (z : ManifoldTwistorSphereCore.SphereBundleTotal R.tangent)
    (t : TangentSpace (JF (F := F)) z)
    (ht : t ∈ horizontalTangentSubmodule R.tangent DR z) :
    mfderiv (JF (F := F)) (JE (E := E))
      (sphereTotalMap P R ι hι hR) z t ∈
        horizontalTangentSubmodule P.tangent DP
          (sphereTotalMap P R ι hι hR z) := by
  have hs := (mem_horizontalTangentSubmodule_iff R.tangent DR z t).mp ht
  have h := connectionTangentEquiv_mfderiv_snd_coefficients
    P R ι hSmooth hι hR DP DR hTot z t
  apply (mem_horizontalTangentSubmodule_iff P.tangent DP
    (sphereTotalMap P R ι hι hR z) _).mpr
  apply Subtype.ext
  change ((connectionTangentEquiv P.tangent DP
      (sphereTotalMap P R ι hι hR z)
      (mfderiv (JF (F := F)) (JE (E := E))
        (sphereTotalMap P R ι hι hR) z t)).2).1 = 0
  rw [h, hs]
  simp

end
end QuaternionicSymmetry.ManifoldQuaternionicInducedSplitDerivative
