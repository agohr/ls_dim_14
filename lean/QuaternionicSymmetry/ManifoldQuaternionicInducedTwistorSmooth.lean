import QuaternionicSymmetry.ManifoldQuaternionicInducedSphereChartIdentity
import QuaternionicSymmetry.ManifoldQuaternionicSphereChartSmooth

/-! Smoothness of the genuine twistor-sphere map induced by a quaternionic
submanifold inclusion. Its local fiber coefficients are reconstructed from
the rectangular derivative and metric, not an inverse tangent derivative. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicInducedTwistorSmooth
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicInducedTwistorMap
open ManifoldQuaternionicInducedLocalSphereSmooth
open ManifoldQuaternionicInducedSphereChartIdentity
open ManifoldQuaternionicSphereChartSmooth
open ManifoldTwistorSphereBundle
open ManifoldTwistorSphereCore
open ManifoldTwistorCoefficientSphere
open Filter
open scoped Manifold ContDiff Topology
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

def localProductMap (c : N) : N × geometricSphere → M × geometricSphere :=
  fun q => (ι q.1, localSphereMap P R ι hι hR c q)

include hSmooth in
theorem localProductMap_smoothAt_center (c : N) (u : geometricSphere) :
    ContMDiffAt (JF (F := F)) (JE (E := E)) ∞
      (localProductMap P R ι hι hR c) (c,u) := by
  have hbase : ContMDiffAt (JF (F := F)) 𝓘(ℝ,E) ∞
      (fun q : N × geometricSphere => ι q.1) (c,u) :=
    hSmooth.contMDiffAt.comp (c,u) contMDiffAt_fst
  exact hbase.prodMk (localSphereMap_smoothAt_center P R ι hSmooth hι hR c u)

theorem localProductMap_eq_chart (c : N) (z : SphereBundleTotal R.tangent)
    (hx : z.1 ∈ (chartAt F c).source)
    (hy : ι z.1 ∈ (chartAt E (ι c)).source) :
    localProductMap P R ι hι hR c
        ((sphereCore R.tangent).localTriv (achart F c) z) =
      (sphereCore P.tangent).localTriv (achart E (ι c))
        (sphereTotalMap P R ι hι hR z) := by
  apply Prod.ext
  · exact (sphereTotalMap_base P R ι hι hR z).symm
  · exact localSphereMap_eq_lift_chart P R ι hι hR c z hx hy

include hSmooth in
theorem sphereTotalMap_contMDiff :
    ContMDiff (JF (F := F)) (JE (E := E)) ∞
      (sphereTotalMap P R ι hι hR) := by
  intro z
  let c := z.1
  let w := sphereTotalMap P R ι hι hR z
  let C := chartAt (N × geometricSphere) z
  let D := chartAt (M × geometricSphere) w
  have hC : ContMDiffAt (JF (F := F)) (JF (F := F)) ∞
      (C : SphereBundleTotal R.tangent → N × geometricSphere) z :=
    preferredLocalTriv_smoothAt R.tangent z
  have hprod : ContMDiffAt (JF (F := F)) (JE (E := E)) ∞
      (localProductMap P R ι hι hR c) (C z) := by
    change ContMDiffAt (JF (F := F)) (JE (E := E)) ∞
      (localProductMap P R ι hι hR c) (c, (C z).2)
    exact localProductMap_smoothAt_center P R ι hSmooth hι hR c (C z).2
  have hcenter : localProductMap P R ι hι hR c (C z) = D w := by
    apply localProductMap_eq_chart P R ι hι hR c z
    · exact mem_chart_source F c
    · exact mem_chart_source E (ι c)
  have hD : ContMDiffAt (JE (E := E)) (JE (E := E)) ∞
      (D.symm : M × geometricSphere → SphereBundleTotal P.tangent)
      (localProductMap P R ι hι hR c (C z)) := by
    rw [hcenter]
    exact preferredLocalTriv_symm_smoothAt P.tangent w
  have hlocal : ContMDiffAt (JF (F := F)) (JE (E := E)) ∞
      (fun y : SphereBundleTotal R.tangent =>
        D.symm (localProductMap P R ι hι hR c (C y))) z :=
    hD.comp z (hprod.comp z hC)
  apply hlocal.congr_of_eventuallyEq
  have hbase : Continuous (fun y : SphereBundleTotal R.tangent => y.1) :=
    (ManifoldTwistorSphereManifold.sphereProjection_smooth R.tangent).continuous
  have h₁ : ∀ᶠ y in nhds z, y.1 ∈ (chartAt F c).source :=
    (((chartAt F c).open_source).preimage hbase).mem_nhds (mem_chart_source F c)
  have h₂ : ∀ᶠ y in nhds z, ι y.1 ∈ (chartAt E (ι c)).source :=
    (((chartAt E (ι c)).open_source).preimage
      (hSmooth.continuous.comp hbase)).mem_nhds (mem_chart_source E (ι c))
  filter_upwards [h₁, h₂] with y hy₁ hy₂
  have hDy : sphereTotalMap P R ι hι hR y ∈ D.source := by
    change sphereTotalMap P R ι hι hR y ∈
      ((sphereCore P.tangent).localTriv (achart E (ι c))).source
    exact ((sphereCore P.tangent).mem_localTriv_source
      (achart E (ι c)) (sphereTotalMap P R ι hι hR y)).2
        (by simpa only [sphereTotalMap_base] using hy₂)
  have heq : localProductMap P R ι hι hR c (C y) =
      D (sphereTotalMap P R ι hι hR y) :=
    localProductMap_eq_chart P R ι hι hR c y hy₁ hy₂
  change sphereTotalMap P R ι hι hR y =
    D.symm (localProductMap P R ι hι hR c (C y))
  rw [heq]
  exact (D.left_inv hDy).symm

include hSmooth in
theorem sphereTotalMap_continuous :
    Continuous (sphereTotalMap P R ι hι hR) :=
  (sphereTotalMap_contMDiff P R ι hSmooth hι hR).continuous

end
end QuaternionicSymmetry.ManifoldQuaternionicInducedTwistorSmooth
