import QuaternionicSymmetry.ManifoldQuaternionicSphereChartSmooth

/-! Smoothness of the actual derivative-induced twistor-sphere lift. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicTwistorLiftSmooth

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicLocalSphereActionSmooth
open ManifoldQuaternionicSphereChartSmooth
open ManifoldTwistorSphereCore
open ManifoldTwistorSphereBundle
open ManifoldTwistorCoefficientSphere
open Filter
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

private abbrev J := (𝓘(ℝ,E)).prod (𝓡 2)

/-- Smooth product-chart representative of an isometry's twistor lift. -/
def localProductAction (f : QuaternionicIsometries Q) (p : M) :
    M × geometricSphere → M × geometricSphere :=
  fun q => (f • q.1, localSphereAction Q f p q)

theorem localProductAction_smoothAt_center
    (f : QuaternionicIsometries Q) (p : M) (u : geometricSphere) :
    ContMDiffAt (J (E := E)) (J (E := E)) ∞
      (localProductAction Q f p) (p,u) := by
  have hf : ContMDiffAt (J (E := E)) 𝓘(ℝ,E) ∞
      (fun q : M × geometricSphere => f • q.1) (p,u) :=
    f.1.contMDiff.contMDiffAt.comp (p,u) contMDiffAt_fst
  exact hf.prodMk (localSphereAction_smoothAt_center Q f p u)

/-- Exact local-coordinate identity at the center of a twistor chart. -/
theorem localProductAction_center
    (f : QuaternionicIsometries Q) (z : SphereBundleTotal Q) :
    localProductAction Q f z.1
        ((sphereCore Q).localTriv (achart E z.1) z) =
      (sphereCore Q).localTriv (achart E (f • z.1))
        (sphereTotalMap Q f z) := by
  apply Prod.ext
  · exact (sphereTotalMap_base Q f z).symm
  · apply localSphereAction_eq_lift_chart Q f z.1 z
        (sphereTotalMap Q f z)
    · exact mem_chart_source E z.1
    · exact mem_chart_source E (f • z.1)
    · change f • z.1 ∈ (chartAt E (f • z.1)).source
      exact mem_chart_source E (f • z.1)
    · exact sphereTotalMap_base Q f z
    · exact (sphereTotalEquiv Q).apply_symm_apply _

/-- The local formula agrees with the actual lift throughout the overlap of
the two chosen base charts. -/
theorem localProductAction_eq_chart
    (f : QuaternionicIsometries Q) (p : M) (z : SphereBundleTotal Q)
    (hx : z.1 ∈ (chartAt E p).source)
    (hy : f • z.1 ∈ (chartAt E (f • p)).source) :
    localProductAction Q f p ((sphereCore Q).localTriv (achart E p) z) =
      (sphereCore Q).localTriv (achart E (f • p))
        (sphereTotalMap Q f z) := by
  apply Prod.ext
  · exact (sphereTotalMap_base Q f z).symm
  · apply localSphereAction_eq_lift_chart Q f p z
        (sphereTotalMap Q f z) hx hy
    · simpa only [sphereTotalMap_base] using hy
    · exact sphereTotalMap_base Q f z
    · exact (sphereTotalEquiv Q).apply_symm_apply _

/-- Every actual quaternionic isometry has a smooth derivative-induced action
on the genuine twistor sphere total space. -/
theorem sphereTotalMap_contMDiff (f : QuaternionicIsometries Q) :
    ContMDiff (J (E := E)) (J (E := E)) ∞ (sphereTotalMap Q f) := by
  intro z
  let p := z.1
  let w := sphereTotalMap Q f z
  let C := chartAt (M × geometricSphere) z
  let D := chartAt (M × geometricSphere) w
  have hC : ContMDiffAt (J (E := E)) (J (E := E)) ∞
      (C : SphereBundleTotal Q → M × geometricSphere) z := by
    exact preferredLocalTriv_smoothAt Q z
  have hprod : ContMDiffAt (J (E := E)) (J (E := E)) ∞
      (localProductAction Q f p) (C z) := by
    change ContMDiffAt (J (E := E)) (J (E := E)) ∞
      (localProductAction Q f p) (p, (C z).2)
    exact localProductAction_smoothAt_center Q f p (C z).2
  have hcenter : localProductAction Q f p (C z) = D w := by
    exact localProductAction_center Q f z
  have hD : ContMDiffAt (J (E := E)) (J (E := E)) ∞
      (D.symm : M × geometricSphere → SphereBundleTotal Q)
      (localProductAction Q f p (C z)) := by
    rw [hcenter]
    exact preferredLocalTriv_symm_smoothAt Q w
  have hlocal : ContMDiffAt (J (E := E)) (J (E := E)) ∞
      (fun y : SphereBundleTotal Q =>
        D.symm (localProductAction Q f p (C y))) z := by
    exact hD.comp z (hprod.comp z hC)
  apply hlocal.congr_of_eventuallyEq
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
  filter_upwards [h₁, h₂] with y hy₁ hy₂
  have hDy : sphereTotalMap Q f y ∈ D.source := by
    change sphereTotalMap Q f y ∈
      ((sphereCore Q).localTriv (achart E (f • p))).source
    exact ((sphereCore Q).mem_localTriv_source
      (achart E (f • p)) (sphereTotalMap Q f y)).2
        (by simpa only [sphereTotalMap_base] using hy₂)
  have heq : localProductAction Q f p (C y) =
      D (sphereTotalMap Q f y) :=
    localProductAction_eq_chart Q f p y hy₁ hy₂
  change sphereTotalMap Q f y = D.symm (localProductAction Q f p (C y))
  rw [heq]
  exact (D.left_inv hDy).symm

end
end QuaternionicSymmetry.ManifoldQuaternionicTwistorLiftSmooth
