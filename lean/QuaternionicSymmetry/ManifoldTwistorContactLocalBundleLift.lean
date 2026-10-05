import QuaternionicSymmetry.ManifoldTwistorContactPullbackLiftSmooth

/-! An explicit smooth fixed-chart horizontal lift. Its input consists of
a raw base chart point, a genuine two-sphere point, and a base tangent
coordinate. The output lies in the actual twistor tangent bundle and is
the connection-horizontal projection of the zero-sphere-direction lift. -/

namespace QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex

open QuaternionicSymmetry.ManifoldTwistorSphereBundle
open QuaternionicSymmetry.ManifoldTwistorCoefficientSphere
open QuaternionicSymmetry.ManifoldTwistorSphereCore
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open QuaternionicSymmetry.ManifoldQuaternionicConnection
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : CompatibleTangentConnection Q)

private abbrev I := (𝓘(ℝ,E)).prod (𝓡 2)
private abbrev J := I (E := E) |>.prod 𝓘(ℝ,E)

def localContactLiftInput (r : (E × geometricSphere) × E) : X (E := E) :=
  ((r.1.1,r.2), ⟨r.1.2,0⟩)

omit [Nontrivial E] [FiniteDimensional ℝ E] in
theorem localContactLiftInput_smooth :
    ContMDiff (J (E := E)) (IX (E := E)) ∞
      (localContactLiftInput (E := E)) := by
  have hbase : ContMDiff (J (E := E)) (𝓘(ℝ,E)) ∞
      (fun r : (E × geometricSphere) × E => r.1.1) :=
    contMDiff_fst.comp contMDiff_fst
  have hdir : ContMDiff (J (E := E)) (𝓘(ℝ,E)) ∞
      (fun r : (E × geometricSphere) × E => r.2) := contMDiff_snd
  have hsphere : ContMDiff (J (E := E)) (𝓡 2) ∞
      (fun r : (E × geometricSphere) × E => r.1.2) :=
    contMDiff_snd.comp contMDiff_fst
  have hzero : ContMDiff (J (E := E)) (𝓡 2).tangent ∞
      (fun r : (E × geometricSphere) × E =>
        (⟨r.1.2,0⟩ : TangentBundle (𝓡 2) geometricSphere)) :=
    (Bundle.contMDiff_zeroSection ℝ (TangentSpace (𝓡 2) : geometricSphere → Type _)).comp hsphere
  exact (hbase.prodMk hdir).prodMk hzero

def localContactBundleLift (p : M) (r : (E × geometricSphere) × E) :
    TangentBundle (I (E := E)) (SphereBundleTotal Q) :=
  rawTangentCoordinatesInv Q p
    (localHorizontalProjection Q D p (localContactLiftInput r))

theorem localContactBundleLift_smoothOn (p : M) :
    ContMDiffOn (J (E := E)) (I (E := E)).tangent ∞
      (localContactBundleLift Q D p)
      {r : (E × geometricSphere) × E |
        r.1.1 ∈ (extChartAt 𝓘(ℝ,E) p).target} := by
  let s : Set ((E × geometricSphere) × E) :=
    {r | r.1.1 ∈ (extChartAt 𝓘(ℝ,E) p).target}
  have hmaps : Set.MapsTo (localContactLiftInput (E := E)) s
      (localDomain (E := E) p) := by
    intro r hr
    exact hr
  have hlocal := (localHorizontalProjection_smooth Q D p).comp
    localContactLiftInput_smooth.contMDiffOn hmaps
  have hmaps' : Set.MapsTo
      (localHorizontalProjection Q D p ∘ localContactLiftInput (E := E))
      s (localDomain (E := E) p) := by
    intro r hr
    exact hr
  simpa only [localContactBundleLift, Function.comp_apply] using
    (rawTangentCoordinatesInv_smoothOn Q p).comp hlocal hmaps'

end
end QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
