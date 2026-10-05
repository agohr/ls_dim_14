import QuaternionicSymmetry.ManifoldQuaternionicTwistorMetricBilinear
import QuaternionicSymmetry.ManifoldQuaternionicCoordinateMetricField
import QuaternionicSymmetry.ManifoldTwistorLocalComplexAmbientSmooth
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! A jointly smooth ambient extension of the connection metric in every
actual fixed quaternionic chart. This avoids dependent sphere-tangent
coordinates while retaining the exact restriction to the twistor metric. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicTwistorLocalMetricSmooth

open ManifoldQuaternionicMetric
open ManifoldQuaternionicAdjointConnection
open ManifoldQuaternionicCoordinateMetricField
open ManifoldQuaternionicTwistorSplitMetric
open ManifoldTwistorSphereBundle
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

private abbrev V := Fin 3 → ℝ
private abbrev X := (E × V) × ((E × V) × (E × V))
private abbrev domain (p : M) : Set (X (E := E)) :=
  ((extChartAt 𝓘(ℝ,E) p).target ×ˢ Set.univ) ×ˢ Set.univ

/-- Local formula on unrestricted ambient coefficient vectors; on the unit
sphere tangent planes it is precisely the horizontal/vertical twistor metric. -/
def ambientLocalMetric (p : M) (z : X (E := E)) : ℝ :=
  let y := z.1.1
  let a := z.1.2
  let u := z.2.1
  let v := z.2.2
  coordinateMetricField Q p y u.1 v.1 +
    (u.2 + inducedForm Q D p y u.1 a) ⬝ᵥ
      (v.2 + inducedForm Q D p y v.1 a)

theorem ambientLocalMetric_smooth (p : M) :
    ContDiffOn ℝ ∞ (ambientLocalMetric Q D p) (domain (E := E) p) := by
  let s := domain (E := E) p
  have hy : ContDiffOn ℝ ∞ (fun z : X (E := E) => z.1.1) s := by fun_prop
  have ha : ContDiffOn ℝ ∞ (fun z : X (E := E) => z.1.2) s := by fun_prop
  have hu : ContDiffOn ℝ ∞ (fun z : X (E := E) => z.2.1.1) s := by fun_prop
  have hv : ContDiffOn ℝ ∞ (fun z : X (E := E) => z.2.2.1) s := by fun_prop
  have hbu : ContDiffOn ℝ ∞ (fun z : X (E := E) => z.2.1.2) s := by fun_prop
  have hbv : ContDiffOn ℝ ∞ (fun z : X (E := E) => z.2.2.2) s := by fun_prop
  have hG0 : ContDiffOn ℝ ∞ (coordinateMetricField Q p)
      (extChartAt 𝓘(ℝ,E) p).target := by
    have hs := Q.smooth_chartMetricForm (achart E p)
    have hsymm := contMDiffOn_extChartAt_symm (n := ∞) (I := 𝓘(ℝ,E)) p
    exact (hs.comp hsymm (by
      intro y hy
      simpa only [tangentBundleCore_baseSet, coe_achart,
        ← extChartAt_source 𝓘(ℝ,E)] using
        (extChartAt 𝓘(ℝ,E) p).map_target hy)).contDiffOn
  have hG : ContDiffOn ℝ ∞ (fun z : X (E := E) => coordinateMetricField Q p z.1.1) s :=
    hG0.comp hy (by intro z hz; exact hz.1.1)
  have hbase : ContDiffOn ℝ ∞
      (fun z : X (E := E) => coordinateMetricField Q p z.1.1 z.2.1.1 z.2.2.1) s :=
    (hG.clm_apply hu).clm_apply hv
  have hA : ContDiffOn ℝ ∞ (fun z : X (E := E) => inducedForm Q D p z.1.1) s :=
    (inducedForm_smooth Q D p).comp hy (by intro z hz; exact hz.1.1)
  have hAu : ContDiffOn ℝ ∞ (fun z : X (E := E) => inducedForm Q D p z.1.1 z.2.1.1 z.1.2) s :=
    (hA.clm_apply hu).clm_apply ha
  have hAv : ContDiffOn ℝ ∞ (fun z : X (E := E) => inducedForm Q D p z.1.1 z.2.2.1 z.1.2) s :=
    (hA.clm_apply hv).clm_apply ha
  have hdot : ContDiffOn ℝ ∞
      (fun z : X (E := E) =>
        (z.2.1.2 + inducedForm Q D p z.1.1 z.2.1.1 z.1.2) ⬝ᵥ
          (z.2.2.2 + inducedForm Q D p z.1.1 z.2.2.1 z.1.2)) s := by
    change ContDiffOn ℝ ∞
      (fun z : X (E := E) => ∑ i : Fin 3,
        (z.2.1.2 + inducedForm Q D p z.1.1 z.2.1.1 z.1.2) i *
          (z.2.2.2 + inducedForm Q D p z.1.1 z.2.2.1 z.1.2) i) s
    apply ContDiffOn.sum
    intro i hi
    fun_prop (disch := assumption)
  exact hbase.add hdot

end
end QuaternionicSymmetry.ManifoldQuaternionicTwistorLocalMetricSmooth
