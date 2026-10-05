import QuaternionicSymmetry.ManifoldTwistorLocalComplexSmoothness
/-! A jointly smooth ambient extension of the full connection-corrected
local twistor almost complex operator. On the actual sphere tangent plane
this formula is definitionally the local operator proved to square to -1. -/
namespace QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
open QuaternionicSymmetry.ManifoldTwistorVerticalComplex
open QuaternionicSymmetry.ManifoldQuaternionicAdjointConnection
open QuaternionicSymmetry.ManifoldQuaternionicConnection
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open QuaternionicSymmetry.ManifoldTwistorLocalAlmostComplex
open QuaternionicSymmetry.ManifoldTwistorHorizontalConnection
open QuaternionicSymmetry.ManifoldTwistorSphereBundle
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : CompatibleTangentConnection Q)
private abbrev V := Fin 3 → ℝ
private abbrev S (p : M) : Set ((E × V) × (E × V)) :=
  ((extChartAt 𝓘(ℝ,E) p).target ×ˢ Set.univ) ×ˢ Set.univ

def ambientLocalComplex (p : M) (z : (E × V) × (E × V)) : E × V :=
  let y := z.1.1
  let a := z.1.2
  let u := z.2.1
  let v := z.2.2
  let A := inducedForm Q D p y
  let B := ambientBaseComplex Q p y a
  (B u, crossProduct a (v + A u a) - A (B u) a)

theorem ambientLocalComplex_smooth (p : M) :
    ContDiffOn ℝ ∞ (ambientLocalComplex Q D p) (S p) := by
  have hpos : ContDiffOn ℝ ∞ (fun z : (E × V) × (E × V) => z.1.1) (S p) := by fun_prop
  have ha : ContDiffOn ℝ ∞ (fun z : (E × V) × (E × V) => z.1.2) (S p) := by fun_prop
  have hu : ContDiffOn ℝ ∞ (fun z : (E × V) × (E × V) => z.2.1) (S p) := by fun_prop
  have hv : ContDiffOn ℝ ∞ (fun z : (E × V) × (E × V) => z.2.2) (S p) := by fun_prop
  have hB : ContDiffOn ℝ ∞ (fun z : (E × V) × (E × V) => ambientBaseComplex Q p z.1.1 z.1.2) (S p) :=
    (ambientBaseComplex_smooth Q p).comp contDiffOn_fst (by intro z hz; exact hz.1)
  have hA : ContDiffOn ℝ ∞ (fun z : (E × V) × (E × V) => inducedForm Q D p z.1.1) (S p) :=
    (inducedForm_smooth Q D p).comp hpos (by intro z hz; exact hz.1.1)
  have hBu : ContDiffOn ℝ ∞ (fun z : (E × V) × (E × V) => ambientBaseComplex Q p z.1.1 z.1.2 z.2.1) (S p) :=
    hB.clm_apply hu
  have hAu : ContDiffOn ℝ ∞ (fun z : (E × V) × (E × V) => inducedForm Q D p z.1.1 z.2.1) (S p) :=
    hA.clm_apply hu
  have hAua : ContDiffOn ℝ ∞ (fun z : (E × V) × (E × V) => inducedForm Q D p z.1.1 z.2.1 z.1.2) (S p) :=
    hAu.clm_apply ha
  have hABu : ContDiffOn ℝ ∞ (fun z : (E × V) × (E × V) => inducedForm Q D p z.1.1 (ambientBaseComplex Q p z.1.1 z.1.2 z.2.1)) (S p) :=
    hA.clm_apply hBu
  have hABua : ContDiffOn ℝ ∞ (fun z : (E × V) × (E × V) => inducedForm Q D p z.1.1 (ambientBaseComplex Q p z.1.1 z.1.2 z.2.1) z.1.2) (S p) :=
    hABu.clm_apply ha
  have hcross : ContDiffOn ℝ ∞ (fun z : (E × V) × (E × V) => crossProduct z.1.2 (z.2.2 + inducedForm Q D p z.1.1 z.2.1 z.1.2)) (S p) :=
    (crossSmooth.contDiffOn (s := Set.univ)).comp
      (ha.prodMk (hv.add hAua)) (by intro z hz; exact Set.mem_univ _)
  simpa only [ambientLocalComplex] using hBu.prodMk (hcross.sub hABua)

theorem ambientLocalComplex_eq_local (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (a : coefficientSphere) (uv : E × verticalSubmodule a) :
    ambientLocalComplex Q D p ((y,a.1),(uv.1,uv.2.1)) =
      ((localTwistorComplex Q D p y hy a uv).1,
       (localTwistorComplex Q D p y hy a uv).2.1) := by
  rfl
end
end QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
