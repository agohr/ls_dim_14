import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Analysis.Complex.Basic

/-! The complex and real tangent bundles in the same complex self-model
atlas have the same underlying topology. The coordinate comparison uses
actual real restrictions of complex chart derivatives.
-/

namespace QuaternionicSymmetry.ComplexRealTangentTopology

open Manifold
open scoped Manifold ContDiff Topology
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ,E) 1 M] [IsManifold 𝓘(ℝ,E) 1 M]

/-- Actual tangent coordinate changes agree after restricting scalars. -/
theorem coordChange_real_complex (x y z : M)
    (hzx : z ∈ (extChartAt 𝓘(ℂ,E) x).source)
    (hzy : z ∈ (extChartAt 𝓘(ℂ,E) y).source) :
    tangentCoordChange 𝓘(ℝ,E) x y z =
      (tangentCoordChange 𝓘(ℂ,E) x y z).restrictScalars ℝ := by
  have hc := hasFDerivWithinAt_tangentCoordChange (I := 𝓘(ℂ,E)) ⟨hzx,hzy⟩
  have hc' : HasFDerivAt
      ((extChartAt 𝓘(ℂ,E) y) ∘ (extChartAt 𝓘(ℂ,E) x).symm)
      (tangentCoordChange 𝓘(ℂ,E) x y z) (extChartAt 𝓘(ℂ,E) x z) := by
    simpa only [modelWithCornersSelf_coe, Set.range_id, hasFDerivWithinAt_univ] using hc
  have hr := hc'.restrictScalars ℝ
  simpa only [tangentCoordChange_def, modelWithCornersSelf_coe,
    Set.range_id, fderivWithin_univ] using hr.fderiv

/-- Forget the complex scalars on an actual tangent vector without
changing its base point or vector. -/
def toReal (p : TangentBundle 𝓘(ℂ,E) M) : TangentBundle 𝓘(ℝ,E) M :=
  ⟨p.1,p.2⟩

/-- The inverse map of underlying tangent-bundle points. -/
def toComplex (p : TangentBundle 𝓘(ℝ,E) M) : TangentBundle 𝓘(ℂ,E) M :=
  ⟨p.1,p.2⟩

theorem continuous_toReal : Continuous (toReal (E := E) (M := M)) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply (FiberBundle.continuousAt_totalSpace E (toReal (E := E) (M := M))).mpr
  constructor
  · exact (FiberBundle.continuous_proj E (TangentSpace 𝓘(ℂ,E) : M → Type _)).continuousAt
  · let e := trivializationAt E (TangentSpace 𝓘(ℂ,E) : M → Type _) p.1
    have hp : p ∈ e.source := FiberBundle.mem_trivializationAt_proj_source
    have h : ContinuousAt (fun q : TangentBundle 𝓘(ℂ,E) M => (e q).2) p :=
      (e.continuousAt hp).snd
    apply h.congr_of_eventuallyEq
    have hbase : ∀ᶠ q : TangentBundle 𝓘(ℂ,E) M in 𝓝 p,
        q.1 ∈ (extChartAt 𝓘(ℂ,E) p.1).source :=
      (FiberBundle.continuous_proj E (TangentSpace 𝓘(ℂ,E) : M → Type _)).continuousAt
        |>.preimage_mem_nhds ((isOpen_extChartAt_source p.1).mem_nhds (by simp))
    filter_upwards [hbase] with q hq
    change tangentCoordChange 𝓘(ℝ,E) q.1 p.1 q.1 q.2 =
      tangentCoordChange 𝓘(ℂ,E) q.1 p.1 q.1 q.2
    rw [coordChange_real_complex q.1 p.1 q.1 (by simp) hq]
    rfl

theorem continuous_toComplex : Continuous (toComplex (E := E) (M := M)) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply (FiberBundle.continuousAt_totalSpace E (toComplex (E := E) (M := M))).mpr
  constructor
  · exact (FiberBundle.continuous_proj E (TangentSpace 𝓘(ℝ,E) : M → Type _)).continuousAt
  · let e := trivializationAt E (TangentSpace 𝓘(ℝ,E) : M → Type _) p.1
    have hp : p ∈ e.source := FiberBundle.mem_trivializationAt_proj_source
    have h : ContinuousAt (fun q : TangentBundle 𝓘(ℝ,E) M => (e q).2) p :=
      (e.continuousAt hp).snd
    apply h.congr_of_eventuallyEq
    have hbase : ∀ᶠ q : TangentBundle 𝓘(ℝ,E) M in 𝓝 p,
        q.1 ∈ (extChartAt 𝓘(ℂ,E) p.1).source :=
      (FiberBundle.continuous_proj E (TangentSpace 𝓘(ℝ,E) : M → Type _)).continuousAt
        |>.preimage_mem_nhds ((isOpen_extChartAt_source p.1).mem_nhds (by simp))
    filter_upwards [hbase] with q hq
    change tangentCoordChange 𝓘(ℂ,E) q.1 p.1 q.1 q.2 =
      tangentCoordChange 𝓘(ℝ,E) q.1 p.1 q.1 q.2
    rw [coordChange_real_complex q.1 p.1 q.1 (by simp) hq]
    rfl

/-- A genuine homeomorphism, not a pointwise identification with an
unproved topology comparison. -/
def tangentHomeomorph : TangentBundle 𝓘(ℂ,E) M ≃ₜ TangentBundle 𝓘(ℝ,E) M where
  toFun := toReal
  invFun := toComplex
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_toReal
  continuous_invFun := continuous_toComplex

end
end QuaternionicSymmetry.ComplexRealTangentTopology
