import QuaternionicSymmetry.ProjectiveAdjointBundle
import QuaternionicSymmetry.LocalChernWeilTracePowers

/-!
# Continuous curvature section of the supplied projective adjoint bundle

The algebraically descended curvature of a supplied `GaugeAtlas.Connection`
is expressed as a section of the existing mathlib vector bundle. Its local
trivialization is exactly the local curvature coefficient, so local C²
regularity makes the total-space section continuous. No PQK-derived atlas is
constructed here.
-/

namespace QuaternionicSymmetry.ProjectiveAdjointDescent.GaugeAtlas

open QuaternionicSymmetry.ProjectiveAdjointDescent
  QuaternionicSymmetry.LocalConnection
  QuaternionicSymmetry.LocalConnectionForms
  QuaternionicSymmetry.LocalChernWeilTracePowers
open TopologicalSpace
open scoped Topology Bundle

noncomputable section

variable {ι E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A]

local instance instCurvatureBundleNormedSpace : NormedSpace ℝ A :=
  NormedAlgebra.toNormedSpace A

variable (P : GaugeAtlas ι E A) (D : P.Connection)

/-- The algebraic quotient curvature section, expressed in the actual
continuous adjoint vector bundle's canonical fiber coordinate. -/
def curvatureTotalSection (v : Fin 2 → E) : E → P.vectorCore.TotalSpace :=
  fun x => ⟨x, P.fiberEquiv x (P.curvatureSection D x v)⟩

@[simp] theorem curvatureTotalSection_proj (v : Fin 2 → E) (x : E) :
    P.vectorCore.proj (P.curvatureTotalSection D v x) = x := rfl

/-- In every available chart, the total-space section has precisely the
local curvature two-form as its trivialized coordinate. -/
theorem localTriv_curvatureTotalSection (v : Fin 2 → E) (i : ι)
    (x : E) (hi : x ∈ P.U i) :
    (P.vectorCore.localTriv i) (P.curvatureTotalSection D v x) =
      (x, curvatureForm (D.Γ i) x v) := by
  have hc : x ∈ P.U (P.vectorCore.indexAt x) :=
    P.vectorCore.mem_baseSet_at x
  change (x, P.adjointCoordChange (P.vectorCore.indexAt x) i x
    (P.fiberEquiv x (P.curvatureSection D x v))) =
      (x, curvatureForm (D.Γ i) x v)
  rw [P.curvatureSection_bundle_coordinate D x i hi v]
  rw [P.adjointCoordChange_comp i (P.vectorCore.indexAt x) i x hi hc hi]
  rw [P.adjointCoordChange_self i x hi]

/-- The fiber coordinate of curvature is itself a continuous alternating
two-form. This records fiberwise multilinearity and alternation independently
of any operation on points of the bundle total space. -/
def curvatureFiberForm (x : E) : E [⋀^Fin 2]→L[ℝ] A :=
  curvatureForm (D.Γ (P.vectorCore.indexAt x)) x

theorem curvatureFiberForm_apply (x : E) (v : Fin 2 → E) :
    P.curvatureFiberForm D x v = (P.curvatureTotalSection D v x).2 := by
  have hi : x ∈ P.U (P.vectorCore.indexAt x) :=
    P.vectorCore.mem_baseSet_at x
  have hcoord := P.curvatureSection_bundle_coordinate D x
    (P.vectorCore.indexAt x) hi v
  rw [P.adjointCoordChange_self (P.vectorCore.indexAt x) x hi] at hcoord
  exact hcoord.symm

theorem curvatureTotalSection_fiber_alt (x : E) (v : Fin 2 → E)
    (h : v 0 = v 1) :
    (P.curvatureTotalSection D v x).2 = 0 := by
  rw [← P.curvatureFiberForm_apply D x v]
  exact (P.curvatureFiberForm D x).map_eq_zero_of_eq v h (by decide)

theorem curvatureTotalSection_fiber_swap (x : E) (v : Fin 2 → E) :
    (P.curvatureTotalSection D (v ∘ Equiv.swap (0 : Fin 2) 1) x).2 =
      -(P.curvatureTotalSection D v x).2 := by
  rw [← P.curvatureFiberForm_apply D x (v ∘ Equiv.swap (0 : Fin 2) 1),
    ← P.curvatureFiberForm_apply D x v]
  exact (P.curvatureFiberForm D x).map_swap (v := v)
    (i := 0) (j := 1) (by decide)

/-- The curvature coefficient in a fixed pair of tangent directions is
continuous at every point where the chart connection is C². -/
theorem continuousAt_curvatureCoefficient (v : Fin 2 → E) (i : ι)
    (x : E) (hΓ : ContDiffAt ℝ 2 (D.Γ i) x) :
    ContinuousAt (fun y => curvatureForm (D.Γ i) y v) x := by
  have hF : DifferentiableAt ℝ (curvatureForm (D.Γ i)) x := by
    simpa only [curvaturePowerForm] using
      (differentiableAt_curvaturePowerForm (D.Γ i) x hΓ 0)
  simpa only using (hF.continuousAlternatingMap_apply
    (g := fun i (_ : E) => v i)
    (fun i => differentiableAt_const (v i))).continuousAt

/-- For each fixed pair of tangent directions, the curvature section is
continuous as a map into the actual vector-bundle total space. -/
theorem continuous_curvatureTotalSection (v : Fin 2 → E)
    (hD2 : ∀ i x, x ∈ P.U i → ContDiffAt ℝ 2 (D.Γ i) x) :
    Continuous (P.curvatureTotalSection D v) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  let i := P.vectorCore.indexAt x
  have hi : x ∈ P.U i := P.vectorCore.mem_baseSet_at x
  have hU : (P.U i : Set E) ∈ 𝓝 x := (P.U i).isOpen.mem_nhds hi
  have hsource :
      (P.curvatureTotalSection D v) ⁻¹' (P.vectorCore.localTriv i).source ∈ 𝓝 x := by
    convert hU using 1
  refine ((P.vectorCore.localTriv i).toOpenPartialHomeomorph.continuousAt_iff_continuousAt_comp_left hsource).2 ?_
  have hlocal :
      (fun y => (P.vectorCore.localTriv i) (P.curvatureTotalSection D v y))
        =ᶠ[𝓝 x] (fun y => (y, curvatureForm (D.Γ i) y v)) := by
    filter_upwards [hU] with y hy
    exact P.localTriv_curvatureTotalSection D v i y hy
  exact (continuousAt_id.prodMk
    (P.continuousAt_curvatureCoefficient D v i x (hD2 i x hi))).congr_of_eventuallyEq
      hlocal

end
end QuaternionicSymmetry.ProjectiveAdjointDescent.GaugeAtlas
