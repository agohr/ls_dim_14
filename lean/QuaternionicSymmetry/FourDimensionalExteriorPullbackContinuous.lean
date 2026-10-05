import QuaternionicSymmetry.FourDimensionalExteriorTwoFormCanonicalTopology
import QuaternionicSymmetry.ManifoldQuaternionicFourGlobalHodge

/-! Genuine exterior two-form pullback by any fixed linear map is continuous
for the basis-independent finite-dimensional topology. In particular the
actual tangent-frame pullbacks used by the twistor sphere comparison are
topological linear maps on each fiber. -/

namespace QuaternionicSymmetry.FourDimensionalExteriorPullbackContinuous

open Module
open FourDimensionalExteriorHodge
open FourDimensionalExteriorTwoFormCanonicalTopology
open ManifoldQuaternionicFourGlobalHodge
noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [Nontrivial V]

theorem pullbackTwoFormLinear_continuous
    (hdim : Module.finrank ℝ V = 4)
    (b : Basis (Fin 4) ℝ V) (T : V →ₗ[ℝ] V) :
    @Continuous (TwoForm V) (TwoForm V)
      (canonicalTwoFormTopology hdim) (canonicalTwoFormTopology hdim)
      (pullbackTwoFormLinear b T) := by
  letI : TopologicalSpace (TwoForm V) := canonicalTwoFormTopology hdim
  let F : FourDimensionalCoordinateHodge.Two →ₗ[ℝ]
      FourDimensionalCoordinateHodge.Two :=
    (coordinates b).comp ((pullbackTwoFormLinear b T).comp (reconstruct b))
  have hF : Continuous F := F.continuous_of_finiteDimensional
  have hcoord (α : TwoForm V) :
      coordinates b (pullbackTwoFormLinear b T α) =
      F (coordinates b α) := by
    simp [F]
  rw [canonicalTwoFormTopology_eq hdim b]
  letI : TopologicalSpace (TwoForm V) :=
    FourDimensionalExteriorTwoFormTopology.twoFormTopology b
  apply continuous_induced_rng.mpr
  have hfun : (fun α : TwoForm V =>
      coordinates b (pullbackTwoFormLinear b T α)) =
      (fun α => F (coordinates b α)) := by
    funext α
    exact hcoord α
  change @Continuous (TwoForm V) FourDimensionalCoordinateHodge.Two
    (FourDimensionalExteriorTwoFormTopology.twoFormTopology b) inferInstance
    (fun α => coordinates b (pullbackTwoFormLinear b T α))
  rw [hfun]
  exact hF.comp continuous_induced_dom

end
end QuaternionicSymmetry.FourDimensionalExteriorPullbackContinuous
