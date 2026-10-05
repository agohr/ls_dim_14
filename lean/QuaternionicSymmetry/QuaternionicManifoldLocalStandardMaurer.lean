import QuaternionicSymmetry.QuaternionicManifoldProductGaugeDifferential
import QuaternionicSymmetry.QuaternionicProjectiveStandardMaurer

/-! The two Maurer--Cartan blocks for an actual smooth local lift of an
adapted tangent transition, expressed in a source manifold chart. -/

namespace QuaternionicSymmetry.QuaternionicManifoldLocalStandardMaurer

open scoped Manifold ContDiff Quaternion Topology
open QuaternionicManifoldLocalScalarLifts
open QuaternionicManifoldSmoothProductLifts
open QuaternionicManifoldKernelOperatorProperties
open QuaternionicManifoldProductGaugeDifferential
open QuaternionicProjectiveProductMaurer
open QuaternionicProjectiveStandardMaurer
open QuaternionicProjectiveLineMaurer
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open VectorBundleFrameTransitions

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))

def scalarChart (p : M) (i j : atlas E M) (q : unitary ℍ) (y : E) : ℍ :=
  scalarLiftRaw Q i j q ((extChartAt 𝓘(ℝ, E) p).symm y)

def kernelChart (p : M) (i j : atlas E M) (q : unitary ℍ)
    (y : E) : E →L[ℝ] E :=
  symplecticFactorOperator S Q i j q ((extChartAt 𝓘(ℝ, E) p).symm y)

theorem local_standard_maurer_blocks (p : M) (i j : atlas E M)
    (q : unitary ℍ) (y u : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target)
    (hx : (extChartAt 𝓘(ℝ, E) p).symm y ∈ liftNeighborhood Q i j q) :
    let r := scalarChart Q p i j q
    let h := kernelChart S Q p i j q
    let hInv := (h y).adjoint
    QuaternionicLieAlgebraProjection.symplecticProjection S
      ((hInv * scalarActionLinear S (star (r y))) *
        fderiv ℝ (productGauge S r h) y u) = hInv * fderiv ℝ h y u ∧
    QuaternionicProjectiveStandardLie.scalarLineLie S
      ((hInv * scalarActionLinear S (star (r y))) *
        fderiv ℝ (productGauge S r h) y u) =
      rightStar (star (r y)) * fderiv ℝ (fun z => rightStar (r z)) y u := by
  dsimp
  let r := scalarChart Q p i j q
  let h := kernelChart S Q p i j q
  let x := (extChartAt 𝓘(ℝ, E) p).symm y
  have hr : DifferentiableAt ℝ r y :=
    scalarLift_chart_differentiableAt Q p i j q y hy hx
  have hh : DifferentiableAt ℝ h y :=
    symplecticFactor_chart_differentiableAt S Q p i j q y hy hx
  have hneigh : ∀ᶠ z in 𝓝 y,
      (extChartAt 𝓘(ℝ, E) p).symm z ∈ liftNeighborhood Q i j q :=
    (continuousAt_extChartAt_symm'' hy).preimage_mem_nhds
      ((isOpen_liftNeighborhood Q i j q).mem_nhds hx)
  have hunit : ∀ᶠ z in 𝓝 y, star (r z) * r z = 1 := by
    filter_upwards [hneigh] with z hz
    change star (scalarLiftRaw Q i j q _) * scalarLiftRaw Q i j q _ = 1
    rw [Quaternion.star_mul_self, (scalarLiftRaw_valid Q S i j q _ hz).1]
    rfl
  have hright : r y * star (r y) = 1 := by
    change scalarLiftRaw Q i j q x * star (scalarLiftRaw Q i j q x) = 1
    rw [Quaternion.self_mul_star, (scalarLiftRaw_valid Q S i j q x hx).1]
    rfl
  have hleft : (h y).adjoint * h y = 1 :=
    (symplecticFactor_adjoint_inverse S Q i j q x hx).1
  have hc : ∀ a : Fin 3 → ℝ,
      ∀ᶠ z in 𝓝 y, h z * synth S a = synth S a * h z := by
    intro a
    filter_upwards [hneigh] with z hz
    exact symplecticFactor_commutes_synth S Q i j q _ hz a
  have hInvC : ∀ a : Fin 3 → ℝ,
      (h y).adjoint * synth S a = synth S a * (h y).adjoint :=
    fun a => symplecticFactor_adjoint_commutes_synth S Q i j q x hx a
  exact ⟨standardMaurer_kernel_block S r h y u hr hh hunit hright
      (h y).adjoint hleft hc hInvC,
    standardMaurer_line_block S r h y u hr hh hunit hright
      (h y).adjoint hleft hc hInvC⟩

end
end QuaternionicSymmetry.QuaternionicManifoldLocalStandardMaurer
