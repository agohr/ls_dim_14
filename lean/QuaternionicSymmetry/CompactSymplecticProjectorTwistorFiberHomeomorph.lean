import QuaternionicSymmetry.CompactSymplecticProjectorTwistorFiberContinuous
import QuaternionicSymmetry.FiniteComplexProjectiveHausdorff
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCompact

/-! Each actual fiber of the continuous CP-to-HP map is homeomorphic to
CP¹: the concrete projective-line parametrization is a closed embedding
because its source is compact and the ambient finite-dimensional complex
projective space is Hausdorff. No holomorphic twistor assertion is used. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorTwistorFiberHomeomorph

open CompactSymplecticProjectorTwistorFiberLine
open CompactSymplecticProjectorTwistorFiberContinuous
open CompactSymplecticProjectorTwistorExactFiber
open CompactSymplecticProjectorTwistorCarrierMap
open scoped LinearAlgebra.Projectivization

noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev V (n : ℕ) := I n → ℂ
private abbrev EV (n : ℕ) := EuclideanSpace ℂ (I n)

theorem fiberProjectiveLine_closedEmbedding (n : ℕ)
    (w : Metric.sphere (0 : EV n) 1) :
    Topology.IsClosedEmbedding (fiberProjectiveLine n w) := by
  letI : T2Space (ℙ ℂ (V n)) :=
    FiniteComplexProjectiveHausdorff.t2Space (I n)
  exact (continuous_fiberProjectiveLine n w).isClosedEmbedding
    (fiberProjectiveLine_injective n w)

def fiberHomeomorph (n : ℕ)
    (w : Metric.sphere (0 : EV n) 1) :
    ℙ ℂ (Fin 2 → ℂ) ≃ₜ
      {p : ℙ ℂ (V n) | twistorToCarrier n p =
        twistorToCarrier n
          (Projectivization.mk ℂ ((EuclideanSpace.equiv (I n) ℂ) w.1) (by
            intro hz
            have hw : w.1 = 0 := (EuclideanSpace.equiv (I n) ℂ).injective hz
            have hn := mem_sphere_zero_iff_norm.mp w.2
            simp [hw] at hn))} := by
  have hset : Set.range (fiberProjectiveLine n w) =
      {p : ℙ ℂ (V n) | twistorToCarrier n p =
        twistorToCarrier n
          (Projectivization.mk ℂ ((EuclideanSpace.equiv (I n) ℂ) w.1) (by
            intro hz
            have hw : w.1 = 0 := (EuclideanSpace.equiv (I n) ℂ).injective hz
            have hn := mem_sphere_zero_iff_norm.mp w.2
            simp [hw] at hn))} := by
    ext p
    exact (twistorToCarrier_fiber_eq_projectiveLine n w p).symm
  exact (fiberProjectiveLine_closedEmbedding n w).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr hset)

end
end QuaternionicSymmetry.CompactSymplecticProjectorTwistorFiberHomeomorph
