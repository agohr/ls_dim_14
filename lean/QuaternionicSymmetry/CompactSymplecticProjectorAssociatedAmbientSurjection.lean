import QuaternionicSymmetry.CompactSymplecticProjectorAssociatedToAmbient
import QuaternionicSymmetry.CompactSymplecticProjectorTwistorExactFiber

/-! The representative-independent associated bundle actually covers every
point of the independently constructed ambient complex projective twistor
space. Injectivity/topological-smooth comparison are separate obligations. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorAssociatedAmbientSurjection

open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorAssociatedHopf
open CompactSymplecticProjectorAssociatedToAmbient
open CompactSymplecticProjectorTwistorCarrierMap
open CompactSymplecticProjectorTwistorFiberConstant
open CompactSymplecticProjectorTwistorExactFiber
open CompactSymplecticProjectorTwistorGroupFiberBase
open CompactSymplecticProjectorTwistorFiberLine
open CompactSymplecticProjectorFirstColumnUnit
open FourDimensionalHalfSpinProjective
open scoped LinearAlgebra.Projectivization

noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev V (n : ℕ) := I n → ℂ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

private def fiberOrigin : ProjectiveSpinor :=
  Projectivization.mk ℂ (![1, 0] : Fin 2 → ℂ) (by simp)

theorem associatedToAmbient_surjective (n : ℕ) :
    Function.Surjective (associatedToAmbient n) := by
  intro p
  let x := twistorToCarrier n p
  let u : G n := x.out
  have hu : (u : ProjectiveCarrier n) = x := Quotient.out_eq x
  let w := firstColumnSphere n u
  have hbase : twistorToCarrier n
      (Projectivization.mk ℂ ((EuclideanSpace.equiv (I n) ℂ) w.1) (by
        intro hz
        have hw : w.1 = 0 := (EuclideanSpace.equiv (I n) ℂ).injective hz
        have hn := mem_sphere_zero_iff_norm.mp w.2
        simp [hw] at hn)) = x := by
    calc
      _ = twistorToCarrier n (fiberProjectiveLine n w fiberOrigin) :=
        (fiberProjectiveLine_constant n w fiberOrigin).symm
      _ = (u : ProjectiveCarrier n) :=
        twistorToCarrier_fiberLine_at_group n u fiberOrigin
      _ = x := hu
  obtain ⟨z, hz⟩ := (twistorToCarrier_fiber_eq_projectiveLine n w p).mp
    (by simpa [x] using hbase.symm)
  refine ⟨(⟦(u,z)⟧ : AssociatedProjectiveFiber n), ?_⟩
  simpa [associatedToAmbient, w] using hz

end
end QuaternionicSymmetry.CompactSymplecticProjectorAssociatedAmbientSurjection
