import QuaternionicSymmetry.CompactSymplecticProjectorTwistorPhaseNorm

/-! Exact unit-column fiber criterion: two unit complex columns define the
same quaternionic line precisely when a unit quaternionic phase relates
them. Projectivizing its `(a,b)` parameters is the remaining CP¹ step. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorTwistorUnitFiber

open CompactSymplecticProjectorFirstColumn
open CompactSymplecticProjectorColumnPhase
open CompactSymplecticProjectorColumnUnit
open CompactSymplecticProjectorColumnSphereMap
open CompactSymplecticProjectorTwistorNormalized
open CompactSymplecticProjectorTwistorPhaseNorm
open CompactSymplecticProjectorTwistorFiberSpan

noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev EV (n : ℕ) := EuclideanSpace ℂ (I n)

theorem same_unitProjector_iff_unitQuaternionicPhase (n : ℕ)
    (v w : Metric.sphere (0 : EV n) 1) :
    sphereColumnProjector n v = sphereColumnProjector n w ↔
      ∃ a b : ℂ, star a * a + star b * b = 1 ∧
        ((EuclideanSpace.equiv (I n) ℂ) w.1) =
          phaseRotate n a b ((EuclideanSpace.equiv (I n) ℂ) v.1) := by
  constructor
  · intro h
    obtain ⟨a,b,hab⟩ := same_unitProjector_implies_span n v w h
    have hv : columnNormSq n ((EuclideanSpace.equiv (I n) ℂ) v.1) = 1 := by
      simpa [columnNormSq] using unit_column_dot_self n v
    have hw : columnNormSq n ((EuclideanSpace.equiv (I n) ℂ) w.1) = 1 := by
      simpa [columnNormSq] using unit_column_dot_self n w
    have hphase : ((EuclideanSpace.equiv (I n) ℂ) w.1) =
        phaseRotate n a b ((EuclideanSpace.equiv (I n) ℂ) v.1) := hab
    rw [hphase, columnNormSq_phaseRotate, hv, mul_one] at hw
    exact ⟨a,b,hw,hphase⟩
  · rintro ⟨a,b,hab,hphase⟩
    change columnProjector n ((EuclideanSpace.equiv (I n) ℂ) v.1) =
      columnProjector n ((EuclideanSpace.equiv (I n) ℂ) w.1)
    rw [hphase, columnProjector_phaseRotate n a b _ hab]

end
end QuaternionicSymmetry.CompactSymplecticProjectorTwistorUnitFiber
