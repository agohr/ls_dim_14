import QuaternionicSymmetry.CompactSymplecticProjectorTwistorFiberConverse

/-! Every fiber of the concrete CP-to-HP map over the point represented by
a unit complex column is exactly the image of its embedded CP¹. This is a
set-theoretic fiber identification, not yet a holomorphic bundle theorem. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorTwistorExactFiber

open CompactSymplecticProjectorFirstColumn
open CompactSymplecticProjectorColumnUnit
open CompactSymplecticProjectorTwistorNormalized
open CompactSymplecticProjectorTwistorProjection
open CompactSymplecticProjectorTwistorCarrierMap
open CompactSymplecticProjectorTwistorFiberLine
open CompactSymplecticProjectorTwistorFiberConstant
open CompactSymplecticProjectorTwistorFiberConverse
open CompactSymplecticProjectorOrbitQuotient
open scoped LinearAlgebra.Projectivization

noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev V (n : ℕ) := I n → ℂ
private abbrev EV (n : ℕ) := EuclideanSpace ℂ (I n)

private theorem unit_normalizedProjector (n : ℕ)
    (w : Metric.sphere (0 : EV n) 1) :
    normalizedProjector n ((EuclideanSpace.equiv (I n) ℂ) w.1) =
      columnProjector n ((EuclideanSpace.equiv (I n) ℂ) w.1) := by
  have hn : columnNormSq n ((EuclideanSpace.equiv (I n) ℂ) w.1) = 1 := by
    simpa [columnNormSq] using unit_column_dot_self n w
  simp [normalizedProjector, hn]

theorem twistorToCarrier_fiber_eq_projectiveLine (n : ℕ)
    (w : Metric.sphere (0 : EV n) 1)
    (p : ℙ ℂ (V n)) :
    twistorToCarrier n p =
        twistorToCarrier n
          (Projectivization.mk ℂ ((EuclideanSpace.equiv (I n) ℂ) w.1) (by
            intro hz
            have hw : w.1 = 0 := (EuclideanSpace.equiv (I n) ℂ).injective hz
            have hn := mem_sphere_zero_iff_norm.mp w.2
            simp [hw] at hn)) ↔
      p ∈ Set.range (fiberProjectiveLine n w) := by
  constructor
  · intro heq
    induction p using Projectivization.ind with
    | h y hy =>
      let u : V n := (EuclideanSpace.equiv (I n) ℂ) w.1
      have hproj := congrArg (quotientOrbitProjector n) heq
      rw [carrier_projector_twistorToCarrier,
        carrier_projector_twistorToCarrier,
        projectiveProjector_mk, projectiveProjector_mk] at hproj
      obtain ⟨a,b,hspan⟩ := same_normalizedProjector_implies_span n u y hy
        hproj.symm
      let z : Fin 2 → ℂ := fun i => if i = 0 then a else b
      have hmap : fiberLineMap n w z = y := by
        simpa [fiberLineMap, CompactSymplecticProjectorColumnPhase.phaseRotate,
          z, u] using hspan.symm
      have hz : z ≠ 0 := by
        intro hz
        rw [hz, map_zero] at hmap
        exact hy hmap.symm
      refine ⟨Projectivization.mk ℂ z hz, ?_⟩
      simp [fiberProjectiveLine, Projectivization.map_mk, hmap]
  · rintro ⟨z,rfl⟩
    exact fiberProjectiveLine_constant n w z

end
end QuaternionicSymmetry.CompactSymplecticProjectorTwistorExactFiber
