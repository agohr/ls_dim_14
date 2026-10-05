import QuaternionicSymmetry.CompactSymplecticProjectorTwistorExactFiber
import QuaternionicSymmetry.ComplexProjectiveTopology

/-! The embedded CP¹ fiber parametrizations are continuous for the actual
quotient topologies on both complex projective spaces. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorTwistorFiberContinuous

open CompactSymplecticProjectorTwistorFiberLine
open ComplexProjectiveTopology
open scoped LinearAlgebra.Projectivization

noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev V (n : ℕ) := I n → ℂ
private abbrev EV (n : ℕ) := EuclideanSpace ℂ (I n)

theorem continuous_fiberProjectiveLine (n : ℕ)
    (w : Metric.sphere (0 : EV n) 1) :
    Continuous (fiberProjectiveLine n w) := by
  apply (isQuotientMap_quotient_mk' : Topology.IsQuotientMap
    (Projectivization.mk' ℂ : {z : Fin 2 → ℂ // z ≠ 0} →
      ℙ ℂ (Fin 2 → ℂ))).continuous_iff.mpr
  have hlin : Continuous (fiberLineMap n w) :=
    (fiberLineMap n w).continuous_of_finiteDimensional
  have hsub : Continuous (fun z : {z : Fin 2 → ℂ // z ≠ 0} =>
      (⟨fiberLineMap n w z.1,
        (by simpa using (fiberLineMap_injective n w).ne z.2)⟩ :
          {v : V n // v ≠ 0})) :=
    (hlin.comp continuous_subtype_val).subtype_mk _
  have hmk : Continuous
      (Projectivization.mk' ℂ : {v : V n // v ≠ 0} → ℙ ℂ (V n)) :=
    continuous_quotient_mk'
  convert hmk.comp hsub using 1

end
end QuaternionicSymmetry.CompactSymplecticProjectorTwistorFiberContinuous
