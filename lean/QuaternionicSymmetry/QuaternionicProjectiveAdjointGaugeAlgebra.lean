import QuaternionicSymmetry.QuaternionicManifoldProjectiveAdjointConnection

/-! Algebra behind affine gauge descent of the projective adjoint
connection.  The derivative of an inverse gauge contributes the commutator
with the Maurer–Cartan term. -/

namespace QuaternionicSymmetry.QuaternionicProjectiveAdjointGaugeAlgebra

theorem commutator_affine {R : Type*} [Ring R]
    (g h Γ dg dh B : R)
    (hh : h * g = 1)
    (hd : dh * g = -(h * dg)) :
    (h * (Γ * g + dg)) * B - B * (h * (Γ * g + dg)) =
      h * (Γ * (g * B * h) - (g * B * h) * Γ) * g +
        h * (dg * B * h + g * B * dh) * g := by
  have hc (X : R) : X * h * g = X := by rw [mul_assoc, hh, mul_one]
  have h1 : h * (Γ * (g * B * h)) * g = h * (Γ * (g * B)) := by
    calc
      _ = (h * (Γ * (g * B))) * h * g := by noncomm_ring
      _ = _ := hc _
  have h2 : h * ((g * B * h) * Γ) * g = B * (h * (Γ * g)) := by
    calc
      _ = (h * g) * (B * (h * (Γ * g))) := by noncomm_ring
      _ = _ := by rw [hh, one_mul]
  have h3 : h * (dg * B * h) * g = h * (dg * B) := by
    calc
      _ = (h * (dg * B)) * h * g := by noncomm_ring
      _ = _ := hc _
  have h4 : h * (g * B * dh) * g = -(B * (h * dg)) := by
    calc
      _ = (h * g) * B * (dh * g) := by noncomm_ring
      _ = B * -(h * dg) := by rw [hh, one_mul, hd]
      _ = _ := by simp
  simp only [mul_add, add_mul, mul_sub, sub_mul, h1, h2, h3, h4]
  noncomm_ring

end QuaternionicSymmetry.QuaternionicProjectiveAdjointGaugeAlgebra
