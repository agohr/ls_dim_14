import Mathlib.Topology.Instances.RatLemmas
import Mathlib.Topology.NhdsWithin
import Mathlib.Algebra.Ring.Rat

/-! A nonempty open cone in a finite real coordinate space contains an
integer point. This is the rational-density/denominator-clearing step used
to expose finite integral weight-polytope vertices. -/

namespace QuaternionicSymmetry.TorusRationalConeIntegralPoint

open Set
noncomputable section

variable {r : ℕ}

private theorem rational_vector_dense :
    DenseRange (fun q : Fin r → ℚ => (fun i => (q i : ℝ))) := by
  exact DenseRange.piMap (fun _ : Fin r => Rat.denseRange_cast)

theorem exists_integer_of_open_cone
    (U : Set (Fin r → ℝ)) (hOpen : IsOpen U) (hNonempty : U.Nonempty)
    (hCone : ∀ a : ℝ, 0 < a → ∀ x ∈ U, a • x ∈ U) :
    ∃ u : Fin r → ℤ, (fun i => (u i : ℝ)) ∈ U := by
  classical
  obtain ⟨q, hq⟩ := rational_vector_dense.exists_mem_open hOpen hNonempty
  let N : ℕ := ∏ i : Fin r, (q i).den
  have hN : 0 < N := Finset.prod_pos fun i _ => (q i).den_pos
  have hDiv (i : Fin r) : (q i).den ∣ N := by
    simpa [N] using
      (Finset.dvd_prod_of_mem (fun j : Fin r => (q j).den) (Finset.mem_univ i))
  let u : Fin r → ℤ := fun i => (q i).num * (N / (q i).den)
  refine ⟨u, ?_⟩
  convert hCone (N : ℝ) (by exact_mod_cast hN) _ hq using 1
  ext i
  have hd : (q i).den * (N / (q i).den) = N := Nat.mul_div_cancel' (hDiv i)
  have hden : ((q i).den : ℝ) ≠ 0 := by exact_mod_cast (q i).den_nz
  change ((q i).num * (N / (q i).den) : ℤ) = (N : ℝ) * (q i : ℝ)
  rw [Rat.cast_def]
  push_cast
  field_simp
  have hdR : ((q i).den : ℝ) * ((N / (q i).den : ℕ) : ℝ) = (N : ℝ) :=
    by exact_mod_cast hd
  calc
    ((q i).num : ℝ) * ↑(N / (q i).den) * ↑(q i).den =
        ((q i).num : ℝ) * (↑(q i).den * ↑(N / (q i).den)) := by ring
    _ = ((q i).num : ℝ) * ↑N := by rw [hdR]

end
end QuaternionicSymmetry.TorusRationalConeIntegralPoint
