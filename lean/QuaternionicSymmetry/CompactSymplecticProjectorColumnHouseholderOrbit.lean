import QuaternionicSymmetry.CompactSymplecticProjectorColumnHouseholderAction

/-! The explicit Householder reflection places every real-first-pair unit
column projector in the actual compact-symplectic projector orbit. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorColumnHouseholderOrbit

open Matrix CompactSymplecticProjectorFirstColumn
open CompactSymplecticProjectorColumnHouseholderNorm
open CompactSymplecticProjectorColumnHouseholderUnit
open CompactSymplecticProjectorColumnHouseholderAction
open CompactSymplecticProjectorColumnReflection
open CompactSymplecticProjectorOrbit
open CompactSymplecticProjectorOrbitQuotient
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev V (n : ℕ) := EuclideanSpace ℂ (I n)

theorem pairedColumn_neg (n : ℕ) (v : I n → ℂ) :
    pairedColumn n (-v) = -pairedColumn n v := by
  funext i
  cases i <;> simp [pairedColumn]

theorem columnProjector_neg (n : ℕ) (v : I n → ℂ) :
    columnProjector n (-v) = columnProjector n v := by
  ext i j
  simp [columnProjector, pairedColumn_neg, Pi.neg_apply]

theorem firstColumn_one (n : ℕ) :
    firstColumn n (1 : CompactSymplecticHaar.Group (n + 1)) =
      (EuclideanSpace.equiv (I n) ℂ) (baseColumn n) := by
  funext i
  change (1 : Matrix (I n) (I n) ℂ) i (Sum.inl 0) =
    (EuclideanSpace.equiv (I n) ℂ) (baseColumn n) i
  simp [baseColumn, EuclideanSpace.single_apply, Matrix.one_apply]

theorem realGauge_columnProjector_mem_orbit (n : ℕ)
    (w : Metric.sphere (0 : V n) 1) (r : ℝ)
    (hfirst : w.1 (Sum.inl 0) = (r : ℂ))
    (hsecond : w.1 (Sum.inr 0) = 0) :
    columnProjector n ((EuclideanSpace.equiv (I n) ℂ) w.1) ∈ projectorOrbit n := by
  by_cases hw : w.1 = baseColumn n
  · refine ⟨1, ?_⟩
    rw [orbitProjector_eq_columnProjector, firstColumn_one]
    rw [hw]
  · let u := unitColumnReflection n (householderUnit n w hw)
    refine ⟨u, ?_⟩
    rw [orbitProjector_eq_columnProjector]
    have hcol : firstColumn n u =
        -(EuclideanSpace.equiv (I n) ℂ) w.1 := by
      funext i
      exact householderReflection_firstColumn n w r hfirst hsecond hw i
    rw [hcol, columnProjector_neg]

end
end QuaternionicSymmetry.CompactSymplecticProjectorColumnHouseholderOrbit
