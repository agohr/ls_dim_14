import QuaternionicSymmetry.TangentAhatCharacterDensity

/-! The full tangent A-hat/virtual-character convolution in dimensions 2–10
is the checked finite density polynomial. All higher tangent coefficients
vanish from these expressions by the genuine character coefficient tables. -/
namespace QuaternionicSymmetry.TangentAhatLowerDensities
open MvPolynomial Characters FormalExponentialCoefficients
open AhatCoefficientPolynomials RecoveredLogAhat TangentAhatCharacterDensity
noncomputable section
variable {R : Type} [CommRing R] [Algebra ℚ R]

theorem old_evaluate (q : AlgebraCertificates.P) (v : Fin 6 → R) :
    aeval v (DimensionElevenTwelveDensity.old q) =
      AlgebraCertificates.evaluate (v 0) (2*v 1) (2*v 2) (2*v 3) (2*v 4) q := by
  unfold DimensionElevenTwelveDensity.old AlgebraCertificates.evaluate
  rw [comp_aeval_apply]
  apply congrArg (fun w : Fin 5 → R => aeval w q)
  funext i
  fin_cases i <;> simp [DimensionElevenTwelveDensity.u,
    DimensionElevenTwelveDensity.p1, DimensionElevenTwelveDensity.p2,
    DimensionElevenTwelveDensity.p3, DimensionElevenTwelveDensity.p4]

theorem characterDensity_2 (u : R) (t : ℕ → R) :
    characterDensity 2 u t (virtual 2) =
      aeval (standardValues 2 u t)
        (DimensionElevenTwelveDensity.old AlgebraCertificates.K₂) := by
  have h := Characters.taylor_two
  norm_num [List.range_succ] at h
  rcases h with ⟨h0, h1, h2⟩
  simp only [characterDensity, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub]
  rw [h0, h1, h2]
  simp only [map_zero, zero_mul, zero_add, add_zero]
  unfold tangentAhatCoefficient
  rw [coefficient_recovered 2 u t ⟨0, by decide⟩]
  simp only [coefficientPolynomial, DimensionElevenTwelveDensity.a0,
        old_evaluate,
    AlgebraCertificates.K₂, AlgebraCertificates.c, AlgebraCertificates.U,
    AlgebraCertificates.A₀, map_mul, map_pow, map_one,
    AlgebraCertificates.evaluate, aeval_C, aeval_X]
  simp only [show standardValues 2 u t 0 = u from rfl, Matrix.cons_val_zero]

theorem characterDensity_3 (u : R) (t : ℕ → R) :
    characterDensity 3 u t (virtual 3) =
      aeval (standardValues 3 u t)
        (DimensionElevenTwelveDensity.old AlgebraCertificates.K₃) := by
  have h := Characters.taylor_three
  norm_num [List.range_succ] at h
  rcases h with ⟨h0, h1, h2, h3⟩
  simp only [characterDensity, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub]
  rw [h0, h1, h2, h3]
  simp only [map_zero, zero_mul, zero_add, add_zero]
  unfold tangentAhatCoefficient
  rw [coefficient_recovered 3 u t ⟨0, by decide⟩]
  rw [coefficient_recovered 3 u t ⟨1, by decide⟩]
  simp only [coefficientPolynomial, DimensionElevenTwelveDensity.a0,
    DimensionElevenTwelveDensity.a1,     old_evaluate,
    AlgebraCertificates.K₃, AlgebraCertificates.c, AlgebraCertificates.U,
    AlgebraCertificates.A₀, map_add, map_mul, map_pow, map_one,
    AlgebraCertificates.evaluate, aeval_C, aeval_X]
  simp only [show standardValues 3 u t 0 = u from rfl, Nat.cast_ofNat, Matrix.cons_val_zero]
  ring

theorem characterDensity_4 (u : R) (t : ℕ → R) :
    characterDensity 4 u t (virtual 4) =
      aeval (standardValues 4 u t)
        (DimensionElevenTwelveDensity.old AlgebraCertificates.K₄) := by
  have h := Characters.taylor_four
  norm_num [List.range_succ] at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  simp only [characterDensity, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub]
  rw [h0, h1, h2, h3, h4]
  simp only [map_zero, zero_mul, zero_add, add_zero]
  unfold tangentAhatCoefficient
  rw [coefficient_recovered 4 u t ⟨0, by decide⟩]
  rw [coefficient_recovered 4 u t ⟨1, by decide⟩]
  simp only [coefficientPolynomial, DimensionElevenTwelveDensity.a0,
    DimensionElevenTwelveDensity.a1,     old_evaluate,
    AlgebraCertificates.K₄, AlgebraCertificates.c, AlgebraCertificates.U,
    AlgebraCertificates.A₀, map_add, map_mul, map_pow, map_one,
    AlgebraCertificates.evaluate, aeval_C, aeval_X]
  simp only [show standardValues 4 u t 0 = u from rfl, Nat.cast_ofNat, Matrix.cons_val_zero]
  ring

theorem characterDensity_5 (u : R) (t : ℕ → R) :
    characterDensity 5 u t (virtual 5) =
      aeval (standardValues 5 u t)
        (DimensionElevenTwelveDensity.old AlgebraCertificates.K₅) := by
  have h := Characters.taylor_five
  norm_num [List.range_succ] at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  simp only [characterDensity, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub]
  rw [h0, h1, h2, h3, h4, h5]
  simp only [map_zero, zero_mul, zero_add, add_zero]
  unfold tangentAhatCoefficient
  rw [coefficient_recovered 5 u t ⟨0, by decide⟩]
  rw [coefficient_recovered 5 u t ⟨1, by decide⟩]
  rw [coefficient_recovered 5 u t ⟨2, by decide⟩]
  simp only [coefficientPolynomial, DimensionElevenTwelveDensity.a0,
    DimensionElevenTwelveDensity.a1, DimensionElevenTwelveDensity.a2,
    old_evaluate,
    AlgebraCertificates.K₅, AlgebraCertificates.c, AlgebraCertificates.U,
    AlgebraCertificates.A₀, map_add, map_mul, map_pow, map_one,
    AlgebraCertificates.evaluate, aeval_C, aeval_X]
  simp only [show standardValues 5 u t 0 = u from rfl, Nat.cast_ofNat, Matrix.cons_val_zero]
  ring

theorem characterDensity_6 (u : R) (t : ℕ → R) :
    characterDensity 6 u t (virtual 6) =
      aeval (standardValues 6 u t)
        (DimensionElevenTwelveDensity.old AlgebraCertificates.K₆) := by
  have h := Characters.taylor_six
  norm_num [List.range_succ] at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  simp only [characterDensity, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub]
  rw [h0, h1, h2, h3, h4, h5, h6]
  simp only [map_zero, zero_mul, zero_add, add_zero]
  unfold tangentAhatCoefficient
  rw [coefficient_recovered 6 u t ⟨0, by decide⟩]
  rw [coefficient_recovered 6 u t ⟨1, by decide⟩]
  rw [coefficient_recovered 6 u t ⟨2, by decide⟩]
  simp only [coefficientPolynomial, DimensionElevenTwelveDensity.a0,
    DimensionElevenTwelveDensity.a1, DimensionElevenTwelveDensity.a2,
    old_evaluate,
    AlgebraCertificates.K₆, AlgebraCertificates.c, AlgebraCertificates.U,
    AlgebraCertificates.A₀, map_add, map_mul, map_pow, map_one,
    AlgebraCertificates.evaluate, aeval_C, aeval_X]
  simp only [show standardValues 6 u t 0 = u from rfl, Nat.cast_ofNat, Matrix.cons_val_zero]
  ring

theorem characterDensity_7 (u : R) (t : ℕ → R) :
    characterDensity 7 u t (virtual 7) =
      aeval (standardValues 7 u t)
        (DimensionElevenTwelveDensity.old AlgebraCertificates.K₇) := by
  have h := Characters.taylor_seven
  norm_num [List.range_succ] at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  simp only [characterDensity, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub]
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  simp only [map_zero, zero_mul, zero_add, add_zero]
  unfold tangentAhatCoefficient
  rw [coefficient_recovered 7 u t ⟨0, by decide⟩]
  rw [coefficient_recovered 7 u t ⟨1, by decide⟩]
  rw [coefficient_recovered 7 u t ⟨2, by decide⟩]
  rw [coefficient_recovered 7 u t ⟨3, by decide⟩]
  simp only [coefficientPolynomial, DimensionElevenTwelveDensity.a0,
    DimensionElevenTwelveDensity.a1, DimensionElevenTwelveDensity.a2,
    DimensionElevenTwelveDensity.a3, old_evaluate,
    AlgebraCertificates.K₇, AlgebraCertificates.c, AlgebraCertificates.U,
    AlgebraCertificates.A₀, map_add, map_mul, map_pow, map_one,
    AlgebraCertificates.evaluate, aeval_C, aeval_X]
  simp only [show standardValues 7 u t 0 = u from rfl, Nat.cast_ofNat, Matrix.cons_val_zero]
  ring

theorem characterDensity_8 (u : R) (t : ℕ → R) :
    characterDensity 8 u t (virtual 8) =
      aeval (standardValues 8 u t)
        (DimensionElevenTwelveDensity.old AlgebraCertificates.K₈) := by
  have h := Characters.taylor_eight
  norm_num [List.range_succ] at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp only [characterDensity, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8]
  simp only [map_zero, zero_mul, zero_add, add_zero]
  unfold tangentAhatCoefficient
  rw [coefficient_recovered 8 u t ⟨0, by decide⟩]
  rw [coefficient_recovered 8 u t ⟨1, by decide⟩]
  rw [coefficient_recovered 8 u t ⟨2, by decide⟩]
  rw [coefficient_recovered 8 u t ⟨3, by decide⟩]
  simp only [coefficientPolynomial, DimensionElevenTwelveDensity.a0,
    DimensionElevenTwelveDensity.a1, DimensionElevenTwelveDensity.a2,
    DimensionElevenTwelveDensity.a3, old_evaluate,
    AlgebraCertificates.K₈, AlgebraCertificates.c, AlgebraCertificates.U,
    AlgebraCertificates.A₀, map_add, map_mul, map_pow, map_one,
    AlgebraCertificates.evaluate, aeval_C, aeval_X]
  simp only [show standardValues 8 u t 0 = u from rfl, Nat.cast_ofNat, Matrix.cons_val_zero]
  ring

theorem characterDensity_9 (u : R) (t : ℕ → R) :
    characterDensity 9 u t (virtual 9) =
      aeval (standardValues 9 u t)
        (DimensionElevenTwelveDensity.old AlgebraCertificates.K₉) := by
  have h := Characters.taylor_nine
  norm_num [List.range_succ] at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  simp only [characterDensity, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  simp only [map_zero, zero_mul, zero_add, add_zero]
  unfold tangentAhatCoefficient
  rw [coefficient_recovered 9 u t ⟨0, by decide⟩]
  rw [coefficient_recovered 9 u t ⟨1, by decide⟩]
  rw [coefficient_recovered 9 u t ⟨2, by decide⟩]
  rw [coefficient_recovered 9 u t ⟨3, by decide⟩]
  rw [coefficient_recovered 9 u t ⟨4, by decide⟩]
  simp only [coefficientPolynomial, DimensionElevenTwelveDensity.a0,
    DimensionElevenTwelveDensity.a1, DimensionElevenTwelveDensity.a2,
    DimensionElevenTwelveDensity.a3, DimensionElevenTwelveDensity.a4, old_evaluate,
    AlgebraCertificates.K₉, AlgebraCertificates.c, AlgebraCertificates.U,
    AlgebraCertificates.A₀, map_add, map_mul, map_pow, map_one,
    AlgebraCertificates.evaluate, aeval_C, aeval_X]
  simp only [show standardValues 9 u t 0 = u from rfl, Nat.cast_ofNat, Matrix.cons_val_zero]
  ring

theorem characterDensity_10 (u : R) (t : ℕ → R) :
    characterDensity 10 u t (virtual 10) =
      aeval (standardValues 10 u t)
        (DimensionElevenTwelveDensity.old AlgebraCertificates.K₁₀) := by
  have h := Characters.taylor_ten
  norm_num [List.range_succ] at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  simp only [characterDensity, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  simp only [map_zero, zero_mul, zero_add, add_zero]
  unfold tangentAhatCoefficient
  rw [coefficient_recovered 10 u t ⟨0, by decide⟩]
  rw [coefficient_recovered 10 u t ⟨1, by decide⟩]
  rw [coefficient_recovered 10 u t ⟨2, by decide⟩]
  rw [coefficient_recovered 10 u t ⟨3, by decide⟩]
  rw [coefficient_recovered 10 u t ⟨4, by decide⟩]
  simp only [coefficientPolynomial, DimensionElevenTwelveDensity.a0,
    DimensionElevenTwelveDensity.a1, DimensionElevenTwelveDensity.a2,
    DimensionElevenTwelveDensity.a3, DimensionElevenTwelveDensity.a4, old_evaluate,
    AlgebraCertificates.K₁₀, AlgebraCertificates.c, AlgebraCertificates.U,
    AlgebraCertificates.A₀, map_add, map_mul, map_pow, map_one,
    AlgebraCertificates.evaluate, aeval_C, aeval_X]
  simp only [show standardValues 10 u t 0 = u from rfl, Nat.cast_ofNat, Matrix.cons_val_zero]
  ring

end
end QuaternionicSymmetry.TangentAhatLowerDensities
