import QuaternionicSymmetry.ManifoldSevenVariableGradedEvaluation
import QuaternionicSymmetry.H2WitnessThirteen
import QuaternionicSymmetry.H2WitnessFourteen

/-! Weighted homogeneity of the exact seven-variable printed certificates. -/

namespace QuaternionicSymmetry.ManifoldSevenVariableWeightedDensity

open QuaternionicSymmetry.DimensionThirteenFourteenDensity
open QuaternionicSymmetry.ManifoldSevenVariableGradedEvaluation
open MvPolynomial

set_option maxHeartbeats 2000000

private def coefficient13 : Fin 30 → ℚ := ![392, (45727288 / 315315), (121006364 / 5457375), (1781548 / 716625), (3397924 / 1913625), (36184556 / 49116375), (1323256 / 34827975), (9911 / 127575), (16042 / 212625), (26423 / 4465125), (284456 / 16372125), (8894 / 19348875), (19 / 10935), (1214 / 382725), (116 / 76545), (61 / 70875), (1154 / 2338875), (3596 / 13395375), (1168 / 19348875), (1 / 65610), (1 / 21870), (8 / 229635), (1 / 36450), (1 / 42525), (8 / 382725), (16 / 1403325), (1 / 546750), (1 / 212625), (16 / 8037225), (5528 / 1915538625)]
private def coefficient14 : Fin 30 → ℚ := ![448, (816577408 / 4729725), (152085968 / 5457375), (620496752 / 212837625), (655424 / 273375), (46487872 / 49116375), (10779136 / 383107725), (4904 / 42525), (23024 / 212625), (36256 / 4465125), (1084576 / 49116375), (-170152 / 212837625), (32 / 10935), (2008 / 382725), (184 / 76545), (296 / 212625), (1648 / 2338875), (5512 / 13395375), (3712 / 70945875), (1 / 32805), (1 / 10935), (16 / 229635), (1 / 18225), (2 / 42525), (16 / 382725), (32 / 1403325), (1 / 273375), (2 / 212625), (32 / 8037225), (11056 / 1915538625)]

noncomputable def pattern (k : ℕ) (a : Fin 30 → ℚ) : P :=
  C (a 0) * u ^ (k + 6)
    + C (a 1) * p1 * u ^ (k + 5)
    + C (a 2) * p1 ^ 2 * u ^ (k + 4)
    + C (a 3) * p2 * u ^ (k + 4)
    + C (a 4) * p1 ^ 3 * u ^ (k + 3)
    + C (a 5) * p1 * p2 * u ^ (k + 3)
    + C (a 6) * p3 * u ^ (k + 3)
    + C (a 7) * p1 ^ 4 * u ^ (k + 2)
    + C (a 8) * p1 ^ 2 * p2 * u ^ (k + 2)
    + C (a 9) * p2 ^ 2 * u ^ (k + 2)
    + C (a 10) * p1 * p3 * u ^ (k + 2)
    + C (a 11) * p4 * u ^ (k + 2)
    + C (a 12) * p1 ^ 5 * u ^ (k + 1)
    + C (a 13) * p1 ^ 3 * p2 * u ^ (k + 1)
    + C (a 14) * p1 ^ 2 * p3 * u ^ (k + 1)
    + C (a 15) * p1 * p2 ^ 2 * u ^ (k + 1)
    + C (a 16) * p1 * p4 * u ^ (k + 1)
    + C (a 17) * p2 * p3 * u ^ (k + 1)
    + C (a 18) * p5 * u ^ (k + 1)
    + C (a 19) * p1 ^ 6 * u ^ k
    + C (a 20) * p1 ^ 4 * p2 * u ^ k
    + C (a 21) * p1 ^ 3 * p3 * u ^ k
    + C (a 22) * p1 ^ 2 * p2 ^ 2 * u ^ k
    + C (a 23) * p1 ^ 2 * p4 * u ^ k
    + C (a 24) * p1 * p2 * p3 * u ^ k
    + C (a 25) * p1 * p5 * u ^ k
    + C (a 26) * p2 ^ 3 * u ^ k
    + C (a 27) * p2 * p4 * u ^ k
    + C (a 28) * p3 ^ 2 * u ^ k
    + C (a 29) * p6 * u ^ k

theorem pattern_weighted (k : ℕ) (a : Fin 30 → ℚ) :
    IsWeightedHomogeneous slotGrade (pattern k a) (k + 6) := by
  have h0 : IsWeightedHomogeneous slotGrade u 1 := by
    exact isWeightedHomogeneous_X (R := ℚ) slotGrade 0
  have h1 : IsWeightedHomogeneous slotGrade p1 1 := by
    exact isWeightedHomogeneous_X (R := ℚ) slotGrade 1
  have h2 : IsWeightedHomogeneous slotGrade p2 2 := by
    exact isWeightedHomogeneous_X (R := ℚ) slotGrade 2
  have h3 : IsWeightedHomogeneous slotGrade p3 3 := by
    exact isWeightedHomogeneous_X (R := ℚ) slotGrade 3
  have h4 : IsWeightedHomogeneous slotGrade p4 4 := by
    exact isWeightedHomogeneous_X (R := ℚ) slotGrade 4
  have h5 : IsWeightedHomogeneous slotGrade p5 5 := by
    exact isWeightedHomogeneous_X (R := ℚ) slotGrade 5
  have h6 : IsWeightedHomogeneous slotGrade p6 6 := by
    exact isWeightedHomogeneous_X (R := ℚ) slotGrade 6
  have ht0 : IsWeightedHomogeneous slotGrade (C (a 0) * u ^ (k + 6)) (k + 6) := by
    convert (isWeightedHomogeneous_C slotGrade (a 0)).mul (h0.pow (k + 6)) using 1
    all_goals simp
  have ht1 : IsWeightedHomogeneous slotGrade (C (a 1) * p1 * u ^ (k + 5)) (k + 6) := by
    convert ((h1).C_mul (a 1)).mul (h0.pow (k + 5)) using 1
    all_goals (first | (solve | simp) | ring)
  have ht2 : IsWeightedHomogeneous slotGrade (C (a 2) * p1 ^ 2 * u ^ (k + 4)) (k + 6) := by
    convert ((h1.pow 2).C_mul (a 2)).mul (h0.pow (k + 4)) using 1
    all_goals (first | (solve | simp) | ring)
  have ht3 : IsWeightedHomogeneous slotGrade (C (a 3) * p2 * u ^ (k + 4)) (k + 6) := by
    convert ((h2).C_mul (a 3)).mul (h0.pow (k + 4)) using 1
    all_goals (first | (solve | simp) | ring)
  have ht4 : IsWeightedHomogeneous slotGrade (C (a 4) * p1 ^ 3 * u ^ (k + 3)) (k + 6) := by
    convert ((h1.pow 3).C_mul (a 4)).mul (h0.pow (k + 3)) using 1
    all_goals (first | (solve | simp) | ring)
  have ht5 : IsWeightedHomogeneous slotGrade (C (a 5) * p1 * p2 * u ^ (k + 3)) (k + 6) := by
    convert (((h1).mul (h2)).C_mul (a 5)).mul (h0.pow (k + 3)) using 1
    all_goals (first | (solve | simp) | ring)
  have ht6 : IsWeightedHomogeneous slotGrade (C (a 6) * p3 * u ^ (k + 3)) (k + 6) := by
    convert ((h3).C_mul (a 6)).mul (h0.pow (k + 3)) using 1
    all_goals (first | (solve | simp) | ring)
  have ht7 : IsWeightedHomogeneous slotGrade (C (a 7) * p1 ^ 4 * u ^ (k + 2)) (k + 6) := by
    convert ((h1.pow 4).C_mul (a 7)).mul (h0.pow (k + 2)) using 1
    all_goals (first | (solve | simp) | ring)
  have ht8 : IsWeightedHomogeneous slotGrade (C (a 8) * p1 ^ 2 * p2 * u ^ (k + 2)) (k + 6) := by
    convert (((h1.pow 2).mul (h2)).C_mul (a 8)).mul (h0.pow (k + 2)) using 1
    all_goals (first | (solve | simp) | ring)
  have ht9 : IsWeightedHomogeneous slotGrade (C (a 9) * p2 ^ 2 * u ^ (k + 2)) (k + 6) := by
    convert ((h2.pow 2).C_mul (a 9)).mul (h0.pow (k + 2)) using 1
    all_goals (first | (solve | simp) | ring)
  have ht10 : IsWeightedHomogeneous slotGrade (C (a 10) * p1 * p3 * u ^ (k + 2)) (k + 6) := by
    convert (((h1).mul (h3)).C_mul (a 10)).mul (h0.pow (k + 2)) using 1
    all_goals (first | (solve | simp) | ring)
  have ht11 : IsWeightedHomogeneous slotGrade (C (a 11) * p4 * u ^ (k + 2)) (k + 6) := by
    convert ((h4).C_mul (a 11)).mul (h0.pow (k + 2)) using 1
    all_goals (first | (solve | simp) | ring)
  have ht12 : IsWeightedHomogeneous slotGrade (C (a 12) * p1 ^ 5 * u ^ (k + 1)) (k + 6) := by
    convert ((h1.pow 5).C_mul (a 12)).mul (h0.pow (k + 1)) using 1
    all_goals (first | (solve | simp) | ring)
  have ht13 : IsWeightedHomogeneous slotGrade (C (a 13) * p1 ^ 3 * p2 * u ^ (k + 1)) (k + 6) := by
    convert (((h1.pow 3).mul (h2)).C_mul (a 13)).mul (h0.pow (k + 1)) using 1
    all_goals (first | (solve | simp) | ring)
  have ht14 : IsWeightedHomogeneous slotGrade (C (a 14) * p1 ^ 2 * p3 * u ^ (k + 1)) (k + 6) := by
    convert (((h1.pow 2).mul (h3)).C_mul (a 14)).mul (h0.pow (k + 1)) using 1
    all_goals (first | (solve | simp) | ring)
  have ht15 : IsWeightedHomogeneous slotGrade (C (a 15) * p1 * p2 ^ 2 * u ^ (k + 1)) (k + 6) := by
    convert (((h1).mul (h2.pow 2)).C_mul (a 15)).mul (h0.pow (k + 1)) using 1
    all_goals (first | (solve | simp) | ring)
  have ht16 : IsWeightedHomogeneous slotGrade (C (a 16) * p1 * p4 * u ^ (k + 1)) (k + 6) := by
    convert (((h1).mul (h4)).C_mul (a 16)).mul (h0.pow (k + 1)) using 1
    all_goals (first | (solve | simp) | ring)
  have ht17 : IsWeightedHomogeneous slotGrade (C (a 17) * p2 * p3 * u ^ (k + 1)) (k + 6) := by
    convert (((h2).mul (h3)).C_mul (a 17)).mul (h0.pow (k + 1)) using 1
    all_goals (first | (solve | simp) | ring)
  have ht18 : IsWeightedHomogeneous slotGrade (C (a 18) * p5 * u ^ (k + 1)) (k + 6) := by
    convert ((h5).C_mul (a 18)).mul (h0.pow (k + 1)) using 1
    all_goals (first | (solve | simp) | ring)
  have ht19 : IsWeightedHomogeneous slotGrade (C (a 19) * p1 ^ 6 * u ^ k) (k + 6) := by
    convert ((h1.pow 6).C_mul (a 19)).mul (h0.pow k) using 1
    all_goals (first | (solve | simp) | ring)
  have ht20 : IsWeightedHomogeneous slotGrade (C (a 20) * p1 ^ 4 * p2 * u ^ k) (k + 6) := by
    convert (((h1.pow 4).mul (h2)).C_mul (a 20)).mul (h0.pow k) using 1
    all_goals (first | (solve | simp) | ring)
  have ht21 : IsWeightedHomogeneous slotGrade (C (a 21) * p1 ^ 3 * p3 * u ^ k) (k + 6) := by
    convert (((h1.pow 3).mul (h3)).C_mul (a 21)).mul (h0.pow k) using 1
    all_goals (first | (solve | simp) | ring)
  have ht22 : IsWeightedHomogeneous slotGrade (C (a 22) * p1 ^ 2 * p2 ^ 2 * u ^ k) (k + 6) := by
    convert (((h1.pow 2).mul (h2.pow 2)).C_mul (a 22)).mul (h0.pow k) using 1
    all_goals (first | (solve | simp) | ring)
  have ht23 : IsWeightedHomogeneous slotGrade (C (a 23) * p1 ^ 2 * p4 * u ^ k) (k + 6) := by
    convert (((h1.pow 2).mul (h4)).C_mul (a 23)).mul (h0.pow k) using 1
    all_goals (first | (solve | simp) | ring)
  have ht24 : IsWeightedHomogeneous slotGrade (C (a 24) * p1 * p2 * p3 * u ^ k) (k + 6) := by
    convert ((((h1).mul (h2)).mul (h3)).C_mul (a 24)).mul (h0.pow k) using 1
    all_goals (first | (solve | simp) | ring)
  have ht25 : IsWeightedHomogeneous slotGrade (C (a 25) * p1 * p5 * u ^ k) (k + 6) := by
    convert (((h1).mul (h5)).C_mul (a 25)).mul (h0.pow k) using 1
    all_goals (first | (solve | simp) | ring)
  have ht26 : IsWeightedHomogeneous slotGrade (C (a 26) * p2 ^ 3 * u ^ k) (k + 6) := by
    convert ((h2.pow 3).C_mul (a 26)).mul (h0.pow k) using 1
    all_goals (first | (solve | simp) | ring)
  have ht27 : IsWeightedHomogeneous slotGrade (C (a 27) * p2 * p4 * u ^ k) (k + 6) := by
    convert (((h2).mul (h4)).C_mul (a 27)).mul (h0.pow k) using 1
    all_goals (first | (solve | simp) | ring)
  have ht28 : IsWeightedHomogeneous slotGrade (C (a 28) * p3 ^ 2 * u ^ k) (k + 6) := by
    convert ((h3.pow 2).C_mul (a 28)).mul (h0.pow k) using 1
    all_goals (first | (solve | simp) | ring)
  have ht29 : IsWeightedHomogeneous slotGrade (C (a 29) * p6 * u ^ k) (k + 6) := by
    convert ((h6).C_mul (a 29)).mul (h0.pow k) using 1
    all_goals (first | (solve | simp) | ring)
  unfold pattern
  exact (((((((((((((((((((((((((((((ht0).add ht1).add ht2).add ht3).add ht4).add ht5).add ht6).add ht7).add ht8).add ht9).add ht10).add ht11).add ht12).add ht13).add ht14).add ht15).add ht16).add ht17).add ht18).add ht19).add ht20).add ht21).add ht22).add ht23).add ht24).add ht25).add ht26).add ht27).add ht28).add ht29

private theorem printed13_eq_pattern : printed13 = pattern 7 coefficient13 := by
  unfold printed13 q13 pattern coefficient13
  dsimp
  ring

theorem printed13_weighted :
    IsWeightedHomogeneous slotGrade printed13 13 := by
  rw [printed13_eq_pattern]
  simpa using pattern_weighted 7 coefficient13

theorem density13_weighted :
    IsWeightedHomogeneous slotGrade density13 13 := by
  rw [density13_printed]
  exact printed13_weighted

private theorem printed14_eq_pattern : printed14 = pattern 8 coefficient14 := by
  unfold printed14 q14 pattern coefficient14
  dsimp
  have hc : (C (-170152 / 212837625) : P) =
      - C (170152 / 212837625) := by norm_num
  rw [hc]
  ring

theorem printed14_weighted :
    IsWeightedHomogeneous slotGrade printed14 14 := by
  rw [printed14_eq_pattern]
  simpa using pattern_weighted 8 coefficient14

theorem density14_weighted :
    IsWeightedHomogeneous slotGrade density14 14 := by
  rw [density14_printed]
  exact printed14_weighted

private theorem factor_pattern_weighted (a b c d : ℚ) :
    IsWeightedHomogeneous slotGrade
      (C a * p1 * u ^ 2 + C b * p3 + C c * p1 * p2 + C d * p1 ^ 3) 3 := by
  have hu : IsWeightedHomogeneous slotGrade u 1 :=
    isWeightedHomogeneous_X (R := ℚ) slotGrade 0
  have h1 : IsWeightedHomogeneous slotGrade p1 1 :=
    isWeightedHomogeneous_X (R := ℚ) slotGrade 1
  have h2 : IsWeightedHomogeneous slotGrade p2 2 :=
    isWeightedHomogeneous_X (R := ℚ) slotGrade 2
  have h3 : IsWeightedHomogeneous slotGrade p3 3 :=
    isWeightedHomogeneous_X (R := ℚ) slotGrade 3
  have ha : IsWeightedHomogeneous slotGrade (C a * p1 * u ^ 2) 3 := by
    convert (h1.C_mul a).mul (hu.pow 2) using 1
  have hb : IsWeightedHomogeneous slotGrade (C b * p3) 3 := h3.C_mul b
  have hc : IsWeightedHomogeneous slotGrade (C c * p1 * p2) 3 := by
    convert (h1.mul h2).C_mul c using 1
    all_goals (first | (solve | simp) | ring)
  have hd : IsWeightedHomogeneous slotGrade (C d * p1 ^ 3) 3 :=
    (h1.pow 3).C_mul d
  exact ((ha.add hb).add hc).add hd

private theorem factor13_eq : QuaternionicSymmetry.H2WitnessThirteen.factor =
    C (999999993 / 1000000000 : ℚ) * p1 * u ^ 2 +
    C (29552 / 1000000000 : ℚ) * p3 +
    C (83790 / 1000000000 : ℚ) * p1 * p2 +
    C (74653 / 1000000000 : ℚ) * p1 ^ 3 := by
  unfold QuaternionicSymmetry.H2WitnessThirteen.factor
    QuaternionicSymmetry.H2WitnessThirteen.f1
    QuaternionicSymmetry.H2WitnessThirteen.f3
    QuaternionicSymmetry.H2WitnessThirteen.embed
  simp [QuaternionicSymmetry.FiniteTypeCSchurSix.p1,
    QuaternionicSymmetry.FiniteTypeCSchurSix.p2,
    QuaternionicSymmetry.FiniteTypeCSchurSix.p3]
  ring

private theorem factor14_eq : QuaternionicSymmetry.H2WitnessFourteen.factor =
    p1 * u ^ 2 +
    C (88656 / 1000000000 : ℚ) * p3 +
    C (251370 / 1000000000 : ℚ) * p1 * p2 +
    C (223959 / 1000000000 : ℚ) * p1 ^ 3 := by
  unfold QuaternionicSymmetry.H2WitnessFourteen.factor
    QuaternionicSymmetry.H2WitnessFourteen.f1
    QuaternionicSymmetry.H2WitnessFourteen.f3
    QuaternionicSymmetry.H2WitnessFourteen.embed
    QuaternionicSymmetry.H2WitnessThirteen.embed
  simp [QuaternionicSymmetry.FiniteTypeCSchurSix.p1,
    QuaternionicSymmetry.FiniteTypeCSchurSix.p2,
    QuaternionicSymmetry.FiniteTypeCSchurSix.p3]
  ring

/-- The dimension-thirteen Hodge-square factor is an H¹² expression. -/
theorem factor13_weighted :
    IsWeightedHomogeneous slotGrade QuaternionicSymmetry.H2WitnessThirteen.factor 3 := by
  rw [factor13_eq]
  exact factor_pattern_weighted _ _ _ _

/-- The dimension-fourteen Hodge-square factor is an H¹² expression. -/
theorem factor14_weighted :
    IsWeightedHomogeneous slotGrade QuaternionicSymmetry.H2WitnessFourteen.factor 3 := by
  rw [factor14_eq]
  have h := factor_pattern_weighted (1 : ℚ) (88656 / 1000000000)
    (251370 / 1000000000) (223959 / 1000000000)
  simpa only [map_one, one_mul] using h

end QuaternionicSymmetry.ManifoldSevenVariableWeightedDensity
