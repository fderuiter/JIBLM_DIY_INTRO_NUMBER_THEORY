import Init.Data.Int.DivMod.Lemmas

namespace JIBLM_DIY_INTRO_NUMBER_THEORY

/-- Starter theorem for chapter 1. -/
theorem one_dvd_one : (1 : Int) ∣ (1 : Int) := by
  simp

/-- Exercise 1.1: The only units in `ℤ` are `1` and `-1`. -/
theorem int_unit_eq_one_or_neg_one {u : Int} (hu : u ∣ (1 : Int)) : u = 1 ∨ u = -1 := by
  by_cases hnonneg : 0 ≤ u
  · exact Or.inl (Int.eq_one_of_dvd_one hnonneg hu)
  · have hneg : u < 0 := Int.lt_of_not_ge hnonneg
    have hnegdvd : -u ∣ (1 : Int) := by
      simpa using (Int.neg_dvd.2 hu)
    have hneg_nonneg : 0 ≤ -u := Int.neg_nonneg.2 (Int.le_of_lt hneg)
    have hnegu_eq_one : -u = 1 := Int.eq_one_of_dvd_one hneg_nonneg hnegdvd
    have hu_eq_neg_one : u = -1 := by
      calc
        u = -(-u) := by simp
        _ = -1 := by simp [hnegu_eq_one]
    exact Or.inr hu_eq_neg_one

/-- Exercise 1.1: Any unit in `ℤ` divides every integer. -/
theorem int_unit_dvd_every_int {u n : Int} (hu : u ∣ (1 : Int)) : u ∣ n := by
  rcases int_unit_eq_one_or_neg_one hu with rfl | rfl <;> simp

/-- Exercise 1.2: If `a = u * b` for a unit `u` in `ℤ`, then `b = v * a` for a unit `v` in `ℤ`. -/
theorem int_associates_symm_of_unit_mul {a b u : Int} (hu : u ∣ (1 : Int)) (h : a = u * b) :
    ∃ v : Int, v ∣ (1 : Int) ∧ b = v * a := by
  rcases int_unit_eq_one_or_neg_one hu with rfl | rfl
  · have hab : a = b := by simpa using h
    refine ⟨1, by simp, ?_⟩
    simpa using hab.symm
  · have hab : a = -b := by simpa using h
    refine ⟨-1, by simp, ?_⟩
    have hba : b = -a := by
      calc
        b = -(-b) := by simp
        _ = -a := by simp [hab]
    simpa using hba

end JIBLM_DIY_INTRO_NUMBER_THEORY
