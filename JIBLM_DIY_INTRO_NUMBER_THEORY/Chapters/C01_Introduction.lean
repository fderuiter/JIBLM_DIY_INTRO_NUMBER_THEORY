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

/-- Definition: `a` and `b` are associates in `ℤ` if `a = u * b` for some unit `u` in `ℤ`. -/
def int_associates (a b : Int) : Prop :=
  ∃ u : Int, u ∣ (1 : Int) ∧ a = u * b

/-- Exercise 1.3: In `ℤ`, two integers are associates iff each divides the other. -/
theorem int_associates_iff_dvd_dvd {a b : Int} :
    int_associates a b ↔ a ∣ b ∧ b ∣ a := by
  constructor
  · intro h
    rcases h with ⟨u, hu, hab⟩
    rcases int_associates_symm_of_unit_mul hu hab with ⟨v, _hv, hba⟩
    refine ⟨⟨v, hba⟩, ⟨u, ?_⟩⟩
    simpa [mul_comm] using hab
  · intro h
    rcases h with ⟨hab, hba⟩
    rcases hab with ⟨m, hbm⟩
    rcases hba with ⟨n, han⟩
    by_cases hb0 : b = 0
    · have ha0 : a = 0 := by simpa [hb0] using han
      refine ⟨1, by simp, ?_⟩
      simp [ha0, hb0]
    · have hone : 1 = m * n := by
        have hbcalc : b = b * (m * n) := by
          calc
            b = a * m := hbm
            _ = (b * n) * m := by simpa [han]
            _ = b * (m * n) := by simp [mul_assoc, mul_comm, mul_left_comm]
        have hbmul : b * 1 = b * (m * n) := by simpa using hbcalc
        exact mul_left_cancel₀ hb0 hbmul
      refine ⟨n, ?_, ?_⟩
      · refine ⟨m, ?_⟩
        simpa [mul_comm] using hone
      · simpa [mul_comm] using han

/-- Exercise 1.4: The associates of `a` in `ℤ` are exactly `a` and `-a`. -/
theorem int_associates_iff_eq_or_eq_neg {a b : Int} :
    int_associates a b ↔ a = b ∨ a = -b := by
  constructor
  · intro h
    rcases h with ⟨u, hu, hab⟩
    rcases int_unit_eq_one_or_neg_one hu with hu' | hu'
    · left
      simpa [hu'] using hab
    · right
      simpa [hu'] using hab
  · intro h
    rcases h with hab | hab
    · refine ⟨1, by simp, ?_⟩
      simpa [hab]
    · refine ⟨-1, by simp, ?_⟩
      simpa [hab]

/-- Exercise 1.5: Every integer has the form `2q + r` with `r = 0` or `r = 1`. -/
theorem int_two_mul_add_zero_or_one {a : Int} :
    ∃ q r : Int, (r = 0 ∨ r = 1) ∧ a = 2 * q + r := by
  refine ⟨a / 2, a % 2, ?_, ?_⟩
  · simpa using Int.emod_two_eq_zero_or_one a
  · simpa [mul_comm, mul_left_comm, mul_assoc] using (Int.ediv_add_emod a 2).symm

/-- Exercise 1.6: Every integer has the form `3q + r` with `r = 0`, `1`, or `2`. -/
theorem int_three_mul_add_zero_one_or_two {a : Int} :
    ∃ q r : Int, (r = 0 ∨ r = 1 ∨ r = 2) ∧ a = 3 * q + r := by
  refine ⟨a / 3, a % 3, ?_, ?_⟩
  · simpa using Int.emod_three_eq_zero_or_one_or_two a
  · simpa [mul_comm, mul_left_comm, mul_assoc] using (Int.ediv_add_emod a 3).symm

/-- Exercise 1.7: Division algorithm in `ℤ` for positive divisor. -/
theorem int_division_algorithm {a b : Int} (hb : 0 < b) :
    ∃ q r : Int, 0 ≤ r ∧ r < b ∧ a = b * q + r := by
  refine ⟨a / b, a % b, Int.emod_nonneg a (ne_of_gt hb), Int.emod_lt_of_pos a hb, ?_⟩
  simpa [mul_comm, mul_left_comm, mul_assoc] using (Int.ediv_add_emod a b).symm

end JIBLM_DIY_INTRO_NUMBER_THEORY
