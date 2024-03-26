/-- Given `(S : Solution)`, we have that `λ ^ 2` does not divide `S.a + η * S.b`. -/
lemma lambda_sq_not_a_add_eta_mul_b : ¬ λ ^ 2 ∣ (S.a + η * S.b) := by
  rw [show S.a + η * S.b = (S.a + S.b) + λ * S.b by ring]
  intro h
  replace h : _ := (dvd_add_right S.hab).mp h
  apply S.hb
  rw [pow_two] at h
  exact dvd_of_mul_dvd_mul_left hζ.lambda_prime.ne_zero h
