import Mathlib

/-!
# Thomson problem for N = 7 (and the D3h stretch target for N = 9)

Minimise the Coulomb energy `E(x) = ∑_{i<j} 1 / ‖x i - x j‖` over configurations of `N` pairwise
distinct points on the unit sphere `S² ⊂ ℝ³`.

* `N = 7`: the unique minimiser (up to `O(3)` and relabelling) is the regular pentagonal bipyramid,
  with `E = 1/2 + 5√2 + 5/(2 sin(π/5)) + 5/(2 sin(2π/5)) = 14.452977414…`.
* `N = 9`: the (numerically known) minimiser is the D3h tricapped trigonal prism, which has one free
  parameter `z` (the height of the two triangular faces); numerically `z ≈ 0.70365`,
  `E ≈ 25.759986531`.
-/

open Real

namespace ThomsonN7

/-- Euclidean 3-space. -/
abbrev R3 := EuclideanSpace ℝ (Fin 3)

/-- `n` pairwise distinct points on the unit sphere of `ℝ³`.
Injectivity is essential: with `1 / 0 = 0` in Lean, coincident points would otherwise be free. -/
def SphereConfig (n : ℕ) : Set (Fin n → R3) :=
  {x | (∀ i, ‖x i‖ = 1) ∧ Function.Injective x}

/-- Coulomb (Riesz `s = 1`) energy `∑_{i<j} 1 / ‖x i - x j‖`. -/
noncomputable def coulombEnergy {n : ℕ} (x : Fin n → R3) : ℝ :=
  ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, ‖x i - x j‖⁻¹

/-- The point with cylindrical coordinates `(ρ, θ, h)`. -/
noncomputable def cyl (ρ θ h : ℝ) : R3 := !₂[ρ * cos θ, ρ * sin θ, h]

/-- The regular pentagonal bipyramid: indices `0..4` are the equatorial pentagon
(angles `2πk/5`), index `5` is the north pole and index `6` the south pole. -/
noncomputable def pentBipyramid : Fin 7 → R3 := fun i =>
  if (i : ℕ) < 5 then cyl 1 (2 * π * (i : ℕ) / 5) 0
  else if (i : ℕ) = 5 then cyl 0 0 1
  else cyl 0 0 (-1)

/-- The D3h tricapped trigonal prism with prism height parameter `z` (for `z ∈ (0,1)`):
indices `0..2` are the top triangle (height `z`, angles `2πk/3`), indices `3..5` the bottom triangle
(height `-z`, same angles), and indices `6..8` the three equatorial caps at angles `π/3 + 2πk/3`. -/
noncomputable def triCapPrism (z : ℝ) : Fin 9 → R3 := fun i =>
  if (i : ℕ) < 3 then cyl (√(1 - z ^ 2)) (2 * π * (i : ℕ) / 3) z
  else if (i : ℕ) < 6 then cyl (√(1 - z ^ 2)) (2 * π * ((i : ℕ) - 3) / 3) (-z)
  else cyl 1 (π / 3 + 2 * π * ((i : ℕ) - 6) / 3) 0

/-! ## Auxiliary facts (already proved; they show the definitions are well-posed) -/

lemma norm_sq_cyl_sub (ρ θ h ρ' θ' h' : ℝ) :
    ‖cyl ρ θ h - cyl ρ' θ' h'‖ ^ 2 = ρ ^ 2 + ρ' ^ 2 - 2 * ρ * ρ' * cos (θ - θ') + (h - h') ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [cyl, Fin.sum_univ_three, cos_sub]
  nlinarith [sin_sq_add_cos_sq θ, sin_sq_add_cos_sq θ']

lemma norm_sq_cyl (ρ θ h : ℝ) : ‖cyl ρ θ h‖ ^ 2 = ρ ^ 2 + h ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [cyl, Fin.sum_univ_three, mul_pow]
  nlinarith [sin_sq_add_cos_sq θ]

lemma int_eq_zero_of_cos_eq_one (m : ℕ) (hm : 0 < m) (d : ℤ) (hd : |d| < m)
    (h : cos (2 * π * d / m) = 1) : d = 0 := by
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).1 h
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 : (n : ℝ) * m = d := by
    field_simp at hn
    nlinarith [Real.pi_pos]
  have h2 : n * (m : ℤ) = d := by exact_mod_cast h1
  have hm2 : (0 : ℤ) < m := by exact_mod_cast hm
  rw [abs_lt] at hd
  rcases lt_trichotomy n 0 with hn0 | hn0 | hn0
  · nlinarith
  · subst hn0; simpa using h2.symm
  · nlinarith

lemma cos_sub_eq_one_of_cyl_eq {ρ θ θ' h : ℝ} (hρ : 0 < ρ)
    (H : cyl ρ θ h = cyl ρ θ' h) : cos (θ - θ') = 1 := by
  have := norm_sq_cyl_sub ρ θ h ρ θ' h
  rw [H, sub_self, norm_zero] at this
  have hρ2 : 0 < ρ ^ 2 := by positivity
  nlinarith

lemma pent_angle_inj {i j : ℕ} (hi : i < 5) (hj : j < 5)
    (H : cos (2 * π * (i : ℕ) / 5 - 2 * π * (j : ℕ) / 5) = 1) : i = j := by
  have := int_eq_zero_of_cos_eq_one 5 (by norm_num) ((i : ℤ) - j) (by rw [abs_lt]; constructor <;> omega)
    (by convert H using 2; push_cast; ring)
  omega

lemma pent_of_lt {i : Fin 7} (hi : (i : ℕ) < 5) :
    pentBipyramid i = cyl 1 (2 * π * (i : ℕ) / 5) 0 := by
  simp [pentBipyramid, hi]

lemma pent_five : pentBipyramid 5 = cyl 0 0 1 := by simp [pentBipyramid]
lemma pent_six : pentBipyramid 6 = cyl 0 0 (-1) := by simp [pentBipyramid]

lemma pent_cases (i : Fin 7) : (i : ℕ) < 5 ∨ i = 5 ∨ i = 6 := by
  fin_cases i <;> simp

theorem pentBipyramid_injective : Function.Injective pentBipyramid := by
  intro i j hij
  have h2 := congrArg (fun v : R3 => v 2) hij
  rcases pent_cases i with hi | rfl | rfl <;> rcases pent_cases j with hj | rfl | rfl
  · rw [pent_of_lt hi, pent_of_lt hj] at hij
    exact Fin.ext (pent_angle_inj hi hj (cos_sub_eq_one_of_cyl_eq one_pos hij))
  · simp [pent_of_lt hi, pent_five, cyl] at h2
  · simp [pent_of_lt hi, pent_six, cyl] at h2
  · simp [pent_of_lt hj, pent_five, cyl] at h2
  · rfl
  · simp [pent_five, pent_six, cyl] at h2; norm_num at h2
  · simp [pent_of_lt hj, pent_six, cyl] at h2
  · simp [pent_five, pent_six, cyl] at h2; norm_num at h2
  · rfl

/-- The pentagonal bipyramid is an admissible configuration. -/
theorem pentBipyramid_mem : pentBipyramid ∈ SphereConfig 7 := by
  refine ⟨fun i => ?_, pentBipyramid_injective⟩
  have : ‖pentBipyramid i‖ ^ 2 = 1 := by
    rcases pent_cases i with hi | rfl | rfl
    · rw [pent_of_lt hi, norm_sq_cyl]; norm_num
    · rw [pent_five, norm_sq_cyl]; norm_num
    · rw [pent_six, norm_sq_cyl]; norm_num
  nlinarith [norm_nonneg (pentBipyramid i)]

lemma tri_idx_inj {i j : ℕ} (hd : |(i : ℤ) - j| < 3)
    (H : cos (2 * π * ((i : ℝ) - j) / 3) = 1) : i = j := by
  have := int_eq_zero_of_cos_eq_one 3 (by norm_num) ((i : ℤ) - j) (by exact_mod_cast hd)
    (by convert H using 2; push_cast; ring)
  omega

lemma tri_top {z : ℝ} {i : Fin 9} (hi : (i : ℕ) < 3) :
    triCapPrism z i = cyl (√(1 - z ^ 2)) (2 * π * (i : ℕ) / 3) z := by
  simp [triCapPrism, hi]

lemma tri_bot {z : ℝ} {i : Fin 9} (hi : 3 ≤ (i : ℕ)) (hi' : (i : ℕ) < 6) :
    triCapPrism z i = cyl (√(1 - z ^ 2)) (2 * π * ((i : ℕ) - 3) / 3) (-z) := by
  have h3 : ¬ (i : ℕ) < 3 := by omega
  simp [triCapPrism, h3, hi']

lemma tri_cap {z : ℝ} {i : Fin 9} (hi : 6 ≤ (i : ℕ)) :
    triCapPrism z i = cyl 1 (π / 3 + 2 * π * ((i : ℕ) - 6) / 3) 0 := by
  have h3 : ¬ (i : ℕ) < 3 := by omega
  have h6 : ¬ (i : ℕ) < 6 := by omega
  simp [triCapPrism, h3, h6]

lemma tri_cases (i : Fin 9) : (i : ℕ) < 3 ∨ (3 ≤ (i : ℕ) ∧ (i : ℕ) < 6) ∨ 6 ≤ (i : ℕ) := by
  omega

theorem triCapPrism_injective {z : ℝ} (hz : z ∈ Set.Ioo (0 : ℝ) 1) :
    Function.Injective (triCapPrism z) := by
  obtain ⟨hz0, hz1⟩ := hz
  have hr : 0 < √(1 - z ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  intro i j hij
  have h2 := congrArg (fun v : R3 => v 2) hij
  rcases tri_cases i with hi | ⟨hi, hi'⟩ | hi <;> rcases tri_cases j with hj | ⟨hj, hj'⟩ | hj
  · rw [tri_top hi, tri_top hj] at hij
    refine Fin.ext (tri_idx_inj (by rw [abs_lt]; constructor <;> omega) ?_)
    have := cos_sub_eq_one_of_cyl_eq hr hij
    convert this using 2; ring
  · simp [tri_top hi, tri_bot hj hj', cyl] at h2; linarith
  · simp [tri_top hi, tri_cap hj, cyl] at h2; linarith
  · simp [tri_top hj, tri_bot hi hi', cyl] at h2; linarith
  · rw [tri_bot hi hi', tri_bot hj hj'] at hij
    refine Fin.ext (tri_idx_inj (by rw [abs_lt]; constructor <;> omega) ?_)
    have := cos_sub_eq_one_of_cyl_eq hr hij
    convert this using 2; ring
  · simp [tri_bot hi hi', tri_cap hj, cyl] at h2; linarith
  · simp [tri_top hj, tri_cap hi, cyl] at h2; linarith
  · simp [tri_bot hj hj', tri_cap hi, cyl] at h2; linarith
  · rw [tri_cap hi, tri_cap hj] at hij
    refine Fin.ext (tri_idx_inj (by rw [abs_lt]; constructor <;> omega) ?_)
    have := cos_sub_eq_one_of_cyl_eq one_pos hij
    convert this using 2; ring

/-- The tricapped prism is an admissible configuration for every `z ∈ (0,1)`. -/
theorem triCapPrism_mem : ∀ z ∈ Set.Ioo (0 : ℝ) 1, triCapPrism z ∈ SphereConfig 9 := by
  intro z hz
  refine ⟨fun i => ?_, triCapPrism_injective hz⟩
  obtain ⟨hz0, hz1⟩ := hz
  have hr : √(1 - z ^ 2) ^ 2 = 1 - z ^ 2 := Real.sq_sqrt (by nlinarith)
  have : ‖triCapPrism z i‖ ^ 2 = 1 := by
    rcases tri_cases i with hi | ⟨hi, hi'⟩ | hi
    · rw [tri_top hi, norm_sq_cyl, hr]; ring
    · rw [tri_bot hi hi', norm_sq_cyl, hr]; ring
    · rw [tri_cap hi, norm_sq_cyl]; norm_num
  nlinarith [norm_nonneg (triCapPrism z i)]

lemma coulombEnergy_seven (x : Fin 7 → R3) : coulombEnergy x =
    ‖x 0 - x 1‖⁻¹ + ‖x 0 - x 2‖⁻¹ + ‖x 0 - x 3‖⁻¹ + ‖x 0 - x 4‖⁻¹ + ‖x 0 - x 5‖⁻¹ + ‖x 0 - x 6‖⁻¹
    + ‖x 1 - x 2‖⁻¹ + ‖x 1 - x 3‖⁻¹ + ‖x 1 - x 4‖⁻¹ + ‖x 1 - x 5‖⁻¹ + ‖x 1 - x 6‖⁻¹
    + ‖x 2 - x 3‖⁻¹ + ‖x 2 - x 4‖⁻¹ + ‖x 2 - x 5‖⁻¹ + ‖x 2 - x 6‖⁻¹
    + ‖x 3 - x 4‖⁻¹ + ‖x 3 - x 5‖⁻¹ + ‖x 3 - x 6‖⁻¹
    + ‖x 4 - x 5‖⁻¹ + ‖x 4 - x 6‖⁻¹ + ‖x 5 - x 6‖⁻¹ := by
  have hI : ∀ i : Fin 7, ∑ j ∈ Finset.Ioi i, ‖x i - x j‖⁻¹ =
      ∑ j, if i < j then ‖x i - x j‖⁻¹ else 0 := by
    intro i
    rw [← Finset.sum_filter]
    congr 1
    ext j; simp
  simp only [coulombEnergy, hI, Fin.sum_univ_seven]
  simp
  ring

lemma norm_eq_of_sq_eq {v : R3} {c : ℝ} (hc : 0 ≤ c) (h : ‖v‖ ^ 2 = c ^ 2) : ‖v‖ = c :=
  (sq_eq_sq₀ (norm_nonneg v) hc).1 h

lemma ring_dist (a b : ℝ) :
    ‖cyl 1 a 0 - cyl 1 b 0‖ ^ 2 = (2 * sin ((a - b) / 2)) ^ 2 := by
  rw [norm_sq_cyl_sub]
  have h1 : cos (a - b) = 1 - 2 * sin ((a - b) / 2) ^ 2 := by
    have := cos_two_mul ((a - b) / 2)
    have h2 := sin_sq_add_cos_sq ((a - b) / 2)
    rw [show 2 * ((a - b) / 2) = a - b by ring] at this
    rw [this]; nlinarith
  rw [h1]; ring

lemma pent_dist_pent {i j : Fin 7} (hi : (i : ℕ) < 5) (hj : (j : ℕ) < 5) (hij : i < j) :
    ‖pentBipyramid i - pentBipyramid j‖ = 2 * sin (π * (((j : ℕ) : ℝ) - (i : ℕ)) / 5) := by
  have hij' : (i : ℕ) < (j : ℕ) := hij
  rw [pent_of_lt hi, pent_of_lt hj]
  apply norm_eq_of_sq_eq
  · have : 0 < sin (π * (((j : ℕ) : ℝ) - (i : ℕ)) / 5) := by
      apply sin_pos_of_pos_of_lt_pi
      · have : (0 : ℝ) < ((j : ℕ) : ℝ) - (i : ℕ) := by
          rw [sub_pos]; exact_mod_cast hij'
        positivity
      · have : (((j : ℕ) : ℝ) - (i : ℕ)) < 5 := by
          have : (j : ℕ) < 5 := hj
          have : (((j : ℕ) : ℝ)) < 5 := by exact_mod_cast this
          have : (0 : ℝ) ≤ (i : ℕ) := Nat.cast_nonneg _
          linarith
        nlinarith [Real.pi_pos]
    linarith
  · rw [ring_dist]
    have : sin ((2 * π * ((i : ℕ) : ℝ) / 5 - 2 * π * ((j : ℕ) : ℝ) / 5) / 2)
        = - sin (π * (((j : ℕ) : ℝ) - (i : ℕ)) / 5) := by
      rw [← sin_neg]; congr 1; ring
    rw [this]; ring

lemma pent_dist_north {i : Fin 7} (hi : (i : ℕ) < 5) :
    ‖pentBipyramid i - pentBipyramid 5‖ = √2 := by
  rw [pent_of_lt hi, pent_five]
  apply norm_eq_of_sq_eq (Real.sqrt_nonneg _)
  rw [norm_sq_cyl_sub, Real.sq_sqrt (by norm_num)]; norm_num

lemma pent_dist_south {i : Fin 7} (hi : (i : ℕ) < 5) :
    ‖pentBipyramid i - pentBipyramid 6‖ = √2 := by
  rw [pent_of_lt hi, pent_six]
  apply norm_eq_of_sq_eq (Real.sqrt_nonneg _)
  rw [norm_sq_cyl_sub, Real.sq_sqrt (by norm_num)]; norm_num

lemma pent_dist_poles : ‖pentBipyramid 5 - pentBipyramid 6‖ = 2 := by
  rw [pent_five, pent_six]
  apply norm_eq_of_sq_eq (by norm_num)
  rw [norm_sq_cyl_sub]; norm_num

/-- Closed form of the pentagonal bipyramid energy (`≈ 14.452977414`). -/
theorem pentBipyramid_energy :
    coulombEnergy pentBipyramid =
      1 / 2 + 5 * √2 + 5 / (2 * sin (π / 5)) + 5 / (2 * sin (2 * π / 5)) := by
  have hs3 : sin (3 * π / 5) = sin (2 * π / 5) := by
    rw [← sin_pi_sub]; congr 1; ring
  have hs4 : sin (4 * π / 5) = sin (π / 5) := by
    rw [← sin_pi_sub]; congr 1; ring
  have d01 : ‖pentBipyramid 0 - pentBipyramid 1‖ = 2 * sin (π / 5) := by
    rw [pent_dist_pent (by decide) (by decide) (by decide)]; norm_num
  have d12 : ‖pentBipyramid 1 - pentBipyramid 2‖ = 2 * sin (π / 5) := by
    rw [pent_dist_pent (by decide) (by decide) (by decide)]; norm_num
  have d23 : ‖pentBipyramid 2 - pentBipyramid 3‖ = 2 * sin (π / 5) := by
    rw [pent_dist_pent (by decide) (by decide) (by decide)]; norm_num
  have d34 : ‖pentBipyramid 3 - pentBipyramid 4‖ = 2 * sin (π / 5) := by
    rw [pent_dist_pent (by decide) (by decide) (by decide)]; norm_num
  have d04 : ‖pentBipyramid 0 - pentBipyramid 4‖ = 2 * sin (π / 5) := by
    rw [pent_dist_pent (by decide) (by decide) (by decide)]; norm_num
    rw [← hs4]; congr 2; ring
  have d02 : ‖pentBipyramid 0 - pentBipyramid 2‖ = 2 * sin (2 * π / 5) := by
    rw [pent_dist_pent (by decide) (by decide) (by decide)]; norm_num
    congr 2; ring
  have d13 : ‖pentBipyramid 1 - pentBipyramid 3‖ = 2 * sin (2 * π / 5) := by
    rw [pent_dist_pent (by decide) (by decide) (by decide)]; norm_num
    congr 2; ring
  have d24 : ‖pentBipyramid 2 - pentBipyramid 4‖ = 2 * sin (2 * π / 5) := by
    rw [pent_dist_pent (by decide) (by decide) (by decide)]; norm_num
    congr 2; ring
  have d03 : ‖pentBipyramid 0 - pentBipyramid 3‖ = 2 * sin (2 * π / 5) := by
    rw [pent_dist_pent (by decide) (by decide) (by decide)]; norm_num
    rw [← hs3]; congr 2; ring
  have d14 : ‖pentBipyramid 1 - pentBipyramid 4‖ = 2 * sin (2 * π / 5) := by
    rw [pent_dist_pent (by decide) (by decide) (by decide)]; norm_num
    rw [← hs3]; congr 2; ring
  have hp1 : 0 < sin (π / 5) := sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  have hp2 : 0 < sin (2 * π / 5) :=
    sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  rw [coulombEnergy_seven, d01, d12, d23, d34, d04, d02, d13, d24, d03, d14,
    pent_dist_north (i := 0) (by decide), pent_dist_north (i := 1) (by decide),
    pent_dist_north (i := 2) (by decide), pent_dist_north (i := 3) (by decide),
    pent_dist_north (i := 4) (by decide), pent_dist_south (i := 0) (by decide),
    pent_dist_south (i := 1) (by decide), pent_dist_south (i := 2) (by decide),
    pent_dist_south (i := 3) (by decide), pent_dist_south (i := 4) (by decide),
    pent_dist_poles]
  have h2 : (0 : ℝ) < √2 := by positivity
  have h3 : (√2)⁻¹ = √2 / 2 := by
    field_simp
    rw [Real.sq_sqrt (by norm_num)]
  rw [h3]
  field_simp
  ring


/-! ## Challenge statements (to be proved) -/

/-- **Main target (Thomson, N = 7).** The regular pentagonal bipyramid minimises the Coulomb
energy among all configurations of 7 distinct points on the unit sphere. -/
theorem thomson_seven :
    ∀ x ∈ SphereConfig 7, coulombEnergy pentBipyramid ≤ coulombEnergy x := by
  sorry

/-- **Uniqueness (N = 7).** Any minimiser is the pentagonal bipyramid up to an orthogonal
transformation of `ℝ³` and a relabelling of the points. -/
theorem thomson_seven_unique :
    ∀ x ∈ SphereConfig 7, coulombEnergy x = coulombEnergy pentBipyramid →
      ∃ (g : R3 ≃ₗᵢ[ℝ] R3) (σ : Equiv.Perm (Fin 7)), ∀ i, x i = g (pentBipyramid (σ i)) := by
  sorry

/-- **Stretch target (Thomson, N = 9).** Some D3h tricapped trigonal prism (numerically
`z ≈ 0.70365`, energy `≈ 25.759986531`) is a global minimiser among 9-point configurations. -/
theorem thomson_nine :
    ∃ z ∈ Set.Ioo (0 : ℝ) 1,
      ∀ x ∈ SphereConfig 9, coulombEnergy (triCapPrism z) ≤ coulombEnergy x := by
  sorry

end ThomsonN7
