import Mathlib

open Real
open EuclideanGeometry

/- 余弦定理：在任意三角形 ABC 中，设三边分别为 a, b, c，
   其中 a = BC, b = AC, c = AB，
   角 C 为边 a 和边 b 的夹角（即 ∠ACB），
   则有：c² = a² + b² - 2ab·cos(C) -/

-- 使用向量方法证明余弦定理
theorem law_of_cosines_vector {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (a b : V) : ‖a - b‖^2 = ‖a‖^2 + ‖b‖^2 - 2 * (inner a b : ℝ) := by
  -- 展开 ‖a - b‖² = ⟨a - b, a - b⟩
  have h1 : ‖a - b‖^2 = (inner (a - b) (a - b) : ℝ) := by
    simp [norm_sq_eq_inner]
  -- 展开内积
  have h2 : (inner (a - b) (a - b) : ℝ) = (inner a a : ℝ) - 2 * (inner a b : ℝ) + (inner b b : ℝ) := by
    rw [inner_sub_left, inner_sub_right]
    rw [inner_sub_left]
    ring
  -- 代回并整理
  rw [h1, h2]
  have h3 : (inner a a : ℝ) = ‖a‖^2 := by
    simp [norm_sq_eq_inner]
  have h4 : (inner b b : ℝ) = ‖b‖^2 := by
    simp [norm_sq_eq_inner]
  rw [h3, h4]
  ring

-- 几何形式的余弦定理：在三角形 ABC 中，c² = a² + b² - 2ab·cos(∠C)
theorem law_of_cosines_triangle {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {A B C : V} (h : B ≠ A) (h' : C ≠ A) :
    dist B C ^ 2 = dist A B ^ 2 + dist A C ^ 2 - 2 * dist A B * dist A C * cos (angle B A C) := by
  -- 将点表示为从 A 出发的向量
  let u := B - A
  let v := C - A
  -- 边长关系：BC = ‖v - u‖, AB = ‖u‖, AC = ‖v‖
  have hbc : dist B C = ‖v - u‖ := by
    simp [u, v, dist_eq_norm]
    rw [← norm_neg]
    simp
  have hab : dist A B = ‖u‖ := by
    simp [u, dist_eq_norm]
  have hac : dist A C = ‖v‖ := by
    simp [v, dist_eq_norm]
  -- 角 BAC 的余弦等于向量 u 和 v 的夹角余弦
  have h_angle : cos (angle B A C) = (inner u v : ℝ) / (‖u‖ * ‖v‖) := by
    simp [u, v, angle, inner_mul_inner_div_norm_mul_norm_eq_cos_angle]
    field_simp
  -- 应用向量形式的余弦定理
  rw [hbc, hab, hac, h_angle]
  have h_vec : ‖v - u‖^2 = ‖u‖^2 + ‖v‖^2 - 2 * (inner u v : ℝ) := by
    apply law_of_cosines_vector
  rw [h_vec]
  -- 代数整理
  have h_pos1 : ‖u‖ ≠ 0 := by
    intro h0
    have : B = A := by
      have : u = 0 := by
        simpa [u, norm_eq_zero] using h0
      have : B - A = 0 := by exact this
      exact eq_of_sub_eq_zero this
    contradiction
  have h_pos2 : ‖v‖ ≠ 0 := by
    intro h0
    have : C = A := by
      have : v = 0 := by
        simpa [v, norm_eq_zero] using h0
      have : C - A = 0 := by exact this
      exact eq_of_sub_eq_zero this
    contradiction
  have h_pos1' : ‖u‖ > 0 := by
    exact lt_of_le_of_ne (norm_nonneg u) (Ne.symm h_pos1)
  have h_pos2' : ‖v‖ > 0 := by
    exact lt_of_le_of_ne (norm_nonneg v) (Ne.symm h_pos2)
  field_simp
  ring_nf
  <;> field_simp
  <;> ring
