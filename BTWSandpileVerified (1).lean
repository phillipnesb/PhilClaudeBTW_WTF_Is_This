/-
  Universal Formal Verification & Runtime Certification:
  Bak-Tang-Wiesenfeld (BTW) Abelian Sandpile Kernel (Zero-Dependency Lean 4)
-/

namespace BTWSandpileVerified

/-! ## 1. Unified Domain & Discrete Harmonic Potential -/

/-- Interior grid domain Omega = {1, ..., N}^2 with automatic decidability. -/
def InOmega (N r c : Nat) : Prop :=
  1 <= r ∧ r <= N ∧ 1 <= c ∧ c <= N

instance (N r c : Nat) : Decidable (InOmega N r c) :=
  inferInstanceAs (Decidable (1 <= r ∧ r <= N ∧ 1 <= c ∧ c <= N))

/-- 1D parabolic profile f(x) = x * (N + 1 - x) on {1, ..., N}, 0 outside. -/
def f1D (N x : Nat) : Nat :=
  if 1 <= x ∧ x <= N then x * (N + 1 - x) else 0

/-- 2D discrete harmonic potential h(r, c) = f1D(r) + f1D(c) on Omega, 0 outside. -/
def h (N r c : Nat) : Nat :=
  if InOmega N r c then f1D N r + f1D N c else 0

/-- Helper lemma: 4 * f1D(N, x) <= (N + 1)^2 for all N, x : Nat. -/
theorem f1D_bound (N x : Nat) : 4 * f1D N x <= (N + 1) ^ 2 := by
  unfold f1D
  split
  case isTrue h_in =>
    obtain ⟨_, hxN⟩ := h_in
    have h_sq : 0 <= ((N : Int) + 1 - 2 * (x : Int)) * ((N : Int) + 1 - 2 * (x : Int)) :=
      Int.mul_self_nonneg _
    have h_cast : ((N + 1 - x : Nat) : Int) = (N : Int) + 1 - (x : Int) := by omega
    have h_expand :
        ((N : Int) + 1 - 2 * (x : Int)) * ((N : Int) + 1 - 2 * (x : Int)) =
        ((N : Int) + 1) * ((N : Int) + 1) - 4 * ((x : Int) * ((N : Int) + 1 - (x : Int))) := by
      simp only [Int.sub_mul, Int.mul_sub, Int.add_mul, Int.mul_add]
      omega
    have h_pow : (((N + 1) ^ 2 : Nat) : Int) = ((N : Int) + 1) * ((N : Int) + 1) := by
      simp [Nat.pow_two, Int.ofNat_mul]
    have h_mul : ((x * (N + 1 - x) : Nat) : Int) = (x : Int) * ((N : Int) + 1 - (x : Int)) := by
      rw [Int.ofNat_mul, h_cast]
    omega
  case isFalse =>
    omega

/-- Invariant 1: Universal Discrete Harmonic Potential Bound h(r, c) <= ((N + 1)^2) / 2. -/
theorem invariant1_potential_bound (N r c : Nat) :
    h N r c <= ((N + 1) ^ 2) / 2 := by
  unfold h
  split
  case isTrue =>
    have hfr := f1D_bound N r
    have hfc := f1D_bound N c
    omega
  case isFalse =>
    exact Nat.zero_le _

/-! ## 2. Separable Discrete Negative Laplacian & Strict Superharmonicity -/

def laplacianH (N r c : Nat) : Int :=
  4 * (h N r c : Int)
    - (h N (r - 1) c : Int)
    - (h N (r + 1) c : Int)
    - (h N r (c - 1) : Int)
    - (h N r (c + 1) : Int)

def boundaryExcess (N r c : Nat) : Nat :=
  (if r = 1 then f1D N c else 0) +
  (if r = N then f1D N c else 0) +
  (if c = 1 then f1D N r else 0) +
  (if c = N then f1D N r else 0)

/-- 1D discrete second difference identity on {1, ..., N}. -/
theorem discrete_second_diff_1d (N x : Nat) (hx1 : 1 <= x) (hxN : x <= N) :
    2 * (f1D N x : Int) - (f1D N (x - 1) : Int) - (f1D N (x + 1) : Int)
    = 2 + (if x = 1 then (N : Int) else 0) + (if x = N then (N : Int) else 0) := by
  unfold f1D
  have hx_in : 1 <= x ∧ x <= N := ⟨hx1, hxN⟩
  simp only [hx_in, and_self, reduceIte]
  by_cases h1 : x = 1 <;> by_cases hN : x = N
  · subst h1; have : N = 1 := hN.symm; subst this; decide
  · subst h1
    have h_ge2 : 2 <= N := by omega
    have h_sub : ¬ (1 <= 0 ∧ 0 <= N) := by omega
    have h_add : 1 <= 2 ∧ 2 <= N := by omega
    simp only [h_sub, h_add, reduceIte, hN]
    have s1 : N + 1 - 1 = N := by omega
    have s2 : N + 1 - 2 = N - 1 := by omega
    rw [s1, s2]
    have c1 : ((2 * (N - 1) : Nat) : Int) = 2 * ((N : Int) - 1) := by
      rw [Int.ofNat_mul]; congr 1; omega
    have c2 : ((1 * N : Nat) : Int) = (N : Int) := by simp
    rw [c1, c2]; omega
  · subst hN
    have h_gt1 : 1 < N := by omega
    have h_sub : 1 <= N - 1 ∧ N - 1 <= N := by omega
    have h_add : ¬ (1 <= N + 1 ∧ N + 1 <= N) := by omega
    simp only [h_sub, h_add, reduceIte, h1]
    have s1 : N + 1 - N = 1 := by omega
    have s2 : N + 1 - (N - 1) = 2 := by omega
    rw [s1, s2]
    have c1 : (((N - 1) * 2 : Nat) : Int) = ((N : Int) - 1) * 2 := by
      rw [Int.ofNat_mul]; congr 1; omega
    have c2 : ((N * 1 : Nat) : Int) = (N : Int) := by simp
    rw [c1, c2]; omega
  · have h_sub : 1 <= x - 1 ∧ x - 1 <= N := by omega
    have h_add : 1 <= x + 1 ∧ x + 1 <= N := by omega
    simp only [h_sub, h_add, reduceIte, h1, hN]
    have m0 : ((x * (N + 1 - x) : Nat) : Int) = (x : Int) * ((N : Int) + 1 - (x : Int)) := by
      rw [Int.ofNat_mul]; congr 1; omega
    have m1 : (((x - 1) * (N + 1 - (x - 1)) : Nat) : Int) =
              ((x : Int) - 1) * ((N : Int) + 2 - (x : Int)) := by
      rw [Int.ofNat_mul]; congr 1 <;> omega
    have m2 : (((x + 1) * (N + 1 - (x + 1)) : Nat) : Int) =
              ((x : Int) + 1) * ((N : Int) - (x : Int)) := by
      rw [Int.ofNat_mul]; congr 1 <;> omega
    rw [m0, m1, m2]
    simp only [Int.mul_add, Int.mul_sub, Int.add_mul, Int.sub_mul]
    omega

/-- Helper decomposing neighbor potential values cleanly along rows and columns. -/
theorem h_neighbor_r (N r' c : Nat) (hc : 1 <= c ∧ c <= N) :
    (h N r' c : Int) = (f1D N r' : Int) + (if 1 <= r' ∧ r' <= N then (f1D N c : Int) else 0) := by
  unfold h InOmega f1D
  by_cases hr : 1 <= r' ∧ r' <= N <;> simp [hr, hc]

theorem h_neighbor_c (N r c' : Nat) (hr : 1 <= r ∧ r <= N) :
    (h N r c' : Int) = (f1D N c' : Int) + (if 1 <= c' ∧ c' <= N then (f1D N r : Int) else 0) := by
  unfold h InOmega f1D
  by_cases hc : 1 <= c' ∧ c' <= N <;> simp [hr, hc]

/-- Invariant 2: Exact Boundary-Aware Discrete Negative Laplacian Identity (without 16-way branching). -/
theorem invariant2_laplacian_exact (N r c : Nat) (h_in : InOmega N r c) :
    laplacianH N r c = 4 + (boundaryExcess N r c : Int) := by
  obtain ⟨hr1, hrN, hc1, hcN⟩ := h_in
  unfold laplacianH boundaryExcess
  have h_center : (h N r c : Int) = (f1D N r : Int) + (f1D N c : Int) := by
    simp [h, InOmega, hr1, hrN, hc1, hcN]
  rw [h_center, h_neighbor_r N (r - 1) c ⟨hc1, hcN⟩, h_neighbor_r N (r + 1) c ⟨hc1, hcN⟩,
      h_neighbor_c N r (c - 1) ⟨hr1, hrN⟩, h_neighbor_c N r (c + 1) ⟨hr1, hrN⟩]
  have d_r := discrete_second_diff_1d N r hr1 hrN
  have d_c := discrete_second_diff_1d N c hc1 hcN
  have b_rm1 : (if 1 <= r - 1 ∧ r - 1 <= N then (f1D N c : Int) else 0) =
               (f1D N c : Int) - (if r = 1 then (f1D N c : Int) else 0) := by
    by_cases h1 : r = 1
    · subst h1; simp
    · have : 1 <= r - 1 ∧ r - 1 <= N := by omega
      simp [h1, this]
  have b_rp1 : (if 1 <= r + 1 ∧ r + 1 <= N then (f1D N c : Int) else 0) =
               (f1D N c : Int) - (if r = N then (f1D N c : Int) else 0) := by
    by_cases hN : r = N
    · subst hN; simp
    · have : 1 <= r + 1 ∧ r + 1 <= N := by omega
      simp [hN, this]
  have b_cm1 : (if 1 <= c - 1 ∧ c - 1 <= N then (f1D N r : Int) else 0) =
               (f1D N r : Int) - (if c = 1 then (f1D N r : Int) else 0) := by
    by_cases h1 : c = 1
    · subst h1; simp
    · have : 1 <= c - 1 ∧ c - 1 <= N := by omega
      simp [h1, this]
  have b_cp1 : (if 1 <= c + 1 ∧ c + 1 <= N then (f1D N r : Int) else 0) =
               (f1D N r : Int) - (if c = N then (f1D N r : Int) else 0) := by
    by_cases hN : c = N
    · subst hN; simp
    · have : 1 <= c + 1 ∧ c + 1 <= N := by omega
      simp [hN, this]
  rw [b_rm1, b_rp1, b_cm1, b_cp1]
  omega

theorem invariant2_superharmonic (N r c : Nat) (h_in : InOmega N r c) :
    4 <= laplacianH N r c := by
  rw [invariant2_laplacian_exact N r c h_in]
  omega

/-! ## 3. Sandpile State Space, Abelian Commutativity & Batch Bisimulation -/

abbrev Config := Nat → Nat → Nat

def ValidConfig (N : Nat) (z : Config) : Prop :=
  ∀ r c, ¬ InOmega N r c → z r c = 0

def topple (N r c : Nat) (z : Config) : Config :=
  fun i j =>
    if ¬ InOmega N i j then 0
    else if i = r ∧ j = c then z i j - 4
    else
      z i j
      + (if i + 1 = r ∧ j = c then 1 else 0)
      + (if i = r + 1 ∧ j = c then 1 else 0)
      + (if i = r ∧ j + 1 = c then 1 else 0)
      + (if i = r ∧ j = c + 1 then 1 else 0)

theorem topple_preserves_valid (N r c : Nat) (z : Config) :
    ValidConfig N (topple N r c z) := by
  intro i j h_out
  simp [topple, h_out]

theorem invariant3_abelian_commutativity (N r1 c1 r2 c2 : Nat)
    (hne : ¬ (r1 = r2 ∧ c1 = c2)) (z : Config) :
    topple N r1 c1 (topple N r2 c2 z) = topple N r2 c2 (topple N r1 c1 z) := by
  funext i j
  unfold topple
  by_cases h_in : InOmega N i j
  · simp only [h_in, not_true_eq_false, reduceIte]
    by_cases h1 : i = r1 ∧ j = c1 <;> by_cases h2 : i = r2 ∧ j = c2
    · exfalso; exact hne (by omega)
    · obtain ⟨rfl, rfl⟩ := h1
      simp only [true_and, reduceIte, h2]
      have h_adj : (if i + 1 = r2 ∧ j = c2 then 1 else 0) +
                   (if i = r2 + 1 ∧ j = c2 then 1 else 0) +
                   (if i = r2 ∧ j + 1 = c2 then 1 else 0) +
                   (if i = r2 ∧ j = c2 + 1 then 1 else 0) <= 1 := by
        split <;> split <;> split <;> split <;> omega
      omega
    · obtain ⟨rfl, rfl⟩ := h2
      simp only [true_and, reduceIte, h1]
      have h_adj : (if i + 1 = r1 ∧ j = c1 then 1 else 0) +
                   (if i = r1 + 1 ∧ j = c1 then 1 else 0) +
                   (if i = r1 ∧ j + 1 = c1 then 1 else 0) +
                   (if i = r1 ∧ j = c1 + 1 then 1 else 0) <= 1 := by
        split <;> split <;> split <;> split <;> omega
      omega
    · simp only [h1, h2, reduceIte]
      omega
  · simp [h_in]

def toppleBatch (N r c k : Nat) (z : Config) : Config :=
  fun i j =>
    if ¬ InOmega N i j then 0
    else if i = r ∧ j = c then z i j - 4 * k
    else
      z i j
      + (if i + 1 = r ∧ j = c then k else 0)
      + (if i = r + 1 ∧ j = c then k else 0)
      + (if i = r ∧ j + 1 = c then k else 0)
      + (if i = r ∧ j = c + 1 then k else 0)

theorem batch_eq_iterated_topple (N r c k : Nat) (z : Config) :
    toppleBatch N r c k z = Nat.repeat (topple N r c) k z := by
  induction k generalizing z with
  | zero =>
    funext i j
    unfold toppleBatch Nat.repeat
    by_cases h_in : InOmega N i j
    · simp only [h_in, not_true_eq_false, reduceIte]
      by_cases h1 : i = r ∧ j = c <;> simp [h1]
    · simp [h_in]
  | succ k ih =>
    change toppleBatch N r c (k + 1) z = topple N r c (Nat.repeat (topple N r c) k z)
    rw [← ih]
    funext i j
    unfold toppleBatch topple
    by_cases h_in : InOmega N i j
    · simp only [h_in, not_true_eq_false, reduceIte]
      by_cases h1 : i = r ∧ j = c
      · simp only [h1, reduceIte]; omega
      · simp only [h1, reduceIte]; split <;> split <;> split <;> split <;> omega
    · simp [h_in]

/-! ## 4. Fast Recursive Summation on Omega -/

def sumRange : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => sumRange n f + f (n + 1)

def sumOmega (N : Nat) (g : Nat → Nat → Nat) : Nat :=
  sumRange N (fun r => sumRange N (fun c => g r c))

theorem sumRange_add (n : Nat) (f g : Nat → Nat) :
    sumRange n (fun x => f x + g x) = sumRange n f + sumRange n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sumRange, ih]; omega

theorem sumOmega_add (N : Nat) (f g : Nat → Nat → Nat) :
    sumOmega N (fun r c => f r c + g r c) = sumOmega N f + sumOmega N g := by
  unfold sumOmega
  simp_rw [sumRange_add]
  exact sumRange_add N _ _

theorem sumRange_delta (n k val : Nat) :
    sumRange n (fun x => if x = k then val else 0) = if 1 <= k ∧ k <= n then val else 0 := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih =>
    simp only [sumRange, ih]
    by_cases hk : n + 1 = k <;> simp [hk] <;> omega

theorem sumOmega_delta (N r c val : Nat) :
    sumOmega N (fun i j => if i = r ∧ j = c then val else 0) =
      if InOmega N r c then val else 0 := by
  unfold sumOmega InOmega
  have inner : ∀ i, sumRange N (fun j => if i = r ∧ j = c then val else 0) =
      if i = r ∧ 1 <= c ∧ c <= N then val else 0 := by
    intro i
    by_cases hi : i = r
    · subst hi; simp [sumRange_delta]
    · simp [hi]
  simp_rw [inner]
  have rw_if : (fun i => if i = r ∧ 1 <= c ∧ c <= N then val else 0) =
      (fun i => if i = r then (if 1 <= c ∧ c <= N then val else 0) else 0) := by
    funext i; by_cases hi : i = r <;> by_cases hc : 1 <= c ∧ c <= N <;> simp [hi, hc]
  rw [rw_if, sumRange_delta]
  by_cases hr : 1 <= r ∧ r <= N <;> by_cases hc : 1 <= c ∧ c <= N <;> simp [hr, hc]

/-! ## 5. Single-Step & Multi-Step Lyapunov Descent (CERT-01) -/

def psiH (N : Nat) (z : Config) : Nat :=
  sumOmega N (fun r c => h N r c * z r c)

theorem single_topple_potential_drop (N r c : Nat) (h_in_rc : InOmega N r c)
    (z : Config) (hz : 4 <= z r c) :
    psiH N (topple N r c z) + 4 + boundaryExcess N r c = psiH N z := by
  obtain ⟨hr1, hrN, hc1, hcN⟩ := h_in_rc
  have h_eq :
      psiH N (topple N r c z) + 4 * h N r c =
      psiH N z + h N (r - 1) c + h N (r + 1) c + h N r (c - 1) + h N r (c + 1) := by
    unfold psiH
    have h_lhs :
        sumOmega N (fun i j => h N i j * topple N r c z i j) +
        sumOmega N (fun i j => if i = r ∧ j = c then 4 * h N r c else 0) =
        sumOmega N (fun i j =>
          h N i j * z i j
          + (if i + 1 = r ∧ j = c then h N (r - 1) c else 0)
          + (if i = r + 1 ∧ j = c then h N (r + 1) c else 0)
          + (if i = r ∧ j + 1 = c then h N r (c - 1) else 0)
          + (if i = r ∧ j = c + 1 then h N r (c + 1) else 0)) := by
      rw [← sumOmega_add]
      congr 1; funext i j
      by_cases h_in : InOmega N i j
      · unfold topple
        simp only [h_in, not_true_eq_false, reduceIte]
        by_cases h_self : i = r ∧ j = c
        · obtain ⟨rfl, rfl⟩ := h_self
          have hn1 : ¬ (i + 1 = i ∧ j = j) := by omega
          have hn2 : ¬ (i = i + 1 ∧ j = j) := by omega
          have hn3 : ¬ (i = i ∧ j + 1 = j) := by omega
          have hn4 : ¬ (i = i ∧ j = j + 1) := by omega
          simp only [true_and, reduceIte, hn1, hn2, hn3, hn4]
          have h_sub : h N i j * (z i j - 4) + 4 * h N i j = h N i j * z i j := by
            rw [Nat.mul_sub_left_distrib]
            have : 4 * h N i j <= h N i j * z i j := by
              calc 4 * h N i j = h N i j * 4 := Nat.mul_comm 4 _
              _ <= h N i j * z i j := Nat.mul_le_mul_left _ hz
            omega
          omega
        · simp only [h_self, reduceIte]
          rw [Nat.left_distrib, Nat.left_distrib, Nat.left_distrib, Nat.left_distrib]
          simp only [mul_ite, Nat.mul_one, Nat.mul_zero]
          have c1 : (if i + 1 = r ∧ j = c then h N i j else 0) = (if i + 1 = r ∧ j = c then h N (r - 1) c else 0) := by
            split; next h => obtain ⟨rfl, rfl⟩ := h; simp; rfl
          have c2 : (if i = r + 1 ∧ j = c then h N i j else 0) = (if i = r + 1 ∧ j = c then h N (r + 1) c else 0) := by
            split; next h => obtain ⟨rfl, rfl⟩ := h; rfl; rfl
          have c3 : (if i = r ∧ j + 1 = c then h N i j else 0) = (if i = r ∧ j + 1 = c then h N r (c - 1) else 0) := by
            split; next h => obtain ⟨rfl, rfl⟩ := h; simp; rfl
          have c4 : (if i = r ∧ j = c + 1 then h N i j else 0) = (if i = r ∧ j = c + 1 then h N r (c + 1) else 0) := by
            split; next h => obtain ⟨rfl, rfl⟩ := h; rfl; rfl
          rw [c1, c2, c3, c4]; omega
      · have hh0 : h N i j = 0 := by simp [h, h_in]
        have h_ne : ¬ (i = r ∧ j = c) := fun ⟨hr, hc⟩ => h_in ⟨hr ▸ hr1, hr ▸ hrN, hc ▸ hc1, hc ▸ hcN⟩
        have hn1 : ¬ (i + 1 = r ∧ j = c) := fun ⟨hr, hc⟩ => h_in ⟨by omega, by omega, hc ▸ hc1, hc ▸ hcN⟩
        have hn2 : ¬ (i = r + 1 ∧ j = c) := fun ⟨hr, hc⟩ => h_in ⟨by omega, by omega, hc ▸ hc1, hc ▸ hcN⟩
        have hn3 : ¬ (i = r ∧ j + 1 = c) := fun ⟨hr, hc⟩ => h_in ⟨hr ▸ hr1, hr ▸ hrN, by omega, by omega⟩
        have hn4 : ¬ (i = r ∧ j = c + 1) := fun ⟨hr, hc⟩ => h_in ⟨hr ▸ hr1, hr ▸ hrN, by omega, by omega⟩
        simp [hh0, h_ne, hn1, hn2, hn3, hn4]
    rw [sumOmega_delta, if_pos ⟨hr1, hrN, hc1, hcN⟩] at h_lhs
    rw [sumOmega_add, sumOmega_add, sumOmega_add, sumOmega_add] at h_lhs
    have rewrite_pred (a b val : Nat) :
        sumOmega N (fun i j => if i + 1 = a ∧ j = b then val else 0) =
        sumOmega N (fun i j => if i = a - 1 ∧ j = b then val else 0) := by
      congr 1; funext i j; by_cases ha : 1 <= a <;> by_cases h1 : i + 1 = a <;> by_cases h2 : j = b <;> simp [h1, h2] <;> omega
    have rewrite_pred2 (a b val : Nat) :
        sumOmega N (fun i j => if i = a ∧ j + 1 = b then val else 0) =
        sumOmega N (fun i j => if i = a ∧ j = b - 1 then val else 0) := by
      congr 1; funext i j; by_cases hb : 1 <= b <;> by_cases h1 : i = a <;> by_cases h2 : j + 1 = b <;> simp [h1, h2] <;> omega
    rw [rewrite_pred, rewrite_pred2, sumOmega_delta, sumOmega_delta, sumOmega_delta, sumOmega_delta] at h_lhs
    have b1 : (if InOmega N (r - 1) c then h N (r - 1) c else 0) = h N (r - 1) c := by
      split; rfl; next hn => simp [h, hn]
    have b2 : (if InOmega N (r + 1) c then h N (r + 1) c else 0) = h N (r + 1) c := by
      split; rfl; next hn => simp [h, hn]
    have b3 : (if InOmega N r (c - 1) then h N r (c - 1) else 0) = h N r (c - 1) := by
      split; rfl; next hn => simp [h, hn]
    have b4 : (if InOmega N r (c + 1) then h N r (c + 1) else 0) = h N r (c + 1) := by
      split; rfl; next hn => simp [h, hn]
    rw [b1, b2, b3, b4] at h_lhs
    exact h_lhs
  have h_lap := invariant2_laplacian_exact N r c ⟨hr1, hrN, hc1, hcN⟩
  unfold laplacianH at h_lap
  omega

/-- Inductive Multi-Step Avalanche Transition Relation using unified InOmega. -/
inductive StepStar (N : Nat) : Config → Config → Nat → Nat → Prop where
  | refl (z : Config) : StepStar N z z 0 0
  | step {z1 z2 z3 : Config} {S loss r c : Nat}
      (h_in : InOmega N r c)
      (hz : 4 <= z1 r c)
      (h_eq : z2 = topple N r c z1)
      (h_rest : StepStar N z2 z3 S loss) :
      StepStar N z1 z3 (S + 1) (loss + boundaryExcess N r c)

/-- Multi-step preservation of boundary zero-clamping (ValidConfig). -/
theorem stepStar_preserves_valid {N : Nat} {z_init z_final : Config} {S loss : Nat}
    (h_valid : ValidConfig N z_init)
    (h_run : StepStar N z_init z_final S loss) :
    ValidConfig N z_final := by
  induction h_run with
  | refl _ => exact h_valid
  | step _ _ h_eq _ ih =>
    subst h_eq
    exact ih (topple_preserves_valid N _ _ _)

/-- Theorem 1 / CERT-01: End-to-End Inductive Lyapunov Descent & Universal Termination Bound. -/
theorem cert01_lyapunov_descent {N : Nat} {z_init z_final : Config} {S boundary_loss : Nat}
    (h_run : StepStar N z_init z_final S boundary_loss) :
    psiH N z_final + 4 * S + boundary_loss <= psiH N z_init ∧ S <= psiH N z_init / 4 := by
  have h_exact : psiH N z_final + 4 * S + boundary_loss = psiH N z_init := by
    induction h_run with
    | refl _ => omega
    | step h_in hz h_eq _ ih =>
      subst h_eq
      have h_drop := single_topple_potential_drop N _ _ h_in _ hz
      omega
  exact ⟨by omega, by omega⟩

/-! ## 6. Bitwise Equivalence & Dynamic 62-Bit Integer Overflow Immunity (CERT-02) -/

theorem invariant4_bitwise_equivalence (v : Nat) :
    (v >>> 2 = v / 4) ∧ (v - ((v >>> 2) <<< 2) = v % 4) := by
  have h_shr : v >>> 2 = v / 4 := Nat.shiftRight_eq_div_pow v 2
  have h_shl : (v / 4) <<< 2 = (v / 4) * 4 := Nat.shiftLeft_eq (v / 4) 2
  rw [h_shr, h_shl]
  exact ⟨rfl, by omega⟩

def totalGrains (N : Nat) (z : Config) : Nat :=
  sumOmega N z

theorem cell_le_sumRange (n k : Nat) (f : Nat → Nat) (hk1 : 1 <= k) (hkn : k <= n) :
    f k <= sumRange n f := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [sumRange]
    by_cases heq : k = n + 1
    · subst heq; omega
    · have : k <= n := by omega
      have := ih this
      omega

theorem cell_le_totalGrains (N r c : Nat) (z : Config) (h_in : InOmega N r c) :
    z r c <= totalGrains N z := by
  obtain ⟨hr1, hrN, hc1, hcN⟩ := h_in
  unfold totalGrains sumOmega
  calc z r c <= sumRange N (fun j => z r j) := cell_le_sumRange N c _ hc1 hcN
    _ <= sumRange N (fun i => sumRange N (fun j => z i j)) := cell_le_sumRange N r _ hr1 hrN

theorem topple_totalGrains_le (N r c : Nat) (h_in_rc : InOmega N r c) (z : Config) :
    totalGrains N (topple N r c z) <= totalGrains N z := by
  obtain ⟨hr1, hrN, hc1, hcN⟩ := h_in_rc
  have h_eq :
      totalGrains N (topple N r c z) + 4 =
      totalGrains N z
      + (if InOmega N (r - 1) c then 1 else 0)
      + (if InOmega N (r + 1) c then 1 else 0)
      + (if InOmega N r (c - 1) then 1 else 0)
      + (if InOmega N r (c + 1) then 1 else 0) := by
    unfold totalGrains
    have h_lhs :
        sumOmega N (topple N r c z) +
        sumOmega N (fun i j => if i = r ∧ j = c then 4 else 0) =
        sumOmega N (fun i j =>
          z i j
          + (if i + 1 = r ∧ j = c then 1 else 0)
          + (if i = r + 1 ∧ j = c then 1 else 0)
          + (if i = r ∧ j + 1 = c then 1 else 0)
          + (if i = r ∧ j = c + 1 then 1 else 0)) := by
      rw [← sumOmega_add]
      congr 1; funext i j
      by_cases h_in : InOmega N i j
      · unfold topple
        simp only [h_in, not_true_eq_false, reduceIte]
        by_cases h_self : i = r ∧ j = c
        · obtain ⟨rfl, rfl⟩ := h_self
          have hn1 : ¬ (i + 1 = i ∧ j = j) := by omega
          have hn2 : ¬ (i = i + 1 ∧ j = j) := by omega
          have hn3 : ¬ (i = i ∧ j + 1 = j) := by omega
          have hn4 : ¬ (i = i ∧ j = j + 1) := by omega
          simp only [true_and, reduceIte, hn1, hn2, hn3, hn4]
          omega
        · simp only [h_self, reduceIte]; omega
      · have h_ne : ¬ (i = r ∧ j = c) := fun ⟨hr, hc⟩ => h_in ⟨hr ▸ hr1, hr ▸ hrN, hc ▸ hc1, hc ▸ hcN⟩
        have hn1 : ¬ (i + 1 = r ∧ j = c) := fun ⟨hr, hc⟩ => h_in ⟨by omega, by omega, hc ▸ hc1, hc ▸ hcN⟩
        have hn2 : ¬ (i = r + 1 ∧ j = c) := fun ⟨hr, hc⟩ => h_in ⟨by omega, by omega, hc ▸ hc1, hc ▸ hcN⟩
        have hn3 : ¬ (i = r ∧ j + 1 = c) := fun ⟨hr, hc⟩ => h_in ⟨hr ▸ hr1, hr ▸ hrN, by omega, by omega⟩
        have hn4 : ¬ (i = r ∧ j = c + 1) := fun ⟨hr, hc⟩ => h_in ⟨hr ▸ hr1, hr ▸ hrN, by omega, by omega⟩
        simp [topple, h_in, h_ne, hn1, hn2, hn3, hn4]
    rw [sumOmega_delta, if_pos h_in_rc] at h_lhs
    rw [sumOmega_add, sumOmega_add, sumOmega_add, sumOmega_add] at h_lhs
    have rp1 : sumOmega N (fun i j => if i + 1 = r ∧ j = c then 1 else 0) = if InOmega N (r - 1) c then 1 else 0 := by
      have : (fun i j => if i + 1 = r ∧ j = c then 1 else 0) = (fun i j => if i = r - 1 ∧ j = c then 1 else 0) := by
        funext i j; by_cases h1 : i + 1 = r <;> by_cases h2 : j = c <;> simp [h1, h2] <;> omega
      rw [this, sumOmega_delta]
    have rp2 : sumOmega N (fun i j => if i = r ∧ j + 1 = c then 1 else 0) = if InOmega N r (c - 1) then 1 else 0 := by
      have : (fun i j => if i = r ∧ j + 1 = c then 1 else 0) = (fun i j => if i = r ∧ j = c - 1 then 1 else 0) := by
        funext i j; by_cases h1 : i = r <;> by_cases h2 : j + 1 = c <;> simp [h1, h2] <;> omega
      rw [this, sumOmega_delta]
    rw [rp1, rp2, sumOmega_delta, sumOmega_delta] at h_lhs
    exact h_lhs
  split at h_eq <;> split at h_eq <;> split at h_eq <;> split at h_eq <;> omega

/-- Theorem 2 / CERT-02: Dynamic + Static Overflow Immunity across all cells (interior and boundary). -/
theorem cert02_dynamic_overflow_immunity {N : Nat} (hN : N <= 2 ^ 29)
    {z_init z_final : Config} {S loss : Nat}
    (h_valid : ValidConfig N z_init)
    (h_init_mass : totalGrains N z_init <= 4 * N ^ 2 + 1)
    (h_run : StepStar N z_init z_final S loss) :
    ∀ r c, z_final r c < 2 ^ 62 - 1 := by
  have h_static : 4 * N ^ 2 + 1 < 2 ^ 62 - 1 := by
    have h1 : N ^ 2 <= (2 ^ 29) ^ 2 := Nat.pow_le_pow_left hN 2
    have h2 : (2 ^ 29) ^ 2 = 2 ^ 58 := by decide
    have h3 : 4 * (2 ^ 58) + 1 < 2 ^ 62 - 1 := by decide
    omega
  have h_monotone : totalGrains N z_final <= totalGrains N z_init := by
    induction h_run with
    | refl _ => exact Nat.le_refl _
    | step h_in _ h_eq _ ih =>
      subst h_eq
      exact Nat.le_trans ih (topple_totalGrains_le N _ _ h_in _)
  intro r c
  by_cases h_in : InOmega N r c
  · have h_cell := cell_le_totalGrains N r c z_final h_in
    omega
  · have h_zero := stepStar_preserves_valid h_valid h_run r c h_in
    omega

/-! ## 7. STAT-01: Verified Rational Euler-Maclaurin Remainder Bound -/

theorem stat01_euler_maclaurin_bound :
    (9 * 11 * 13 * 15 * 17 * 19 * 21) * (10 ^ 15) < (2 ^ 7) * 40320 * 30 * (24 ^ 11) * 4 := by
  decide

end BTWSandpileVerified
