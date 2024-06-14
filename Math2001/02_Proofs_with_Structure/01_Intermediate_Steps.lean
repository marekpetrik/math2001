/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

-- my examples
example {x y : ℝ} (h1 : x ≥ 0) (h2 : y ≥ 0) : x*y ≥ 0 := by extra

example {x y : ℝ} (h1 : x ≥ 0) (h2 : -y ≥ 0) : x*y ≤ 0 := 
  calc 
    x*y ≤ x*y + (x*(-y)) := by extra
    _  = 0 := by ring
    
example {x : ℝ} (h1: x ≤ 0) : -x ≥ 0 := by linarith[h1]

example {x y : ℝ} (h1 : x ≥ 0) (h2 : y ≤ 0) : x*y ≤ 0 := 
  calc
    x * y ≤ x * 0 := by rel[h2]
    _ = 0 := by ring
--  have ha : -y ≥ 0 := by linarith[h2]
--  sorry


example {x y : ℝ} (h1 : x ≤ 0) (h2 : y ≤ 0) : x*y ≥ 0 := by
  have ha: (-x ≥ 0) := by linarith[h1]
  have hb: (-y ≥ 0) := by linarith[h2]
  calc
    x * y = (-x) * (-y) := by ring 
    _ ≥ (-x) * 0 := by rel[ha,hb]
    _ = 0 := by ring

example {x : ℝ} : x ≥ x - 1 := 
  calc
    x = x - 1 + 1 := by ring
    _ ≥ x - 1 := by extra

--- book's examples

example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 := by
  have hb : b = 1 := by addarith [h2]
  calc
    a = a - 5 * b + 5 * b := by ring
    _ = 4 + 5 * 1 := by rw [h1, hb]
    _ = 9 := by ring


example {m n : ℤ} (h1 : m + 3 ≤ 2 * n - 1) (h2 : n ≤ 5) : m ≤ 6 := by
  have h3 :=
  calc
    m + 3 ≤ 2 * n - 1 := by rel [h1]
    _ ≤ 2 * 5 - 1 := by rel [h2]
    _ = 9 := by numbers
  addarith [h3]


example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 := by
  have h3 : r ≤ 3 + s := by addarith[h1]
  have h4 : r ≤ 3 - s := by addarith[h2]
  calc
    r = (r + r) / 2 := by ring
    _ ≤ (3 - s + (3 + s)) / 2 := by rel[h3,h4]
    _ = 3 := by ring

example {t : ℝ} (h1 : t ^ 2 = 3 * t) (h2 : t ≥ 1) : t ≥ 2 := by
  have h3 :=
  calc t * t = t ^ 2 := by ring
    _ = 3 * t := by rw [h1]
  cancel t at h3
  calc 
    t = 3 := by rw[h3]
    _ ≥ 2 := by numbers


example {a b : ℝ} (h1 : a ^ 2 = b ^ 2 + 1) (h2 : a ≥ 0) : a ≥ 1 := by
  have h3 :=
  calc
    a^2 = b^2 + 1 := by rw [h1]
    _ ≥ 1     := by extra
    _ = 1 ^ 2 := by ring
  cancel 2 at h3


example {x y : ℤ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 := by
  have hz : x ≤ -1 := by addarith[hx]
  calc
    y ≥ 3 - 2*x     := by addarith[hy]
    _ ≥ 3 - 2*(-1)  := by rel[hz]
    _ > 3           := by numbers

example (a b : ℝ) (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  have ha : a + b ≥ 0 := by addarith[h1]
  have hb : b - a ≥ 0 := by addarith[h2]
  calc
    a^2 ≤ a^2 + (a+b)*(b-a) := by extra -- add zero, automatically recognizes terms
    _ = b^2 := by ring

-- the cube function is monotone
--- theorem exm1 (a b : ℝ) (h : a ≤ b) : a ^ 3 ≤ b ^ 3 := by
example (a b : ℝ) (h : a ≤ b) : a ^ 3 ≤ b ^ 3 := by
  have ha : b - a ≥ 0 := by addarith[h]
  calc
    a^3 ≤ a^3 + (b-a) * ( (b-a)^2 + 3*(b+a)^2) / 4 := by extra 
    _ = b^3 := by ring

--- #print exm1
/-! # Exercises -/


example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  have ha : x * (x + 2) = 2 * (x + 2) := by 
    --linarith [h1]
    -- TODO: there should be a simpler way than below
    calc
      x * (x + 2)  = x^2 + 2*x := by ring
      _ = 4 + 2*x := by rw[h1]
      _ = 2 * (x+2) := by ring
  cancel (x+2) at ha  -- can cancel because I know that x+2 ≠ 0
  

example {n : ℤ} (hn : n ^ 2 + 4 = 4 * n) : n = 2 := by
  have ha : (n - 2)^2 = 0 := by 
    calc 
      (n-2)^2 = n^2 - 4*n + 4 := by ring
      _ = 0 := by addarith[hn]
  cancel 2 at ha

-- this is a good one!
example (x y : ℚ) (h1 : x * y = 1) (h2 : x ≥ 1) : y ≤ 1 := by
  have ha: (0 < x * y) := by addarith[h1]
  have hb: (1 - x ≤ 0) := by addarith[h2]
  cancel x at ha  -- uses h2 implicitly
  calc 
    y = y*(1 - x) + x*y := by ring
    _ = y*(1-x) + 1 := by rw[h1]
    _ ≤ y*0 + 1 := by rel[h2,hb]
    _ = 0 + 1 := by ring
    _ ≤ 1 := by numbers

