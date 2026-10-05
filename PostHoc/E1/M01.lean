import Mathlib

/-! -/

noncomputable section

open MeasureTheory

namespace NS1

abbrev abb_001 := {r : ℝ // 0 < r}

structure str_001 where
  gamma : ℝ
  nu : ℝ
  alpha : ℝ
  beta : ℝ
  nu_pos : 0 < nu
  alpha_pos : 0 < alpha
  beta_pos : 0 < beta

def def_001 (a b x : ℝ) : ℝ :=
  if 0 < x then
    Real.rpow b a / Real.Gamma a *
      Real.rpow x (-a - 1) * Real.exp (-b / x)
  else
    0

def def_002 (a b : abb_001) : Measure ℝ :=
  (volume : Measure ℝ).withDensity
    (fun x => ENNReal.ofReal (def_001 a.val b.val x))

def def_003 (m v z : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi * v))⁻¹ *
    Real.exp (-((z - m) ^ 2) / (2 * v))

def def_004 (m : ℝ) (v : abb_001) : Measure ℝ :=
  (volume : Measure ℝ).withDensity
    (fun z => ENNReal.ofReal (def_003 m v.val z))

def def_005 (p : str_001) : Measure ℝ :=
  def_002 ⟨p.alpha, p.alpha_pos⟩ ⟨p.beta, p.beta_pos⟩

def def_006 (p : str_001) (x : abb_001) : Measure ℝ :=
  def_004 p.gamma ⟨x.val / p.nu, div_pos x.property p.nu_pos⟩

def def_007 (m : ℝ) (x : abb_001) : Measure ℝ :=
  def_004 m x

def def_008 (p : str_001) (h : ℝ × ℝ) : ℝ :=
  def_001 p.alpha p.beta h.2 *
    def_003 p.gamma (h.2 / p.nu) h.1

def def_009 (p : str_001) : Measure (ℝ × ℝ) :=
  (volume : Measure (ℝ × ℝ)).withDensity
    (fun h => ENNReal.ofReal (def_008 p h))

def def_010 (p₀ : str_001) : Measure (ℝ × ℝ) :=
  def_009 p₀

abbrev abb_002 := (ℝ × ℝ) × ℝ

def def_011 (h : abb_002) : ℝ :=
  h.1.2

def def_012 (h : abb_002) : ℝ :=
  h.1.1

def def_013 (h : abb_002) : ℝ :=
  h.2

def def_014 (p : str_001) (h : abb_002) : ℝ :=
  def_008 p h.1 *
    def_003 (def_012 h) (def_011 h) (def_013 h)

def def_015 (p : str_001) : Measure abb_002 :=
  (volume : Measure abb_002).withDensity
    (fun h => ENNReal.ofReal (def_014 p h))

def def_016 (p : str_001) : Measure ℝ :=
  Measure.map def_013 (def_015 p)

def def_017 (p p₀ : str_001) : ℝ :=
  ∫ h : ℝ × ℝ,
    Real.log (def_008 p h / def_008 p₀ h) ∂(def_009 p)

abbrev abb_003 (Y : Type*) :=
  Measure ℝ → Y → EReal

def def_018 {Y : Type*} (reconstruction : abb_003 Y)
    (p p₀ : str_001) (weight : abb_001) (y : Y) : EReal :=
  reconstruction (def_016 p) y +
    ((weight.val * def_017 p p₀ : ℝ) : EReal)

end NS1
