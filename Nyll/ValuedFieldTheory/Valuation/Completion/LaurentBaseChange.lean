/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.LaurentSeries
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Laurent Base Change
-/

noncomputable section

open HahnSeries IntermediateField

namespace ModularCurve

section CoeffMap

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

/-- The homomorphism of Laurent series induced by a homomorphism of coefficient rings. -/
def coeffMap (f : R →+* S) : LaurentSeries R →+* LaurentSeries S where
  toFun x := x.map f
  map_zero' := by
    ext k
    exact map_zero f
  map_one' := HahnSeries.map_one f.toMonoidWithZeroHom
  map_add' x y := HahnSeries.map_add f.toAddMonoidHom
  map_mul' x y := HahnSeries.map_mul (f := (f : R →ₙ+* S))
@[simp]
theorem coeffMap_coeff (f : R →+* S) (x : LaurentSeries R) (k : ℤ) :
    (coeffMap f x).coeff k = f (x.coeff k) :=
  rfl
@[simp]
theorem coeffMap_single (f : R →+* S) (k : ℤ) (r : R) :
    coeffMap f (HahnSeries.single k r) = HahnSeries.single k (f r) := by
  ext m
  rcases eq_or_ne m k with rfl | hm
  · simp only [coeffMap_coeff, HahnSeries.coeff_single_same]
  · simp only [coeffMap_coeff, HahnSeries.coeff_single_of_ne hm, map_zero]

theorem coeffMap_coeffMap (g : S →+* T) (f : R →+* S) (x : LaurentSeries R) :
    coeffMap g (coeffMap f x) = coeffMap (g.comp f) x := by
  ext k
  rfl
@[simp]
theorem coeffMap_id (x : LaurentSeries R) : coeffMap (RingHom.id R) x = x := by
  ext k
  rfl

theorem coeffMap_congr {f g : R →+* S} (h : f = g) (x : LaurentSeries R) :
    coeffMap f x = coeffMap g x := by
  subst h; rfl

end CoeffMap

section Constants

variable (L : Type*) [Field L]

theorem algebraMap_laurentSeries_eq_single (c : L) :
    algebraMap L (LaurentSeries L) c = HahnSeries.single 0 c := by
  have h1 : algebraMap L (PowerSeries L) c = PowerSeries.C c := by
    rw [PowerSeries.algebraMap_apply, Algebra.algebraMap_self_apply]
  rw [HahnSeries.algebraMap_apply', h1, HahnSeries.ofPowerSeries_C]
  rfl

variable {L} in
theorem coeffMap_algebraMap (φ : L →+* L) (c : L) :
    coeffMap φ (algebraMap L (LaurentSeries L) c) = algebraMap L (LaurentSeries L) (φ c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

variable [Algebra ℚ L]

/-- The inclusion of rational-coefficient Laurent series into Laurent series over the extension
field. -/
def coeffEmb : LaurentSeries ℚ →+* LaurentSeries L :=
  coeffMap (algebraMap ℚ L)
@[simp]
theorem coeffEmb_coeff (x : LaurentSeries ℚ) (k : ℤ) :
    (coeffEmb L x).coeff k = algebraMap ℚ L (x.coeff k) :=
  rfl

variable {L} in
theorem coeffMap_coeffEmb (σ : L ≃ₐ[ℚ] L) (x : LaurentSeries ℚ) :
    coeffMap (σ : L →+* L) (coeffEmb L x) = coeffEmb L x := by
  rw [coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr (RingHom.ext fun c => σ.commutes c) x

end Constants

section BaseChange

variable (L : Type*) [Field L] [Algebra ℚ L]
variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ))

/-- The intermediate field generated after extending the coefficients of the Laurent series. -/
def laurentBaseChange : IntermediateField L (LaurentSeries L) :=
  IntermediateField.adjoin L (⇑(coeffEmb L) '' (F₀ : Set (LaurentSeries ℚ)))

variable {F₀} in
theorem coeffEmb_mem_laurentBaseChange {x : LaurentSeries ℚ} (hx : x ∈ F₀) :
    coeffEmb L x ∈ laurentBaseChange L F₀ :=
  IntermediateField.subset_adjoin L _ ⟨x, hx, rfl⟩

variable {L F₀} in
theorem mem_laurentBaseChange_iff {x : LaurentSeries L} :
    x ∈ laurentBaseChange L F₀ ↔
      x ∈ Subfield.closure
        (Set.range (algebraMap L (LaurentSeries L)) ∪
          (⇑(coeffEmb L) '' (F₀ : Set (LaurentSeries ℚ)))) :=
  Iff.rfl

variable {L F₀} in
theorem coeffMap_mem_laurentBaseChange (σ : L ≃ₐ[ℚ] L) {x : LaurentSeries L}
    (hx : x ∈ laurentBaseChange L F₀) :
    coeffMap (σ : L →+* L) x ∈ laurentBaseChange L F₀ := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨z, hz, rfl⟩
      · rw [coeffMap_algebraMap]
        exact (laurentBaseChange L F₀).algebraMap_mem _
      · rw [coeffMap_coeffEmb]
        exact coeffEmb_mem_laurentBaseChange L hz
  | one =>
      rw [map_one]
      exact (laurentBaseChange L F₀).one_mem
  | add x y _ _ hx hy =>
      rw [map_add]
      exact add_mem hx hy
  | neg x _ hx =>
      rw [map_neg]
      exact neg_mem hx
  | inv x _ hx =>
      rw [map_inv₀]
      exact inv_mem hx
  | mul x y _ _ hx hy =>
      rw [map_mul]
      exact mul_mem hx hy

end BaseChange

end ModularCurve

end
