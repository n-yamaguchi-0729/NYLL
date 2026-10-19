/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
Repository: https://github.com/n-yamaguchi-0729
-/

import Nyll.AlgebraicCurves.Divisors.Modulus.Modulus
import Nyll.JacobianVarieties.Pic0.MkEqNotMemSupport
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Divisor classes with a modulus

These are abstract divisor class groups, not a construction of a representing scheme.
The congruence uses units of the local ring modulo the full power of its maximal ideal.
The degree-zero quotient forgets the modulus to the existing `AlgebraicCurve.Pic0`.
-/

noncomputable section

namespace AlgebraicCurve.Modulus

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Divisors supported away from the support of the modulus. -/
def divAway (D : Modulus K F) : AddSubgroup (Divisor K F) where
  carrier := {E | ∀ v, D v ≠ 0 → E v = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' := by
    intro E G hE hG v hv
    simp only [Finsupp.add_apply, hE v hv, hG v hv, add_zero]
  neg_mem' := by
    intro E hE v hv
    simp only [Finsupp.neg_apply, hE v hv, neg_zero]

/-- Degree-zero divisors whose support avoids the modulus. -/
def divAwayZero (D : Modulus K F) : AddSubgroup (Divisor K F) :=
  D.divAway ⊓ Divisor.degZero

/-- Principal divisors of functions congruent to one along the modulus. -/
def principal (D : Modulus K F) : AddSubgroup (Divisor K F) where
  carrier := {E | ∃ f : F, D.CongruentOne f ∧ ∀ v, E v = v.ord f}
  zero_mem' := ⟨1, CongruentOne.one D, fun v => v.ord_one.symm⟩
  add_mem' := by
    rintro E G ⟨f, hf, hE⟩ ⟨g, hg, hG⟩
    exact ⟨f * g, hf.mul hg, fun v => by
      simp only [Finsupp.add_apply, hE v, hG v, v.ord_mul hf.ne_zero hg.ne_zero]⟩
  neg_mem' := by
    rintro E ⟨f, hf, hE⟩
    exact ⟨f⁻¹, hf.inv, fun v => by simp only [Finsupp.neg_apply, hE v, v.ord_inv]⟩

/-- A modulus-principal divisor avoids the modulus. -/
theorem principal_le_divAway (D : Modulus K F) : D.principal ≤ D.divAway := by
  rintro E ⟨f, hf, hE⟩ v hv
  exact (hE v).trans (hf.ord_eq_zero v hv)

/-- Forgetting the congruence leaves an ordinary principal divisor. -/
theorem principal_le_principal (D : Modulus K F) : D.principal ≤ Divisor.principal := by
  rintro E ⟨f, hf, hE⟩
  exact ⟨f, hf.ne_zero, hE⟩

/-- Degree zero follows from the existing principal-divisor theorem. -/
theorem principal_le_degZero [HasPrincipalDivisors K F] (D : Modulus K F) :
    D.principal ≤ Divisor.degZero := by
  rintro E ⟨f, hf, hE⟩
  obtain ⟨G, hG, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf.ne_zero
  have heq : E = G := Finsupp.ext fun v => (hE v).trans (hG v).symm
  exact Divisor.mem_degZero.mpr (heq ▸ hdeg)

/-- All divisor classes with modulus, with no degree restriction. -/
abbrev ClassGroup (D : Modulus K F) := D.divAway ⧸ D.principal.addSubgroupOf D.divAway

/-- Degree-zero divisor classes with modulus. -/
abbrev ClassGroupZero (D : Modulus K F) :=
  D.divAwayZero ⧸ D.principal.addSubgroupOf D.divAwayZero

/-- The degree-zero quotient map. -/
def mkZero (D : Modulus K F) : D.divAwayZero →+ D.ClassGroupZero :=
  QuotientAddGroup.mk' _

/-- The inclusion of degree-zero divisors avoiding the modulus into all degree-zero divisors. -/
def toDegreeZero (D : Modulus K F) : D.divAwayZero →+ Divisor.degZero (K := K) (F := F) where
  toFun E := ⟨E.1, E.2.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The forgetful homomorphism to the ordinary degree-zero divisor class group. -/
def toPic0 (D : Modulus K F) : D.ClassGroupZero →+ Pic0 K F :=
  QuotientAddGroup.map _ _ D.toDegreeZero (by
    intro E hE
    exact D.principal_le_principal hE)

@[simp]
theorem toPic0_mkZero (D : Modulus K F) (E : D.divAwayZero) :
    D.toPic0 (D.mkZero E) = Pic0.mk (D.toDegreeZero E) := rfl

/-- Moving ordinary divisors away from the finite support proves surjectivity. -/
theorem toPic0_surjective [HasPrincipalDivisors K F] (D : Modulus K F) :
    Function.Surjective D.toPic0 := by
  classical
  intro x
  obtain ⟨E, hE, haway⟩ := Pic0.exists_mk_eq_forall_notMem_support x D.support
  have ha : (E : Divisor K F) ∈ D.divAway := by
    intro v hv
    by_contra he
    exact haway v (Finsupp.mem_support_iff.mpr he) (Finsupp.mem_support_iff.mpr hv)
  exact ⟨D.mkZero ⟨E.1, ha, E.2⟩, hE⟩

/-- Forgetting the modulus kills precisely representatives that are ordinary principal divisors. -/
theorem toPic0_mkZero_eq_zero_iff (D : Modulus K F) (E : D.divAwayZero) :
    D.toPic0 (D.mkZero E) = 0 ↔ (E : Divisor K F) ∈ Divisor.principal := by
  exact QuotientAddGroup.eq_zero_iff _

/-- A smaller modulus imposes fewer support restrictions. -/
def restrictDivisors {D E : Modulus K F} (h : E ≤ D) : D.divAwayZero →+ E.divAwayZero where
  toFun G := ⟨G.1, (by
    intro v hv
    apply G.2.1 v
    intro hd
    have := h v
    simp only [hd, Nat.le_zero] at this
    exact hv this), G.2.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The canonical homomorphism induced by shrinking the modulus. -/
def transition {D E : Modulus K F} (h : E ≤ D) : D.ClassGroupZero →+ E.ClassGroupZero :=
  QuotientAddGroup.map _ _ (restrictDivisors h) (by
    rintro G ⟨f, hf, hG⟩
    exact ⟨f, hf.mono h, hG⟩)

@[simp]
theorem transition_mkZero {D E : Modulus K F} (h : E ≤ D) (G : D.divAwayZero) :
    transition h (D.mkZero G) = E.mkZero (restrictDivisors h G) := rfl

/-- Restriction to the same modulus is the identity. -/
@[simp]
theorem transition_refl (D : Modulus K F) (x : D.ClassGroupZero) :
    transition (le_refl D) x = x := by
  obtain ⟨G, rfl⟩ := QuotientAddGroup.mk_surjective x
  rfl

/-- Shrinking twice agrees with shrinking directly. -/
theorem transition_trans {D E G : Modulus K F} (h : E ≤ D) (h' : G ≤ E)
    (x : D.ClassGroupZero) : transition h' (transition h x) = transition (h'.trans h) x := by
  obtain ⟨H, rfl⟩ := QuotientAddGroup.mk_surjective x
  rfl

/-- Forgetting the modulus commutes with transition. -/
@[simp]
theorem toPic0_transition {D E : Modulus K F} (h : E ≤ D) (x : D.ClassGroupZero) :
    E.toPic0 (transition h x) = D.toPic0 x := by
  obtain ⟨G, rfl⟩ := QuotientAddGroup.mk_surjective x
  rfl

/-- The zero modulus has exactly the ordinary principal subgroup. -/
@[simp]
theorem principal_zero : (0 : Modulus K F).principal = Divisor.principal := by
  ext E
  constructor
  · intro h
    exact principal_le_principal (0 : Modulus K F) h
  · rintro ⟨f, hf, hE⟩
    exact ⟨f, (congruentOne_zero f).mpr hf, hE⟩

/-- With zero modulus, the forgetful homomorphism is injective. -/
theorem toPic0_zero_injective : Function.Injective (toPic0 (0 : Modulus K F)) := by
  apply (injective_iff_map_eq_zero (toPic0 (0 : Modulus K F))).mpr
  intro x hx
  obtain ⟨E, rfl⟩ := QuotientAddGroup.mk_surjective x
  apply (QuotientAddGroup.eq_zero_iff E).mpr
  change (E : Divisor K F) ∈ (0 : Modulus K F).principal
  rw [principal_zero]
  exact (toPic0_mkZero_eq_zero_iff 0 E).mp hx

/-- Every ordinary degree-zero divisor is allowed for the zero modulus. -/
theorem toPic0_zero_surjective : Function.Surjective (toPic0 (0 : Modulus K F)) := by
  intro x
  obtain ⟨E, rfl⟩ := Pic0.mk_surjective x
  have haway : E.1 ∈ divAway (0 : Modulus K F) := by
    intro v hv
    exact (hv rfl).elim
  exact ⟨mkZero 0 ⟨E.1, haway, E.2⟩, rfl⟩

/-- The zero-modulus abstract degree-zero class group recovers the existing `Pic0`. -/
def zeroEquivPic0 : (0 : Modulus K F).ClassGroupZero ≃+ Pic0 K F :=
  AddEquiv.ofBijective (toPic0 0) ⟨toPic0_zero_injective, toPic0_zero_surjective⟩

end AlgebraicCurve.Modulus
