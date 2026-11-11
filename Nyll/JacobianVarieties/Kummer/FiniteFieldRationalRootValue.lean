/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.JacobianVarieties.Kummer.PlaceOrdZeroRationalRootAction
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Finite-field values from original rational root specialization

At degree `|kˣ|`, the scalar by which an original Frobenius decomposition
element moves a root is the actual order-zero value of its function. The
proof uses one specialization retaining both root scaling and the actual
decomposition action, with the prescribed constant embedding unchanged.
-/

@[expose] public section

universe u

noncomputable section

open SchemeTheory EtaleFundamentalGroups.Inertia

namespace AlgebraicCurve.Place

attribute [local instance] normalizationCommAlgGaloisAction

variable (k F κ Ω : Type u) [Field k] [Fintype k] [Field F] [Field κ] [Field Ω]
  [Algebra k F] [Algebra k κ] [Algebra k Ω] [Algebra F Ω] [Algebra κ Ω]
  [IsScalarTower k F Ω] [IsScalarTower k κ Ω]
  [IsAlgClosed κ] [Normal k κ]
  [IsGalois F Ω] [IsSepClosed Ω]

/-- The scalar of the original Frobenius action on an actual radical
equals the original value of its function at the rational place. -/
theorem ordZeroValue_eq_of_frobenius_rootScale
    (v : Place k F) (hv : v.IsRational)
    [Algebra v.toValuationSubring Ω] [IsScalarTower v.toValuationSubring F Ω]
    [IsScalarTower k v.toValuationSubring Ω]
    (Q : Ideal (normalizationCommAlgCat v.toValuationSubring Ω)) [Q.IsMaximal]
    (u : Fˣ) (hu : v.ord (u : F) = 0)
    (r : Ω) (hr : r ^ Nat.card kˣ = algebraMap F Ω (u : F))
    (d : normalizationDecompositionGroup v.toValuationSubring F Ω Q)
    (hd : (d.val.restrictScalars k).restrictNormal κ =
      FiniteField.frobeniusAlgEquivOfAlgebraic k κ)
    (a : kˣ) (ha : d.val r = algebraMap k Ω (a : k) * r) :
    ordZeroValue v hv u hu = a := by
  classical
  have : (show Ideal (integralClosure v.toValuationSubring Ω) from Q).IsMaximal :=
    inferInstanceAs Q.IsMaximal
  have hcardUnit : (Nat.card kˣ : k) = -1 := by
    rw [Nat.card_units, Nat.card_eq_fintype_card,
      Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero),
      Nat.cast_card_eq_zero, Nat.cast_one, zero_sub]
  have hn : IsUnit (Nat.card kˣ : k) := hcardUnit.symm ▸ isUnit_one.neg
  obtain ⟨E, _hlift, hscale, haction⟩ :=
    exists_ordZero_rationalRootSpecialization_scaling_equivariant
      v hv u hu (Nat.card kˣ) hn κ Ω Q
  let b : {b : Ω // b ^ Nat.card kˣ = algebraMap F Ω (u : F)} := ⟨r, hr⟩
  let x : κ := (E b).val
  have hpow : x ^ Nat.card kˣ = algebraMap k κ (ordZeroValue v hv u hu : k) :=
    (E b).property
  have hx : x ≠ 0 := by
    intro hz
    rw [hz, zero_pow (Nat.card_pos (α := kˣ)).ne'] at hpow
    exact ((ordZeroValue v hv u hu).isUnit.map (algebraMap k κ)).ne_zero hpow.symm
  let ζ : rootsOfUnity (Nat.card kˣ) κ :=
    restrictRootsOfUnity (algebraMap k κ) (Nat.card kˣ)
      ⟨a, (mem_rootsOfUnity _ _).mpr (pow_card_eq_one' (x := a))⟩
  have hscalar : (ζ.val : κ) = algebraMap k κ (a : k) := rfl
  have hroot : d.val r = algebraMap κ Ω (ζ.val : κ) * r := by
    rw [hscalar, ← IsScalarTower.algebraMap_apply k κ Ω]
    exact ha
  have hvalue :
      ((d.val.restrictScalars k).restrictNormal κ) x = (ζ.val : κ) * x := by
    refine (haction d b).symm.trans (Eq.trans ?_ (hscale ζ b))
    exact congrArg
      (fun t : {b : Ω // b ^ Nat.card kˣ = algebraMap F Ω (u : F)} => (E t).val)
      (Subtype.ext hroot)
  rw [hd, hscalar] at hvalue
  have hfrob : x ^ Nat.card k = algebraMap k κ (a : k) * x := by
    rw [Nat.card_eq_fintype_card]
    exact (congrFun (FiniteField.coe_frobeniusAlgEquivOfAlgebraic k κ) x).symm.trans hvalue
  have hcard : Nat.card kˣ + 1 = Nat.card k := by
    exact (Nat.card_eq_card_units_add_one k).symm
  apply Units.ext
  apply (algebraMap k κ).injective
  apply mul_right_cancel₀ hx
  rw [← hpow, ← pow_succ, hcard]
  exact hfrob

end AlgebraicCurve.Place
