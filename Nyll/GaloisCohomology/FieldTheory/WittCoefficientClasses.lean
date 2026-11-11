/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.FieldTheory.WittCoefficientFrobenius
public import Nyll.GaloisCohomology.ArtinSchreier.WittCharacters

/-!
# Vanishing of coefficient-Frobenius coinvariants on Witt classes

Arithmetic coefficient Frobenius commutes with absolute Frobenius. Its
difference from the identity is therefore surjective on the actual
Artin–Schreier–Witt quotient of the scalar-extended coordinate ring,
at every finite Witt length and every positive arithmetic Frobenius power.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace FiniteField

variable (k Ω R : Type*) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
  [Algebra.IsAlgebraic k Ω] [CommRing R] [Algebra k R]
  (p m : ℕ) [Fact p.Prime] [CharP (R ⊗[k] Ω) p]

/-- Coefficient Frobenius on the actual finite-length Witt classes. -/
def coefficientFrobeniusWittClasses (n : ℕ) :
    TruncatedWittVector p m (R ⊗[k] Ω) ⧸
      ((TruncatedWittVector.map (frobenius (R ⊗[k] Ω) p)).toAddMonoidHom -
        AddMonoidHom.id (TruncatedWittVector p m (R ⊗[k] Ω))).range →+
    TruncatedWittVector p m (R ⊗[k] Ω) ⧸
      ((TruncatedWittVector.map (frobenius (R ⊗[k] Ω) p)).toAddMonoidHom -
        AddMonoidHom.id (TruncatedWittVector p m (R ⊗[k] Ω))).range :=
  QuotientAddGroup.map _ _
    (TruncatedWittVector.map (coefficientFrobenius k Ω R n).toRingHom).toAddMonoidHom (by
      rintro a ⟨b, rfl⟩
      refine ⟨TruncatedWittVector.map (coefficientFrobenius k Ω R n).toRingHom b, ?_⟩
      change TruncatedWittVector.map (frobenius (R ⊗[k] Ω) p)
          (TruncatedWittVector.map (coefficientFrobenius k Ω R n).toRingHom b) -
          TruncatedWittVector.map (coefficientFrobenius k Ω R n).toRingHom b =
        TruncatedWittVector.map (coefficientFrobenius k Ω R n).toRingHom
          (TruncatedWittVector.map (frobenius (R ⊗[k] Ω) p) b - b)
      rw [map_sub, TruncatedWittVector.map_frobenius])

variable [IsAlgClosed Ω]

/-- Coefficient Frobenius has no additive coinvariants on the original
Witt classes of any finite length. -/
theorem coefficientFrobeniusWittClasses_sub_id_surjective (n : ℕ) (hn : n ≠ 0) :
    Function.Surjective (fun x => coefficientFrobeniusWittClasses k Ω R p m n x - x) := by
  let N := ((TruncatedWittVector.map (frobenius (R ⊗[k] Ω) p)).toAddMonoidHom -
    AddMonoidHom.id (TruncatedWittVector p m (R ⊗[k] Ω))).range
  intro a
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk'_surjective N a
  obtain ⟨b, hb⟩ := coefficientFrobenius_witt_sub_id_surjective k Ω R p n hn m r
  have hdiff :
      TruncatedWittVector.map (coefficientFrobenius k Ω R n).toRingHom
          (WittVector.truncate m b) - WittVector.truncate m b = r := by
    rw [TruncatedWittVector.map_wittVector_truncate, ← map_sub]
    exact hb
  refine ⟨QuotientAddGroup.mk' N (WittVector.truncate m b), ?_⟩
  change QuotientAddGroup.mk' N
      (TruncatedWittVector.map (coefficientFrobenius k Ω R n).toRingHom
        (WittVector.truncate m b)) - QuotientAddGroup.mk' N (WittVector.truncate m b) =
      QuotientAddGroup.mk' N r
  rw [← map_sub, hdiff]

end FiniteField
