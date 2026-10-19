/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.Modulus.LocalSymbolExistence
import Mathlib.Data.Finsupp.WellFounded

/-!
# Independence of modulus and the least conductor

Local symbols are unchanged when a modulus is enlarged. The common local
symbol for two moduli also satisfies their coefficientwise minimum, so a map
admitting any modulus has a unique least modulus. Existence of this conductor
uses the actual well-founded coefficientwise order on finitely supported
natural-number divisors.
-/

noncomputable section

namespace AlgebraicCurve.Modulus

variable {K F A : Type*} [Field K] [Field F] [Algebra K F] [AddCommGroup A]
  {D E : Modulus K F} {a : Place K F → A}

/-- A larger modulus imposes a stronger condition on its test functions. -/
theorem HasModulus.mono (ha : D.HasModulus a) (hDE : D ≤ E) : E.HasModulus a :=
  fun g hg => ha g (hg.mono hDE)

/-- The same actual local symbols satisfy every larger modulus. -/
theorem IsLocalSymbol.mono {σ : Place K F → Additive Fˣ →+ A}
    (hσ : D.IsLocalSymbol a σ) (hDE : D ≤ E) : E.IsLocalSymbol a σ := by
  refine ⟨fun v g hg => hσ.1 v g (hg.mono (hDE v)), ?_, hσ.2.2⟩
  intro v hv g
  have hDv : D v = 0 := Nat.eq_zero_of_le_zero (hv ▸ hDE v)
  exact hσ.2.1 v hDv g

variable [HasPrincipalDivisors K F]

/-- Local symbols obtained from different full moduli are the same actual
homomorphisms on nonzero functions. -/
theorem HasModulus.localSymbol_eq (hD : D.HasModulus a) (hE : E.HasModulus a) :
    hD.localSymbol = hE.localSymbol :=
  (hD.isLocalSymbol.mono (show D ≤ D ⊔ E from le_sup_left)).unique
    (hE.isLocalSymbol.mono (show E ≤ D ⊔ E from le_sup_right))

/-- The coefficientwise minimum of two actual moduli is again a modulus. -/
theorem HasModulus.inf (hD : D.HasModulus a) (hE : E.HasModulus a) :
    (D ⊓ E).HasModulus a := by
  have heq : hD.localSymbol = hE.localSymbol := hD.localSymbol_eq hE
  have hs : (D ⊓ E).IsLocalSymbol a hD.localSymbol := by
    refine ⟨?_, ?_, hD.isLocalSymbol.2.2⟩
    · intro v g hg
      by_cases hv : D v ≤ E v
      · have hn : (D ⊓ E) v = D v := min_eq_left hv
        rw [hn] at hg
        exact hD.isLocalSymbol.1 v g hg
      · have hn : (D ⊓ E) v = E v := min_eq_right (le_of_not_ge hv)
        rw [hn] at hg
        rw [heq]
        exact hE.isLocalSymbol.1 v g hg
    · intro v hv g
      change min (D v) (E v) = 0 at hv
      by_cases hDv : D v = 0
      · exact hD.isLocalSymbol.2.1 v hDv g
      · have hEv : E v = 0 := by omega
        rw [heq]
        exact hE.isLocalSymbol.2.1 v hEv g
  exact hs.hasModulus

/-- Every group-valued map that admits a modulus has a unique least one,
with leastness in every coefficient rather than merely in total degree. -/
theorem existsUnique_least_modulus (ha : ∃ D : Modulus K F, D.HasModulus a) :
    ∃! D : Modulus K F, D.HasModulus a ∧
      ∀ E : Modulus K F, E.HasModulus a → D ≤ E := by
  obtain ⟨D, hD, hmin⟩ := wellFounded_lt.has_min
    {D : Modulus K F | D.HasModulus a} ha
  have hleast (E : Modulus K F) (hE : E.HasModulus a) : D ≤ E := by
    rcases lt_or_eq_of_le (inf_le_left : D ⊓ E ≤ D) with hlt | heq
    · exact (hmin (D ⊓ E) (hD.inf hE) hlt).elim
    · exact heq.symm.trans_le inf_le_right
  refine ⟨D, ⟨hD, hleast⟩, ?_⟩
  intro E hE
  exact le_antisymm (hE.2 D hD) (hleast E hE.1)

/-- The least full modulus, constructed from a proved existence of a modulus. -/
def conductor (ha : ∃ D : Modulus K F, D.HasModulus a) : Modulus K F :=
  (existsUnique_least_modulus ha).choose

/-- The conductor itself has the modulus property. -/
theorem conductor_hasModulus (ha : ∃ D : Modulus K F, D.HasModulus a) :
    (conductor ha).HasModulus a :=
  (existsUnique_least_modulus ha).choose_spec.1.1

/-- Its universal lower bound compares all local multiplicities. -/
theorem conductor_le (ha : ∃ D : Modulus K F, D.HasModulus a)
    {E : Modulus K F} (hE : E.HasModulus a) : conductor ha ≤ E :=
  (existsUnique_least_modulus ha).choose_spec.1.2 E hE

end AlgebraicCurve.Modulus
