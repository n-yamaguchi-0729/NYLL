/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
Repository: https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.DivisorClasses
import Nyll.AlgebraicCurves.Places.Evaluation.Value
import Nyll.AlgebraicCurves.Places.Evaluation.Evaluation

/-!
# A reduced rational point as modulus

For a single reduced rational place, normalizing a principal function by its
nonzero residue makes it congruent to one without changing its divisor. Thus
the abstract degree-zero divisor class group with this modulus is the existing
`Pic0`. This is an isomorphism of abstract groups, not of representing schemes.
-/

noncomputable section

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

/-- First-order congruence to one is precisely the existing residue-value
condition. No rationality hypothesis is needed for this local statement. -/
theorem congruentOne_one_iff_hasValue (v : Place K F) (f : F) :
    v.CongruentOne 1 f ↔ v.HasValue f 1 := by
  constructor
  · rintro ⟨u, rfl, hu⟩
    refine ⟨(u : v.toValuationSubring).2, ?_⟩
    have hres := (IsLocalRing.residue_eq_zero_iff
      ((u : v.toValuationSubring) - 1)).mpr (by simpa only [pow_one] using hu)
    simpa only [map_sub, map_one, sub_eq_zero] using hres
  · intro hf
    obtain ⟨u, hu⟩ := hf.isUnit one_ne_zero
    refine ⟨u, congrArg Subtype.val hu, ?_⟩
    rw [pow_one, ← IsLocalRing.residue_eq_zero_iff, map_sub, map_one,
      hu, hf.residue_eq, map_one, sub_self]

end Place

namespace Modulus

/-- At a reduced rational place, every ordinary principal divisor avoiding the
place admits a defining function congruent to one there. -/
theorem principal_single_one_of_isPrincipal (v : Place K F) (hv : v.IsRational)
    {E : Divisor K F} (haway : E ∈ divAway (Finsupp.single v 1 : Modulus K F))
    (hprincipal : E ∈ Divisor.principal) :
    E ∈ principal (Finsupp.single v 1 : Modulus K F) := by
  classical
  obtain ⟨f, hf, hE⟩ := hprincipal
  have hord : v.ord f = 0 := (hE v).symm.trans
    (haway v (by simp only [Finsupp.single_eq_same, ne_eq, one_ne_zero, not_false_eq_true]))
  obtain ⟨hm, hu⟩ := v.exists_isUnit_of_ord_eq_zero hf hord
  obtain ⟨c, hc, hc0⟩ := v.exists_hasValue_of_surjective hv hm
  have hcne : c ≠ 0 := hc0 hu
  have hval : v.HasValue (f * algebraMap K F c⁻¹) 1 := by
    simpa only [mul_inv_cancel₀ hcne] using hc.mul (v.hasValue_algebraMap c⁻¹)
  refine ⟨f * algebraMap K F c⁻¹, ?_, fun w => ?_⟩
  · apply (congruentOne_single v 1 _).mpr
    exact ⟨hval.ne_zero one_ne_zero,
      fun _ => (v.congruentOne_one_iff_hasValue _).mpr hval⟩
  · have hcn : algebraMap K F c⁻¹ ≠ 0 :=
      (map_ne_zero _).mpr (inv_ne_zero hcne)
    rw [w.ord_mul hf hcn,
      (w.hasValue_algebraMap c⁻¹).ord_eq_zero (inv_ne_zero hcne), add_zero]
    exact hE w

/-- Forgetting a reduced rational point as modulus is injective. -/
theorem toPic0_single_one_injective (v : Place K F) (hv : v.IsRational) :
    Function.Injective (toPic0 (Finsupp.single v 1 : Modulus K F)) := by
  apply (injective_iff_map_eq_zero (toPic0 (Finsupp.single v 1 : Modulus K F))).mpr
  intro x hx
  obtain ⟨E, rfl⟩ := QuotientAddGroup.mk_surjective x
  apply (QuotientAddGroup.eq_zero_iff E).mpr
  change (E : Divisor K F) ∈ principal (Finsupp.single v 1 : Modulus K F)
  exact principal_single_one_of_isPrincipal v hv E.2.1
    ((toPic0_mkZero_eq_zero_iff _ E).mp hx)

/-- A single reduced rational place imposes no extra relation on abstract
degree-zero divisor classes. Surjectivity uses the existing moving theorem,
whose hypothesis is `HasPrincipalDivisors K F`. -/
def singleOneEquivPic0 [HasPrincipalDivisors K F] (v : Place K F) (hv : v.IsRational) :
    ClassGroupZero (Finsupp.single v 1 : Modulus K F) ≃+ Pic0 K F :=
  AddEquiv.ofBijective (toPic0 (Finsupp.single v 1 : Modulus K F))
    ⟨toPic0_single_one_injective v hv, toPic0_surjective _⟩

end Modulus

end AlgebraicCurve
