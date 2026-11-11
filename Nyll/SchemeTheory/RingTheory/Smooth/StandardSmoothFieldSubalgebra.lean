/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Smooth.Field
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree

/-!
# Standard smooth subalgebras containing prescribed field coordinates

Every finitely generated subalgebra of a field over a perfect coefficient
field is contained in an actual standard smooth subalgebra of that field.
The larger subalgebra is the image of a principal localization of the
original one, and the localization map into the field is proved injective.

The target field need not be perfect or finite type as an algebra. In
particular, this applies over a perfect prime field to the finitely many
coordinates of a finite extension of a residue field. Standard smoothness
provides an actual finite submersive presentation for the larger algebra;
formal smoothness of the field is not used as a finite presentation.
-/

@[expose] public section

noncomputable section

universe u v

namespace Subalgebra

/-- A finite collection of field coordinates over a perfect coefficient
field lies in an actual standard smooth subalgebra of that same field. -/
theorem exists_le_isStandardSmooth_of_fg
    {K : Type u} {L : Type v} [Field K] [PerfectField K] [Field L] [Algebra K L]
    (S : Subalgebra K L) (hS : S.FG) :
    ∃ T : Subalgebra K L, S ≤ T ∧ Algebra.IsStandardSmooth K T := by
  have : Algebra.FiniteType K S := S.fg_iff_finiteType.mp hS
  have : Algebra.FinitePresentation K S :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let F := Localization.AtPrime (⊥ : Ideal S)
  have : IsFractionRing S F := by
    change IsLocalization (nonZeroDivisors S) F
    rw [← Ideal.primeCompl_bot]
    infer_instance
  let : Field F := IsFractionRing.toField S
  have : Algebra.IsSmoothAt K (⊥ : Ideal S) :=
    Algebra.FormallySmooth.of_perfectField
  obtain ⟨d, hd, hstd⟩ :=
    Algebra.IsSmoothAt.exists_notMem_isStandardSmooth K (⊥ : Ideal S)
  have hu : IsUnit (S.val d) := by
    apply isUnit_iff_ne_zero.mpr
    intro h
    apply hd
    exact Ideal.mem_bot.mpr (Subtype.ext h)
  let β : Localization.Away d →ₐ[K] L := IsLocalization.Away.liftAlgHom d hu
  have hβ (x : S) : β (algebraMap S (Localization.Away d) x) = (x : L) :=
    IsLocalization.Away.lift_eq d hu x
  have hβinj : Function.Injective β := by
    apply (IsLocalization.injective_iff_map_algebraMap_eq
      (Submonoid.powers d) β.toRingHom).mpr
    intro x y
    constructor
    · exact congrArg β
    · intro h
      have hxy : (x : L) = (y : L) := (hβ x).symm.trans (h.trans (hβ y))
      exact congrArg (algebraMap S (Localization.Away d)) (Subtype.ext hxy)
  have : Algebra.IsStandardSmooth K (Localization.Away d) := hstd
  refine ⟨β.range, ?_, Algebra.IsStandardSmooth.of_algEquiv (AlgEquiv.ofInjective β hβinj)⟩
  intro x hx
  exact ⟨algebraMap S (Localization.Away d) ⟨x, hx⟩, hβ ⟨x, hx⟩⟩

end Subalgebra
