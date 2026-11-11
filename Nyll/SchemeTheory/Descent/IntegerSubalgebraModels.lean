/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Descent.FgSubalgebraPullbackFinitePresentation
public import Nyll.SchemeTheory.Descent.FgSubalgebraProperFlatPullback
public import Mathlib.Algebra.Algebra.Subalgebra.Tower
public import Mathlib.RingTheory.Adjoin.FG
public import Mathlib.RingTheory.FiniteType

/-!
# Integer subalgebra models in the original coefficient universe

The integer image inside an arbitrary coefficient ring has the same universe as that ring.
Descent over this finitely generated image therefore applies the existing scheme model theorems
without lifting the coefficient ring or changing the original scheme. Restricting scalars back to
`ℤ` preserves the underlying subring, the structure morphism and the Cartesian comparison.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A scheme of finite presentation descends to an integer subalgebra in the original coefficient
ring's universe, retaining the specified coefficients and the actual Cartesian square. -/
theorem exists_int_subalgebra_isPullback_of_locallyOfFinitePresentation
    {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [QuasiCompact f] [QuasiSeparated f] [LocallyOfFinitePresentation f] (s : Finset A) :
    ∃ (T : Subalgebra ℤ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      ∃ (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (.of T)) (π : X ⟶ X₀),
        LocallyOfFinitePresentation f₀ ∧ QuasiCompact f₀ ∧ QuasiSeparated f₀ ∧
        IsPullback π f f₀ (Spec.map (CommRingCat.ofHom (algebraMap T A))) := by
  let B : Subalgebra ℤ A := ⊥
  have : Algebra.FiniteType ℤ B :=
    (Subalgebra.fg_iff_finiteType B).mp Subalgebra.fg_bot
  obtain ⟨T, hT, hs, X₀, f₀, π, hfp, hqc, hqs, hpb⟩ :=
    exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation (A₀ := B) f s
  have : Algebra.FiniteType B T := (Subalgebra.fg_iff_finiteType T).mp hT
  have hTInt : Algebra.FiniteType ℤ T :=
    Algebra.FiniteType.trans (R := ℤ) (S := B) (A := T) inferInstance inferInstance
  exact ⟨T.restrictScalars ℤ, (Subalgebra.fg_iff_finiteType _).mpr hTInt,
    hs, X₀, f₀, π, hfp, hqc, hqs, hpb⟩

/-- A proper smooth scheme descends to a proper smooth model over an integer subalgebra in the
original coefficient universe, with the same specified coefficients and Cartesian comparison. -/
theorem exists_int_subalgebra_isPullback_of_proper_smooth
    {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsProper f] [Smooth f] (s : Finset A) :
    ∃ (T : Subalgebra ℤ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      ∃ (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (.of T)) (π : X ⟶ X₀),
        IsProper f₀ ∧ Smooth f₀ ∧
          IsPullback π f f₀ (Spec.map (CommRingCat.ofHom (algebraMap T A))) := by
  let B : Subalgebra ℤ A := ⊥
  have : Algebra.FiniteType ℤ B :=
    (Subalgebra.fg_iff_finiteType B).mp Subalgebra.fg_bot
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℤ B
  obtain ⟨T, hT, hs, X₀, f₀, π, hproper, hsmooth, hpb⟩ :=
    ProperSmoothFinitePresentationDescent (A₀ := B) f s
  have : Algebra.FiniteType B T := (Subalgebra.fg_iff_finiteType T).mp hT
  have hTInt : Algebra.FiniteType ℤ T :=
    Algebra.FiniteType.trans (R := ℤ) (S := B) (A := T) inferInstance inferInstance
  exact ⟨T.restrictScalars ℤ, (Subalgebra.fg_iff_finiteType _).mpr hTInt,
    hs, X₀, f₀, π, hproper, hsmooth, hpb⟩

end AlgebraicGeometry
