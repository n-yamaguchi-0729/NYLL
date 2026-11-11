/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.RegularLocal.DualRegularPair
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.Noetherian.Basic
public import Nyll.SchemeTheory.RingTheory.Localization.LocalAlgebra

/-!
# Depth of the actual localized dual

Finite presentation identifies the localization of a dual with the
dual of the localization, using the native Hom-localization maps.
The regular-pair theorem therefore gives depth at least two to the
actual base change of a finite module's dual. In particular this applies
to localizations and to the stalk algebras of an affine scheme.
-/

@[expose] public section

noncomputable section

open TensorProduct RingTheory

namespace SchemeTheory

universe u v

variable (R : Type u) [CommRing R]
  (T : Submonoid R) (S : Type v) [CommRing S] [Algebra R S]
  [IsLocalization T S]
  (M : Type u) [AddCommGroup M] [Module R M]

/-- The canonical dual-localization comparison. Its value on an
original functional is the native extension of that functional. -/
def dualLocalizationEquiv [Module.FinitePresentation R M] :
    S ⊗[R] Module.Dual R M ≃ₗ[S] Module.Dual S (S ⊗[R] M) :=
  (IsLocalizedModule.linearEquiv T
    (TensorProduct.mk R S (Module.Dual R M) 1)
    (IsLocalizedModule.mapExtendScalars T
      (TensorProduct.mk R S M 1) (Algebra.linearMap R S) S)).extendScalarsOfIsLocalization T S

/-- The comparison preserves the actual evaluation pairing. -/
theorem dualLocalizationEquiv_apply_one_tmul [Module.FinitePresentation R M]
    (f : Module.Dual R M) (m : M) :
    dualLocalizationEquiv R T S M (1 ⊗ₜ[R] f) (1 ⊗ₜ[R] m) =
      algebraMap R S (f m) := by
  change (IsLocalizedModule.linearEquiv T
    (TensorProduct.mk R S (Module.Dual R M) 1)
    (IsLocalizedModule.mapExtendScalars T
      (TensorProduct.mk R S M 1) (Algebra.linearMap R S) S)
      ((TensorProduct.mk R S (Module.Dual R M) 1) f))
        ((TensorProduct.mk R S M 1) m) = _
  rw [IsLocalizedModule.linearEquiv_apply]
  exact IsLocalizedModule.map_apply T
    (TensorProduct.mk R S M 1) (Algebra.linearMap R S) f m

include T in
/-- Over a local Noetherian localization, the actual base change of a
finite module's dual inherits boundary depth from the base ring. -/
theorem two_le_depth_baseChange_dual
    [IsNoetherianRing R] [Module.Finite R M]
    [IsLocalRing S] [IsNoetherianRing S]
    (hdepth : (2 : ℕ∞) ≤ Module.depth S S) :
    (2 : ℕ∞) ≤ Module.depth S (S ⊗[R] Module.Dual R M) := by
  have : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  let e := dualLocalizationEquiv R T S M
  have he : Module.depth S (S ⊗[R] Module.Dual R M) =
      Module.depth S (Module.Dual S (S ⊗[R] M)) := by
    simp only [Module.depth, e.isWeaklyRegular_congr]
  rw [he]
  exact two_le_depth_dual S (S ⊗[R] M) hdepth

/-- The usual localized module of the dual, rather than a separately
chosen local model, has depth at least two at every such prime. -/
theorem two_le_depth_localized_dual
    [IsNoetherianRing R] [Module.Finite R M]
    (p : Ideal R) [p.IsPrime]
    (hdepth : (2 : ℕ∞) ≤
      Module.depth (Localization.AtPrime p) (Localization.AtPrime p)) :
    (2 : ℕ∞) ≤ Module.depth (Localization.AtPrime p)
      (LocalizedModule.AtPrime p (Module.Dual R M)) := by
  let e : LocalizedModule.AtPrime p (Module.Dual R M) ≃ₗ[Localization.AtPrime p]
      ((Localization.AtPrime p) ⊗[R] Module.Dual R M) :=
    LocalizedModule.equivTensorProduct p.primeCompl (Module.Dual R M)
  have hregular (rs : List (Localization.AtPrime p)) :
      Sequence.IsWeaklyRegular (LocalizedModule.AtPrime p (Module.Dual R M)) rs ↔
        Sequence.IsWeaklyRegular
          ((Localization.AtPrime p) ⊗[R] Module.Dual R M) rs :=
    LinearEquiv.isWeaklyRegular_congr (R := Localization.AtPrime p)
      (M := LocalizedModule.AtPrime p (Module.Dual R M))
      (M₂ := (Localization.AtPrime p) ⊗[R] Module.Dual R M) e rs
  have he : Module.depth (Localization.AtPrime p)
        (LocalizedModule.AtPrime p (Module.Dual R M)) =
      Module.depth (Localization.AtPrime p)
        ((Localization.AtPrime p) ⊗[R] Module.Dual R M) := by
    simp only [Module.depth, hregular]
  rw [he]
  exact two_le_depth_baseChange_dual R p.primeCompl (Localization.AtPrime p) M hdepth

end SchemeTheory
