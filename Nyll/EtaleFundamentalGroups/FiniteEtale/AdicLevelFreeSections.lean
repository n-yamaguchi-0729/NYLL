/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicClosedPullbackSections
import Nyll.SchemeTheory.Modules.Sections.FiniteFreeSections
import Nyll.SchemeTheory.Modules.Sections.InverseLimit
import Nyll.SchemeTheory.RingTheory.AdicCompletion.QuotientFreeSequence
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Original affine sections of closed-level free modules

The original pullback unit on a finite free sheaf has exactly the
coefficient ideal power as kernel. Its first-isomorphism comparison
identifies the actual closed-level sections with the literal quotient
coefficient vectors. This fixes the native source needed to compare
categorical syzygies with their affine presentation kernels.
-/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

open Scheme.Modules AdicModuleSystem

private theorem quotientFreeCoefficients_ker {R : Type u} [CommRing R]
    (I : Ideal R) (J : Type u) :
    (quotientFreeCoefficients I J).ker = I • (⊤ : Submodule R (J →₀ R)) := by
  let q : R →ₗ[R] R ⧸ I := (Ideal.Quotient.mkₐ R I).toLinearMap
  have hq : q.ker = I • (⊤ : Submodule R R) := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
    ext r
    exact Ideal.Quotient.eq_zero_iff_mem
  change (Finsupp.mapRange.linearMap (α := J) q).ker = _
  rw [Finsupp.ker_mapRange, hq, Finsupp.submodule_smul, Finsupp.submodule_top]

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) (I : Ideal A) (J : Type u) [Finite J]
  (U : X.affineOpens) (n : ℕ)

/-- The actual closed-level unit applied to the original finite free coefficients. -/
def levelFreeSectionsCoefficients :
    (J →₀ Γ(X, U)) →ₗ[Γ(X, U)]
      Γ(levelPullbackModule f I (show X.Modules from SheafOfModules.free J) n, U) :=
  { toFun := fun c =>
      (levelPullbackUnit f I (show X.Modules from SheafOfModules.free J) n).app U
        (finiteFreeSectionsEquiv (X := X) J (U : X.Opens) c)
    map_add' x y := by
      let η := levelPullbackUnit f I (show X.Modules from SheafOfModules.free J) n
      let e := finiteFreeSectionsEquiv (X := X) J (U : X.Opens)
      exact (congrArg (η.app U) (e.map_add x y)).trans (map_add (η.app U).hom (e x) (e y))
    map_smul' a x := by
      let η := levelPullbackUnit f I (show X.Modules from SheafOfModules.free J) n
      let e := finiteFreeSectionsEquiv (X := X) J (U : X.Opens)
      exact (congrArg (η.app U) (e.map_smul a x)).trans
        (Scheme.Modules.Hom.app_smul (U := (U : X.Opens)) η a (e x)) }

/-- The coefficient map uses the original unit on the original free section. -/
theorem levelFreeSectionsCoefficients_apply (a : J →₀ Γ(X, U)) :
    levelFreeSectionsCoefficients f I J U n a =
      (levelPullbackUnit f I (show X.Modules from SheafOfModules.free J) n).app U
        (finiteFreeSectionsEquiv (X := X) J (U : X.Opens) a) := rfl

/-- Every native closed-level free section has original coefficients. -/
theorem levelFreeSectionsCoefficients_surjective :
    Function.Surjective (levelFreeSectionsCoefficients f I J U n) :=
  (levelPullbackUnit_app_surjective f I
    (show X.Modules from SheafOfModules.free J) n U).comp
      (finiteFreeSectionsEquiv (X := X) J (U : X.Opens)).surjective

/-- The native coefficient map has the original ideal-power kernel. -/
theorem levelFreeSectionsCoefficients_ker :
    (levelFreeSectionsCoefficients f I J U n).ker =
      (sectionsIdeal f I U) ^ (n + 1) • (⊤ : Submodule Γ(X, U) (J →₀ Γ(X, U))) := by
  let e := finiteFreeSectionsEquiv (X := X) J (U : X.Opens)
  let K := (sectionsIdeal f I U) ^ (n + 1)
  have he : (K • (⊤ : Submodule Γ(X, U) (J →₀ Γ(X, U)))).map e.toLinearMap =
      K • (⊤ : Submodule Γ(X, U) Γ((show X.Modules from SheafOfModules.free J), U)) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr e.surjective]
  ext c
  change (levelPullbackUnit f I (show X.Modules from SheafOfModules.free J) n).app U
      (e c) = 0 ↔ c ∈ K • (⊤ : Submodule Γ(X, U) (J →₀ Γ(X, U)))
  rw [levelPullbackUnit_app_eq_zero_iff]
  change e c ∈ K • (⊤ : Submodule Γ(X, U)
    Γ((show X.Modules from SheafOfModules.free J), U)) ↔ _
  rw [← he]
  constructor
  · rintro ⟨b, hb, hbc⟩
    exact e.injective hbc ▸ hb
  · intro hc
    exact ⟨c, hc, rfl⟩

/-- Literal quotient coefficients identify with the actual native closed-level sections. -/
private def constructedLevelFreeSectionsEquiv :
    (J →₀ Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1)) ≃ₗ[Γ(X, U)]
      Γ(levelPullbackModule f I (show X.Modules from SheafOfModules.free J) n, U) := by
  let q := quotientFreeCoefficients ((sectionsIdeal f I U) ^ (n + 1)) J
  let l := levelFreeSectionsCoefficients f I J U n
  have hker : q.ker = l.ker :=
    (quotientFreeCoefficients_ker ((sectionsIdeal f I U) ^ (n + 1)) J).trans
      (levelFreeSectionsCoefficients_ker f I J U n).symm
  exact (LinearMap.quotKerEquivOfSurjective q
      (quotientFreeCoefficients_surjective ((sectionsIdeal f I U) ^ (n + 1)) J)).symm.trans
    ((Submodule.quotEquivOfEq q.ker l.ker hker).trans
      (LinearMap.quotKerEquivOfSurjective l
        (levelFreeSectionsCoefficients_surjective f I J U n)))

/-- Reduction of original coefficients becomes the original adjunction unit on sections. -/
private theorem constructedLevelFreeSectionsEquiv_coefficients (c : J →₀ Γ(X, U)) :
    constructedLevelFreeSectionsEquiv f I J U n
        (quotientFreeCoefficients ((sectionsIdeal f I U) ^ (n + 1)) J c) =
      levelFreeSectionsCoefficients f I J U n c := by
  let q := quotientFreeCoefficients ((sectionsIdeal f I U) ^ (n + 1)) J
  let l := levelFreeSectionsCoefficients f I J U n
  let eq := LinearMap.quotKerEquivOfSurjective q
    (quotientFreeCoefficients_surjective ((sectionsIdeal f I U) ^ (n + 1)) J)
  let el := LinearMap.quotKerEquivOfSurjective l
    (levelFreeSectionsCoefficients_surjective f I J U n)
  have hker : q.ker = l.ker :=
    (quotientFreeCoefficients_ker ((sectionsIdeal f I U) ^ (n + 1)) J).trans
      (levelFreeSectionsCoefficients_ker f I J U n).symm
  have hq : eq (Submodule.Quotient.mk c) = q c :=
    LinearMap.quotKerEquivOfSurjective_apply_mk q
      (quotientFreeCoefficients_surjective ((sectionsIdeal f I U) ^ (n + 1)) J) c
  change el ((Submodule.quotEquivOfEq q.ker l.ker hker) (eq.symm (q c))) = l c
  rw [← hq, eq.symm_apply_apply]
  exact LinearMap.quotKerEquivOfSurjective_apply_mk l
    (levelFreeSectionsCoefficients_surjective f I J U n) c

private theorem exists_levelFreeSectionsEquiv :
    ∃ e : (J →₀ Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1)) ≃ₗ[Γ(X, U)]
        Γ(levelPullbackModule f I (show X.Modules from SheafOfModules.free J) n, U),
      ∀ c : J →₀ Γ(X, U),
        e (quotientFreeCoefficients ((sectionsIdeal f I U) ^ (n + 1)) J c) =
          levelFreeSectionsCoefficients f I J U n c :=
  ⟨constructedLevelFreeSectionsEquiv f I J U n,
    constructedLevelFreeSectionsEquiv_coefficients f I J U n⟩

/-- The original coefficient-compatible equivalence, selected with its proved formula. -/
def levelFreeSectionsEquiv :
    (J →₀ Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1)) ≃ₗ[Γ(X, U)]
      Γ(levelPullbackModule f I (show X.Modules from SheafOfModules.free J) n, U) :=
  Classical.choose (exists_levelFreeSectionsEquiv f I J U n)

/-- The selected equivalence retains the original adjunction-unit formula. -/
theorem levelFreeSectionsEquiv_coefficients (c : J →₀ Γ(X, U)) :
    levelFreeSectionsEquiv f I J U n
        (quotientFreeCoefficients ((sectionsIdeal f I U) ^ (n + 1)) J c) =
      levelFreeSectionsCoefficients f I J U n c :=
  Classical.choose_spec (exists_levelFreeSectionsEquiv f I J U n) c

private theorem compatible_of_surjective_coefficients
    {P Q₁ Q₀ M₁ M₀ : Type u}
    (c₁ : P → Q₁) (hc₁ : Function.Surjective c₁) (c₀ : P → Q₀)
    (v : Q₁ → Q₀) (e₁ : Q₁ → M₁) (e₀ : Q₀ → M₀) (τ : M₁ → M₀)
    (l₁ : P → M₁) (l₀ : P → M₀)
    (hv : ∀ a, v (c₁ a) = c₀ a)
    (he₁ : ∀ a, e₁ (c₁ a) = l₁ a) (he₀ : ∀ a, e₀ (c₀ a) = l₀ a)
    (hl : ∀ a, l₀ a = τ (l₁ a)) (x : Q₁) : e₀ (v x) = τ (e₁ x) := by
  obtain ⟨a, rfl⟩ := hc₁ x
  exact (congrArg e₀ (hv a)).trans
    ((he₀ a).trans ((hl a).trans (congrArg τ (he₁ a).symm)))

private theorem app_comp_eq_of_eq {Y : Scheme.{u}} {P Q T : Y.Modules}
    (α : P ⟶ Q) (β : Q ⟶ T) (γ : P ⟶ T) (h : α ≫ β = γ)
    (W : Y.Opens) (x : Γ(P, W)) : β.app W (α.app W x) = γ.app W x := by
  have h' : α.app W ≫ β.app W = γ.app W :=
    (Scheme.Modules.Hom.comp_app (U := W) α β).symm.trans
      (congrArg (fun k => k.app W) h)
  exact congrArg (fun k : Γ(P, W) ⟶ Γ(T, W) => k x) h'

private theorem levelUnit_app_transition
    (M : X.Modules) (x : Γ(M, U)) :
    (levelPullbackUnit f I M n).app U x =
      (levelPullbackTransition f I M n).app U
        ((levelPullbackUnit f I M (n + 1)).app U x) :=
  (app_comp_eq_of_eq (levelPullbackUnit f I M (n + 1))
    (levelPullbackTransition f I M n) (levelPullbackUnit f I M n)
    (levelPullbackUnit_transition f I M n) (U : X.Opens) x).symm

/-- The literal coefficient maps commute with the original native level transition. -/
theorem levelFreeSectionsCoefficients_transition (a : J →₀ Γ(X, U)) :
    levelFreeSectionsCoefficients f I J U n a =
      (levelPullbackTransition f I (show X.Modules from SheafOfModules.free J) n).app U
        (levelFreeSectionsCoefficients f I J U (n + 1) a) :=
  (levelFreeSectionsCoefficients_apply f I J U n a).trans
    ((levelUnit_app_transition f I U n (show X.Modules from SheafOfModules.free J)
      (finiteFreeSectionsEquiv (X := X) J (U : X.Opens) a)).trans
      (congrArg
        ((levelPullbackTransition f I (show X.Modules from SheafOfModules.free J) n).app U)
        (levelFreeSectionsCoefficients_apply f I J U (n + 1) a).symm))

/-- The native comparison retains the literal coefficient transition between levels. -/
theorem levelFreeSectionsEquiv_transition
    (c : J →₀ Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1 + 1)) :
    levelFreeSectionsEquiv f I J U n
        (quotientFreeFactor J ((sectionsIdeal f I U) ^ (n + 1 + 1))
          (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))) c) =
      (levelPullbackTransition f I (show X.Modules from SheafOfModules.free J) n).app U
        (levelFreeSectionsEquiv f I J U (n + 1) c) := by
  apply compatible_of_surjective_coefficients
    (quotientFreeCoefficients ((sectionsIdeal f I U) ^ (n + 1 + 1)) J)
    (quotientFreeCoefficients_surjective ((sectionsIdeal f I U) ^ (n + 1 + 1)) J)
    (quotientFreeCoefficients ((sectionsIdeal f I U) ^ (n + 1)) J)
    (quotientFreeFactor J ((sectionsIdeal f I U) ^ (n + 1 + 1))
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))
    (levelFreeSectionsEquiv f I J U (n + 1)) (levelFreeSectionsEquiv f I J U n)
    ((levelPullbackTransition f I (show X.Modules from SheafOfModules.free J) n).app U)
    (levelFreeSectionsCoefficients f I J U (n + 1))
    (levelFreeSectionsCoefficients f I J U n)
    (fun a => LinearMap.congr_fun
      (quotientFreeFactor_coefficients J ((sectionsIdeal f I U) ^ (n + 1 + 1))
        (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))) a)
    (levelFreeSectionsEquiv_coefficients f I J U (n + 1))
    (levelFreeSectionsEquiv_coefficients f I J U n)
  exact levelFreeSectionsCoefficients_transition f I J U n

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
