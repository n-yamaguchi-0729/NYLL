/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.NativeSourceAbelianComparison
public import Nyll.GaloisCohomology.Kummer.NativeSemilinearConjugation
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGaloisNaturality
public import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedMaps
public import Nyll.ProCGroups.Topologies.Conjugation

/-!
# Native field conjugation on an actual covering group

An original ambient Galois automorphism restricts to the actual normal
covering field. Transporting its semilinear conjugation to that field's
native separable closure gives an original native absolute action.

The actual generic-source naturality square identifies this action with
conjugation by the same original ambient fundamental-group element on the
actual covering subgroup. The comparison is proved before abelianization
and therefore retains all original abelian representatives afterward.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.PreGaloisCategory
open AlgebraicGeometry ProCGroups.Abelian KummerTheory

namespace AlgebraicGeometry.FiniteEtale

variable (K L Ω : Type u) [Field K] [Field L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
  [Normal K L] [IsSepClosure K Ω] [IsSepClosure L Ω] [IsSepClosed Ω]
  {X : Scheme.{u}} [IsIntegral X]
  (W : FiniteEtale X) [IsIntegral W.left]
  (p : Spec (.of K) ⟶ X) (q : Spec (.of L) ⟶ W.left)
  (hpoint : (ξ L Ω ≫ q) ≫ W.hom = ξ K Ω ≫ p)
  (M : OpenNormalSubgroup π₁ᵉᵗ(ξ K Ω ≫ p))
  (eW : π₁ᵉᵗ(ξ L Ω ≫ q) ≃ₜ* M.toSubgroup)
  (heW : ∀ g : π₁ᵉᵗ(ξ L Ω ≫ q),
    (eW g).val = pointedFundamentalGroupHom W.hom
      (ξ L Ω ≫ q) (ξ K Ω ≫ p) hpoint g)
  (eL : SeparableClosure L ≃ₐ[L] Ω)

include heW in
omit [Normal K L] in
/-- The original native covering source, included into the original
ambient group, is literal restriction of scalars of its original Galois action. -/
theorem nativeSourceGaloisHom_cover_image (τ : Gal(SeparableClosure L/L)) :
    (eW (nativeSourceGaloisHomOfClosure q eL τ)).val =
      fieldSourceAbsoluteGaloisHom K Ω p ((AlgEquiv.autCongr eL τ).restrictScalars K) := by
  have : IsIntegral ((Functor.fromPUnit X).obj W.right) := inferInstanceAs (IsIntegral X)
  have : IsIntegral ((𝟭 Scheme).obj W.left) := inferInstanceAs (IsIntegral W.left)
  rw [heW, nativeSourceGaloisHomOfClosure_apply]
  have htransport {x y : Spec (.of Ω) ⟶ X} (h : x = y) (a : π₁ᵉᵗ(x)) :
      continuousConjAut (eqToIso (congrArg fiber h)) a = h ▸ a := by
    subst y
    rfl
  exact (pointedFundamentalGroupHom_apply W.hom (ξ L Ω ≫ q) (ξ K Ω ≫ p) hpoint
    (fieldSourceAbsoluteGaloisHom L Ω q (AlgEquiv.autCongr eL τ))).trans
      ((htransport hpoint _).symm.trans
        (fieldSourceAbsoluteGaloisHom_naturality K L Ω W.hom q p hpoint
          (AlgEquiv.autCongr eL τ)))

variable (σ : Gal(Ω/K))

local notation "τL" => AlgEquiv.toRingEquiv (AlgEquiv.restrictNormal σ L)
local notation "hσ" => fun x : L => Eq.symm (AlgEquiv.restrictNormal_commutes σ L x)
local notation "δ" => nativeSemilinearGaloisEquiv eL τL (AlgEquiv.toRingEquiv σ) hσ
local notation "g" => fieldSourceAbsoluteGaloisHom K Ω p σ

include heW in
/-- Native semilinear conjugation is the same original ambient
conjugation on the actual covering subgroup, before any abelian quotient. -/
theorem nativeSourceGaloisHom_cover_conjugation
    (ρ : Gal(SeparableClosure L/L)) :
    eW (nativeSourceGaloisHomOfClosure q eL (δ ρ)) =
      MulAut.conjNormal g (eW (nativeSourceGaloisHomOfClosure q eL ρ)) := by
  apply Subtype.ext
  change (eW (nativeSourceGaloisHomOfClosure q eL (δ ρ))).val =
    g * (eW (nativeSourceGaloisHomOfClosure q eL ρ)).val * g⁻¹
  rw [nativeSourceGaloisHom_cover_image K L Ω W p q hpoint M eW heW eL,
    nativeSourceGaloisHom_cover_image K L Ω W p q hpoint M eW heW eL,
    nativeSemilinearGaloisEquiv_ambient]
  have hconj :
      (semilinearGaloisConjugate τL σ.toRingEquiv hσ
        (AlgEquiv.autCongr eL ρ)).restrictScalars K =
        σ * (AlgEquiv.autCongr eL ρ).restrictScalars K * σ⁻¹ := by
    apply AlgEquiv.ext
    intro x
    rfl
  rw [hconj, map_mul, map_mul, map_inv]

include heW in
/-- The same native absolute-abelian action is the original covering
deck action under the actual pointed-cover comparison. -/
theorem nativeSourceAbelianHom_cover_conjugation
    (a : TopologicalAbelianization Gal(SeparableClosure L/L)) :
    let abelianConjugation : TopologicalAbelianization Gal(SeparableClosure L/L) ≃ₜ*
        TopologicalAbelianization Gal(SeparableClosure L/L) :=
      nativeSemilinearAbsoluteAbelianEquiv eL τL (AlgEquiv.toRingEquiv σ) hσ
    TopologicalAbelianization.congr eW
        (nativeSourceAbelianHomOfClosure q eL (abelianConjugation a)) =
      TopologicalAbelianization.congr
        (ProCGroups.Subgroup.conjNormalContinuousMulEquiv M.toSubgroup g)
        (TopologicalAbelianization.congr eW
          (nativeSourceAbelianHomOfClosure q eL a)) := by
  intro abelianConjugation
  obtain ⟨ρ, rfl⟩ := TopologicalAbelianization.surjective_mk Gal(SeparableClosure L/L) a
  change TopologicalAbelianization.mk M.toSubgroup
      (eW (nativeSourceGaloisHomOfClosure q eL (δ ρ))) =
    TopologicalAbelianization.mk M.toSubgroup
      (MulAut.conjNormal g (eW (nativeSourceGaloisHomOfClosure q eL ρ)))
  exact congrArg (TopologicalAbelianization.mk M.toSubgroup)
    (nativeSourceGaloisHom_cover_conjugation K L Ω W p q hpoint M eW heW eL σ ρ)

end AlgebraicGeometry.FiniteEtale
