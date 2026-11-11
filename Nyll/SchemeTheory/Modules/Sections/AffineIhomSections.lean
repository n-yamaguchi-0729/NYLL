/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Modules.Sections.IhomSections
public import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeAffineSections
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Actual affine sections of internal Hom

The tilde adjunction identifies actual sheaf morphisms from a
quasicoherent module with the linear maps on global sections. Together
with the existing concrete internal-Hom evaluation, this gives the
canonical linear equivalence on sections. In particular, global sections
of the dual of a finite quasicoherent module are finite over a Noetherian
affine base. No quasicoherence of that dual is assumed in this argument.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- On an affine scheme, the actual global-section map on morphisms from
a quasicoherent module is bijective. The target may be any module sheaf. -/
theorem moduleSpecΓ_map_bijective {R : CommRingCat.{u}}
    (M N : (Spec R).Modules) [M.IsQuasicoherent] :
    Function.Bijective (fun f : M ⟶ N => (moduleSpecΓFunctor (R := R)).map f) := by
  let adj := tilde.adjunction (R := R)
  let ε : (tilde.functor R).obj ((moduleSpecΓFunctor (R := R)).obj M) ⟶ M :=
    adj.counit.app M
  have : IsIso ε := inferInstanceAs (IsIso M.fromTildeΓ)
  let e : (M ⟶ N) ≃
      ((moduleSpecΓFunctor (R := R)).obj M ⟶
        (moduleSpecΓFunctor (R := R)).obj N) :=
    (Iso.homCongr (asIso ε).symm (Iso.refl N)).trans
      (adj.homEquiv ((moduleSpecΓFunctor (R := R)).obj M) N)
  have he (f : M ⟶ N) : e f = (moduleSpecΓFunctor (R := R)).map f := by
    change adj.homEquiv _ _ (ε ≫ f ≫ 𝟙 N) = _
    rw [Category.comp_id, Adjunction.homEquiv_unit]
    calc
      adj.unit.app ((moduleSpecΓFunctor (R := R)).obj M) ≫
          (moduleSpecΓFunctor (R := R)).map (ε ≫ f) =
        adj.unit.app ((moduleSpecΓFunctor (R := R)).obj M) ≫
          ((moduleSpecΓFunctor (R := R)).map ε ≫
            (moduleSpecΓFunctor (R := R)).map f) :=
        congrArg (fun k => adj.unit.app ((moduleSpecΓFunctor (R := R)).obj M) ≫ k)
          ((moduleSpecΓFunctor (R := R)).map_comp ε f)
      _ = (adj.unit.app ((moduleSpecΓFunctor (R := R)).obj M) ≫
          (moduleSpecΓFunctor (R := R)).map ε) ≫
            (moduleSpecΓFunctor (R := R)).map f := (Category.assoc _ _ _).symm
      _ = (moduleSpecΓFunctor (R := R)).map f :=
        (congrArg (fun k => k ≫ (moduleSpecΓFunctor (R := R)).map f)
          (adj.right_triangle_components M)).trans (Category.id_comp _)
  constructor
  · intro f g h
    apply e.injective
    exact (he f).trans (h.trans (he g).symm)
  · intro f
    obtain ⟨g, hg⟩ := e.surjective f
    exact ⟨g, (he g).symm.trans hg⟩

private theorem ihomGlobalSectionsEquiv_app_top
    {X : Scheme.{u}} (M N : X.Modules)
    (t : Γ((ihom M).obj N, ⊤)) (m : Γ(M, ⊤)) :
    (ihomGlobalSectionsEquiv M N t).app ⊤ m = ihomEval M N ⊤ m t := by
  rw [ihomGlobalSectionsEquiv_app_apply]
  have h : (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_top)).op = 𝟙 (op ⊤) :=
    Subsingleton.elim _ _
  rw [h, CategoryTheory.Functor.map_id]
  rfl

private theorem smul_spec_top {R : CommRingCat.{u}}
    (M : (Spec R).Modules) (r : R) (m : Γ(M, ⊤)) :
    r • m = (Scheme.ΓSpecIso R).inv r • m := by
  rw [smul_Spec_def]
  have h : (⊤ : (Spec R).Opens).leTop.op = 𝟙 (op ⊤) := Subsingleton.elim _ _
  rw [h, CategoryTheory.Functor.map_id]
  rfl

/-- An internal-Hom section acts on actual global sections by evaluation.
This map uses the canonical `R`-actions on the original section modules. -/
def ihomSpecSectionsLinearMap {R : CommRingCat.{u}}
    (M N : (Spec R).Modules) :
    (moduleSpecΓFunctor (R := R)).obj ((ihom M).obj N) →ₗ[R]
      ((moduleSpecΓFunctor (R := R)).obj M →ₗ[R]
        (moduleSpecΓFunctor (R := R)).obj N) where
  toFun t := ((moduleSpecΓFunctor (R := R)).map (ihomGlobalSectionsEquiv M N t)).hom
  map_add' t s := by
    ext m
    exact congrArg (fun f : M ⟶ N => f.app ⊤ (show Γ(M, ⊤) from m))
      ((ihomGlobalSectionsEquiv M N).map_add
        (show Γ((ihom M).obj N, ⊤) from t) (show Γ((ihom M).obj N, ⊤) from s))
  map_smul' r t := by
    ext m
    calc
      (ihomGlobalSectionsEquiv M N
          (show Γ((ihom M).obj N, ⊤) from r • t)).app ⊤ m =
        ihomEval M N ⊤ m (show Γ((ihom M).obj N, ⊤) from r • t) :=
        ihomGlobalSectionsEquiv_app_top M N _ _
      _ = ihomEval M N ⊤ m ((Scheme.ΓSpecIso R).inv r •
          (show Γ((ihom M).obj N, ⊤) from t)) :=
        congrArg (ihomEval M N ⊤ (show Γ(M, ⊤) from m))
          (smul_spec_top ((ihom M).obj N) r t)
      _ = (Scheme.ΓSpecIso R).inv r • ihomEval M N ⊤ m t :=
        ihomEval_smul_right ⊤ _ _ _
      _ = r • ihomEval M N ⊤ m t := (smul_spec_top N r _).symm
      _ = r • (ihomGlobalSectionsEquiv M N t).app ⊤ m :=
        congrArg (fun n : (moduleSpecΓFunctor (R := R)).obj N => r • n)
          (ihomGlobalSectionsEquiv_app_top M N t m).symm

/-- The affine internal-Hom section map is the actual evaluation pairing. -/
theorem ihomSpecSectionsLinearMap_apply {R : CommRingCat.{u}}
    (M N : (Spec R).Modules)
    (t : (moduleSpecΓFunctor (R := R)).obj ((ihom M).obj N))
    (m : (moduleSpecΓFunctor (R := R)).obj M) :
    ihomSpecSectionsLinearMap M N t m = ihomEval M N ⊤ m t :=
  ihomGlobalSectionsEquiv_app_top M N t m

/-- The canonical affine linear equivalence between internal-Hom sections
and linear maps on actual section modules. -/
def ihomSpecSectionsLinearEquiv {R : CommRingCat.{u}}
    (M N : (Spec R).Modules) [M.IsQuasicoherent] :
    (moduleSpecΓFunctor (R := R)).obj ((ihom M).obj N) ≃ₗ[R]
      ((moduleSpecΓFunctor (R := R)).obj M →ₗ[R]
        (moduleSpecΓFunctor (R := R)).obj N) :=
  LinearEquiv.ofBijective (ihomSpecSectionsLinearMap M N)
    (ModuleCat.homEquiv.bijective.comp
      ((moduleSpecΓ_map_bijective M N).comp (ihomGlobalSectionsEquiv M N).bijective))

/-- Finite type of a quasicoherent module on an affine scheme gives
finite global sections over the original ring `R`. -/
theorem moduleFinite_moduleSpecΓ_of_isFiniteType {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    Module.Finite R ((moduleSpecΓFunctor (R := R)).obj M) := by
  have : Module.Finite Γ(Spec R, ⊤) Γ(M, ⊤) :=
    moduleFinite_sections_of_isFiniteType M ⊤ (isAffineOpen_top (Spec R))
  let σ : Γ(Spec R, ⊤) →+* R := (Scheme.ΓSpecIso R).hom.hom
  let l : Γ(M, ⊤) →ₛₗ[σ] (moduleSpecΓFunctor (R := R)).obj M :=
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun r m => by
        exact ((smul_spec_top M (σ r) m).trans
          (congrArg (fun a : Γ(Spec R, ⊤) => a • m)
            (Iso.hom_inv_id_apply (Scheme.ΓSpecIso R) r))).symm }
  exact Module.Finite.of_surjective l Function.surjective_id

/-- The actual global sections of the dual of a finite quasicoherent
module over a Noetherian affine scheme form a finite module. -/
theorem moduleFinite_moduleSpecΓ_dual_of_isFiniteType
    {R : CommRingCat.{u}} [IsNoetherianRing R]
    (M : (Spec R).Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    Module.Finite R ((moduleSpecΓFunctor (R := R)).obj (dual M)) := by
  have : Module.Finite R ((moduleSpecΓFunctor (R := R)).obj M) :=
    moduleFinite_moduleSpecΓ_of_isFiniteType M
  have : Module.Finite R
      ((moduleSpecΓFunctor (R := R)).obj (𝟙_ (Spec R).Modules)) :=
    Module.Finite.equiv (tilde.isoTop (ModuleCat.of R R)).toLinearEquiv
  exact Module.Finite.equiv (ihomSpecSectionsLinearEquiv M (𝟙_ (Spec R).Modules)).symm

end AlgebraicGeometry.Scheme.Modules
