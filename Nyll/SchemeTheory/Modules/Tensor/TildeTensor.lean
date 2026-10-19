/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.CategoryTheory.ModuleColimitGenerator
import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentLocal
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Nyll.SchemeTheory.Modules.Tensor.TensorSections
import Nyll.SchemeTheory.Modules.Tensor.TensorSectionMaps
import Nyll.SchemeTheory.Modules.Tensor.TensorSectionNaturality
import Nyll.SchemeTheory.Modules.Tensor.TensorSectionRightUnitor
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.LinearAlgebra.BilinearMap

/-!
# Tensor products of actual affine tilde modules

The comparison is the adjoint of the original bilinear tensor-section
map. Its component on the coefficient module is the actual right unitor.
Both functors preserve colimits, so the free cokernel presentation of an
arbitrary module proves that the comparison is an isomorphism.

No flatness, finite presentation, or tensor-comparison hypothesis is used.
The formula on the original global pure tensors is retained explicitly.
-/

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}}

/-- The original tensor-section map, using the existing affine global
section modules and their original coefficient actions. -/
def specTensorSectionsMap (F G : (Spec R).Modules) :
    (moduleSpecΓFunctor (R := R)).obj F ⊗ (moduleSpecΓFunctor (R := R)).obj G ⟶
      (moduleSpecΓFunctor (R := R)).obj (tensor F G) := by
  let P : ModuleCat.{u} R := (moduleSpecΓFunctor (R := R)).obj F
  let Q : ModuleCat.{u} R := (moduleSpecΓFunctor (R := R)).obj G
  let T : ModuleCat.{u} R := (moduleSpecΓFunctor (R := R)).obj (tensor F G)
  let b : P →ₗ[R] Q →ₗ[R] T := LinearMap.mk₂ R
    (fun x y => (tensorSections x y : T))
    (fun x x' y => tensorSections_add_left x x' y)
    (by
      intro r x y
      have hx := smul_Spec_def (M := F) (U := ⊤) r x
      have hz := smul_Spec_def (M := tensor F G) (U := ⊤) r (tensorSections x y)
      have ht := tensorSections_smul_left (L := F) (M := G) (U := ⊤)
        (((Spec R).presheaf.map (⊤ : (Spec R).Opens).leTop.op)
          ((Scheme.ΓSpecIso R).inv r)) x y
      exact ((congrArg (fun z : Γ(F, ⊤) => tensorSections z y) hx).trans ht).trans hz.symm)
    (fun x y y' => tensorSections_add_right x y y')
    (by
      intro r x y
      have hy := smul_Spec_def (M := G) (U := ⊤) r y
      have hz := smul_Spec_def (M := tensor F G) (U := ⊤) r (tensorSections x y)
      have ht := tensorSections_smul_right (L := F) (M := G) (U := ⊤)
        (((Spec R).presheaf.map (⊤ : (Spec R).Opens).leTop.op)
          ((Scheme.ΓSpecIso R).inv r)) x y
      exact ((congrArg (fun z : Γ(G, ⊤) => tensorSections x z) hy).trans ht).trans hz.symm)
  exact ModuleCat.ofHom (X := P ⊗[R] Q) (Y := T) (TensorProduct.lift b)

/-- The global tensor comparison is induced by the literal tensor of sections. -/
theorem specTensorSectionsMap_tmul (F G : (Spec R).Modules)
    (x : (moduleSpecΓFunctor (R := R)).obj F)
    (y : (moduleSpecΓFunctor (R := R)).obj G) :
    specTensorSectionsMap F G (x ⊗ₜ[R] y) = tensorSections x y := rfl

/-- The original global tensor-section map is natural in both sheaf factors. -/
theorem specTensorSectionsMap_naturality
    {F F' G G' : (Spec R).Modules} (φ : F ⟶ F') (ψ : G ⟶ G') :
    ((moduleSpecΓFunctor (R := R)).map φ ⊗ₘ
        (moduleSpecΓFunctor (R := R)).map ψ) ≫ specTensorSectionsMap F' G' =
      specTensorSectionsMap F G ≫ (moduleSpecΓFunctor (R := R)).map (φ ⊗ₘ ψ) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  exact (tensorHom_app_tensorSections φ ψ x y).symm

/-- The actual sheaf map adjoint to the original pure-tensor global section map. -/
def tildeTensorMap (M N : ModuleCat.{u} R) :
    tilde (M ⊗ N) ⟶ tensor (tilde M) (tilde N) :=
  ((tilde.adjunction (R := R)).homEquiv (M ⊗ N) (tensor (tilde M) (tilde N))).symm
    (((tilde.isoTop M).hom ⊗ₘ (tilde.isoTop N).hom) ≫
      specTensorSectionsMap (tilde M) (tilde N))

/-- The comparison is adjoint to the literal section tensor, with the
original tilde--Gamma unit on every factor. -/
theorem tildeTensorMap_globalSections (M N : ModuleCat.{u} R) :
    (tilde.isoTop (M ⊗ N)).hom ≫
        (moduleSpecΓFunctor (R := R)).map (tildeTensorMap M N) =
      ((tilde.isoTop M).hom ⊗ₘ (tilde.isoTop N).hom) ≫
        specTensorSectionsMap (tilde M) (tilde N) := by
  have h := ((tilde.adjunction (R := R)).homEquiv (M ⊗ N)
    (tensor (tilde M) (tilde N))).apply_symm_apply
      (((tilde.isoTop M).hom ⊗ₘ (tilde.isoTop N).hom) ≫
        specTensorSectionsMap (tilde M) (tilde N))
  rw [Adjunction.homEquiv_unit] at h
  exact h

/-- The constructed tilde comparison retains the actual global pure tensor. -/
theorem tildeTensorMap_tmul (M N : ModuleCat.{u} R) (m : M) (n : N) :
    (tildeTensorMap M N).app ⊤ ((tilde.isoTop (M ⊗ N)).hom (m ⊗ₜ[R] n)) =
      tensorSections ((tilde.isoTop M).hom m) ((tilde.isoTop N).hom n) :=
  congrArg (fun k : (M ⊗ N) ⟶
      (moduleSpecΓFunctor (R := R)).obj (tensor (tilde M) (tilde N)) => k (m ⊗ₜ[R] n))
    (tildeTensorMap_globalSections M N)

private theorem tildeMap_top {M N : ModuleCat.{u} R} (f : M ⟶ N) (m : M) :
    (tilde.map f).app ⊤ ((tilde.isoTop M).hom m) = (tilde.isoTop N).hom (f m) :=
  congrArg (fun k : M ⟶ (moduleSpecΓFunctor (R := R)).obj (tilde N) => k m)
    (tilde.toOpen_map_app f ⊤)

private theorem tilde_hom_ext_top {M : ModuleCat.{u} R} {F : (Spec R).Modules}
    (a b : tilde M ⟶ F)
    (h : (tilde.isoTop M).hom ≫ (moduleSpecΓFunctor (R := R)).map a =
      (tilde.isoTop M).hom ≫ (moduleSpecΓFunctor (R := R)).map b) : a = b := by
  let a' : (tilde.functor R).obj M ⟶ F := a
  let b' : (tilde.functor R).obj M ⟶ F := b
  have ha := Adjunction.homEquiv_unit (tilde.adjunction (R := R)) M F a'
  have hb := Adjunction.homEquiv_unit (tilde.adjunction (R := R)) M F b'
  exact ((tilde.adjunction (R := R)).homEquiv M F).injective
    (ha.trans (h.trans hb.symm))

/-- The actual tilde tensor comparison is natural in its second module. -/
theorem tildeTensorMap_naturality_right (M : ModuleCat.{u} R)
    {N N' : ModuleCat.{u} R} (f : N ⟶ N') :
    tilde.map (M ◁ f) ≫ tildeTensorMap M N' =
      tildeTensorMap M N ≫ (tilde M ◁ tilde.map f) := by
  apply tilde_hom_ext_top
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro m
  apply LinearMap.ext
  intro n
  change (tildeTensorMap M N').app ⊤
      ((tilde.map (M ◁ f)).app ⊤ ((tilde.isoTop (M ⊗ N)).hom (m ⊗ₜ[R] n))) =
    (tilde M ◁ tilde.map f).app ⊤
      ((tildeTensorMap M N).app ⊤ ((tilde.isoTop (M ⊗ N)).hom (m ⊗ₜ[R] n)))
  rw [tildeMap_top, ModuleCat.MonoidalCategory.whiskerLeft_apply,
    tildeTensorMap_tmul, tildeTensorMap_tmul]
  have h := whiskerLeft_app_tensorSections (tilde M) (tilde.map f)
    ((tilde.isoTop M).hom m) ((tilde.isoTop N).hom n)
  have hn := tildeMap_top f n
  exact (h.trans (congrArg (tensorSections ((tilde.isoTop M).hom m)) hn)).symm

private def tildeTensorNatTrans (M : ModuleCat.{u} R) :
    tensorLeft M ⋙ tilde.functor R ⟶
      tilde.functor R ⋙ tensorLeft (tilde M) where
  app N := tildeTensorMap M N
  naturality {_ _} f := tildeTensorMap_naturality_right M f

private theorem tildeUnit_top (r : R) :
    ((tildeSelf (R := R)).hom).app ⊤
      ((tilde.isoTop (ModuleCat.of R R)).hom r) = (Scheme.ΓSpecIso R).inv r := rfl

private theorem tildeTensorMap_unit (M : ModuleCat.{u} R) :
    tildeTensorMap M (ModuleCat.of R R) ≫
        (tilde M ◁ (tildeSelf (R := R)).hom) ≫ (ρ_ (tilde M)).hom =
      tilde.map (ρ_ M).hom := by
  apply tilde_hom_ext_top
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro m
  apply LinearMap.ext
  intro r
  change (ρ_ (tilde M)).hom.app ⊤
      ((tilde M ◁ (tildeSelf (R := R)).hom).app ⊤
        ((tildeTensorMap M (ModuleCat.of R R)).app ⊤
          ((tilde.isoTop (M ⊗ ModuleCat.of R R)).hom (m ⊗ₜ[R] r)))) =
    (tilde.map (ρ_ M).hom).app ⊤
      ((tilde.isoTop (M ⊗ ModuleCat.of R R)).hom (m ⊗ₜ[R] r))
  have hβ := tildeTensorMap_tmul M (ModuleCat.of R R) m r
  have hr := tildeMap_top (ρ_ M).hom (m ⊗ₜ[R] r)
  have hr' := ModuleCat.MonoidalCategory.rightUnitor_hom_apply m r
  have hrhs := hr.trans (congrArg (fun x : M => (tilde.isoTop M).hom x) hr')
  have ht := whiskerLeft_app_tensorSections (tilde M) (tildeSelf (R := R)).hom
    ((tilde.isoTop M).hom m) ((tilde.isoTop (ModuleCat.of R R)).hom r)
  have hu := tildeUnit_top (R := R) r
  have hmul := smul_Spec_def (M := tilde M) (U := ⊤) r ((tilde.isoTop M).hom m)
  have hid : (Spec R).presheaf.map (⊤ : (Spec R).Opens).leTop.op = 𝟙 _ := by
    rw [Subsingleton.elim (⊤ : (Spec R).Opens).leTop (𝟙 _), op_id,
      CategoryTheory.Functor.map_id]
  rw [hid] at hmul
  have h₁ := congrArg
    (fun x : Γ(tensor (tilde M) (tilde (ModuleCat.of R R)), ⊤) =>
      (show Γ(tilde M, ⊤) from
        (ρ_ (tilde M)).hom.app ⊤ ((tilde M ◁ (tildeSelf (R := R)).hom).app ⊤ x))) hβ
  have h₂ := congrArg
    (fun x : Γ(tensor (tilde M) (𝟙_ (Spec R).Modules), ⊤) =>
      (show Γ(tilde M, ⊤) from (ρ_ (tilde M)).hom.app ⊤ x))
    (ht.trans (congrArg (tensorSections ((tilde.isoTop M).hom m)) hu))
  have h₃ := rightUnitor_hom_app_tensorSections (N := tilde M) (U := ⊤)
    ((tilde.isoTop M).hom m) ((Scheme.ΓSpecIso R).inv r)
  have h₄ : r • (show Γ(tilde M, ⊤) from (tilde.isoTop M).hom m) =
      (tilde.isoTop M).hom (r • m) := ((tilde.isoTop M).hom.hom.map_smul r m).symm
  exact h₁.trans (h₂.trans (h₃.trans (hmul.symm.trans (h₄.trans hrhs.symm))))

/-- The original tilde comparison is an isomorphism for arbitrary modules. -/
theorem isIso_tildeTensorMap (M N : ModuleCat.{u} R) : IsIso (tildeTensorMap M N) := by
  have : PreservesColimitsOfSize.{u, u} (tilde.functor R) :=
    (tilde.adjunction (R := R)).leftAdjoint_preservesColimits
  have hunit : IsIso (tildeTensorMap M (ModuleCat.of R R)) := by
    let e₀ : tilde (ModuleCat.of R R) ≅ (𝟙_ (Spec R).Modules) := tildeSelf (R := R)
    let e : tensor (tilde M) (tilde (ModuleCat.of R R)) ≅ tilde M :=
      whiskerLeftIso (tilde M) e₀ ≪≫ ρ_ (tilde M)
    let k : tensor (tilde M) (tilde (ModuleCat.of R R)) ⟶ tilde M :=
      e.hom
    have hk : IsIso k := e.isIso_hom
    have hc : IsIso (tildeTensorMap M (ModuleCat.of R R) ≫ k) :=
      Eq.mp (congrArg (fun a => IsIso (C := (Spec R).Modules) a)
        (tildeTensorMap_unit M).symm)
          (CategoryTheory.Functor.map_isIso (tilde.functor R) (ρ_ M).hom)
    exact (isIso_comp_right_iff (tildeTensorMap M (ModuleCat.of R R)) k).mp hc
  exact (tildeTensorNatTrans M).isIso_app_of_module_unit hunit N

/-- The constructed sheaf tensor isomorphism is induced by the actual
tensor of original affine sections. -/
def tildeTensorIso (M N : ModuleCat.{u} R) :
    tilde (M ⊗ N) ≅ tensor (tilde M) (tilde N) := by
  have h : IsIso (C := (Spec R).Modules) (tildeTensorMap M N) := isIso_tildeTensorMap M N
  exact asIso (C := (Spec R).Modules) (tildeTensorMap M N)

/-- The isomorphism retains the original pure-tensor formula. -/
theorem tildeTensorIso_hom_tmul (M N : ModuleCat.{u} R) (m : M) (n : N) :
    (tildeTensorIso M N).hom.app ⊤ ((tilde.isoTop (M ⊗ N)).hom (m ⊗ₜ[R] n)) =
      tensorSections ((tilde.isoTop M).hom m) ((tilde.isoTop N).hom n) :=
  tildeTensorMap_tmul M N m n

end AlgebraicGeometry.Scheme.Modules
