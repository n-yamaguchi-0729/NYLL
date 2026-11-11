/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.RingTheory.LocalProperties.Submodule
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Basic
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.Ring
public import Nyll.SchemeTheory.Modules.PresheafInternalHom
public import Nyll.SchemeTheory.Modules.Tensor.Monoidal
public import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
public import Nyll.SchemeTheory.Modules.Tensor.TensorSections
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Tensor.BijectiveLiftTensorSectionsBilinQuasicoherent
public import Nyll.AlgebraicCurves.Cohomology.Sheaves.Complexes.OModulePresheafOfModules

/-!
# Tensor sections on affine opens

The tensor-sections map of quasicoherent modules is bijective on affine opens.
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.TensorProduct
open _root_.Opposite


noncomputable section

namespace P2mQcTensorCompare

variable {X : Scheme.{u}}

section BasicOpen

variable (N : X.Modules) (U : X.Opens) (f : Γ(X, U))

/-- The scalar action on basic-open sections induced by restriction. -/
@[reducible] def modBO : Module Γ(X, U) Γ(N, X.basicOpen f) :=
  Module.compHom Γ(N, X.basicOpen f) (algebraMap Γ(X, U) Γ(X, X.basicOpen f))

attribute [local instance] modBO

scoped instance isScalarTower_modBO : IsScalarTower Γ(X, U) Γ(X, X.basicOpen f) Γ(N, X.basicOpen f)
  :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- Restriction of module sections to a basic open, as a linear map. -/
def resBO : Γ(N, U) →ₗ[Γ(X, U)] Γ(N, X.basicOpen f) where
  toFun := N.presheaf.map (homOfLE (X.basicOpen_le f)).op
  map_add' x y := map_add _ x y
  map_smul' a x := Scheme.Modules.map_smul N (homOfLE (X.basicOpen_le f)) a x

theorem resBO_apply (x : Γ(N, U)) : resBO N U f x = N.presheaf.map (homOfLE (X.basicOpen_le f)).op
  x := rfl

theorem isLocalizedModule_resBO {R : Type u} [CommRing R] (π : X ⟶ Spec (.of R))
    (hN : (OModulePresheaf.ofModules π N).IsQuasicoherent) (hU : IsAffineOpen U) :
    IsLocalizedModule (Submonoid.powers f) (resBO N U f) := by
  have : IsLocalization.Away f Γ(X, X.basicOpen f) := hU.isLocalization_basicOpen f
  obtain ⟨h1, h2⟩ := hN ⟨U, hU⟩ f
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨s, n, rfl⟩
    rw [Module.End.isUnit_iff]
    have hu : IsUnit (algebraMap Γ(X, U) Γ(X, X.basicOpen f) (f ^ n)) := by
      rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit f).pow n
    have := hu.smul_bijective (β := Γ(N, X.basicOpen f))
    exact this
  · intro y
    obtain ⟨n, x, hx⟩ := h1 y
    exact ⟨⟨x, ⟨f ^ n, n, rfl⟩⟩, hx.symm⟩
  · intro x₁ x₂ h
    have h0 : N.presheaf.map (homOfLE (X.basicOpen_le f)).op (x₁ - x₂) = 0 := by
      rw [map_sub]; exact sub_eq_zero.mpr h
    obtain ⟨n, hn⟩ := h2 (x₁ - x₂) h0
    refine ⟨⟨f ^ n, n, rfl⟩, ?_⟩
    rw [Submonoid.smul_def, Submonoid.smul_def, ← sub_eq_zero, ← smul_sub]
    exact hn

theorem res_resBO {g : Γ(X, U)} (h : X.basicOpen g ≤ X.basicOpen f) (x : Γ(N, U)) :
    N.presheaf.map (homOfLE h).op (resBO N U f x) = resBO N U g x := by
  rw [resBO_apply, resBO_apply, ← CategoryTheory.ConcreteCategory.comp_apply, ← N.presheaf.map_comp]
  rfl

end BasicOpen

attribute [local instance] modBO

section Theta

variable (L M : X.Modules)

/-- The tensor-sections linear map. -/
abbrev theta (U : X.Opens) : Γ(L, U) ⊗[Γ(X, U)] Γ(M, U) →ₗ[Γ(X, U)] Γ(L ⊗ M, U) :=
  TensorProduct.lift (Scheme.Modules.tensorSectionsBilin L M U)

theorem theta_tmul (U : X.Opens) (s : Γ(L, U)) (t : Γ(M, U)) :
    theta L M U (s ⊗ₜ t) = Scheme.Modules.tensorSections s t := by
  simp [theta]

variable (U : X.Opens) (f : Γ(X, U))

/-- The tensor-sections map over a basic open with scalars restricted to the source. -/
def thetaBO : Γ(L, X.basicOpen f) ⊗[Γ(X, U)] Γ(M, X.basicOpen f) →ₗ[Γ(X, U)] Γ(L ⊗ M, X.basicOpen
  f) :=
  TensorProduct.lift
    (LinearMap.mk₂ Γ(X, U) (fun x y => Scheme.Modules.tensorSections x y)
      (fun x₁ x₂ y => Scheme.Modules.tensorSections_add_left x₁ x₂ y)
      (fun a x y => by
        rw [← algebraMap_smul Γ(X, X.basicOpen f) a x, Scheme.Modules.tensorSections_smul_left,
          algebraMap_smul])
      (fun x y₁ y₂ => Scheme.Modules.tensorSections_add_right x y₁ y₂)
      (fun a x y => by
        rw [← algebraMap_smul Γ(X, X.basicOpen f) a y, Scheme.Modules.tensorSections_smul_right,
          algebraMap_smul]))

theorem thetaBO_tmul (x : Γ(L, X.basicOpen f)) (y : Γ(M, X.basicOpen f)) :
    thetaBO L M U f (x ⊗ₜ y) = Scheme.Modules.tensorSections x y := rfl

theorem thetaBO_comp_map :
    thetaBO L M U f ∘ₗ TensorProduct.map (resBO L U f) (resBO M U f) = resBO (L ⊗ M) U f ∘ₗ theta L
      M U := by
  refine TensorProduct.ext' fun s t => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, TensorProduct.map_tmul, thetaBO_tmul, theta_tmul,
    resBO_apply, resBO_apply, resBO_apply]
  exact (Scheme.Modules.map_homOfLE_tensorSections (X.basicOpen_le f) s t).symm

theorem thetaBO_map (z : Γ(L, U) ⊗[Γ(X, U)] Γ(M, U)) :
    thetaBO L M U f (TensorProduct.map (resBO L U f) (resBO M U f) z) = resBO (L ⊗ M) U f (theta L
      M U z) :=
  congrFun (congrArg DFunLike.coe (thetaBO_comp_map L M U f)) z

/-- Compare tensor products before and after localization. -/
def tensorBOEquiv (hU : IsAffineOpen U) :
    Γ(L, X.basicOpen f) ⊗[Γ(X, X.basicOpen f)] Γ(M, X.basicOpen f) ≃ₗ[Γ(X, U)]
      Γ(L, X.basicOpen f) ⊗[Γ(X, U)] Γ(M, X.basicOpen f) :=
  have : IsLocalization.Away f Γ(X, X.basicOpen f) := hU.isLocalization_basicOpen f
  (IsLocalization.moduleTensorEquiv (Submonoid.powers f) Γ(X, X.basicOpen f)
    Γ(L, X.basicOpen f) Γ(M, X.basicOpen f)).restrictScalars Γ(X, U)

theorem tensorBOEquiv_tmul (hU : IsAffineOpen U) (x : Γ(L, X.basicOpen f)) (y : Γ(M, X.basicOpen
  f)) :
    tensorBOEquiv L M U f hU (x ⊗ₜ[Γ(X, X.basicOpen f)] y) = x ⊗ₜ[Γ(X, U)] y := rfl

theorem thetaBO_tensorBOEquiv (hU : IsAffineOpen U)
    (w : Γ(L, X.basicOpen f) ⊗[Γ(X, X.basicOpen f)] Γ(M, X.basicOpen f)) :
    thetaBO L M U f (tensorBOEquiv L M U f hU w) = theta L M (X.basicOpen f) w := by
  induction w using TensorProduct.inductionOn with
  | tmul x y => rw [tensorBOEquiv_tmul, thetaBO_tmul, theta_tmul]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

theorem thetaBO_injective_of (hU : IsAffineOpen U) (h : Function.Injective (theta L M (X.basicOpen
  f))) :
    Function.Injective (thetaBO L M U f) := by
  intro a b hab
  have ha := thetaBO_tensorBOEquiv L M U f hU ((tensorBOEquiv L M U f hU).symm a)
  have hb := thetaBO_tensorBOEquiv L M U f hU ((tensorBOEquiv L M U f hU).symm b)
  rw [LinearEquiv.apply_symm_apply] at ha hb
  have := h (ha.symm.trans (hab.trans hb))
  simpa using congrArg (tensorBOEquiv L M U f hU) this

end Theta

section Local

variable (L M : X.Modules)

/-- The tensor-sections comparison on underlying presheaves. -/
def phi := (PresheafOfModules.toPresheaf _).map (Scheme.Modules.tensorSectionsHom L M)

theorem phi_isLocallyInjective :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) (phi L M) := by
  unfold phi Scheme.Modules.tensorSectionsHom
  let Q := (SheafOfModules.toPMod X.sheaf.obj X.ringCatSheaf.property).obj
    ((SheafOfModules.sheafifyFunctor X.sheaf.obj X.ringCatSheaf.property).obj (L.val ⊗ M.val))
  let LM : X.Modules := L ⊗ M
  let T := (SheafOfModules.toPMod X.sheaf.obj X.ringCatSheaf.property).obj LM
  let a : (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).obj (L.val ⊗ M.val) ⟶
      (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).obj Q :=
    (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
      ((SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property).unit.app (L.val ⊗ M.val))
  let e : (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).obj Q ≅
      (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).obj T :=
    (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).mapIso
      ((SheafOfModules.toPMod X.sheaf.obj X.ringCatSheaf.property).mapIso (L.tensorIsoSheafify M))
  have hA : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) a :=
    (inferInstance : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (L.val ⊗ M.val).presheaf))
  have hB : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) e.hom := inferInstance
  have hAB : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) (a ≫ e.hom) :=
    Presheaf.isLocallyInjective_comp (C := X.Opens) (D := AddCommGrpCat.{u})
      (Opens.grothendieckTopology X) a e.hom
  have hcomp := (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map_comp
    ((SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property).unit.app (L.val ⊗ M.val))
    ((SheafOfModules.toPMod X.sheaf.obj X.ringCatSheaf.property).map (L.tensorIsoSheafify M).hom)
  exact hcomp.symm ▸ hAB

theorem phi_isLocallySurjective :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) (phi L M) := by
  unfold phi Scheme.Modules.tensorSectionsHom
  let Q := (SheafOfModules.toPMod X.sheaf.obj X.ringCatSheaf.property).obj
    ((SheafOfModules.sheafifyFunctor X.sheaf.obj X.ringCatSheaf.property).obj (L.val ⊗ M.val))
  let LM : X.Modules := L ⊗ M
  let T := (SheafOfModules.toPMod X.sheaf.obj X.ringCatSheaf.property).obj LM
  let a : (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).obj (L.val ⊗ M.val) ⟶
      (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).obj Q :=
    (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
      ((SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property).unit.app (L.val ⊗ M.val))
  let e : (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).obj Q ≅
      (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).obj T :=
    (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).mapIso
      ((SheafOfModules.toPMod X.sheaf.obj X.ringCatSheaf.property).mapIso (L.tensorIsoSheafify M))
  have hA : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) a :=
    (inferInstance : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (L.val ⊗ M.val).presheaf))
  have hB : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) e.hom := inferInstance
  have hAB : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) (a ≫ e.hom) :=
    Presheaf.isLocallySurjective_comp (C := X.Opens) (A := AddCommGrpCat.{u})
      (Opens.grothendieckTopology X) a e.hom
  have hcomp := (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map_comp
    ((SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property).unit.app (L.val ⊗ M.val))
    ((SheafOfModules.toPMod X.sheaf.obj X.ringCatSheaf.property).map (L.tensorIsoSheafify M).hom)
  exact hcomp.symm ▸ hAB

variable (U : X.Opens)

/-- The additive tensor-sections map on an open subset. -/
def phiU : Γ(L, U) ⊗[Γ(X, U)] Γ(M, U) →+ Γ(L ⊗ M, U) := ((phi L M).app (op U)).hom

theorem phiU_eq_theta (z : Γ(L, U) ⊗[Γ(X, U)] Γ(M, U)) : phiU L M U z = theta L M U z := by
  induction z using TensorProduct.inductionOn with
  | tmul s t => rw [theta_tmul]; rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- Restriction in the tensor presheaf. -/
def resT {W : X.Opens} (i : W ⟶ U) : Γ(L, U) ⊗[Γ(X, U)] Γ(M, U) →+ Γ(L, W) ⊗[Γ(X, W)] Γ(M, W) :=
  ((L.val ⊗ M.val).presheaf.map i.op).hom

theorem resT_tmul {W : X.Opens} (i : W ⟶ U) (s : Γ(L, U)) (t : Γ(M, U)) :
    resT L M U i (s ⊗ₜ t) = L.presheaf.map i.op s ⊗ₜ M.presheaf.map i.op t := by
  rfl

end Local

section Extract

variable (L M : X.Modules) (U : X.Opens)

theorem resT_comp {W W' : X.Opens} (i : W ⟶ U) (j : W' ⟶ W) (z : Γ(L, U) ⊗[Γ(X, U)] Γ(M, U)) :
    resT L M U (j ≫ i) z = resT L M W j (resT L M U i z) := by
  unfold resT
  rw [op_comp, Functor.map_comp]
  rfl

theorem exists_resT_eq_of_theta_eq (z z' : Γ(L, U) ⊗[Γ(X, U)] Γ(M, U)) (h : theta L M U z = theta L
  M U z')
    {x : X} (hx : x ∈ U) : ∃ (W : X.Opens) (i : W ⟶ U), x ∈ W ∧ resT L M U i z = resT L M U i z' :=
      by
  have := phi_isLocallyInjective L M
  have hφ : phiU L M U z = phiU L M U z' := by rw [phiU_eq_theta, phiU_eq_theta, h]
  have hmem := Presheaf.equalizerSieve_mem (Opens.grothendieckTopology X) (phi L M) (X := op U) z
    z' hφ
  obtain ⟨W, i, hi, hxW⟩ := hmem x hx
  exact ⟨W, i, hxW, hi⟩

theorem exists_theta_eq_res (y : Γ(L ⊗ M, U)) {x : X} (hx : x ∈ U) :
    ∃ (W : X.Opens) (i : W ⟶ U), x ∈ W ∧
      ∃ w : Γ(L, W) ⊗[Γ(X, W)] Γ(M, W), theta L M W w = (L ⊗ M).presheaf.map i.op y := by
  have := phi_isLocallySurjective L M
  have hmem := Presheaf.imageSieve_mem (Opens.grothendieckTopology X) (phi L M) (U := op U) y
  obtain ⟨W, i, ⟨t, ht⟩, hxW⟩ := hmem x hx
  let w : Γ(L, W) ⊗[Γ(X, W)] Γ(M, W) := t
  have ht' : phiU L M W w = (L ⊗ M).presheaf.map i.op y := ht
  exact ⟨W, i, hxW, w, (phiU_eq_theta L M W w).symm.trans ht'⟩

end Extract

section Injective

variable (L M : X.Modules)

theorem theta_resT {W W' : X.Opens} (j : W' ⟶ W) (w : Γ(L, W) ⊗[Γ(X, W)] Γ(M, W)) :
    theta L M W' (resT L M W j w) = (L ⊗ M).presheaf.map j.op (theta L M W w) := by
  induction w using TensorProduct.inductionOn with
  | tmul s t =>
    rw [resT_tmul, theta_tmul, theta_tmul]
    exact (Scheme.Modules.map_tensorSections j s t).symm
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tensorBOEquiv_resT (U : X.Opens) (hU : IsAffineOpen U) (g : Γ(X, U)) (z : Γ(L, U) ⊗[Γ(X,
  U)] Γ(M, U)) :
    tensorBOEquiv L M U g hU (resT L M U (homOfLE (X.basicOpen_le g)) z) =
      TensorProduct.map (resBO L U g) (resBO M U g) z := by
  induction z using TensorProduct.inductionOn with
  | tmul s t => rw [resT_tmul, tensorBOEquiv_tmul, TensorProduct.map_tmul]; rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

theorem theta_injective {R : Type u} [CommRing R] (π : X ⟶ Spec (.of R))
    (hL : (OModulePresheaf.ofModules π L).IsQuasicoherent) (hM : (OModulePresheaf.ofModules π
      M).IsQuasicoherent)
    (U : X.Opens) (hU : IsAffineOpen U) : Function.Injective (theta L M U) :=
  (Scheme.Modules.bijective_lift_tensorSectionsBilin_of_isQuasicoherent
    π hL hM ⟨U, hU⟩).1

end Injective

section Surjective

variable (L M : X.Modules) {R : Type u} [CommRing R] (π : X ⟶ Spec (.of R))
  (hL : (OModulePresheaf.ofModules π L).IsQuasicoherent) (hM : (OModulePresheaf.ofModules π
    M).IsQuasicoherent)
  (U : X.Opens) (hU : IsAffineOpen U)

include hL hM hU in
theorem exists_basicOpen_theta_res (y : Γ(L ⊗ M, U)) {x : X} (hx : x ∈ U) :
    ∃ g : Γ(X, U), x ∈ X.basicOpen g ∧ ∃ (z : Γ(L, U) ⊗[Γ(X, U)] Γ(M, U)) (n : ℕ),
      resBO (L ⊗ M) U g (theta L M U z) = resBO (L ⊗ M) U g (g ^ n • y) := by
  obtain ⟨W, i, hxW, w, hw⟩ := exists_theta_eq_res L M U y hx
  obtain ⟨g, hgW, hxg⟩ := hU.exists_basicOpen_le ⟨x, hxW⟩ hx
  refine ⟨g, hxg, ?_⟩
  have hw' : theta L M (X.basicOpen g) (resT L M W (homOfLE hgW) w) = resBO (L ⊗ M) U g y := by
    rw [theta_resT, hw, resBO_apply, ← CategoryTheory.ConcreteCategory.comp_apply, ←
      Functor.map_comp]
    rfl
  have := isLocalizedModule_resBO L U g π hL hU
  have := isLocalizedModule_resBO M U g π hM hU
  obtain ⟨⟨z, ⟨_, n, rfl⟩⟩, hz⟩ := IsLocalizedModule.surj (Submonoid.powers g)
    (TensorProduct.map (resBO L U g) (resBO M U g)) (tensorBOEquiv L M U g hU (resT L M W (homOfLE
      hgW) w))
  refine ⟨z, n, ?_⟩
  rw [← thetaBO_map, ← hz, Submonoid.smul_def, map_smul, thetaBO_tensorBOEquiv, hw', map_smul]

theorem bump (y : Γ(L ⊗ M, U)) (g : Γ(X, U)) (z : Γ(L, U) ⊗[Γ(X, U)] Γ(M, U)) (n m : ℕ)
    (h : resBO (L ⊗ M) U g (theta L M U z) = resBO (L ⊗ M) U g (g ^ n • y)) :
    resBO (L ⊗ M) U g (theta L M U (g ^ m • z)) = resBO (L ⊗ M) U g (g ^ (m + n) • y) := by
  rw [map_smul, map_smul, h, ← map_smul, smul_smul, ← pow_add]

end Surjective

section Glue

variable (L M : X.Modules) {R : Type u} [CommRing R] (π : X ⟶ Spec (.of R))
  (hL : (OModulePresheaf.ofModules π L).IsQuasicoherent) (hM : (OModulePresheaf.ofModules π
    M).IsQuasicoherent)
  (U : X.Opens) (hU : IsAffineOpen U)

include hL hM hU in
theorem exists_pow_smul_sub_eq_zero (y : Γ(L ⊗ M, U)) (g g' : Γ(X, U))
    (z z' : Γ(L, U) ⊗[Γ(X, U)] Γ(M, U)) (n : ℕ)
    (hz : resBO (L ⊗ M) U g (theta L M U z) = resBO (L ⊗ M) U g (g ^ n • y))
    (hz' : resBO (L ⊗ M) U g' (theta L M U z') = resBO (L ⊗ M) U g' (g' ^ n • y)) :
    ∃ m : ℕ, (g * g') ^ m • (g' ^ n • z - g ^ n • z') = 0 := by
  have hle : X.basicOpen (g * g') ≤ X.basicOpen g := by rw [X.basicOpen_mul]; exact inf_le_left
  have hle' : X.basicOpen (g * g') ≤ X.basicOpen g' := by rw [X.basicOpen_mul]; exact inf_le_right
  have e1 : resBO (L ⊗ M) U (g * g') (theta L M U z) = g ^ n • resBO (L ⊗ M) U (g * g') y := by
    rw [← res_resBO (L ⊗ M) U g hle, hz, res_resBO, map_smul]
  have e2 : resBO (L ⊗ M) U (g * g') (theta L M U z') = g' ^ n • resBO (L ⊗ M) U (g * g') y := by
    rw [← res_resBO (L ⊗ M) U g' hle', hz', res_resBO, map_smul]
  have key : resBO (L ⊗ M) U (g * g') (theta L M U (g' ^ n • z - g ^ n • z')) = 0 := by
    rw [map_sub, map_smul, map_smul, map_sub, map_smul, map_smul, e1, e2, smul_smul, smul_smul,
      mul_comm (g' ^ n) (g ^ n), sub_self]
  have hinj := thetaBO_injective_of L M U (g * g') hU
    (theta_injective L M π hL hM _ (hU.basicOpen (g * g')))
  have h0 : TensorProduct.map (resBO L U (g * g')) (resBO M U (g * g')) (g' ^ n • z - g ^ n • z') =
    0 := by
    apply hinj
    rw [thetaBO_map, key, map_zero]
  have := isLocalizedModule_resBO L U (g * g') π hL hU
  have := isLocalizedModule_resBO M U (g * g') π hM hU
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers (g * g'))
    (f := TensorProduct.map (resBO L U (g * g')) (resBO M U (g * g')))).mp h0
  exact ⟨m, hm⟩

include hL hM hU in
theorem theta_surjective : Function.Surjective (theta L M U) :=
  (Scheme.Modules.bijective_lift_tensorSectionsBilin_of_isQuasicoherent
    π hL hM ⟨U, hU⟩).2

end Glue

theorem theta_bijective (L M : X.Modules) {R : Type u} [CommRing R] (π : X ⟶ Spec (.of R))
    (hL : (OModulePresheaf.ofModules π L).IsQuasicoherent) (hM : (OModulePresheaf.ofModules π
      M).IsQuasicoherent)
    (U : X.affineOpens) : Function.Bijective (theta L M U.1) :=
  ⟨theta_injective L M π hL hM U.1 U.2, theta_surjective L M π hL hM U.1 U.2⟩

end P2mQcTensorCompare



end



end Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2
end AlgebraicCurves.Geometry.Sheaves.Proofs

open AlgebraicCurves.Geometry.Sheaves.Proofs
open Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry TensorProduct Opposite

namespace AlgebraicGeometry.Scheme.Modules

universe u

theorem bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2
    {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (.of R)) {L M : X.Modules}
    (hL : (OModulePresheaf.ofModules π L).IsQuasicoherent) (hM : (OModulePresheaf.ofModules π
      M).IsQuasicoherent)
    (U : X.affineOpens) :
    Function.Bijective (TensorProduct.lift (Scheme.Modules.tensorSectionsBilin L M U) :
      Γ(L, U) ⊗[Γ(X, U)] Γ(M, U) →ₗ[Γ(X, U)] Γ(L ⊗ M, U)) :=
  P2mQcTensorCompare.theta_bijective L M π hL hM U
end AlgebraicGeometry.Scheme.Modules
end ProofImplementation
