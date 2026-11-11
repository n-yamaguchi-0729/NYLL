/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.Tactic.Choose
public import Nyll.SchemeTheory.RingTheory.Differentials.TopForms
public import Nyll.SchemeTheory.Modules.Differentials.Bases
public import Nyll.SchemeTheory.Modules.Differentials.Frames
public import Nyll.SchemeTheory.Modules.Differentials.Sections
public import Nyll.SchemeTheory.Affine.PullbackSectionsPushout
public import Nyll.SchemeTheory.Modules.ExteriorPower.Det
public import Nyll.SchemeTheory.Modules.ExteriorPower.PresheafExteriorPower
public import Nyll.SchemeTheory.Modules.Frames.FrameLocality
public import Nyll.SchemeTheory.Modules.Frames.Frames
public import Nyll.SchemeTheory.Modules.Frames.IsFrameOnPullbackLocalSection
public import Nyll.SchemeTheory.Modules.Functoriality.PullbackLocalSection
public import Nyll.SchemeTheory.Modules.Functoriality.PullbackUnitComposition
public import Nyll.SchemeTheory.Modules.KaehlerDifferentials
public import Nyll.SchemeTheory.Modules.Sections.SectionsAlgebra
public import Nyll.SchemeTheory.Modules.Tensor.TensorSections

/-!
# Pullback of top differential forms

The map is induced by base change of Kähler differentials, characterized on affine
sections, compatible with composition, and invertible for smooth Cartesian squares.
-/

@[expose] public section

attribute [local instance] AlgebraicGeometry.Scheme.Hom.kaehlerPresheafModule

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.DifferentialPullback

open AbelianVarieties.NOSProofs.AffineGluing

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

universe u

noncomputable section

namespace Construction

open AbelianVarieties.NOSProofs.AffineExteriorSections
open AbelianVarieties.NOSProofs.TopFormComposition.BenchOTFMComp (topFormMap_ιMulti)


section EA

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N] (d : ℕ)

lemma Λext {P : Type*} [AddCommGroup P] {g₁ g₂ : ⋀[R]^d M →+ P}
    (hsmul : ∀ (r : R) (x : ⋀[R]^d M), g₁ x = g₂ x → g₁ (r • x) = g₂ (r • x))
    (h : ∀ m : Fin d → M, g₁ (exteriorPower.ιMulti R d m) = g₂ (exteriorPower.ιMulti R d m)) :
    g₁ = g₂ := by
  ext x
  have hx : x ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R d (M := M))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨m, rfl⟩ := hx; exact h m
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul r x _ hx => exact hsmul r x hx

lemma Λext_apply {P : Type*} [AddCommGroup P] {g₁ g₂ : ⋀[R]^d M →+ P}
    (hsmul : ∀ (r : R) (x : ⋀[R]^d M), g₁ x = g₂ x → g₁ (r • x) = g₂ (r • x))
    (h : ∀ m : Fin d → M, g₁ (exteriorPower.ιMulti R d m) = g₂ (exteriorPower.ιMulti R d m))
    (x : ⋀[R]^d M) : g₁ x = g₂ x :=
  congrArg (fun g : ⋀[R]^d M →+ P => g x) (Λext d hsmul h)

/-- Restrict scalars along the selected ring homomorphism. -/
@[reducible] def modAlong (N : Type u) [AddCommGroup N] [Module S N] : Module R N := Module.compHom
    N f

variable {f} in
/-- The linear map underlying a semilinear additive map after restricting scalars. -/
def linAlong (ℓ : M →+ N) (hℓ : ∀ (r : R) (m : M), ℓ (r • m) = f r • ℓ m) :
    let _ : Module R N := modAlong f N; M →ₗ[R] N := by
  intro targetModule
  exact { toFun := ℓ, map_add' := ℓ.map_add, map_smul' := hℓ }

variable {f} in
/-- The alternating map induced by a semilinear additive map. -/
def ιAlong (ℓ : M →+ N) (hℓ : ∀ (r : R) (m : M), ℓ (r • m) = f r • ℓ m) :
    let _ : Module R (⋀[S]^d N) := modAlong f (⋀[S]^d N)
    M [⋀^Fin d]→ₗ[R] (⋀[S]^d N) := by
  intro mE
  let mN : Module R N := modAlong f N
  let alg : Algebra R S := f.toAlgebra
  have towerN : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have towerE : IsScalarTower R S (⋀[S]^d N) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact { (@MultilinearMap.restrictScalars R (Fin d) (fun _ => N) (⋀[S]^d N)
      _ _ _ (fun _ => mN) mE S _ _ _ _ (fun _ => towerN) towerE
      (exteriorPower.ιMulti S d (M := N)).toMultilinearMap).compLinearMap
      (fun _ => linAlong ℓ hℓ) with
    map_eq_zero_of_eq' := fun v i j h hij =>
      (exteriorPower.ιMulti S d (M := N)).map_eq_zero_of_eq _ (congrArg ℓ h) hij }

variable {f} in
/-- The additive map induced on exterior powers by a semilinear map. -/
def EA (ℓ : M →+ N) (hℓ : ∀ (r : R) (m : M), ℓ (r • m) = f r • ℓ m) : ⋀[R]^d M →+ ⋀[S]^d N :=
  let _ : Module R (⋀[S]^d N) := modAlong f (⋀[S]^d N)
  (exteriorPower.alternatingMapLinearEquiv (ιAlong d ℓ hℓ)).toAddMonoidHom

variable {f d} in
lemma EA_ιMulti (ℓ : M →+ N) (hℓ : ∀ (r : R) (m : M), ℓ (r • m) = f r • ℓ m) (m : Fin d → M) :
    EA d ℓ hℓ (exteriorPower.ιMulti R d m) = exteriorPower.ιMulti S d (fun i => ℓ (m i)) := by
  let _ : Module R (⋀[S]^d N) := modAlong f (⋀[S]^d N)
  change (exteriorPower.alternatingMapLinearEquiv (ιAlong d ℓ hℓ)) (exteriorPower.ιMulti R d m) = _
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

variable {f d} in
lemma EA_smul (ℓ : M →+ N) (hℓ : ∀ (r : R) (m : M), ℓ (r • m) = f r • ℓ m) (r : R) (x : ⋀[R]^d M) :
    EA d ℓ hℓ (r • x) = f r • EA d ℓ hℓ x := by
  let _ : Module R (⋀[S]^d N) := modAlong f (⋀[S]^d N)
  exact (exteriorPower.alternatingMapLinearEquiv (ιAlong d ℓ hℓ)).map_smul r x

end EA

section TFM

variable (R' K' O F : Type u) [CommRing R'] [CommRing K'] [Algebra R' K']
  [CommRing O] [Algebra R' O] [CommRing F] [Algebra O F] [Algebra K' F] [Algebra R' F]
  [IsScalarTower R' O F] [IsScalarTower R' K' F] (d : ℕ)

lemma topFormMap_smul (r : O) (x : ⋀[O]^d (Ω[O⁄R'])) :
    NeronModelInfra.TopFormOrder.topFormMap R' K' O F d (r • x) =
      algebraMap O F r • NeronModelInfra.TopFormOrder.topFormMap R' K' O F d x := by
  let _ : Module O (⋀[F]^d (Ω[F⁄K'])) :=
    NeronModelInfra.TopFormOrder.moduleAlong O F (⋀[F]^d (Ω[F⁄K']))
  exact (NeronModelInfra.TopFormOrder.topFormMap R' K' O F d).map_smul r x

end TFM

end Construction

namespace Construction

open AbelianVarieties.NOSProofs.AffineExteriorSections
open AbelianVarieties.NOSProofs.TopFormComposition.BenchOTFMComp (topFormMap_ιMulti)

section Main

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X Y : Scheme.{u}} (gY : Y ⟶ Spec (CommRingCat.of A)) (gX : X ⟶ Spec (CommRingCat.of B))
    (φ : X ⟶ Y) (hφ : φ ≫ gY = gX ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) (d : ℕ)

include hφ

lemma fac (U : Y.Opens) :
    CommRingCat.ofHom (algebraMap A B) ≫ gX.constToPresheaf.app (op (φ ⁻¹ᵁ U)) =
      gY.constToPresheaf.app (op U) ≫ φ.app U := by
  have h1 : gY.constToPresheaf.app (op U) ≫ φ.app U =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (φ ≫ gY).appLE ⊤ (φ ⁻¹ᵁ U) le_top := by
    change ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ gY.appLE ⊤ U le_top) ≫ φ.app U = _
    exact (Category.assoc _ _ _).trans
      (congrArg ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ ·)
        ((congrArg (gY.appLE ⊤ U le_top ≫ ·) (φ.app_eq_appLE (U := U))).trans
          (Scheme.Hom.appLE_comp_appLE φ gY ⊤ U (φ ⁻¹ᵁ U) le_top le_rfl)))
  have h2 : CommRingCat.ofHom (algebraMap A B) ≫ gX.constToPresheaf.app (op (φ ⁻¹ᵁ U)) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (gX ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))).appLE ⊤ (φ ⁻¹ᵁ U) le_top := by
    change CommRingCat.ofHom (algebraMap A B) ≫
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ gX.appLE ⊤ (φ ⁻¹ᵁ U) le_top) = _
    let f : CommRingCat.of A ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap A B)
    let r := gX.appLE ⊤ (φ ⁻¹ᵁ U) le_top
    exact (Category.assoc f (Scheme.ΓSpecIso (CommRingCat.of B)).inv r).symm.trans
      ((congrArg (· ≫ r) (Scheme.ΓSpecIso_inv_naturality f)).trans
        ((Category.assoc _ _ r).trans
          (congrArg ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ ·)
            (Scheme.Hom.comp_appLE gX (Spec.map f) ⊤ (φ ⁻¹ᵁ U) le_top).symm)))
  rw [h1, h2, hφ]

lemma fac_apply (U : Y.Opens) (a : A) :
    φ.app U (gY.constToPresheaf.app (op U) a) =
      gX.constToPresheaf.app (op (φ ⁻¹ᵁ U)) (algebraMap A B a) := by
  have := CategoryTheory.ConcreteCategory.congr_hom (fac gY gX φ hφ U) a
  exact this.symm

/-- The map on affine Kähler differentials induced by the commutative square. -/
def kdMap (U : Y.Opens) :
    gY.kaehlerPresheaf.obj (op U) ⟶
      (ModuleCat.restrictScalars (φ.app U).hom).obj (gX.kaehlerPresheaf.obj (op (φ ⁻¹ᵁ U))) :=
  CommRingCat.KaehlerDifferential.map (fac gY gX φ hφ U)

/-- The sheafification unit for Kähler differentials. -/
abbrev unit1 (V : X.Opens) : gX.kaehlerPresheaf.obj (op V) ⟶ gX.kaehler.val.obj (op V) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      gX.kaehlerPresheaf).app (op V)

omit hφ in
lemma unit1_apply (V : X.Opens) (x : gX.kaehlerPresheaf.obj (op V)) :
    unit1 gX V x = gX.kaehlerToSections V x := rfl

omit hφ in
/-- The universal derivation on sections over an open set. -/
def dK {C : Type u} [CommRing C] {Z : Scheme.{u}} (g : Z ⟶ Spec (CommRingCat.of C)) (V : Z.Opens) (b
    : Γ(Z, V)) :
    (g.kaehlerPresheaf.obj (op V) : Type u) :=
  CommRingCat.KaehlerDifferential.d (f := g.constToPresheaf.app (op V)) b

omit hφ in
lemma kp_map_dK {C : Type u} [CommRing C] {Z : Scheme.{u}} (g : Z ⟶ Spec (CommRingCat.of C))
    {V V' : Z.Opens} (i : op V ⟶ op V') (b : Γ(Z, V)) :
    g.kaehlerPresheaf.map i (dK g V b) = dK g V' (Z.presheaf.map i b) :=
  PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'_map_d
    g.constToPresheaf i b

omit hφ in
lemma kp_hom_ext {C : Type u} [CommRing C] {Z : Scheme.{u}} (g : Z ⟶ Spec (CommRingCat.of C)) (V :
    Z.Opens)
    {M : ModuleCat Γ(Z, V)} {α β : g.kaehlerPresheaf.obj (op V) ⟶ M}
    (h : ∀ b : Γ(Z, V), α.hom (dK g V b) = β.hom (dK g V b)) : α = β :=
  CommRingCat.KaehlerDifferential.ext h

omit hφ in
lemma map_unit1 {V V' : X.Opens} (j : op V ⟶ op V') (x : gX.kaehlerPresheaf.obj (op V)) :
    gX.kaehler.val.map j (unit1 gX V x) = unit1 gX V' (gX.kaehlerPresheaf.map j x) :=
  (PresheafOfModules.naturality_apply
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        gX.kaehlerPresheaf) j x).symm

omit hφ in
lemma φ_naturality_apply {U U' : Y.Opens} (i : op U ⟶ op U') (b : Γ(Y, U)) :
    X.presheaf.map ((TopologicalSpace.Opens.map φ.base).map i.unop).op (φ.app U b) =
      φ.app U' (Y.presheaf.map i b) :=
  (CategoryTheory.ConcreteCategory.congr_hom (φ.naturality i) b).symm

/-- The component of the map from presheaf to sheaf differentials. -/
def k1app (U : Y.Opens) :
    gY.kaehlerPresheaf.obj (op U) ⟶ ((Scheme.Modules.pushforward φ).obj gX.kaehler).val.obj (op U)
        :=
  kdMap gY gX φ hφ U ≫ (ModuleCat.restrictScalars (φ.app U).hom).map (unit1 gX (φ ⁻¹ᵁ U))

lemma k1app_dK (U : Y.Opens) (b : Γ(Y, U)) :
    k1app gY gX φ hφ U (dK gY U b) = unit1 gX (φ ⁻¹ᵁ U) (dK gX (φ ⁻¹ᵁ U) (φ.app U b)) := by
  change unit1 gX (φ ⁻¹ᵁ U) (CommRingCat.KaehlerDifferential.map (fac gY gX φ hφ U)
    (CommRingCat.KaehlerDifferential.d b)) = _
  rw [CommRingCat.KaehlerDifferential.map_d]
  rfl

/-- The natural map from presheaf differentials to the pushed forward sheaf. -/
def k1pre : gY.kaehlerPresheaf ⟶ ((Scheme.Modules.pushforward φ).obj gX.kaehler).val where
  app U := k1app gY gX φ hφ U.unop
  naturality {U U'} i := by
    obtain ⟨U⟩ := U; obtain ⟨U'⟩ := U'
    apply kp_hom_ext gY U
    intro b
    change k1app gY gX φ hφ U' (gY.kaehlerPresheaf.map i (dK gY U b)) =
      gX.kaehler.val.map ((TopologicalSpace.Opens.map φ.base).map i.unop).op
        (k1app gY gX φ hφ U (dK gY U b))
    rw [kp_map_dK, k1app_dK, k1app_dK, map_unit1, kp_map_dK, φ_naturality_apply]

/-- The induced map of sheaves of Kähler differentials. -/
def k1 : gY.kaehler ⟶ (Scheme.Modules.pushforward φ).obj gX.kaehler :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).homEquiv gY.kaehlerPresheaf
      ((Scheme.Modules.pushforward φ).obj gX.kaehler)).symm
    (k1pre gY gX φ hφ)

lemma k1_kaehlerToSections (U : Y.Opens) (x : gY.kaehlerPresheaf.obj (op U)) :
    (k1 gY gX φ hφ).app U (gY.kaehlerToSections U x) = (k1app gY gX φ hφ U x : Γ(gX.kaehler, φ ⁻¹ᵁ
        U)) := by
  have h := (PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).homEquiv_unit
      gY.kaehlerPresheaf ((Scheme.Modules.pushforward φ).obj gX.kaehler)
    (k1 gY gX φ hφ)
  let e := (PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).homEquiv
    gY.kaehlerPresheaf ((Scheme.Modules.pushforward φ).obj gX.kaehler)
  have he := (e.apply_symm_apply (k1pre gY gX φ hφ)).symm.trans h
  exact (congrArg (fun (q : gY.kaehlerPresheaf ⟶ _) => (q.app (op U)).hom x) he).symm

/-- The induced additive map on sections of differential sheaves. -/
abbrev k1h (U : Y.Opens) : Γ(gY.kaehler, U) →+ Γ(gX.kaehler, φ ⁻¹ᵁ U) :=
  ((k1 gY gX φ hφ).app U).hom

lemma k1h_smul (U : Y.Opens) (r : Γ(Y, U)) (m : Γ(gY.kaehler, U)) :
    k1h gY gX φ hφ U (r • m) = (φ.app U).hom r • k1h gY gX φ hφ U m :=
  Scheme.Modules.Hom.app_smul (k1 gY gX φ hφ) r m

lemma map_k1h {U U' : Y.Opens} (i : op U ⟶ op U') (m : Γ(gY.kaehler, U)) :
    gX.kaehler.presheaf.map ((Opens.map φ.base).map i.unop).op (k1h gY gX φ hφ U m) =
      k1h gY gX φ hφ U' (gY.kaehler.presheaf.map i m) :=
  (PresheafOfModules.naturality_apply (k1 gY gX φ hφ).val i m).symm

/-- The additive sheafification unit for exterior powers. -/
abbrev unitDh (V : X.Opens) : (⋀[Γ(X, V)]^d Γ(gX.kaehler, V)) →+ Γ(gX.topDifferentials d, V) :=
  (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      (ExteriorSections.pre gX d)).app
      (op V)).hom.toAddMonoidHom

omit hφ in
lemma unitDh_apply (V : X.Opens) (w : ⋀[Γ(X, V)]^d Γ(gX.kaehler, V)) :
    unitDh gX d V w = ExteriorSections.unitD gX d V w := rfl

/-- The map on exterior sections induced by the differential map. -/
def kdfun (U : Y.Opens) : (⋀[Γ(Y, U)]^d Γ(gY.kaehler, U)) →+ Γ(gX.topDifferentials d, φ ⁻¹ᵁ U) :=
  (unitDh gX d (φ ⁻¹ᵁ U)).comp (EA (f := (φ.app U).hom) d (k1h gY gX φ hφ U) (k1h_smul gY gX φ hφ
      U))

lemma kdfun_apply (U : Y.Opens) (w : ⋀[Γ(Y, U)]^d Γ(gY.kaehler, U)) :
    kdfun gY gX φ hφ d U w =
      ExteriorSections.unitD gX d (φ ⁻¹ᵁ U) (EA (f := (φ.app U).hom) d (k1h gY gX φ hφ U) (k1h_smul
          gY gX φ hφ U) w) := rfl

lemma kdfun_smul (U : Y.Opens) (r : Γ(Y, U)) (w : ⋀[Γ(Y, U)]^d Γ(gY.kaehler, U)) :
    kdfun gY gX φ hφ d U (r • w) = (φ.app U).hom r • kdfun gY gX φ hφ d U w := by
  rw [kdfun_apply, kdfun_apply, EA_smul, ExteriorSections.unitD_smul]

lemma kdfun_ιMulti (U : Y.Opens) (m : Fin d → Γ(gY.kaehler, U)) :
    kdfun gY gX φ hφ d U (exteriorPower.ιMulti _ d m) =
      ExteriorSections.unitD gX d (φ ⁻¹ᵁ U) (exteriorPower.ιMulti _ d (fun k => k1h gY gX φ hφ U (m
          k))) := by
  rw [kdfun_apply, EA_ιMulti]

omit hφ in
lemma map_unitD {V V' : X.Opens} (j : op V ⟶ op V') (w : ⋀[Γ(X, V)]^d Γ(gX.kaehler, V)) :
    (gX.topDifferentials d).presheaf.map j (ExteriorSections.unitD gX d V w) =
      ExteriorSections.unitD gX d V' (show ⋀[Γ(X, V')]^d Γ(gX.kaehler, V') from
        (ExteriorSections.pre gX d).map j (show (ExteriorSections.pre gX d).obj (op V) from w))
            := by
  have hnat := (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    (ExteriorSections.pre gX d))).naturality j
  exact (congrArg (fun ψ => ψ.hom (show (ExteriorSections.pre gX d).obj (op V) from w)) hnat).symm

/-- Restriction before applying the map on exterior sections. -/
abbrev L₁ {U U' : Y.Opens} (i : op U ⟶ op U') :
    (⋀[Γ(Y, U)]^d Γ(gY.kaehler, U)) →+ Γ(gX.topDifferentials d, φ ⁻¹ᵁ U') :=
  (kdfun gY gX φ hφ d U').comp ((ExteriorSections.pre gY d).map i).hom.toAddMonoidHom

/-- The map on exterior sections followed by restriction. -/
abbrev L₂ {U U' : Y.Opens} (i : op U ⟶ op U') :
    (⋀[Γ(Y, U)]^d Γ(gY.kaehler, U)) →+ Γ(gX.topDifferentials d, φ ⁻¹ᵁ U') :=
  ((gX.topDifferentials d).presheaf.map ((Opens.map φ.base).map i.unop).op).hom.comp (kdfun gY gX φ
      hφ d U)

lemma L₁_smul {U U' : Y.Opens} (i : op U ⟶ op U') (r : Γ(Y, U)) (x : ⋀[Γ(Y, U)]^d Γ(gY.kaehler, U))
    :
    L₁ gY gX φ hφ d i (r • x) = (φ.app U').hom (Y.presheaf.map i r) • L₁ gY gX φ hφ d i x := by
  have h1 := congrArg (kdfun gY gX φ hφ d U')
    ((ExteriorSections.pre gY d).map_smul i r (show (ExteriorSections.pre gY d).obj (op U) from x))
  exact h1.trans (kdfun_smul gY gX φ hφ d U' _ _)

lemma L₂_smul {U U' : Y.Opens} (i : op U ⟶ op U') (r : Γ(Y, U)) (x : ⋀[Γ(Y, U)]^d Γ(gY.kaehler, U))
    :
    L₂ gY gX φ hφ d i (r • x) = (φ.app U').hom (Y.presheaf.map i r) • L₂ gY gX φ hφ d i x := by
  change (gX.topDifferentials d).presheaf.map ((Opens.map φ.base).map i.unop).op (kdfun gY gX φ hφ d
      U (r • x)) = _
  rw [kdfun_smul, ← φ_naturality_apply]
  exact Scheme.Modules.map_smul _ _ _ _

lemma L₁_ιMulti {U U' : Y.Opens} (i : op U ⟶ op U') (m : Fin d → Γ(gY.kaehler, U)) :
    L₁ gY gX φ hφ d i (exteriorPower.ιMulti _ d m) =
      ExteriorSections.unitD gX d (φ ⁻¹ᵁ U')
        (exteriorPower.ιMulti _ d (fun k => k1h gY gX φ hφ U' (gY.kaehler.presheaf.map i (m k))))
            := by
  have h1 := congrArg (kdfun gY gX φ hφ d U') (PresheafOfModules.exteriorPower_map_ιMulti d
      gY.kaehler.val i m)
  exact h1.trans (kdfun_ιMulti gY gX φ hφ d U' _)

lemma L₂_ιMulti {U U' : Y.Opens} (i : op U ⟶ op U') (m : Fin d → Γ(gY.kaehler, U)) :
    L₂ gY gX φ hφ d i (exteriorPower.ιMulti _ d m) =
      ExteriorSections.unitD gX d (φ ⁻¹ᵁ U')
        (exteriorPower.ιMulti _ d (fun k => k1h gY gX φ hφ U' (gY.kaehler.presheaf.map i (m k))))
            := by
  change (gX.topDifferentials d).presheaf.map ((Opens.map φ.base).map i.unop).op
    (kdfun gY gX φ hφ d U (exteriorPower.ιMulti _ d m)) = _
  rw [kdfun_ιMulti, map_unitD]
  have h2 := PresheafOfModules.exteriorPower_map_ιMulti d gX.kaehler.val ((Opens.map φ.base).map
      i.unop).op
    (fun k => k1h gY gX φ hφ U (m k))
  refine (congrArg (ExteriorSections.unitD gX d (φ ⁻¹ᵁ U')) h2).trans ?_
  congr 1; congr 1
  funext k
  exact map_k1h gY gX φ hφ i (m k)

lemma kdfun_naturality {U U' : Y.Opens} (i : op U ⟶ op U') :
    L₁ gY gX φ hφ d i = L₂ gY gX φ hφ d i := by
  refine Λext d (fun r x hx => ?_) (fun m => ?_)
  · exact (L₁_smul gY gX φ hφ d i r x).trans
      ((congrArg (_ • ·) hx).trans (L₂_smul gY gX φ hφ d i r x).symm)
  · exact (L₁_ιMulti gY gX φ hφ d i m).trans (L₂_ιMulti gY gX φ hφ d i m).symm

/-- The natural additive map on exterior-power presheaves. -/
def kdAb : (ExteriorSections.pre gY d).presheaf ⟶ ((Scheme.Modules.pushforward φ).obj
    (gX.topDifferentials d)).val.presheaf where
  app U := AddCommGrpCat.ofHom (kdfun gY gX φ hφ d U.unop)
  naturality {U U'} i := by
    apply ConcreteCategory.hom_ext
    intro w
    exact DFunLike.congr_fun (kdfun_naturality gY gX φ hφ d i) w

/-- The natural module map on exterior-power presheaves. -/
def kdpre : ExteriorSections.pre gY d ⟶ ((Scheme.Modules.pushforward φ).obj (gX.topDifferentials
    d)).val :=
  PresheafOfModules.homMk (kdAb gY gX φ hφ d) (fun U r w => by
    obtain ⟨U⟩ := U
    exact kdfun_smul gY gX φ hφ d U r w)

/-- The induced map on sheaves of top differential forms. -/
def kd : gY.topDifferentials d ⟶ (Scheme.Modules.pushforward φ).obj (gX.topDifferentials d) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).homEquiv
      (ExteriorSections.pre gY d) ((Scheme.Modules.pushforward φ).obj (gX.topDifferentials d))).symm
    (kdpre gY gX φ hφ d)

lemma kd_unitD (U : Y.Opens) (w : ⋀[Γ(Y, U)]^d Γ(gY.kaehler, U)) :
    (kd gY gX φ hφ d).app U (ExteriorSections.unitD gY d U w) =
      (kdfun gY gX φ hφ d U w : Γ(gX.topDifferentials d, φ ⁻¹ᵁ U)) := by
  have h := (PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).homEquiv_unit
      (ExteriorSections.pre gY d)
    ((Scheme.Modules.pushforward φ).obj (gX.topDifferentials d)) (kd gY gX φ hφ d)
  let e := (PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).homEquiv
    (ExteriorSections.pre gY d) ((Scheme.Modules.pushforward φ).obj (gX.topDifferentials d))
  have he := (e.apply_symm_apply (kdpre gY gX φ hφ d)).symm.trans h
  exact (congrArg (fun (q : ExteriorSections.pre gY d ⟶ _) => (q.app (op U)).hom
    (show (ExteriorSections.pre gY d).obj (op U) from w)) he).symm

/-- The map from the pullback of top differential forms. -/
def θ : (Scheme.Modules.pullback φ).obj (gY.topDifferentials d) ⟶ gX.topDifferentials d :=
  ((Scheme.Modules.pullbackPushforwardAdjunction φ).homEquiv _ _).symm (kd gY gX φ hφ d)

lemma θ_pullbackLocalSection (U : Y.Opens) (s : Γ(gY.topDifferentials d, U)) :
    (θ gY gX φ hφ d).app (φ ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection φ s) =
      ((kd gY gX φ hφ d).app U s : Γ(gX.topDifferentials d, φ ⁻¹ᵁ U)) :=
  Scheme.Modules.homEquiv_symm_app_pullbackLocalSection φ (kd gY gX φ hφ d) s

lemma key (U : Y.Opens) (η : ⋀[Γ(Y, U)]^d (gY.kaehlerPresheaf.obj (op U))) :
    let _ : Algebra A Γ(Y, U) := gY.sectionsAlgebra U
    let _ : Algebra B Γ(X, φ ⁻¹ᵁ U) := gX.sectionsAlgebra (φ ⁻¹ᵁ U)
    let : Algebra Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) := (φ.app U).hom.toAlgebra
    let : Algebra A Γ(X, φ ⁻¹ᵁ U) :=
      (CommRingCat.ofHom (algebraMap A B) ≫ gX.constToPresheaf.app (op (φ ⁻¹ᵁ U))).hom.toAlgebra
    ∀ [IsScalarTower A B Γ(X, φ ⁻¹ᵁ U)] [IsScalarTower A Γ(Y, U) Γ(X, φ ⁻¹ᵁ U)],
    EA (f := (φ.app U).hom) d (k1h gY gX φ hφ U) (k1h_smul gY gX φ hφ U)
        (exteriorPower.map d (gY.kaehlerToSectionsₗ U) η) =
      exteriorPower.map d (gX.kaehlerToSectionsₗ (φ ⁻¹ᵁ U))
        (NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) d η) := by
  intro algYU algXV algYXV algAXV towerAB towerAY
  refine Λext_apply d
    (g₁ := (EA (f := (φ.app U).hom) d (k1h gY gX φ hφ U) (k1h_smul gY gX φ hφ U)).comp
      (exteriorPower.map d (gY.kaehlerToSectionsₗ U)).toAddMonoidHom)
    (g₂ := (exteriorPower.map d (gX.kaehlerToSectionsₗ (φ ⁻¹ᵁ U))).toAddMonoidHom.comp
      (let _ : Module Γ(Y, U) (⋀[Γ(X, φ ⁻¹ᵁ U)]^d (Ω[Γ(X, φ ⁻¹ᵁ U)⁄B])) :=
        NeronModelInfra.TopFormOrder.moduleAlong Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) _
       (NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) d).toAddMonoidHom))
    (fun r x hx => ?_) (fun ω => ?_) η
  · change EA d (k1h gY gX φ hφ U) (k1h_smul gY gX φ hφ U) (exteriorPower.map d
      (gY.kaehlerToSectionsₗ U) (r • x)) =
      exteriorPower.map d (gX.kaehlerToSectionsₗ (φ ⁻¹ᵁ U))
        (NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) d (r • x))
    rw [map_smul, EA_smul]
    have hx' : EA d (k1h gY gX φ hφ U) (k1h_smul gY gX φ hφ U) (exteriorPower.map d
        (gY.kaehlerToSectionsₗ U) x) =
        exteriorPower.map d (gX.kaehlerToSectionsₗ (φ ⁻¹ᵁ U))
          (NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) d x) := hx
    rw [hx']
    have hts : NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) d (r • x) =
        algebraMap Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) r • NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U)
            Γ(X, φ ⁻¹ᵁ U) d x :=
      topFormMap_smul ..
    have hms := (exteriorPower.map d (gX.kaehlerToSectionsₗ (φ ⁻¹ᵁ U))).map_smul ((φ.app U).hom r)
      (NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) d x)
    exact hms.symm.trans (congrArg (exteriorPower.map d (gX.kaehlerToSectionsₗ (φ ⁻¹ᵁ U))) hts.symm)
  · change EA d (k1h gY gX φ hφ U) (k1h_smul gY gX φ hφ U)
        (exteriorPower.map d (gY.kaehlerToSectionsₗ U) (exteriorPower.ιMulti _ d ω)) =
      exteriorPower.map d (gX.kaehlerToSectionsₗ (φ ⁻¹ᵁ U))
        (NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) d (exteriorPower.ιMulti _
            d ω))
    have hleft := congrArg
      (EA d (k1h gY gX φ hφ U) (k1h_smul gY gX φ hφ U))
      (exteriorPower.map_apply_ιMulti (gY.kaehlerToSectionsₗ U) ω)
    have hright := congrArg (exteriorPower.map d (gX.kaehlerToSectionsₗ (φ ⁻¹ᵁ U)))
      (@topFormMap_ιMulti A B Γ(Y, U) Γ(X, φ ⁻¹ᵁ U)
        _ _ _ _ algYU _ algYXV algXV algAXV towerAY towerAB d ω)
    refine hleft.trans ((EA_ιMulti (k1h gY gX φ hφ U)
      (k1h_smul gY gX φ hφ U) _).trans ?_)
    refine Eq.trans ?_ (hright.trans
      (exteriorPower.map_apply_ιMulti (gX.kaehlerToSectionsₗ (φ ⁻¹ᵁ U)) _)).symm
    apply congrArg (exteriorPower.ιMulti Γ(X, φ ⁻¹ᵁ U) d)
    funext i
    change k1h gY gX φ hφ U (gY.kaehlerToSections U (ω i)) =
      gX.kaehlerToSections (φ ⁻¹ᵁ U) (KaehlerDifferential.map A B Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) (ω i))
    refine (k1_kaehlerToSections gY gX φ hφ U (ω i)).trans ?_
    rfl

omit hφ in
lemma emap_eq_topFormMap {V W : X.Opens} (h : W ≤ V) (z : ⋀[Γ(X, V)]^d (gX.kaehlerPresheaf.obj (op
    V))) :
    let _ : Algebra B Γ(X, V) := gX.sectionsAlgebra V
    let _ : Algebra B Γ(X, W) := gX.sectionsAlgebra W
    let : Algebra Γ(X, V) Γ(X, W) := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
    ∀ [IsScalarTower B Γ(X, V) Γ(X, W)],
    ExteriorSections.emap gX d h z = NeronModelInfra.TopFormOrder.topFormMap B B Γ(X, V) Γ(X, W) d z
        := by
  intro algXV algXW algVW towerBVW
  refine Λext_apply d
    (g₁ := ((ExteriorSections.preK gX d).map (homOfLE h).op).hom.toAddMonoidHom)
    (g₂ := (let _ : Module Γ(X, V) (⋀[Γ(X, W)]^d (Ω[Γ(X, W)⁄B])) :=
        NeronModelInfra.TopFormOrder.moduleAlong Γ(X, V) Γ(X, W) _
       (NeronModelInfra.TopFormOrder.topFormMap B B Γ(X, V) Γ(X, W) d).toAddMonoidHom))
    (fun r x hx => ?_) (fun ω => ?_) z
  · have hx' : ExteriorSections.emap gX d h x = NeronModelInfra.TopFormOrder.topFormMap B B Γ(X, V)
      Γ(X, W) d x := hx
    change ExteriorSections.emap gX d h (r • x) = NeronModelInfra.TopFormOrder.topFormMap B B Γ(X,
        V) Γ(X, W) d (r • x)
    refine (ExteriorSections.emap_smul gX d h r x).trans ?_
    rw [hx']
    have hts : NeronModelInfra.TopFormOrder.topFormMap B B Γ(X, V) Γ(X, W) d (r • x) =
        algebraMap Γ(X, V) Γ(X, W) r • NeronModelInfra.TopFormOrder.topFormMap B B Γ(X, V) Γ(X, W) d
            x :=
      topFormMap_smul ..
    exact hts.symm
  · change ExteriorSections.emap gX d h (exteriorPower.ιMulti _ d ω) =
      NeronModelInfra.TopFormOrder.topFormMap B B Γ(X, V) Γ(X, W) d (exteriorPower.ιMulti _ d ω)
    exact (ExteriorSections.emap_ιMulti gX d h ω).trans
      (@topFormMap_ιMulti B B Γ(X, V) Γ(X, W)
        _ _ _ _ algXV _ algVW algXW algXW towerBVW inferInstance d ω).symm

omit hφ in
lemma tower_sections {V W : X.Opens} (h : W ≤ V) :
    let _ : Algebra B Γ(X, V) := gX.sectionsAlgebra V
    let _ : Algebra B Γ(X, W) := gX.sectionsAlgebra W
    let : Algebra Γ(X, V) Γ(X, W) := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
    IsScalarTower B Γ(X, V) Γ(X, W) := by
  intro algXV algXW algVW
  refine IsScalarTower.of_algebraMap_eq fun b => ?_
  have := gX.constToPresheaf.naturality (homOfLE h).op
  have h' := congrArg (fun ψ => ψ.hom b) this
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, CommRingCat.hom_comp]
      at h'
  exact h'

theorem main :
    ∃ θ : (Scheme.Modules.pullback φ).obj (gY.topDifferentials d) ⟶ gX.topDifferentials d,
      ∀ (U : Y.Opens) (_ : IsAffineOpen U) (W : X.Opens) (_ : IsAffineOpen W) (hWU : W ≤ φ ⁻¹ᵁ U),
        let _ : Algebra A Γ(Y, U) := gY.sectionsAlgebra U
        let _ : Algebra B Γ(X, W) := gX.sectionsAlgebra W
        let _ : Algebra Γ(Y, U) Γ(X, W) := (φ.appLE U W hWU).hom.toAlgebra
        ∀ [Algebra A Γ(X, W)] [IsScalarTower A B Γ(X, W)] [IsScalarTower A Γ(Y, U) Γ(X, W)]
          (η : ⋀[Γ(Y, U)]^d (gY.kaehlerPresheaf.obj (op U))),
          (gX.topDifferentials d).presheaf.map (homOfLE hWU).op
              (θ.app (φ ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection φ (gY.topToSections d U η))) =
            gX.topToSections d W (NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, W) d η)
                := by
  refine ⟨θ gY gX φ hφ d, ?_⟩
  intro U _ W _ hWU algYU algXW algYXW instAW instABW instAYW η
  let _ : Algebra B Γ(X, φ ⁻¹ᵁ U) := gX.sectionsAlgebra (φ ⁻¹ᵁ U)
  let : Algebra Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) := (φ.app U).hom.toAlgebra
  let : Algebra A Γ(X, φ ⁻¹ᵁ U) :=
    (CommRingCat.ofHom (algebraMap A B) ≫ gX.constToPresheaf.app (op (φ ⁻¹ᵁ U))).hom.toAlgebra
  have : IsScalarTower A B Γ(X, φ ⁻¹ᵁ U) := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom (fac gY gX φ hφ U))
  let : Algebra Γ(X, φ ⁻¹ᵁ U) Γ(X, W) := (X.presheaf.map (homOfLE hWU).op).hom.toAlgebra
  have : IsScalarTower Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) Γ(X, W) := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower B Γ(X, φ ⁻¹ᵁ U) Γ(X, W) := tower_sections gX hWU
  rw [θ_pullbackLocalSection, ExteriorSections.topToSections_eq, kd_unitD, kdfun_apply, key gY gX φ
      hφ d U η]
  change ExteriorSections.resD gX d hWU (gX.topToSections d (φ ⁻¹ᵁ U)
    (NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) d η)) = _
  refine (ExteriorSections.resD_top gX d hWU
    (NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) d η)).trans ?_
  refine (congrArg (gX.topToSections d W) (emap_eq_topFormMap gX d hWU
    (NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) d η))).trans ?_
  have hA : NeronModelInfra.TopFormOrder.topFormMap B B Γ(X, φ ⁻¹ᵁ U) Γ(X, W) d
      (NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) d η) =
      NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, W) d η :=
    NeronModelInfra.TopFormOrder.topFormMap_topFormMap ..
  exact congrArg (gX.topToSections d W) hA

end Main

end Construction

end

end SchemeTheory.DifferentialPullback

namespace AlgebraicGeometry.Scheme.Hom

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AbelianVarieties.NOSProofs.AffineGluing
open scoped TensorProduct

universe u

open SchemeTheory.DifferentialPullback

theorem exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X Y : Scheme.{u}} (gY : Y ⟶ Spec (CommRingCat.of A)) (gX : X ⟶ Spec (CommRingCat.of B))
    (φ : X ⟶ Y) (hφ : φ ≫ gY = gX ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) (d : ℕ) :
    ∃ θ : (Scheme.Modules.pullback φ).obj (gY.topDifferentials d) ⟶ gX.topDifferentials d,
      ∀ (U : Y.Opens) (_ : IsAffineOpen U) (W : X.Opens) (_ : IsAffineOpen W) (hWU : W ≤ φ ⁻¹ᵁ U),
        letI := gY.sectionsAlgebra U; letI := gX.sectionsAlgebra W
        letI : Algebra Γ(Y, U) Γ(X, W) := (φ.appLE U W hWU).hom.toAlgebra
        ∀ [Algebra A Γ(X, W)] [IsScalarTower A B Γ(X, W)] [IsScalarTower A Γ(Y, U) Γ(X, W)]
          (η : ⋀[Γ(Y, U)]^d (gY.kaehlerPresheaf.obj (op U))),
          (gX.topDifferentials d).presheaf.map (homOfLE hWU).op
              (θ.app (φ ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection φ (gY.topToSections d U η))) =
            gX.topToSections d W (NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, W) d η)
                :=
  Construction.main gY gX φ hφ d

end AlgebraicGeometry.Scheme.Hom
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_isIso_of_map_pullbackLocalSection_topToSections_eq_of_isPullback_of_smoothOfRelativeDimension.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.DifferentialPullback

open AbelianVarieties.NOSProofs.AffineGluing

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped TensorProduct

universe u

namespace BaseChange

theorem tensorKaehlerEquiv_one_tmul (R S A B : Type u) [CommRing R] [CommRing S] [CommRing A]
    [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra A B] [Algebra S B] [Algebra R B] [IsScalarTower R A B]
        [IsScalarTower R S B]
    [Algebra.IsPushout R S A B] (x : Ω[A⁄R]) :
    KaehlerDifferential.tensorKaehlerEquiv R S A B (1 ⊗ₜ x) = KaehlerDifferential.map R S A B x
        := by
  have h1 : ∀ y, y ∈ Submodule.span A (Set.range (KaehlerDifferential.D R A)) →
      KaehlerDifferential.tensorKaehlerEquiv R S A B (1 ⊗ₜ y) = KaehlerDifferential.map R S A B y
          := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      rw [KaehlerDifferential.tensorKaehlerEquiv_tmul_D, one_smul, KaehlerDifferential.map_D]
    | zero => simp only [TensorProduct.tmul_zero, map_zero]
    | add y z _ _ hy hz => rw [TensorProduct.tmul_add, map_add, hy, hz, map_add]
    | smul a y _ hy =>
      rw [TensorProduct.tmul_smul, LinearMap.map_smul, ← IsScalarTower.algebraMap_smul B a (1 ⊗ₜ[A]
          y : B ⊗[A] Ω[A⁄R]),
        LinearEquiv.map_smul, hy, IsScalarTower.algebraMap_smul]
  exact h1 x (by rw [KaehlerDifferential.span_range_derivation]; exact Submodule.mem_top)

theorem appLE_congr' {X Y : Scheme.{u}} {f f' : X ⟶ Y} (h : f = f') (U : Y.Opens) (V : X.Opens) (e :
    V ≤ f ⁻¹ᵁ U) :
    f.appLE U V e = f'.appLE U V (h ▸ e) := by
  subst h; rfl

end BaseChange

end SchemeTheory.DifferentialPullback

namespace AlgebraicGeometry.Scheme.Hom

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AbelianVarieties.NOSProofs.AffineGluing
open scoped TensorProduct

universe u

open SchemeTheory.DifferentialPullback

open SchemeTheory.DifferentialPullback.BaseChange in
theorem
    isIso_of_map_pullbackLocalSection_topToSections_eq_of_isPullback_of_smoothOfRelativeDimension
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X Y : Scheme.{u}} (gY : Y ⟶ Spec (CommRingCat.of A)) (gX : X ⟶ Spec (CommRingCat.of B))
    (φ : X ⟶ Y) (hφ : IsPullback φ gX gY (Spec.map (CommRingCat.ofHom (algebraMap A B)))) (d : ℕ)
    [SmoothOfRelativeDimension d gY]
    (θ : (Scheme.Modules.pullback φ).obj (gY.topDifferentials d) ⟶ gX.topDifferentials d)
    (hθ : ∀ (U : Y.Opens) (_ : IsAffineOpen U) (W : X.Opens) (_ : IsAffineOpen W) (hWU : W ≤ φ ⁻¹ᵁ
        U),
        letI := gY.sectionsAlgebra U; letI := gX.sectionsAlgebra W
        letI : Algebra Γ(Y, U) Γ(X, W) := (φ.appLE U W hWU).hom.toAlgebra
        ∀ [Algebra A Γ(X, W)] [IsScalarTower A B Γ(X, W)] [IsScalarTower A Γ(Y, U) Γ(X, W)]
          (η : ⋀[Γ(Y, U)]^d (gY.kaehlerPresheaf.obj (op U))),
          (gX.topDifferentials d).presheaf.map (homOfLE hWU).op
              (θ.app (φ ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection φ (gY.topToSections d U η))) =
            gX.topToSections d W (NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, W) d η))
                :
    IsIso θ := by
  classical
  have key : ∀ x : X, ∃ (V : X.Opens) (p : Γ((Scheme.Modules.pullback φ).obj (gY.topDifferentials
      d), V)),
      x ∈ V ∧ Scheme.Modules.IsFrameOn p V ∧ Scheme.Modules.IsFrameOn (θ.app V p) V := by
    intro x
    obtain ⟨U₀, hyU₀, _, he⟩ :=
      AlgebraicGeometry.Scheme.Hom.exists_basis_kaehler_of_isAffineOpen_of_smoothOfRelativeDimension
          gY d (φ.base x)
    obtain ⟨U, hU, hyU, hUU₀⟩ := exists_isAffineOpen_mem_and_subset hyU₀
    let algAU : Algebra A Γ(Y, U) := gY.sectionsAlgebra U
    obtain ⟨bU, _⟩ := he U hUU₀ hU
    have hbij : Function.Bijective (gY.kaehlerToSectionsₗ U) :=
      AlgebraicGeometry.Scheme.Hom.kaehlerToSections_bijective_of_isAffineOpen gY hU
    let κU : (Ω[Γ(Y, U)⁄A]) ≃ₗ[Γ(Y, U)] Γ(gY.kaehler, U) := LinearEquiv.ofBijective
        (gY.kaehlerToSectionsₗ U) hbij
    let η : Module.Basis (Fin d) Γ(Y, U) (Ω[Γ(Y, U)⁄A]) := bU.map κU.symm
    have hs : Scheme.Modules.IsFrameOn (gY.topToSections d U (exteriorPower.ιMulti Γ(Y, U) d η)) U
        := by
      refine AlgebraicGeometry.Scheme.Hom.isFrameOn_topToSections_iotaMulti_of_forall_exists_basis
          gY d hU η fun W hW hWaff => ?_
      intro algW algUW tower
      exact AlgebraicGeometry.Scheme.Hom.exists_basis_kaehlerDifferential_map_of_isAffineOpen_le gY
          hU hWaff hW (ι := Fin d) η
    have hp := AlgebraicGeometry.Scheme.Modules.IsFrameOn.pullbackLocalSection φ hs
    obtain ⟨hW₀, hPO⟩ :=
        AlgebraicGeometry.Scheme.Hom.isAffineOpen_preimage_and_isPushout_of_isPullback gY gX φ hφ U
        hU
    let algBW : Algebra B Γ(X, φ ⁻¹ᵁ U) := gX.sectionsAlgebra (φ ⁻¹ᵁ U)
    let algUW : Algebra Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) := (φ.appLE U (φ ⁻¹ᵁ U) le_rfl).hom.toAlgebra
    let algAW : Algebra A Γ(X, φ ⁻¹ᵁ U) := ((algebraMap B Γ(X, φ ⁻¹ᵁ U)).comp (algebraMap A
        B)).toAlgebra
    have : IsScalarTower A B Γ(X, φ ⁻¹ᵁ U) := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have : IsScalarTower A Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) := by
      refine IsScalarTower.of_algebraMap_eq fun a => ?_
      have happ := congrArg
        (fun q : Γ(Y, U) ⟶ Γ(X, φ ⁻¹ᵁ U) =>
          q.hom ((gY.constToPresheaf.app (op U)).hom a))
        (φ.appLE_eq_app (U := U))
      exact (Construction.fac_apply gY gX φ hφ.w U a).symm.trans happ.symm
    have : Algebra.IsPushout A B Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) := hPO
    let η₀' : Fin d → Ω[Γ(X, φ ⁻¹ᵁ U)⁄B] := fun i => KaehlerDifferential.map A B Γ(Y, U) Γ(X, φ ⁻¹ᵁ
        U) (η i)
    let η₀ : Module.Basis (Fin d) Γ(X, φ ⁻¹ᵁ U) (Ω[Γ(X, φ ⁻¹ᵁ U)⁄B]) :=
      (Algebra.TensorProduct.basis Γ(X, φ ⁻¹ᵁ U) η).map
        (KaehlerDifferential.tensorKaehlerEquiv A B Γ(Y, U) Γ(X, φ ⁻¹ᵁ U))
    have hη₀ : ∀ i, η₀ i = η₀' i := by
      intro i
      simp only [η₀, η₀', Module.Basis.map_apply, Algebra.TensorProduct.basis_apply]
      exact tensorKaehlerEquiv_one_tmul A B Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) (η i)
    have hq := hθ U hU (φ ⁻¹ᵁ U) hW₀ le_rfl (exteriorPower.ιMulti Γ(Y, U) d η)
    have hid : (homOfLE (le_refl (φ ⁻¹ᵁ U))).op = 𝟙 (op (φ ⁻¹ᵁ U)) := rfl
    rw [hid, CategoryTheory.Functor.map_id] at hq
    have hRHS : NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) d
        (exteriorPower.ιMulti Γ(Y, U) d η) = exteriorPower.ιMulti Γ(X, φ ⁻¹ᵁ U) d η₀' :=
      AbelianVarieties.NOSProofs.TopFormComposition.BenchOTFMComp.topFormMap_ιMulti
        A B Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) d η
    have hθp : θ.app (φ ⁻¹ᵁ U)
          (Scheme.Modules.pullbackLocalSection φ (gY.topToSections d U (exteriorPower.ιMulti Γ(Y, U)
              d η))) =
        gX.topToSections d (φ ⁻¹ᵁ U) (exteriorPower.ιMulti Γ(X, φ ⁻¹ᵁ U) d η₀') := by
      exact hq.trans (congrArg (gX.topToSections d (φ ⁻¹ᵁ U)) hRHS)
    refine ⟨φ ⁻¹ᵁ U, _, hyU, hp, ?_⟩
    rw [hθp]
    refine AlgebraicGeometry.Scheme.Hom.isFrameOn_topToSections_iotaMulti_of_forall_exists_basis gX
        d hW₀ η₀' fun W' hW' hW'aff => ?_
    intro algW' algWW' tower
    obtain ⟨b', hb'⟩ :=
        AlgebraicGeometry.Scheme.Hom.exists_basis_kaehlerDifferential_map_of_isAffineOpen_le gX hW₀
        hW'aff hW' (ι := Fin d) η₀
    exact ⟨b', fun i => by rw [hb' i, hη₀ i]⟩
  choose V p hV using key
  refine AlgebraicGeometry.Scheme.Modules.isIso_of_isFrameOn_of_iSup_eq_top θ V ?_ p (fun x => θ.app
      (V x) (p x))
    (fun x => (hV x).2.1) (fun x => (hV x).2.2) (fun x => rfl)
  exact top_le_iff.mp fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, (hV x).1⟩

end AlgebraicGeometry.Scheme.Hom
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_eq_of_map_pullbackLocalSection_topToSections_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.DifferentialPullback

open AbelianVarieties.NOSProofs.AffineGluing

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

open TopologicalSpace

namespace Locality

theorem app_naturality {X : Scheme.{u}} {M N : X.Modules} (θ : M ⟶ N) {V W : X.Opens} (i : W ⟶ V)
    (x : Γ(M, V)) :
    N.presheaf.map i.op (θ.app V x) = θ.app W (M.presheaf.map i.op x) := by
  have h := θ.mapPresheaf.naturality i.op
  have h' := congrFun (congrArg (fun f => (ConcreteCategory.hom f : Γ(M, V) → Γ(N, W))) h) x
  exact h'.symm

theorem algebraMap_comm {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X Y : Scheme.{u}} (gY : Y ⟶ Spec (CommRingCat.of A)) (gX : X ⟶ Spec (CommRingCat.of B))
    (φ : X ⟶ Y) (hφ : φ ≫ gY = gX ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)))
    (U : Y.Opens) (W : X.Opens) (hWU : W ≤ φ ⁻¹ᵁ U) (a : A) :
    (φ.appLE U W hWU) ((gY.constToPresheaf.app (op U)) a) =
      (gX.constToPresheaf.app (op W)) (algebraMap A B a) := by
  have hfac := Construction.fac_apply gY gX φ hφ U a
  have hnat := gX.constToPresheaf.naturality (homOfLE hWU).op
  have hnat' := congrArg (fun q => q.hom (algebraMap A B a)) hnat
  change (X.presheaf.map (homOfLE hWU).op).hom
    ((φ.app U).hom ((gY.constToPresheaf.app (op U)).hom a)) = _
  rw [hfac]
  exact hnat'.symm

end Locality

theorem _root_.AlgebraicGeometry.Scheme.Hom.eq_of_map_pullbackLocalSection_topToSections_eq
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X Y : Scheme.{u}} (gY : Y ⟶ Spec (CommRingCat.of A)) (gX : X ⟶ Spec (CommRingCat.of B))
    (φ : X ⟶ Y) (hφ : φ ≫ gY = gX ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) (d : ℕ)
    (θ θ' : (Scheme.Modules.pullback φ).obj (gY.topDifferentials d) ⟶ gX.topDifferentials d)
    (hθ : ∀ (U : Y.Opens) (_ : IsAffineOpen U) (W : X.Opens) (_ : IsAffineOpen W) (hWU : W ≤ φ ⁻¹ᵁ
        U),
        letI := gY.sectionsAlgebra U; letI := gX.sectionsAlgebra W
        letI : Algebra Γ(Y, U) Γ(X, W) := (φ.appLE U W hWU).hom.toAlgebra
        ∀ [Algebra A Γ(X, W)] [IsScalarTower A B Γ(X, W)] [IsScalarTower A Γ(Y, U) Γ(X, W)]
          (η : ⋀[Γ(Y, U)]^d (gY.kaehlerPresheaf.obj (op U))),
          (gX.topDifferentials d).presheaf.map (homOfLE hWU).op
              (θ.app (φ ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection φ (gY.topToSections d U η))) =
            gX.topToSections d W (NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, W) d η))
    (hθ' : ∀ (U : Y.Opens) (_ : IsAffineOpen U) (W : X.Opens) (_ : IsAffineOpen W) (hWU : W ≤ φ
        ⁻¹ᵁ U),
        letI := gY.sectionsAlgebra U; letI := gX.sectionsAlgebra W
        letI : Algebra Γ(Y, U) Γ(X, W) := (φ.appLE U W hWU).hom.toAlgebra
        ∀ [Algebra A Γ(X, W)] [IsScalarTower A B Γ(X, W)] [IsScalarTower A Γ(Y, U) Γ(X, W)]
          (η : ⋀[Γ(Y, U)]^d (gY.kaehlerPresheaf.obj (op U))),
          (gX.topDifferentials d).presheaf.map (homOfLE hWU).op
              (θ'.app (φ ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection φ (gY.topToSections d U η))) =
            gX.topToSections d W (NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, W) d η))
                :
    θ = θ' := by
  have key : ∀ (U : Y.Opens) (hU : IsAffineOpen U) (s : Γ(gY.topDifferentials d, U)),
      θ.app (φ ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection φ s) =
        θ'.app (φ ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection φ s) := by
    intro U hU s
    obtain ⟨η, rfl⟩ := (gY.topToSections_bijective_of_isAffineOpen d hU).2 s
    refine AffineSections.sec_ext (gX.topDifferentials d)
      (fun i : {W : X.affineOpens // (W : X.Opens) ≤ φ ⁻¹ᵁ U} => (i.1 : X.Opens)) (φ ⁻¹ᵁ U)
      (fun i => i.2) ?_ _ _ ?_
    · intro x hx
      obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open hx (φ ⁻¹ᵁ U).2
      exact ⟨⟨⟨W, hW⟩, hWU⟩, hxW⟩
    · rintro ⟨⟨W, hW⟩, hWU⟩
      let _ : Algebra A Γ(Y, U) := gY.sectionsAlgebra U
      let _ : Algebra B Γ(X, W) := gX.sectionsAlgebra W
      let : Algebra Γ(Y, U) Γ(X, W) := (φ.appLE U W hWU).hom.toAlgebra
      let : Algebra A Γ(X, W) :=
        ((algebraMap Γ(Y, U) Γ(X, W)).comp (algebraMap A Γ(Y, U))).toAlgebra
      have : IsScalarTower A Γ(Y, U) Γ(X, W) := IsScalarTower.of_algebraMap_eq' rfl
      have : IsScalarTower A B Γ(X, W) :=
        IsScalarTower.of_algebraMap_eq' (RingHom.ext fun a => Locality.algebraMap_comm gY gX φ hφ U
            W hWU a)
      exact (hθ U hU W hW hWU η).trans (hθ' U hU W hW hWU η).symm
  apply Scheme.Modules.pullback_hom_ext
  intro U s
  refine AffineSections.sec_ext (gX.topDifferentials d)
    (fun i : {U' : Y.affineOpens // (U' : Y.Opens) ≤ U} => φ ⁻¹ᵁ (i.1 : Y.Opens)) (φ ⁻¹ᵁ U)
    (fun i => fun x hx => i.2 hx) ?_ _ _ ?_
  · intro x hx
    obtain ⟨_, ⟨U', hU', rfl⟩, hxU', hU'U⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
    exact ⟨⟨⟨U', hU'⟩, hU'U⟩, hxU'⟩
  · rintro ⟨⟨U', hU'⟩, hU'U⟩
    rw [Locality.app_naturality, Locality.app_naturality,
      Scheme.Modules.map_homOfLE_pullbackLocalSection φ hU'U]
    exact key U' hU' _

end SchemeTheory.DifferentialPullback
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_eq_pullbackComp_inv_app_comp_map_comp_of_map_pullbackLocalSection_topToSections_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.DifferentialPullback

open AbelianVarieties.NOSProofs.AffineGluing

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

open TopologicalSpace

end SchemeTheory.DifferentialPullback

namespace AlgebraicGeometry.Scheme.Hom

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AbelianVarieties.NOSProofs.AffineGluing
open scoped TensorProduct

universe u

open SchemeTheory.DifferentialPullback

theorem eq_pullbackComp_inv_app_comp_map_comp_of_map_pullbackLocalSection_topToSections_eq
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C] [Algebra A
        C]
    [IsScalarTower A B C]
    {X Y Z : Scheme.{u}} (gZ : Z ⟶ Spec (CommRingCat.of A)) (gY : Y ⟶ Spec (CommRingCat.of B))
    (gX : X ⟶ Spec (CommRingCat.of C))
    (ψ : Y ⟶ Z) (hψ : ψ ≫ gZ = gY ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)))
    (φ : X ⟶ Y) (hφ : φ ≫ gY = gX ≫ Spec.map (CommRingCat.ofHom (algebraMap B C))) (d : ℕ)
    (θψ : (Scheme.Modules.pullback ψ).obj (gZ.topDifferentials d) ⟶ gY.topDifferentials d)
    (hθψ : ∀ (U : Z.Opens) (_hU : IsAffineOpen U) (W : Y.Opens) (_hW : IsAffineOpen W) (hWU : W ≤ ψ
        ⁻¹ᵁ U),
        letI := gZ.sectionsAlgebra U; letI := gY.sectionsAlgebra W
        letI : Algebra Γ(Z, U) Γ(Y, W) := (ψ.appLE U W hWU).hom.toAlgebra
        ∀ [Algebra A Γ(Y, W)] [IsScalarTower A B Γ(Y, W)] [IsScalarTower A Γ(Z, U) Γ(Y, W)]
          (η : ⋀[Γ(Z, U)]^d (gZ.kaehlerPresheaf.obj (op U))),
          (gY.topDifferentials d).presheaf.map (homOfLE hWU).op
              (θψ.app (ψ ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection ψ (gZ.topToSections d U η))) =
            gY.topToSections d W (NeronModelInfra.TopFormOrder.topFormMap A B Γ(Z, U) Γ(Y, W) d η))
    (θφ : (Scheme.Modules.pullback φ).obj (gY.topDifferentials d) ⟶ gX.topDifferentials d)
    (hθφ : ∀ (U : Y.Opens) (_ : IsAffineOpen U) (W : X.Opens) (_ : IsAffineOpen W) (hWU : W ≤ φ
        ⁻¹ᵁ U),
        letI := gY.sectionsAlgebra U; letI := gX.sectionsAlgebra W
        letI : Algebra Γ(Y, U) Γ(X, W) := (φ.appLE U W hWU).hom.toAlgebra
        ∀ [Algebra B Γ(X, W)] [IsScalarTower B C Γ(X, W)] [IsScalarTower B Γ(Y, U) Γ(X, W)]
          (η : ⋀[Γ(Y, U)]^d (gY.kaehlerPresheaf.obj (op U))),
          (gX.topDifferentials d).presheaf.map (homOfLE hWU).op
              (θφ.app (φ ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection φ (gY.topToSections d U η))) =
            gX.topToSections d W (NeronModelInfra.TopFormOrder.topFormMap B C Γ(Y, U) Γ(X, W) d η))
    (θ : (Scheme.Modules.pullback (φ ≫ ψ)).obj (gZ.topDifferentials d) ⟶ gX.topDifferentials d)
    (hθ : ∀ (U : Z.Opens) (_ : IsAffineOpen U) (W : X.Opens) (_ : IsAffineOpen W) (hWU : W ≤ (φ ≫
        ψ) ⁻¹ᵁ U),
        letI := gZ.sectionsAlgebra U; letI := gX.sectionsAlgebra W
        letI : Algebra Γ(Z, U) Γ(X, W) := ((φ ≫ ψ).appLE U W hWU).hom.toAlgebra
        ∀ [Algebra A Γ(X, W)] [IsScalarTower A C Γ(X, W)] [IsScalarTower A Γ(Z, U) Γ(X, W)]
          (η : ⋀[Γ(Z, U)]^d (gZ.kaehlerPresheaf.obj (op U))),
          (gX.topDifferentials d).presheaf.map (homOfLE hWU).op
              (θ.app ((φ ≫ ψ) ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection (φ ≫ ψ) (gZ.topToSections
                  d U η))) =
            gX.topToSections d W (NeronModelInfra.TopFormOrder.topFormMap A C Γ(Z, U) Γ(X, W) d η))
                :
    θ = ((Scheme.Modules.pullbackComp φ ψ).app (gZ.topDifferentials d)).inv ≫
      (Scheme.Modules.pullback φ).map θψ ≫ θφ := by
  have hφψ : (φ ≫ ψ) ≫ gZ = gX ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)) := by
    rw [Category.assoc, hψ, ← Category.assoc, hφ, Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq A B C]
  have e2 : ∀ (U : Z.Opens) (s : Γ(gZ.topDifferentials d, U)),
      ((((Scheme.Modules.pullbackComp φ ψ).app (gZ.topDifferentials d)).inv ≫
        (Scheme.Modules.pullback φ).map θψ ≫ θφ).app ((φ ≫ ψ) ⁻¹ᵁ U))
          (Scheme.Modules.pullbackLocalSection (φ ≫ ψ) s) =
        θφ.app (φ ⁻¹ᵁ (ψ ⁻¹ᵁ U)) (Scheme.Modules.pullbackLocalSection φ
          (θψ.app (ψ ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection ψ s))) := by
    intro U s
    have key : (((Scheme.Modules.pullbackComp φ ψ).app (gZ.topDifferentials d)).inv).app ((φ ≫ ψ)
        ⁻¹ᵁ U)
        (Scheme.Modules.pullbackLocalSection (φ ≫ ψ) s) =
        Scheme.Modules.pullbackLocalSection φ (Scheme.Modules.pullbackLocalSection ψ s) :=
      congrFun (congrArg (fun f => (ConcreteCategory.hom f : Γ(gZ.topDifferentials d, U) →
          Γ((Scheme.Modules.pullback φ).obj ((Scheme.Modules.pullback ψ).obj (gZ.topDifferentials
              d)),
            (φ ≫ ψ) ⁻¹ᵁ U)))
        (Scheme.Modules.unit_app_comp_pullbackComp_inv φ ψ (gZ.topDifferentials d) U)) s
    rw [Scheme.Modules.pullbackLocalSection_app, Scheme.Modules.Hom.comp_app,
        Scheme.Modules.Hom.comp_app,
      CategoryTheory.comp_apply, CategoryTheory.comp_apply, key]
    rfl
  refine AlgebraicGeometry.Scheme.Hom.eq_of_map_pullbackLocalSection_topToSections_eq gZ gX (φ ≫ ψ)
      hφψ d
    θ _ hθ ?_
  intro U hU W hW hWU iA iT₁ iT₂ η
  rw [e2 U (gZ.topToSections d U η), ← hθ U hU W hW hWU η]
  let ι : Type u := {p : Y.affineOpens × X.affineOpens //
    (p.1 : Y.Opens) ≤ ψ ⁻¹ᵁ U ∧ (p.2 : X.Opens) ≤ W ∧ (p.2 : X.Opens) ≤ φ ⁻¹ᵁ (p.1 : Y.Opens)}
  refine AffineSections.sec_ext (gX.topDifferentials d) (fun i : ι => (i.1.2 : X.Opens)) W (fun i =>
      i.2.2.1)
    ?_ _ _ ?_
  · intro x hx
    have hx' : φ.base x ∈ (ψ ⁻¹ᵁ U : Y.Opens) := hWU hx
    obtain ⟨_, ⟨W', hW', rfl⟩, hxW', hW'U⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open hx' (ψ ⁻¹ᵁ U).2
    have hx'' : x ∈ (W ⊓ φ ⁻¹ᵁ W' : X.Opens) := ⟨hx, hxW'⟩
    obtain ⟨_, ⟨W₀, hW₀, rfl⟩, hxW₀, hW₀le⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hx'' (W ⊓ φ ⁻¹ᵁ W').2
    exact ⟨⟨⟨⟨W', hW'⟩, ⟨W₀, hW₀⟩⟩, hW'U, fun y hy => (hW₀le hy).1, fun y hy => (hW₀le hy).2⟩, hxW₀⟩
  · rintro ⟨⟨⟨W', hW'⟩, ⟨W₀, hW₀⟩⟩, hW'U, hW₀W, hW₀W'⟩
    have h₀ : W₀ ≤ (φ ≫ ψ) ⁻¹ᵁ U := hW₀W.trans hWU
    have hφW' : φ ⁻¹ᵁ W' ≤ φ ⁻¹ᵁ (ψ ⁻¹ᵁ U) := fun y hy => hW'U hy
    let algAU : Algebra A Γ(Z, U) := gZ.sectionsAlgebra U
    let algBW : Algebra B Γ(Y, W') := gY.sectionsAlgebra W'
    let algCW : Algebra C Γ(X, W₀) := gX.sectionsAlgebra W₀
    let algUW : Algebra Γ(Z, U) Γ(Y, W') := (ψ.appLE U W' hW'U).hom.toAlgebra
    let algWW : Algebra Γ(Y, W') Γ(X, W₀) := (φ.appLE W' W₀ hW₀W').hom.toAlgebra
    let algUW₀ : Algebra Γ(Z, U) Γ(X, W₀) := ((φ ≫ ψ).appLE U W₀ h₀).hom.toAlgebra
    have towerUWW : IsScalarTower Γ(Z, U) Γ(Y, W') Γ(X, W₀) := IsScalarTower.of_algebraMap_eq' (by
      change ((φ ≫ ψ).appLE U W₀ h₀).hom = (φ.appLE W' W₀ hW₀W').hom.comp (ψ.appLE U W' hW'U).hom
      rw [← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE])
    let algAW : Algebra A Γ(Y, W') := ((algebraMap Γ(Z, U) Γ(Y, W')).comp (algebraMap A Γ(Z,
        U))).toAlgebra
    have towerAUW : IsScalarTower A Γ(Z, U) Γ(Y, W') := IsScalarTower.of_algebraMap_eq' rfl
    have towerABW : IsScalarTower A B Γ(Y, W') :=
      IsScalarTower.of_algebraMap_eq' (RingHom.ext fun a => Locality.algebraMap_comm gZ gY ψ hψ U W'
          hW'U a)
    let algBW₀ : Algebra B Γ(X, W₀) := ((algebraMap Γ(Y, W') Γ(X, W₀)).comp (algebraMap B Γ(Y,
        W'))).toAlgebra
    have towerBWW : IsScalarTower B Γ(Y, W') Γ(X, W₀) := IsScalarTower.of_algebraMap_eq' rfl
    have towerBCW : IsScalarTower B C Γ(X, W₀) :=
      IsScalarTower.of_algebraMap_eq' (RingHom.ext fun b => Locality.algebraMap_comm gY gX φ hφ W'
          W₀ hW₀W' b)
    let algAW₀ : Algebra A Γ(X, W₀) := ((algebraMap Γ(Z, U) Γ(X, W₀)).comp (algebraMap A Γ(Z,
        U))).toAlgebra
    have towerAUW₀ : IsScalarTower A Γ(Z, U) Γ(X, W₀) := IsScalarTower.of_algebraMap_eq' rfl
    have towerACW : IsScalarTower A C Γ(X, W₀) :=
      IsScalarTower.of_algebraMap_eq' (RingHom.ext fun a =>
        Locality.algebraMap_comm gZ gX (φ ≫ ψ) hφψ U W₀ h₀ a)
    conv_rhs =>
      rw [AffineSections.map_map (gX.topDifferentials d) (homOfLE hWU) (homOfLE hW₀W) (homOfLE h₀),
        hθ U hU W₀ hW₀ h₀ η]
    have h₀' : W₀ ≤ φ ⁻¹ᵁ (ψ ⁻¹ᵁ U) := hW₀W'.trans hφW'
    refine (AffineSections.map_map (gX.topDifferentials d)
      (homOfLE hWU) (homOfLE hW₀W) (homOfLE h₀) _).trans ?_
    refine (AffineSections.map_map (gX.topDifferentials d)
      (homOfLE hφW') (homOfLE hW₀W') (homOfLE h₀') _).symm.trans ?_
    rw [Locality.app_naturality θφ (homOfLE hφW'),
      Scheme.Modules.map_homOfLE_pullbackLocalSection φ hW'U,
      hθψ U hU W' hW' hW'U η]
    have hcomp := @NeronModelInfra.TopFormOrder.topFormMap_topFormMap
      A B C Γ(Z, U) Γ(Y, W') Γ(X, W₀) _ _ _ _ _ _ _ _ _ _
      algAU algBW algCW algUW algWW algUW₀ towerUWW
      algAW towerAUW towerABW algBW₀ towerBWW towerBCW
      algAW₀ towerAUW₀ towerACW d η
    refine (hθφ W' hW' W₀ hW₀ hW₀W'
      (NeronModelInfra.TopFormOrder.topFormMap A B Γ(Z, U) Γ(Y, W') d η)).trans ?_
    exact congrArg (gX.topToSections d W₀) hcomp

end AlgebraicGeometry.Scheme.Hom
end
