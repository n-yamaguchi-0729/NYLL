/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.SchemeTheory.Morphisms.AppLECongr
public import Nyll.AlgebraicCurves.Geometry.Projective.ChartSectionsBaseChange
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Ext
public import Nyll.SchemeTheory.ProjectiveSpace.Basic
public import Nyll.SchemeTheory.ProjectiveSpace.Cover
public import Nyll.AlgebraicCurves.Geometry.Projective.ProjTwistDatum
public import Nyll.AlgebraicCurves.Geometry.Schemes.Covers.OrderedAffineCoverComap
public import Nyll.AlgebraicCurves.Geometry.Projective.ProjSpaceLinearEquivTwistObj
public import Nyll.AlgebraicCurves.Geometry.Schemes.Sections.IsAffineOpenLinearEquivTensorSections
public import Nyll.SchemeTheory.ProjectiveSpace.StandardChartsBaseChange

/-!
# Proj Space exists linear Equiv base Change cochain twist of is Pullback
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs
namespace ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

open HomogeneousLocalization

namespace P2mWs6C3

open ProjSpace.ChartSectionsBaseChange (
  X_eq_mvMapGraded_mul_one inter_le_pullbackChart isAffineOpen_inter one_mem_zero
  preimage_inter preimage_pullbackChart restrictFun_app_eq restrictFun_app_frameUnit
  restrictFun_app_pullAway toB toB_ratio
)

section Setup

variable {A : Type u} [CommRing A] {n : ℕ} {Z : Scheme.{u}}
  (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsAffineHom ι]
  (B : Type u) [CommRing B] [Algebra A B] {Z' : Scheme.{u}}
  (ι' : Z' ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B)) [IsAffineHom ι']
  (e : Z' ⟶ Z)

local notation "𝒜A" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A
local notation "𝒜B" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B

theorem appLE_hom_apply {X Y : Scheme.{u}} (g : X ⟶ Y) (U : Y.Opens) (V : X.Opens) (h : V ≤ g ⁻¹ᵁ
  U) (x : Γ(Y, U)) :
    (g.appLE U V h).hom x = ProjSpace.restrictFun h ((g.app U).hom x) := rfl

end Setup

/-- Evaluation of all chart components of a twist section as an additive map. -/
noncomputable def valAddHom {R : Type u} [CommRing R] {n : ℕ} {X : Scheme.{u}} (π : X ⟶ Spec (.of
  R))
    (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) (m : ℕ) (U : X.Opens) :
    ProjSpace.twistObj π φ m U →+ (∀ j : Fin (n + 1), Γ(X, U ⊓ ProjSpace.pullbackChart φ j)) :=
  { toFun := ProjSpace.twistObj.val
    map_zero' := ProjSpace.twistObj.zero_val
    map_add' := ProjSpace.twistObj.add_val }

theorem val_sum {R : Type u} [CommRing R] {n : ℕ} {X : Scheme.{u}} (π : X ⟶ Spec (.of R))
    (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) (m : ℕ) (U : X.Opens)
    {κ : Type*} (t : Finset κ) (f : κ → ProjSpace.twistObj π φ m U) :
    (∑ x ∈ t, f x).val = ∑ x ∈ t, (f x).val :=
  map_sum (valAddHom π φ m U) f t

theorem val_zsmul {R : Type u} [CommRing R] {n : ℕ} {X : Scheme.{u}} (π : X ⟶ Spec (.of R))
    (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) (m : ℕ) (U : X.Opens)
    (z : ℤ) (g : ProjSpace.twistObj π φ m U) : (z • g).val = z • g.val :=
  map_zsmul (valAddHom π φ m U) z g

theorem val_sum' {R : Type u} [CommRing R] {n : ℕ} {X : Scheme.{u}} (π : X ⟶ Spec (.of R))
    (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) [IsAffineHom φ] (m : ℕ) (U :
      X.Opens)
    {κ : Type*} (t : Finset κ) (f : κ → (ProjSpace.twist π φ m).obj U) :
    ((∑ x ∈ t, f x : (ProjSpace.twist π φ m).obj U) : ProjSpace.twistObj π φ m U).val
      = ∑ x ∈ t, (f x : ProjSpace.twistObj π φ m U).val :=
  map_sum (valAddHom π φ m U) f t

theorem val_zsmul' {R : Type u} [CommRing R] {n : ℕ} {X : Scheme.{u}} (π : X ⟶ Spec (.of R))
    (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) [IsAffineHom φ] (m : ℕ) (U :
      X.Opens)
    (z : ℤ) (g : (ProjSpace.twist π φ m).obj U) :
    ((z • g : (ProjSpace.twist π φ m).obj U) : ProjSpace.twistObj π φ m U).val = z • (g :
      ProjSpace.twistObj π φ m U).val :=
  map_zsmul (valAddHom π φ m U) z g

end P2mWs6C3

end ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback
end AlgebraicCurves.Cohomology.Sheaves.Proofs

namespace AlgebraicGeometry.ProjSpace

open CategoryTheory CategoryTheory.Limits MvPolynomial TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

open AlgebraicCurves.Cohomology.Sheaves.Proofs in
open _root_.AlgebraicGeometry.ProjSpace.ChartSectionsBaseChange (inter_le_pullbackChart
  preimage_inter isAffineOpen_inter
  preimage_pullbackChart restrictFun_app_eq restrictFun_app_frameUnit) in
open ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback.P2mWs6C3 in
theorem exists_linearEquiv_baseChange_cochain_twist_of_isPullback
    {A : Type u} [CommRing A] {n : ℕ} {Z : Scheme.{u}}
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsAffineHom ι]
    (B : Type u) [CommRing B] [Algebra A B] {Z' : Scheme.{u}}
    (ι' : Z' ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B)) [IsAffineHom ι']
    (e : Z' ⟶ Z)
    (hpb : IsPullback e (ι' ≫ ProjSpace.π B n) (ι ≫ ProjSpace.π A n) (Spec.map (CommRingCat.ofHom
      (algebraMap A B))))
    (hcomp : e ≫ ι = ι' ≫ ProjSpace.map A B n) (d : ℕ) :
    ∃ ε : ∀ i : ℕ,
        B ⊗[A] (ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).cochain (ProjSpace.stdCoverPullback ι) i
          ≃ₗ[B]
          (ProjSpace.twist (ι' ≫ ProjSpace.π B n) ι' d).cochain (ProjSpace.stdCoverPullback ι') i,
      (∀ i : ℕ,
        (ε (i + 1)).toLinearMap ∘ₗ ((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).d
          (ProjSpace.stdCoverPullback ι) i).baseChange B =
          (ProjSpace.twist (ι' ≫ ProjSpace.π B n) ι' d).d (ProjSpace.stdCoverPullback ι') i ∘ₗ (ε
            i).toLinearMap) ∧
      (∀ (i : ℕ) (c : (ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).cochain
        (ProjSpace.stdCoverPullback ι) i)
        (s : (ProjSpace.stdCoverPullback ι).Idx i) (j : Fin (n + 1))
        (h : (ProjSpace.stdCoverPullback ι').inter s ⊓ ProjSpace.pullbackChart ι' j ≤
          e ⁻¹ᵁ ((ProjSpace.stdCoverPullback ι).inter s ⊓ ProjSpace.pullbackChart ι j)),
        (ε i ((1 : B) ⊗ₜ[A] c) s).val j =
          ProjSpace.restrictFun h ((e.app ((ProjSpace.stdCoverPullback ι).inter s ⊓
            ProjSpace.pullbackChart ι j)) ((c s).val j))) := by
  classical
  have hU : ∀ (i : ℕ) (s : (ProjSpace.stdCoverPullback ι).Idx i), (ProjSpace.stdCoverPullback
    ι).inter s ≤ ProjSpace.pullbackChart ι (s.1 0).down :=
    fun i s => inter_le_pullbackChart ι s 0
  have hU' : ∀ (i : ℕ) (s : (ProjSpace.stdCoverPullback ι).Idx i), (ProjSpace.stdCoverPullback
    ι').inter s ≤ ProjSpace.pullbackChart ι' (s.1 0).down :=
    fun i s => inter_le_pullbackChart ι' s 0
  have hpre : ∀ (i : ℕ) (s : (ProjSpace.stdCoverPullback ι).Idx i), e ⁻¹ᵁ
    (ProjSpace.stdCoverPullback ι).inter s = (ProjSpace.stdCoverPullback ι').inter s :=
    fun i s => preimage_inter ι B ι' e hcomp s
  have tU : ∀ (i : ℕ) (s : (ProjSpace.stdCoverPullback ι).Idx i), ∃ f : ProjSpace.twistObj (ι ≫
    ProjSpace.π A n) ι d ((ProjSpace.stdCoverPullback ι).inter s) ≃ₗ[Γ(Z,
    (ProjSpace.stdCoverPullback ι).inter s)] Γ(Z, (ProjSpace.stdCoverPullback ι).inter s),
      (∀ g, ProjSpace.restrictFun (inf_le_left : (ProjSpace.stdCoverPullback ι).inter s ⊓
        ProjSpace.pullbackChart ι (s.1 0).down ≤ (ProjSpace.stdCoverPullback ι).inter s) (f g)
          = g.val (s.1 0).down) ∧
      (∀ (a : Γ(Z, (ProjSpace.stdCoverPullback ι).inter s)) (j : Fin (n + 1)), (f.symm a).val j =
          ProjSpace.restrictFun (inf_le_right : (ProjSpace.stdCoverPullback ι).inter s ⊓
            ProjSpace.pullbackChart ι j ≤ ProjSpace.pullbackChart ι j)
              (ProjSpace.frameUnit ι j (s.1 0).down) ^ d *
            ProjSpace.restrictFun (inf_le_left : (ProjSpace.stdCoverPullback ι).inter s ⊓
              ProjSpace.pullbackChart ι j ≤ (ProjSpace.stdCoverPullback ι).inter s) a) :=
    fun i s => AlgebraicGeometry.ProjSpace.exists_linearEquiv_twistObj_of_le_pullbackChart (ι ≫
      ProjSpace.π A n) ι d (hU i s)
  have tU' : ∀ (i : ℕ) (s : (ProjSpace.stdCoverPullback ι).Idx i), ∃ f : ProjSpace.twistObj (ι' ≫
    ProjSpace.π B n) ι' d ((ProjSpace.stdCoverPullback ι').inter s) ≃ₗ[Γ(Z',
    (ProjSpace.stdCoverPullback ι').inter s)] Γ(Z', (ProjSpace.stdCoverPullback ι').inter s),
      (∀ g, ProjSpace.restrictFun (inf_le_left : (ProjSpace.stdCoverPullback ι').inter s ⊓
        ProjSpace.pullbackChart ι' (s.1 0).down ≤ (ProjSpace.stdCoverPullback ι').inter s) (f g)
          = g.val (s.1 0).down) ∧
      (∀ (a : Γ(Z', (ProjSpace.stdCoverPullback ι').inter s)) (j : Fin (n + 1)), (f.symm a).val j =
          ProjSpace.restrictFun (inf_le_right : (ProjSpace.stdCoverPullback ι').inter s ⊓
            ProjSpace.pullbackChart ι' j ≤ ProjSpace.pullbackChart ι' j)
              (ProjSpace.frameUnit ι' j (s.1 0).down) ^ d *
            ProjSpace.restrictFun (inf_le_left : (ProjSpace.stdCoverPullback ι').inter s ⊓
              ProjSpace.pullbackChart ι' j ≤ (ProjSpace.stdCoverPullback ι').inter s) a) :=
    fun i s => AlgebraicGeometry.ProjSpace.exists_linearEquiv_twistObj_of_le_pullbackChart (ι' ≫
      ProjSpace.π B n) ι' d (hU' i s)
  choose fU hfU1 hfU2 using tU
  choose fU' hfU'1 hfU'2 using tU'
  let instZ : ∀ U : Z.Opens, Algebra A Γ(Z, U) := fun U => Scheme.TwoAffineOpenCover.algebraOfHom
    (ι ≫ ProjSpace.π A n) U
  let instS : ∀ V : (Spec (CommRingCat.of B)).Opens, Algebra A Γ(Spec (CommRingCat.of B), V) :=
    fun V => Scheme.TwoAffineOpenCover.algebraOfHom (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      V
  let instZ'A : ∀ W : Z'.Opens, Algebra A Γ(Z', W) := fun W =>
    Scheme.TwoAffineOpenCover.algebraOfHom (e ≫ (ι ≫ ProjSpace.π A n)) W
  have hΦ : ∀ (i : ℕ) (s : (ProjSpace.stdCoverPullback ι).Idx i), ∃ Φ : Γ(Z,
    (ProjSpace.stdCoverPullback ι).inter s) ⊗[A] Γ(Spec (CommRingCat.of B), (⊤ : (Spec
    (CommRingCat.of B)).Opens))
        ≃ₗ[A] Γ(Z', e ⁻¹ᵁ (ProjSpace.stdCoverPullback ι).inter s ⊓ (ι' ≫ ProjSpace.π B n) ⁻¹ᵁ ⊤),
      ∀ (a : Γ(Z, (ProjSpace.stdCoverPullback ι).inter s)) (b : Γ(Spec (CommRingCat.of B), (⊤ :
        (Spec (CommRingCat.of B)).Opens))), Φ (a ⊗ₜ[A] b) =
        (e.appLE ((ProjSpace.stdCoverPullback ι).inter s) (e ⁻¹ᵁ (ProjSpace.stdCoverPullback
          ι).inter s ⊓ (ι' ≫ ProjSpace.π B n) ⁻¹ᵁ ⊤) inf_le_left).hom a *
          ((ι' ≫ ProjSpace.π B n).appLE ⊤ (e ⁻¹ᵁ (ProjSpace.stdCoverPullback ι).inter s ⊓ (ι' ≫
            ProjSpace.π B n) ⁻¹ᵁ ⊤) inf_le_right).hom b :=
    fun i s =>
      (AlgebraicGeometry.Scheme.isAffineOpen_and_exists_linearEquiv_tensor_sections_of_isPullback
      (ι ≫ ProjSpace.π A n) (Spec.map (CommRingCat.ofHom (algebraMap A B))) e (ι' ≫ ProjSpace.π B
        n) hpb ((ProjSpace.stdCoverPullback ι).inter s) (isAffineOpen_inter ι s) ⊤
      (isAffineOpen_top (Spec (CommRingCat.of B)))).2
  choose Φ hΦ using hΦ
  have hβalg : ∀ a : A, (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (algebraMap A B a)
      = (instS ⊤).algebraMap a := by
    intro a
    rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom]
    erw [Scheme.Hom.appLE_top_eq_appTop]
    have nat := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A B))
    have := congrArg (fun ψ => ψ.hom a) nat
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    exact this
  let β : B ≃ₗ[A] Γ(Spec (CommRingCat.of B), (⊤ : (Spec (CommRingCat.of B)).Opens)) :=
    AddEquiv.toLinearEquiv (Scheme.ΓSpecIso (CommRingCat.of
      B)).commRingCatIsoToRingEquiv.symm.toAddEquiv (by
      intro a b
      change (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (a • b) = a • (Scheme.ΓSpecIso
        (CommRingCat.of B)).inv.hom b
      rw [Algebra.smul_def, map_mul, hβalg, Algebra.smul_def])
  have hβ : ∀ b : B, β b = (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b := fun _ => rfl
  have h1 : ∀ (i : ℕ) (s : (ProjSpace.stdCoverPullback ι).Idx i), (ProjSpace.stdCoverPullback
    ι').inter s ≤ e ⁻¹ᵁ (ProjSpace.stdCoverPullback ι).inter s ⊓ (ι' ≫ ProjSpace.π B n) ⁻¹ᵁ ⊤ :=
    fun i s => le_inf (hpre i s).ge le_top
  have h2 : ∀ (i : ℕ) (s : (ProjSpace.stdCoverPullback ι).Idx i), e ⁻¹ᵁ (ProjSpace.stdCoverPullback
    ι).inter s ⊓ (ι' ≫ ProjSpace.π B n) ⁻¹ᵁ ⊤ ≤ (ProjSpace.stdCoverPullback ι').inter s :=
    fun i s => inf_le_left.trans (hpre i s).le
  let ρ : ∀ (i : ℕ) (s : (ProjSpace.stdCoverPullback ι).Idx i), Γ(Z', e ⁻¹ᵁ
    (ProjSpace.stdCoverPullback ι).inter s ⊓ (ι' ≫ ProjSpace.π B n) ⁻¹ᵁ ⊤) ≃+ Γ(Z',
    (ProjSpace.stdCoverPullback ι').inter s) := fun i s =>
    { toFun := ProjSpace.restrictFun (h1 i s)
      invFun := ProjSpace.restrictFun (h2 i s)
      left_inv := fun x => by
        show ProjSpace.restrictFun (h2 i s) (ProjSpace.restrictFun (h1 i s) x) = x
        rw [ProjSpace.restrictFun_restrictFun]; exact ProjSpace.restrictFun_refl x
      right_inv := fun x => by
        show ProjSpace.restrictFun (h1 i s) (ProjSpace.restrictFun (h2 i s) x) = x
        rw [ProjSpace.restrictFun_restrictFun]; exact ProjSpace.restrictFun_refl x
      map_add' := fun x y => map_add _ x y }
  have hρ : ∀ (i : ℕ) (s : (ProjSpace.stdCoverPullback ι).Idx i) x, ρ i s x = ProjSpace.restrictFun
    (h1 i s) x := fun _ _ _ => rfl
  have hst : ∀ (i : ℕ) (s : (ProjSpace.stdCoverPullback ι).Idx i), IsScalarTower A Γ(Z,
    (ProjSpace.stdCoverPullback ι).inter s) (ProjSpace.twistObj (ι ≫ ProjSpace.π A n) ι d
    ((ProjSpace.stdCoverPullback ι).inter s)) :=
    fun i s => (ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).isScalarTower _
  let fUA : ∀ (i : ℕ) (s : (ProjSpace.stdCoverPullback ι).Idx i), ProjSpace.twistObj (ι ≫
    ProjSpace.π A n) ι d ((ProjSpace.stdCoverPullback ι).inter s) ≃ₗ[A] Γ(Z,
    (ProjSpace.stdCoverPullback ι).inter s) :=
    fun i s => (fU i s).restrictScalars A
  have hfUA : ∀ (i : ℕ) (s : (ProjSpace.stdCoverPullback ι).Idx i) g, fUA i s g = fU i s g := fun _
    _ _ => rfl
  let εs : ∀ (i : ℕ) (s : (ProjSpace.stdCoverPullback ι).Idx i), B ⊗[A] ProjSpace.twistObj (ι ≫
    ProjSpace.π A n) ι d ((ProjSpace.stdCoverPullback ι).inter s) ≃+ ProjSpace.twistObj (ι' ≫
    ProjSpace.π B n) ι' d ((ProjSpace.stdCoverPullback ι').inter s) := fun i s =>
    ((((((fUA i s).baseChange A B _ _).toAddEquiv.trans (TensorProduct.comm A B Γ(Z,
      (ProjSpace.stdCoverPullback ι).inter s)).toAddEquiv).trans
      (TensorProduct.congr (LinearEquiv.refl A Γ(Z, (ProjSpace.stdCoverPullback ι).inter s))
        β).toAddEquiv).trans (Φ i s).toAddEquiv).trans
      (ρ i s)).trans (fU' i s).symm.toAddEquiv
  have keyform : ∀ (i : ℕ) (s : (ProjSpace.stdCoverPullback ι).Idx i) (c : B) (g :
    ProjSpace.twistObj (ι ≫ ProjSpace.π A n) ι d ((ProjSpace.stdCoverPullback ι).inter s)),
      εs i s (c ⊗ₜ[A] g) = c • (fU' i s).symm (ProjSpace.restrictFun ((h1 i s).trans inf_le_left)
        ((e.app ((ProjSpace.stdCoverPullback ι).inter s)).hom (fU i s g))) := by
    intro i s c g
    change (fU' i s).symm (ρ i s (Φ i s ((TensorProduct.congr (LinearEquiv.refl A Γ(Z,
      (ProjSpace.stdCoverPullback ι).inter s)) β)
      ((TensorProduct.comm A B Γ(Z, (ProjSpace.stdCoverPullback ι).inter s)) (((fUA i s).baseChange
        A B _ _) (c ⊗ₜ[A] g)))))) = _
    rw [LinearEquiv.baseChange_tmul, hfUA, TensorProduct.comm_tmul, TensorProduct.congr_tmul,
      LinearEquiv.refl_apply, hβ,
      hΦ, hρ, map_mul]
    have hc : ((ι' ≫ ProjSpace.π B n).appLE ⊤ (e ⁻¹ᵁ (ProjSpace.stdCoverPullback ι).inter s ⊓ (ι' ≫
      ProjSpace.π B n) ⁻¹ᵁ ⊤) inf_le_right).hom
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom c)
        = (Scheme.TwoAffineOpenCover.algebraOfHom (ι' ≫ ProjSpace.π B n) (e ⁻¹ᵁ
          (ProjSpace.stdCoverPullback ι).inter s ⊓ (ι' ≫ ProjSpace.π B n) ⁻¹ᵁ ⊤)).algebraMap c :=
          rfl
    rw [hc, ProjSpace.restrictFun_algebraMap' (ι' ≫ ProjSpace.π B n), appLE_hom_apply,
      ProjSpace.restrictFun_restrictFun, mul_comm,
      ← smul_eq_mul, LinearEquiv.map_smul]
    exact (ProjSpace.twistObj.algebraMap_smul c _).symm
  let ω : ∀ (i : ℕ) (s : (ProjSpace.stdCoverPullback ι).Idx i), ProjSpace.twistObj (ι ≫ ProjSpace.π
    A n) ι d ((ProjSpace.stdCoverPullback ι).inter s) → ProjSpace.twistObj (ι' ≫ ProjSpace.π B n)
    ι' d ((ProjSpace.stdCoverPullback ι').inter s) := fun i s g =>
    (fU' i s).symm (ProjSpace.restrictFun ((h1 i s).trans inf_le_left) ((e.app
      ((ProjSpace.stdCoverPullback ι).inter s)).hom (fU i s g)))
  have hεs : ∀ (i : ℕ) (s : (ProjSpace.stdCoverPullback ι).Idx i) (c : B) g, εs i s (c ⊗ₜ[A] g) = c
    • ω i s g := keyform
  let εB : ∀ (i : ℕ) (s : (ProjSpace.stdCoverPullback ι).Idx i), B ⊗[A] ProjSpace.twistObj (ι ≫
    ProjSpace.π A n) ι d ((ProjSpace.stdCoverPullback ι).inter s) ≃ₗ[B] ProjSpace.twistObj (ι' ≫
    ProjSpace.π B n) ι' d ((ProjSpace.stdCoverPullback ι').inter s) := fun i s =>
    (εs i s).toLinearEquiv (by
      intro b x
      induction x using TensorProduct.inductionOn with
      | tmul c g => rw [TensorProduct.smul_tmul', smul_eq_mul, hεs, hεs, mul_smul]
      | add x y hx hy => rw [smul_add, map_add, map_add, smul_add, hx, hy])
  have hεB : ∀ (i : ℕ) (s : (ProjSpace.stdCoverPullback ι).Idx i) x, εB i s x = εs i s x := fun _ _
    _ => rfl
  let ε : ∀ i : ℕ, B ⊗[A] (ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).cochain
    (ProjSpace.stdCoverPullback ι) i ≃ₗ[B] (ProjSpace.twist (ι' ≫ ProjSpace.π B n) ι' d).cochain
    (ProjSpace.stdCoverPullback ι') i :=
    fun i =>
      let targetGroups : ∀ s : (ProjSpace.stdCoverPullback ι).Idx i,
          AddCommMonoid (ProjSpace.twistObj (ι' ≫ ProjSpace.π B n) ι' d
            ((ProjSpace.stdCoverPullback ι').inter s)) := fun s =>
        ((ProjSpace.twist (ι' ≫ ProjSpace.π B n) ι' d).addCommGroup
          ((ProjSpace.stdCoverPullback ι').inter s)).toAddCommMonoid
      let targetModules : ∀ s : (stdCoverPullback ι).Idx i,
        Module B (twistObj (ι' ≫ π B n) ι' d ((stdCoverPullback ι').inter s)) :=
        fun s => (twist (ι' ≫ π B n) ι' d).module ((stdCoverPullback ι').inter s)
      let ePi := LinearEquiv.piCongrRight (R := B)
        (fun s : (ProjSpace.stdCoverPullback ι).Idx i => εB i s)
      (TensorProduct.piRight A B B (fun s : (ProjSpace.stdCoverPullback ι).Idx i =>
        ProjSpace.twistObj (ι ≫ ProjSpace.π A n) ι d
          ((ProjSpace.stdCoverPullback ι).inter s))).trans ePi
  have hε1 : ∀ (i : ℕ) (c : (ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).cochain
    (ProjSpace.stdCoverPullback ι) i) (s : (ProjSpace.stdCoverPullback ι).Idx i),
      ε i ((1 : B) ⊗ₜ[A] c) s = ω i s (c s) := by
    intro i c s
    have hpi := congrFun (TensorProduct.piRightHom_tmul A B B
      (fun s : (ProjSpace.stdCoverPullback ι).Idx i =>
        ProjSpace.twistObj (ι ≫ ProjSpace.π A n) ι d
          ((ProjSpace.stdCoverPullback ι).inter s)) (1 : B) c) s
    exact (congrArg (εB i s) hpi).trans
      ((hεB i s ((1 : B) ⊗ₜ[A] c s)).trans
        ((hεs i s 1 (c s)).trans (one_smul B (ω i s (c s)))))
  have hval : ∀ (i : ℕ) (c : (ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).cochain
    (ProjSpace.stdCoverPullback ι) i)
      (s : (ProjSpace.stdCoverPullback ι).Idx i) (j : Fin (n + 1))
      (h : (ProjSpace.stdCoverPullback ι').inter s ⊓ ProjSpace.pullbackChart ι' j ≤ e ⁻¹ᵁ
        ((ProjSpace.stdCoverPullback ι).inter s ⊓ ProjSpace.pullbackChart ι j)),
      (ε i ((1 : B) ⊗ₜ[A] c) s).val j =
        ProjSpace.restrictFun h ((e.app ((ProjSpace.stdCoverPullback ι).inter s ⊓
          ProjSpace.pullbackChart ι j)) ((c s).val j)) := by
    intro i c s j h
    rw [hε1]
    change ((fU' i s).symm (ProjSpace.restrictFun ((h1 i s).trans inf_le_left) ((e.app
      ((ProjSpace.stdCoverPullback ι).inter s)).hom (fU i s (c s))))).val j = _
    rw [hfU'2, ProjSpace.restrictFun_restrictFun]
    have hVj : (ProjSpace.stdCoverPullback ι').inter s ⊓ ProjSpace.pullbackChart ι' j ≤ e ⁻¹ᵁ
      ProjSpace.pullbackChart ι j := by
      rw [preimage_pullbackChart ι B ι' e hcomp]; exact inf_le_right
    have hV0 : (ProjSpace.stdCoverPullback ι').inter s ⊓ ProjSpace.pullbackChart ι' j ≤ e ⁻¹ᵁ
      ProjSpace.pullbackChart ι (s.1 0).down :=
      inf_le_left.trans ((hpre i s).ge.trans (e.preimage_mono (hU i s)))
    have hVU : (ProjSpace.stdCoverPullback ι').inter s ⊓ ProjSpace.pullbackChart ι' j ≤ e ⁻¹ᵁ
      (ProjSpace.stdCoverPullback ι).inter s := inf_le_left.trans (hpre i s).ge
    have hVV : (ProjSpace.stdCoverPullback ι').inter s ⊓ ProjSpace.pullbackChart ι' j ≤ e ⁻¹ᵁ
      (((ProjSpace.stdCoverPullback ι).inter s ⊓ ProjSpace.pullbackChart ι j) ⊓
      ProjSpace.pullbackChart ι (s.1 0).down) :=
      le_inf h hV0
    have hW : (ProjSpace.stdCoverPullback ι').inter s ⊓ ProjSpace.pullbackChart ι' j ≤ e ⁻¹ᵁ
      ((ProjSpace.stdCoverPullback ι).inter s ⊓ ProjSpace.pullbackChart ι (s.1 0).down) := le_inf
      hVU hV0
    rw [← restrictFun_app_eq e (inf_le_left : ((ProjSpace.stdCoverPullback ι).inter s ⊓
      ProjSpace.pullbackChart ι j) ⊓ ProjSpace.pullbackChart ι (s.1 0).down ≤
      (ProjSpace.stdCoverPullback ι).inter s ⊓ ProjSpace.pullbackChart ι j) hVV h
      ((c s).val j), (c s).compat j (s.1 0).down]
    let ψ := (ProjSpace.restrictFun hVV).comp (e.app (((ProjSpace.stdCoverPullback ι).inter s ⊓
      ProjSpace.pullbackChart ι j) ⊓ ProjSpace.pullbackChart ι (s.1 0).down)).hom
    have hψ : ∀ x, ψ x = ProjSpace.restrictFun hVV ((e.app (((ProjSpace.stdCoverPullback ι).inter s
      ⊓ ProjSpace.pullbackChart ι j) ⊓ ProjSpace.pullbackChart ι (s.1 0).down)).hom x) :=
      fun _ => rfl
    rw [← hψ, map_mul, map_pow, hψ, hψ]
    rw [restrictFun_app_eq e _ hVV hVj, restrictFun_app_frameUnit ι B ι' e hcomp j (s.1 0).down hVj
      inf_le_right,
      restrictFun_app_eq e _ hVV hW, ← hfU1 i s (c s), restrictFun_app_eq e _ hW hVU]
  let V' : ∀ (W : Z'.Opens), ProjSpace.twistObj (ι' ≫ ProjSpace.π B n) ι' d W →+ (∀ j : Fin (n +
    1), Γ(Z', W ⊓ ProjSpace.pullbackChart ι' j)) := fun W =>
    { toFun := ProjSpace.twistObj.val
      map_zero' := ProjSpace.twistObj.zero_val
      map_add' := ProjSpace.twistObj.add_val }
  have hV' : ∀ W (g : ProjSpace.twistObj (ι' ≫ ProjSpace.π B n) ι' d W), V' W g = g.val := fun _ _
    => rfl
  let V : ∀ (W : Z.Opens), ProjSpace.twistObj (ι ≫ ProjSpace.π A n) ι d W →+ (∀ j : Fin (n + 1),
    Γ(Z, W ⊓ ProjSpace.pullbackChart ι j)) := fun W =>
    { toFun := ProjSpace.twistObj.val
      map_zero' := ProjSpace.twistObj.zero_val
      map_add' := ProjSpace.twistObj.add_val }
  have hV : ∀ W (g : ProjSpace.twistObj (ι ≫ ProjSpace.π A n) ι d W), V W g = g.val := fun _ _ =>
    rfl
  refine ⟨ε, ?_, hval⟩
  intro i
  have key1 : ∀ c : (ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).cochain (ProjSpace.stdCoverPullback
    ι) i,
      ε (i + 1) ((1 : B) ⊗ₜ[A] ((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).d
        (ProjSpace.stdCoverPullback ι) i c))
        = (ProjSpace.twist (ι' ≫ ProjSpace.π B n) ι' d).d (ProjSpace.stdCoverPullback ι') i (ε i
          ((1 : B) ⊗ₜ[A] c)) := by
    intro c
    funext s
    apply ProjSpace.twistObj.ext
    funext j
    have hj : ∀ (W : Z'.Opens), W ⊓ ProjSpace.pullbackChart ι' j ≤ e ⁻¹ᵁ ProjSpace.pullbackChart ι
      j := fun W => by
      rw [preimage_pullbackChart ι B ι' e hcomp]; exact inf_le_right
    have hL := hval (i + 1) ((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).d
      (ProjSpace.stdCoverPullback ι) i c) s j
      (show _ ≤ e ⁻¹ᵁ ((ProjSpace.stdCoverPullback ι).inter s ⊓ ProjSpace.pullbackChart ι j) from
        le_inf (inf_le_left.trans (hpre (i + 1) s).ge) (hj _))
    rw [hL, OModulePresheaf.d_apply (ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d)
      (ProjSpace.stdCoverPullback ι) i c s, OModulePresheaf.d_apply]
    erw [val_sum', val_sum']
    simp only [val_zsmul', Finset.sum_apply, Pi.smul_apply,
      map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_zsmul, map_zsmul]
    congr 1
    erw [ProjSpace.twist_res_val (π := ι ≫ ProjSpace.π A n) (φ := ι)
      ((ProjSpace.stdCoverPullback ι).inter_le_inter_face s t) _ j,
      ProjSpace.twist_res_val (π := ι' ≫ ProjSpace.π B n) (φ := ι')
        ((ProjSpace.stdCoverPullback ι').inter_le_inter_face s t) _ j]
    have hface : (ProjSpace.stdCoverPullback ι').inter s ⊓ ProjSpace.pullbackChart ι' j ≤
        (ProjSpace.stdCoverPullback ι').inter ((ProjSpace.stdCoverPullback ι').face s t) ⊓
          ProjSpace.pullbackChart ι' j :=
      inf_le_inf_right _ ((ProjSpace.stdCoverPullback ι').inter_le_inter_face s t)
    have hface' : (ProjSpace.stdCoverPullback ι').inter ((ProjSpace.stdCoverPullback ι').face s t)
      ⊓ ProjSpace.pullbackChart ι' j ≤
        e ⁻¹ᵁ ((ProjSpace.stdCoverPullback ι).inter ((ProjSpace.stdCoverPullback ι).face s t) ⊓
          ProjSpace.pullbackChart ι j) :=
      show _ ≤ e ⁻¹ᵁ ((ProjSpace.stdCoverPullback ι).inter ((ProjSpace.stdCoverPullback ι).face s
        t) ⊓ ProjSpace.pullbackChart ι j) from
        le_inf (inf_le_left.trans (hpre i _).ge) (hj _)
    rw [hval i c ((ProjSpace.stdCoverPullback ι').face s t) j hface']
    exact (restrictFun_app_eq e
      (inf_le_inf_right _ ((ProjSpace.stdCoverPullback ι).inter_le_inter_face s t))
      _ (hface.trans hface') ((c ((ProjSpace.stdCoverPullback ι).face s t)).val j)).trans
        (ProjSpace.restrictFun_restrictFun hface hface' _).symm
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul b c =>
    have hb : ∀ (M : Type u) [AddCommGroup M] [Module A M] (m : M), b ⊗ₜ[A] m = b • ((1 : B) ⊗ₜ[A]
      m) := by
      intro M _ _ m
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearEquiv.coe_coe,
      LinearEquiv.coe_coe,
      hb, hb, LinearEquiv.map_smul, LinearEquiv.map_smul, LinearMap.map_smul, key1]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
end AlgebraicGeometry.ProjSpace
end ProofImplementation
